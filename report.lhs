\documentclass{article}
%include lhs2TeX.fmt
%options -fglasgow-exts

\usepackage{todonotes}
\usepackage{paralist}
\usepackage[top=2cm,left=3.5cm,right=3.5cm,bottom=2cm]{geometry}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{textcomp}
\usepackage{hyperref}

\title{Exploring and Extending Template Haskell \\ An Experience Report}

\author{Dominik Bollmann}
\date{}

\begin{document}
\maketitle

\abstract{In this report, I explore the Glasgow Haskell Compiler's
  (GHC's) compile-time meta programming in Template Haskell (TH). I
  motivate use cases for meta programming, explain the Template
  Haskell features on simple toy programs, and give an overview of
  TH's overall functionality. Furthermore, I review Template Haskell's
  implementation in GHC from a high-level perspective. Lastly, I
  describe my experience of extending the Template Haskell
  implementation inside GHC to also support the newly added
  \texttt{PatternSynonyms} language extension.}

\section{Introduction}

Template Haskell (TH) is the standard framework for doing type-safe,
compile-time meta programming in the Glasgow Haskell Compiler
(GHC). It allows writing Haskell meta programs, which are evaluated at
compile-time, and which produce Haskell programs as the results of
their execution.

Template Haskell was conceived by Tim Sheard and Simon Peyton Jones in
\cite{th1} by drawing on the ideas of Lisp macros, but in the typed
setting of Haskell. Since then, the original implementation has
evolved quite a bit \cite{th2, th3}. Most notably, in 2007 Geoffrey
Mainland added support for quasi quoting \cite{qq}, which makes the
embedding of domain specific languages into the Haskell host language
much easier.

As it exists today, Template Haskell has two main areas of
application: Haskell code generation at compile-time and facilitating
the embedding of domain specific languages.

As a code generator, Template Haskell empowers a user to write many,
syntactically different, programs all at once by means of a single
meta program. All that is needed is a uniform, algorithmic description
to create the different result programs. And the meta program then
precisely implements the algorithm to compute all the different result
programs as its output. This proves useful for example to avoid
writing the same repetitive, boilerplate code over and over again. To
this end, Template Haskell is used (among many others) in the @aeson@
library to automatically derive a data type's @ToJSON@ and @FromJSON@
instances for JSON serialization; and in the @lens@ library to
mechanically create a data type's lenses.

As a framework for creating domain specific languages (EDSLs),
Template Haskell allows a user to embed programs written in another
programming language inside of a Haskell program. This enables writing
parts of the program in the concrete, domain specific syntax of a
different programming language. It has the benefit to think about --
and to express -- domain specific problems in the language best suited
for the task. In particular, it lets a user focus on the domain
specific problem and removes all additional language burdens induced
by inconvenient syntax, unsuited control constructs, etc. Programs
from the embedded language are parsed and translated into
corresponding (but syntactically heavier) Haskell code at compile-time
by Template Haskell. In this sense, (e.g.,) the shakespearean template
languages from the @shakespeare@ library use Template Haskell at their
core. They expose succinct domain specific languages to write HTML,
CSS, and Javascript code inside of a Haskell based web application.

The remainder of this report is organized as follows. Section 2
reviews Template Haskell's features in an example-driven
manner. Section 3 then outlines the implementation of Template Haskell
in GHC. Section 4 further describes my experience of extending
Template Haskell to also support the \texttt{PatternSynonyms}
extension. The report concludes with a personal review of this
independent study.

\section{Learning Template Haskell by Examples}
\label{sec:th-review}

In this section, I will review the Template Haskell functionality as
introduced in \cite{th1, th2, th3, qq} to write meta programs. In the
first set of examples I will show-case Template Haskell's potential as
a code generator; in the second set of examples I'll highlight its
facilities to create embedded domain specific languages (EDSLs).

To avoid confusion in the sequel, we distinguish between meta programs
and object programs. Meta programs are the Haskell programs that run
at compile-time and which generate Template Haskell object programs as
the result of their execution; they are the programs that devise or
manipulate other programs by some algorithmic means. Object programs,
on the other hand, are the Template Haskell programs manipulated and
built by the Haskell meta programs at compile-time.

%% To avoid confusion in the sequel, we distinguish between Template
%% Haskell's compile-time meta programs and the object programs they
%% generate. Meta programs are programs that compute programs as their
%% data; they manipulate other programs by some algorithmic means. Object
%% programs, on the other hand, are the programs that act like data to
%% the meta programs, i.e., the programs being manipulated by and
%% resulting as output from the meta programs.

\subsection{Template Haskell as a Code Generator}

As an introductory example, consider Haskell's @Prelude@ function
\texttt{curry :: ((a,b) -> c) -> a -> b -> c}, which converts a
function taking a pair to its curried equivalent. Unfortunately, there
are no @Prelude@ functions that provide the same currying
functionality for functions taking arbitrary \(n\)-tuples. Moreover,
having to write more than a few of these functions manually is, while
trivial, a very repetitive and cumbersome task. Instead we wish to
generate needed |curry3|, |curry5|, or |curry8| functions through a
single meta program on demand. Template Haskell let's us do just
this. The idea is to write a meta function |curryN :: Int -> Q Exp|
which, given a number \(n \geq 1\), \textit{constructs the source
  code} for an \(n\)-ary |curry| function:

> import Control.Monad
> import Language.Haskell.TH
>
> curryN :: Int -> Q Exp
> curryN n = do
>   f  <- newName "f"
>   xs <- replicateM n (newName "x")
>   let args = map VarP (f:xs)
>       ntup = TupE (map VarE xs)
>   return $ LamE args (AppE (VarE f) ntup)

|curryN| builds a lambda abstraction |LamE| that pattern matches
against a function |f| and \(n\) argument variables |x1|, |x2|, ...,
|xn|; in its body, it then applies function |f| to the \(n\)-tuple
|(x1, x2, ..., xn)| derived from the pattern matched variables. The
names used to refer to the variables |f| and |x1| through |xn| are
generated monadically by function |newName :: String -> Q Name| to
always generate fresh names not used anywhere else. Hence, the value
returned by |curryN| is a monadic computation of type @Q Exp@. When
executed, this monadic computation yields an expression @Exp@
representing the object program of an \(n\)-ary curry function. For
example, |(curryN 3)| returns a monadic computation that yields an
expression representing the object program of the |curry3| function of
type |((a, b, c) -> d) -> a -> b -> c -> d| in abstract syntax.

To run a meta program like |curryN| at compile-time, Template
Haskell's \textit{splice} operator ``|$|'' is used. When applied to a
@Q Exp@ computation it performs this computation and converts the
resulting object program to real Haskell code. Hence, enclosing a
Haskell meta program by ``|$(..)|'' means to evaluate it and to splice
in the generated Haskell code as the result of the splice. To ensure
type safety, the meta program is type checked before being run at
compile-time. For example, writing |$(curryN 3)| typechecks and then
evaluates the meta function |(curryN 3)| at compile time and puts the
resulting object program |\f x1 x2 x3 -> f (x1, x2, x3)| in place of
the splice.

%% Moreover, after splicing in the resulting object program
%% the entire Haskell module is typechecked again from scratch.

%% After running all of a Haskell module's meta functions,
%% typechecking restarts from scratch.

To generate function declarations for the first \(n\) curry functions,
we can devise a further meta program on top of |curryN| as follows:

> genCurries :: Int -> Q [Dec]
> genCurries n = sequence [ mkCurryDec i | i <- [1..n] ]
>   where mkCurryDec ith = do
>           cury <- curryN ith
>           let name = mkName $ "curry" ++ show ith
>           return $ FunD name [Clause [] (NormalB cury) []]

Running |$(genCurries 20)| will then splice in the first 20 curry
functions at compile-time, namely:

< curry1  = \ f x1 -> f (x1)
< curry2  = \ f x1 x2 -> f (x1, x2)
< curry3  = \ f x1 x2 x3 -> f (x1, x2, x3)
< curry4  = \ f x1 x2 x3 x4 -> f (x1, x2, x3, x4)
< ...
< curry20 = \ f x1 x2 ... x20 -> f (x1, x2, ..., x20)

Note that in this case, |genCurries| returns a list of top-level
function declarations that bind the anonymous lambda abstractions
built by |curryN|. Also, to name the function bindings, we use
function |mkName :: String -> Name| instead of |newName :: String -> Q
Name|. The reason is that here we want to generate functions |curry1|
to |curry20| with exactly the prescribed names, so they can be
captured and referred to from other parts of the program.

Evaluating Haskell (meta) programs at compile-time and splicing in the
generated object programs as regular Haskell code is the first central
building block of Template Haskell. The two other core mechanisms are
exhibited by the implementations of |curryN| and |genCurries|:
algebraic data types and the quotation monad @Q@.

First, object programs created by Template Haskell are represented as
regular algebraic data types, describing a program in the form of an
abstract syntax tree. The Template Haskell library provides algebraic
data types @Exp@, @Pat@, @Dec@, and @Type@ to represent Haskell's
surface syntax of expressions, patterns, declarations, and types,
respectively. Virtually every concrete Haskell syntactic construct has
a corresponding abstract syntax constructor in one of the four
ADTs. Furthermore, all Haskell identifiers are represented by the
abstract @Name@ data type. By representing object programs as regular
algebraic data types (and thus as data), normal Haskell can be used as
the meta programming language to build object programs.

%% The |curryN| example used a few of the available @Exp@ and @Pat@
%% constructors (namely @VarE@, @LamE@, @AppE@, @TupE@, and @VarP@,
%% respectively) to represent the generated Haskell expression and its
%% patterns. Similarly, in the |genCurries| example we represented the
%% generated function declaration using the @Dec@ constructors @FunD@,
%% @Clause@, and @NormalB@.

Second, TH object programs are built inside the quotation monad
@Q@. This monad is performed by the splice operator ``|$|'' at
compile-time as part of evaluating the meta program. In the examples
so far, the @Q@ monad was only needed to provide fresh identifiers
with function |newName :: String -> Q Name| for the generated Haskell
expressions. The other main feature that requires a monadic
construction of object programs is \textit{reification}, which allows
to query compile-time information during the object program's
construction. We will explain reification in detail later.

Thus, Template Haskell's core functionality constitutes evaluating
object programs with ``|$|'' and building them from algebraic data
types inside the quotation monad @Q@. However, constructing object
programs in terms of their abstract syntax trees is quite verbose and
leads to clumsy meta programs. Therefore the Template Haskell API also
provides two further interfaces to build object programs more
conveniently: \textit{syntax construction functions} and
\textit{quotation brackets}.

Syntax construction functions directly relate to the syntax
constructors from the algebraic data types @Exp@, @Pat@, @Dec@, and
@Type@ for representing Haskell code. However, they hide the monadic
nature of building object programs. For example, recall our definition
of the |genCurries| meta function from above:

< genCurries :: Int -> Q [Dec]
< genCurries n = sequence [ mkCurryDec i | i <- [1..n] ]
<   where mkCurryDec ith = do
<           cury <- curryN ith
<           let name = mkName $ "curry" ++ show ith
<           return $ FunD name [Clause [] (NormalB cury) []]

To use the object program generated by the sub call to |curryN| in the
larger context of the returned function declaration, we have to first
perform |curryN| and bind its result to |cury|. The reason is that we
have to account for |curryN|'s generation of fresh names before we can
continue. Using syntax construction functions instead of data
constructors, however, abstracts from the monadic construction of
|genCurries|, thus making its code a little shorter:

> genCurries :: Int -> Q [Dec]
> genCurries n = sequence [ mkCurryDec i | i <- [1..n] ]
>   where mkCurryDec ith = funD name [clause [] (normalB (curryN ith)) []]
>           where name = mkName $ "curry" ++ show ith

The new @funD@, @clause@, and @normalB@ functions directly correspond
to the formerly used @FunD@, @Clause@, and @NormalB@ constructors. The
only difference lies in their types:

\begin{center}
\begin{tabular}{l||l}
|FunD    :: Name -> [Clause] -> Dec| & |funD    :: Name -> [Q Clause] -> Q Dec| \\
|Clause  :: [Pat] -> Body -> Clause| & |clause  :: [Q Pat] -> Q Body -> Q Clause| \\
|NormalB :: Exp -> Body| & |normalB :: Q Exp -> Q Body|
\end{tabular}
\end{center}

While the syntax constructors work with raw TH expressions, the syntax
construction functions expect their monadic counterparts. They
construct a TH object program directly in @Q@, thus freeing the API
consumer from doing the monadic wrapping and unwrapping manually. For
every syntax constructor, there is a corresponding monadic syntax
construction function provided.

On top of syntax construction functions, quotation brackets are a
further shortcut for representing Haskell code. They allow to specify
an object program using just regular Haskell syntax by enclosing it
inside oxford brackets |[|| .. ||]|. That way, object programs can be
specified yet much more succinctly. For example, a meta program
building a Haskell expression for the identity function is still quite
verbose, if expressed with either ADTs or syntax construction
functions:

> genId :: Q Exp
> genId = do
>   x <- newName "x"
>   lamE [varP x] (varE x)

Using quotation brackets, writing the same meta program can be
abbreviated much further as:

< genId' :: Q Dec
< genId' = [| \x -> x |]

Quotation brackets quote regular Haskell code as the corresponding
object program fragments inside the @Q@ monad. There are quotation
brackets for quoting Haskell expressions (|[e|| .. ||]|), patterns
(|[p|| .. ||]|), declarations (|[d|| .. ||]|), and types (|[t||
  .. ||]|). Writing |[|| .. ||]| is hereby just another way of saying
|[e|| .. ||]|. Using quotation brackets in a sense ``lifts'' Haskell's
concrete syntax into corresponding object program expressions inside
the @Q@ monad. By doing so, quotation brackets represent the dual of
the already introduced splice operator ``|$|'': Evaluating a meta
program with ``|$|'' splices in the generated object program as real
Haskell code; in contrast, quotation brackets |[|| .. ||]| turn real
Haskell code into an object program. Consequently, quotation brackets
and the splice operator cancel each other out. The equation |$([|| e
  ||]) = e| holds for all expressions \(e\) and similar equations hold
for declarations, and types \cite{th2}.

In addition, there is support for quoting Haskell (value and type)
identifiers as corresponding @Name@s inside Template Haskell. This
allows to refer to regular Haskell identifiers from within TH object
programs. For example, writing |'genId| yields a TH @Name@ referring
to the |genId| identifier. Similarly, |''Q| gives a @Name@ referring
to the @Q@ type identifier.

\paragraph{Generic Maps.}

As a second example that uses both syntax construction functions as
well as quotation brackets, let's consider a meta program |mapN :: Int
-> Q Dec| to build ``generic'' |map| functions at
compile-time. Invoking |$(mapN 1)| should generate the well-known
standard function |map :: (a -> b) -> [a] -> [b]|; evaluating |$(mapN
2)| should splice in a binary map function of type |(a -> b -> c) ->
[a] -> [b] -> [c]|, and so on\footnote{Note that \(n\)-ary maps are
  better written using Applicative Functors and @ZipList@s. For
  understanding Template Haskell as a code generator, this example is
  still useful though.}.

> mapN :: Int -> Q Dec
> mapN n
>   | n >= 1    = funD name [cl1, cl2]
>   | otherwise = fail "mapN: argument n may not be <= 0."
>   where
>     name = mkName $ "map" ++ show n
>     cl1  = do f  <- newName "f"
>               xs <- replicateM n (newName "x")
>               ys <- replicateM n (newName "ys")
>               let argPatts  = varP f : consPatts
>                   consPatts = [ [p| $(varP x) : $(varP ys) |]
>                               | (x,ys) <- xs `zip` ys ]
>                   apply     = foldl (\ g x -> [| $g $(varE x) |])
>                   first     = apply (varE f) xs
>                   rest      = apply (varE name) (f:ys)
>               clause argPatts (normalB [| $first : $rest |]) []
>     cl2  = clause (replicate (n+1) wildP) (normalB (conE `[])) []

The implementation of |mapN| is very much in the spirit of meta
function |curryN| from the first example. For instance, evaluating
splice |$(mapN 3)| splices in the following map function at
compile-time:

> map3 f (x:xs) (y:ys) (z:zs) = f x y z : map3 f xs ys zs
> map3 _ _      _      _      = []

Nonetheless, meta function |mapN| exhibits a couple of new Template
Haskell features: First, quotation brackets and splices are used in
several places to abbreviate the object program construction. For
example, helper definition |apply| used to generate |map3|'s body |f x
y z : map3 f xs ys zs| shows the use of quotation brackets; it also
highlights how splicing (``|$|'') and quotes (``|[|| .. ||]|'') cancel
each other out. Second, identifier quotes (namely, |'[]|) are used to
create an object program @Name@ that refers to Haskell's built-in list
constructor |[]|. Third, the example advertises how all three APIs for
building Template Haskell object programs can be interleaved. The
lowermost verbose API of building a raw TH data value inside the
quotation monad @Q@ can be abbreviated, where possible, with syntax
constructor functions and quotation brackets.

Lastly, the |mapN| example exemplifies how Haskell's static scoping is
extended to object programs. The scoping principle for object programs
is just as in normal Haskell: Identifiers are bound to their lexically
enclosing binders in scope at the point the object program is
\textit{defined}. Quotation brackets and splices don't alter static
scopes, even though splices may bring an object program into scope at
a location, where a conflicting closure is present. For example,
consider this snippet:

> x :: Int
> x = 42
>
> static :: Q Exp
> static = [| x |]
>
> plus42 :: Int -> Int
> plus42 x = $static + x

Here the occurrence of |x| in |static| refers to the global identifier
|x| that is lexically in scope during its definition.  Splicing in
|static| into a different scope later where a different local |x| is
present (i.e., |plus42|'s local identifier |x|), doesn't alter the
link between |static|'s |x| and the global identifier |x|.

%% Static scoping in Template Haskell is achieved by the abstract name
%% data type @Name@ and its exposed API: of always generating fresh names via
%% @Q@'s |newName :: String -> Q Name| function as well referring to
%% regular Haskell identifiers from within an object program using |`|
%% and |``|.

The only exception to static scoping in Template Haskell are the names
generated by |mkName :: String -> Name|. These names implement dynamic
scoping and \textit{can} be captured in spliced-in code. Changing the
previous snippet to

> x :: Int
> x = 42
>
> dynamic :: Q Exp
> dynamic = VarE (mkName "x")
>
> times2 :: Int -> Int
> times2 x = $dynamic + x

results in the identifier |x| spliced in by |$dynamic| to be bound to
the closest |x| in scope. Hence, its binder is |times2|'s local
identifier |x| and \textit{not} the global |x|.

\paragraph{Reification.}

The final major Template Haskell feature not yet described is program
\textit{reification}. Briefly, reification allows a meta program to
query compile-time information about other program parts while
constructing the object program. It allows the meta program to inspect
other program pieces to answer questions such as: ``what's this
variable's type?'', ``what are the class instances of this type
class?'', or ``which constructors does this data type have and and how
do they look like?''. The main use case is to generate boilerplate
code which ``auto-completes'' manually written code. A prime example
is to generically derive type class instances from bare data type
definitions.

Suppose we've defined the following polymorphic data types for
representing potentially erroneous values, lists, and binary trees,
respectively:

> data Result e a = Err e | Ok a
> data List     a = Nil | Cons a (List a)
> data Tree     a = Leaf a | Node (Tree a) a (Tree a)

Moreover, suppose we want to derive @Functor@ instances for all of
these types. Deriving these instances manually is straightforward, but
writing them all out by hand is quite cumbersome. Especially since
writing a @Functor@ instance follows the same pattern across all of
the above types and in fact any type @T a@.

To make a type constructor @T@ an instance of @Functor@, one needs to
implement method |fmap :: (a -> b) -> T a -> T b|. Its definition is
hereby precisely determined by parametricity and the functor laws: By
parametricity, all values of type @a@ must be replaced according to
the provided function with values of type @b@. Furthermore, by the
functor laws, all other shapes of the input value of type @T a@ must
be preserved when transforming it to the output value of type @T b@.

Meta function |deriveFunctor :: Name -> Q [Dec]| below implements the
idea of this algorithm:

> data Deriving = Deriving { tyCon :: Name, tyVar :: Name }
>
> deriveFunctor :: Name -> Q [Dec]
> deriveFunctor ty
>   = do (TyConI tyCon) <- reify ty
>        (tyConName, tyVars, cs) <- case tyCon of
>          DataD _ nm tyVars cs _   -> return (nm, tyVars, cs)
>          NewtypeD _ nm tyVars c _ -> return (nm, tyVars, [c])
>          _ -> fail "deriveFunctor: tyCon may not be a type synonym."
>
>        let (KindedTV tyVar StarT) = last tyVars
>            instanceType           = conT ``Functor `appT`
>              (foldl apply (conT tyConName) (init tyVars))
>
>        putQ $ Deriving tyConName tyVar
>        sequence [instanceD (return []) instanceType [genFmap cs]]
>   where
>     apply t (PlainTV name)    = appT t (varT name)
>     apply t (KindedTV name _) = appT t (varT name)

Given the name of a type constructor (e.g. @Result@, @List@, etc.),
|deriveFunctor| derives the code for this type constructor's @Functor@
instance.  For example, running the splice |$(deriveFunctor ''Tree)|
generates the following code:

> instance Functor Tree where
>   fmap f (Leaf x)     = Leaf (f x)
>   fmap f (Node l x r) = Node (fmap f l) (f x) (fmap f r)

Most notably, meta function |deriveFunctor| shows reification in
action. It calls function |reify :: Name -> Q Info| on the input type
constructor's name to yield information about this data type's
definition. Using |reify|, it thus learns whether the data type was
defined using the @data@ or @newtype@ keyword, which constructors it
defines and what their shapes are. Based on the learned structure,
|deriveFunctor| is then able to generate a suitable definition of
|fmap| and its different clauses via the auxiliaries |genFmap|,
|genFmapClause|, and |newField|, defined below. These auxiliary
definitions generate one |fmap| clause for each of the data type's
constructors. And each clause then transforms its constructor by
recursively modifying all of the constructor's fields of type @a@
through |fmap|'s function @f@, while retaining all other shapes.

> genFmap :: [Con] -> Q Dec
> genFmap constructors
>   = do funD `fmap (map genFmapClause constructors)
>
> genFmapClause :: Con -> Q Clause
> genFmapClause (NormalC name fieldTypes)
>   = do f          <- newName "f"
>        fieldNames <- replicateM (length fieldTypes) (newName "x")
>
>        let pats = varP f:[conP name (map varP fieldNames)]
>            body = normalB $ appsE $
>              conE name : map (newField f) (zip fieldNames fieldTypes)
>
>        clause pats body []
>
> newField :: Name -> (Name, StrictType) -> Q Exp
> newField f (x, (_, fieldType))
>   = do Just (Deriving typeCon typeVar) <- getQ
>        case fieldType of
>          VarT typeVar' | typeVar' == typeVar ->
>            [| $(varE f) $(varE x) |]
>          ty `AppT` VarT typeVar' |
>            leftmost ty == (ConT typeCon) && typeVar' == typeVar ->
>              [| fmap $(varE f) $(varE x) |]
>          _ -> [| $(varE x) |]
>
> leftmost :: Type -> Type
> leftmost (AppT ty1 _) = leftmost ty1
> leftmost ty           = ty

In an analogous manner to |deriveFunctor|, a function |deriveFoldable
:: Name -> Q [Dec]| can be devised to derive a data type's @Foldable@
instance. All that is needed is to provide a definition for function
|foldMap :: Monoid m => (a -> m) -> T a -> m|. Again, |foldMap|'s
definition follows directly from a data type's bare definition, which
can be observed by means of reification\footnote{In fact, the example
  at
  https://www.github.com/bollmann/th-samples/DeriveFunctorFoldable.hs
  implements a (slightly more involved) meta program to derive both
  @Functor@ and @Foldable@ instances in a single framework.}. This
highlights particularly how the functionality offered by Template
Haskell provides a low-level API into the GHC compiler to manipulate
abstract syntax trees at compile-time. This mechanism is quite
powerful and even allows to simulate some of GHC's offered language
extensions, e.g., @-XDeriveFunctor@ and @-XDeriveFoldable@, to be
implemented as a library on top of Template Haskell.

\subsection{Template Haskell for building Embedded Domain specific
  Languages (EDSLs)}

To see Template Haskell's potential for building an EDSL, consider the
problem of pattern matching text with regular expressions. Suppose, as
part of a Haskell program we need to devise many different regular
expressions and use them to pattern match text fragments. Regular
expressions are easily defined by an algebraic data type capturing
their structure, as well as an evaluator checking whether a regular
expression matches some input string\footnote{This example draws on
  Penn's CIS 552 \textit{Advanced Programming} course, specifically
  Assignment 5:
  http://www.seas.upenn.edu/~cis552/current/hw/hw05/Main.html.}:

> data RegExp
>   = Char (Set Char)    -- [a], [abc], [a-z]; matches a single
>                        -- character from the specified class
>   | Alt RegExp RegExp  -- r1 | r2 (alternation); matches either r1 or r2
>   | Seq RegExp RegExp  -- r1 r2 (concatenation); matches r1 followed by r2
>   | Star RegExp        -- r* (Kleene star); matches r zero or more times
>   | Empty              -- matches only the empty string
>   | Void               -- matches nothing (always fails)
>   | Var String         -- a variable holding another regexp
>                        -- (explained later)
>   deriving Show

> match :: RegExp -> String -> Bool
> match r s = nullable (foldl deriv r s)

The evaluator |match| is hereby based on the concept of
derivatives~\cite{regexps-derivs}: an initial regular expression |r|
matches an input string |s|, if |r| matches the first character of |s|
and its derivative regular expression |(deriv r)| matches the
remainder of |s|:

> nullable :: RegExp -> Bool
> nullable (Char _)    = False
> nullable (Alt r1 r2) = nullable r1 || nullable r2
> nullable (Seq r1 r2) = nullable r1 && nullable r2
> nullable (Star _)    = True
> nullable Empty       = True
> nullable Void        = False
> nullable (Var _)     = False
>
> deriv :: RegExp -> Char -> RegExp
> deriv (Char cs) c
>   | c `Set.member` cs = Empty
>   | otherwise         = Void
> deriv (Alt r1 r2) c   = Alt (deriv r1 c) (deriv r2 c)
> deriv (Seq r1 r2) c
>   | nullable r1       = Alt (Seq (deriv r1 c) r2) (deriv r2 c)
>   | otherwise         = Seq (deriv r1 c) r2
> deriv (Star r) c      = deriv (Alt Empty (Seq r (Star r))) c
> deriv Empty _         = Void
> deriv Void _          = Void
> deriv (Var _) _       = Void

The @RegExp@ datatype and the |match| function solve the initially
posed problem of providing regular expressions in Haskell. However,
specifying regular expressions in abstract syntax is extremely
tedious. For example, consider defining a regular expression for
checking the wellformedness of email addresses ending with the top
level domain \texttt{.com}. In its usual concrete syntax, such a
regular expression is easily defined as
@([a-z]|[0-9])*@@([a-z]|[0-9])*.com@, but writing it in terms of the
@RegExp@ dataype is verbose and unintuitive. Moreover, parsing
functions like
\begin{itemize}
\item |compile  :: String -> RegExp|, or
\item |compile' :: String -> Either CompileError RegExp|
\end{itemize}
do not resolve the problem of working with regular expressions in
concrete syntax. Due to ``compiling'' regular expressions at run time,
they don't provide any compile-time type-safety guarantees that the
input raw expression is wellformed; thus they lead to either run time
exceptions for illformed regular expressions (|compile|) or imply a
tedious usability for compiled regexes (|compile'|).

To preserve type safety and yet to be able to use regular expressions
conveniently, we want to embed the concrete regular expression syntax
into the Haskell host language. This can be done via Template
Haskell's quasi quotes and the @QuasiQuotes@ extension. It allows
defining \textit{quasi quotes} for regular expressions, denoted
|[regex|| .. ||]|, where anything inside the quasi quote is considered
part of an embedded regular expression language. Using quasi quotes,
we can then specify the regex for email addresses from above naturally
as follows:

> alphaNum, validDotComMail :: RegExp
> alphaNum        = [regex|[a-z]|[0-9]|]
> validDotComMail = [regex|${alphaNum}*@${alphaNum}*.com|]

Note how we can even compose regular expressions easily from smaller
building blocks. Writing |${alphaNum}| interpolates the regex referred
to by |alphaNum| into the larger regex |validDotComMail|. In essence,
this means that we can define our own notion of splicing values from
the Haskell meta language into the embedded object language of regular
expressions. We can go further and even allow to run Haskell code when
interpolating with @${..}@. For example, refining our wellformedness
check for ``\texttt{.com}'' mail addresses, we might want to ensure at
least one character to occur on either side of the ``@@'' symbol:

> chars', validDotComMail' :: RegExp
> chars'           = [regex|[a-z]|[A-Z]|[0-9]|[-_.]|]
> validDotComMail' = [regex|${plus chars'}@${plus chars'}.com|]
>
> plus :: RegExp -> RegExp
> plus r = Seq r (Star r)

Here, |plus| corresponds to the usual regex combinator that requires a
given regex to occur at least once. Note how |plus| is defined as a
regular Haskell function and then used \textit{inside} of the embedded
regex language to build the regular expression for |validDotComMail'|.

Intuitively, a quasi quote like |[regex|| .. ||]| converts an embedded
language's concrete syntax to Haskell code at compile time. It is
defined by a \textit{quasi quoter}, which is a parser for the embedded
language. The quasi quoter's task is to parse the embedded language's
syntax into a corresponding Template Haskell expression and then to
splice this expression as real Haskell code in place of the quasi
quote. The conversion of embedded language code to corresponding
Haskell code hereby happens before typechecking the Haskell
module. Hence, trying to splice in malformed embedded language
fragments will raise a Haskell type error at compile time.

The quasi quoter @regex@ for our embedded language of regular
expressions can be defined as follows:

\todo{explain TExp, unTypeQ, [e|| .. ||] or get rid of typed
  expression quotes and splices!}

> regex :: QuasiQuoter
> regex = QuasiQuoter {
>     quoteExp  = unTypeQ . compile
>   , quotePat  = notHandled "patterns"
>   , quoteType = notHandled "types"
>   , quoteDec  = notHandled "declarations"
>   }
>   where notHandled things = error $
>           things ++ " are not handled by the regex quasiquoter."
>
> compile :: String -> Q (TExp RegExp)
> compile s =
>   case P.parse regexParser "" s of
>     Left  err    -> fail (show err)
>     Right regexp -> [e|| regexp ||]

That is, formally a @QuasiQuoter@ consists of four parsers,

< quoteExp  :: String -> Q Exp
< quotePat  :: String -> Q Pat
< quoteType :: String -> Q Type
< quoteDec  :: String -> Q Dec

to parse raw strings of the embedded language into the different
categories of Haskell syntax. In this example, however, we only want
to splice embedded regular expressions into the context of Haskell
expressions, so we only define the @quoteExp@ parser in the @regex@
quasi quoter. This parser compiles an embedded regular expression
given as a string into a corresponding Template Haskell expression.

Compilation by the |compile| function proceeds in two stages: First,
we parse the input string regex into a corresponding @RegExp@
value. Second, we encode this @RegExp@ value as a Haskell expression
in Template Haskell's @Exp@ datatype. It is the second step that
allows us to interpolate variables (or even code) from the Haskell
host language into the EDSL for regular expressions.

Parsing a raw regular expression into a corresponding @RegExp@ value
is a routine task using (e.g.) the \texttt{parsec} library:

> regexParser :: Parsec String () RegExp
> regexParser = alts <* eof where
>   atom       = try var <|> char
>   var        = Var <$> (string "${" *> many1 (noneOf "}") <* P.char '}')
>   char       = charclass <|> singlechar
>   singlechar = (Char . Set.singleton) <$> noneOf specials
>   charclass  = fmap (Char . Set.fromList) $
>                  P.char '[' *> content <* P.char ']'
>   content    = try (concat <$> many1 range)
>                  <|> many1 (noneOf specials)
>   range      = enumFromTo
>                  <$> (noneOf specials <* P.char '-')
>                  <*> noneOf specials
>   alts       = try (Alt <$> seqs <*> (P.char '|' *> alts)) <|> seqs
>   seqs       = try (Seq <$> star <*> seqs) <|> star
>   star       = try (Star <$> (atom <* P.char '*'))
>                  <|> try (Star <$> (P.char '(' *> alts <* string ")*"))
>                  <|> atom
>   specials   = "[]()*|"

To represent regular expressions of type @RegExp@ as Haskell
expressions of type @Q Exp@, Template Haskell's @Lift@ typeclass is
used. Its method @lift :: Lift a => a -> Q Exp@ lifts values from the
Haskell meta language (i.e., a @RegExp@ value) into Template Haskell's
object language (i.e., a value of the @Q Exp@ datatype). The |lift|
function is used implicitly by the quote |[e|||| regexp ||||]| in
function |compile| to represent a @RegExp@ value as a Template Haskell
expression.

Most of the lifting is a direct encoding of the syntactic structure of
the @RegExp@ value; the only interesting case is when lifting the
regular expression variable |Var vars|. In this case, we treat the
words in the string |vars| as referring to identifiers from the
Haskell host language, which we apply in a left associative manner to
each other. Doing this enables interpolation of Haskell identifiers or
even simple forms of Haskell expressions into our EDSL of regular
expressions as shown by the regexes |validDotComMail| and
|validDotComMail'| above.

> instance Lift a => Lift (Set a) where
>   lift set = appE (varE `Set.fromList) (lift (Set.toList set))
>
> instance Lift RegExp where
>   -- lift :: RegExp -> Q Exp
>   lift (Char cs)     = apply `Char  [lift cs]
>   lift (Alt r1 r2)   = apply `Alt   (map lift [r1, r2])
>   lift (Seq r1 r2)   = apply `Seq   (map lift [r1, r2])
>   lift (Star r1)     = apply `Star  (map lift [r1])
>   lift Empty         = apply `Empty []
>   lift Void          = apply `Void  []
>   lift (Var vars)    = foldl1 appE $ map (varE . mkName) (words vars)
>
> apply :: Name -> [Q Exp] -> Q Exp
> apply n = foldl appE (conE n)

These two steps constitute the conversion of raw string regular
expressions into Template Haskell expressions inside of the |compile|
function and define the @regex@ quasiquoter. Whenever we write a quasi
quote like |[regex|| .. ||]| in a Haskell expression context,
|regex|'s parser |quoteExp| converts the regex EDSL into a Template
Haskell expression @Exp@ and splices in the result as a wellformed
@RegExp@ value. This example shows how Template Haskell and quasi
quotes can be used to define a type-safe, domain specific language for
regular expressions.

In much the same manner, Template Haskell and quasi quotes are used in
Michael Snoyman's \texttt{shakespeare}
library~\cite{shakespeare,shakespeare-lib}. It defines embedded
templating languages for working with the internet's web languages
from within a Haskell web application. In particular, the
\texttt{shakespeare} library provides the template languages
\textit{Hamlet}, \textit{Cassius}, and \textit{Julius} for writing
embedded HTML, CSS, and Javascript code, respectively. All three
templating languages internally work quite similarly to the previous
example's EDSL for regular expressions: quasi quotes allow one to
write HTML, CSS, or JavaScript code in concrete (though slightly
modified) syntax inside of Haskell. Moreover, identifiers from the
Haskell host language as well as code fragments can be interpolated
into the template languages at compile-time. In the remainder we will
briefly show-case the \texttt{shakespeare} library's templating
language Hamlet for creating HTML documents; the other templating
languages Cassius and Julius are similar.

To create and output a simple web page from inside a Haskell
application, the following is enough:

> import Data.Text
> import Text.Hamlet
> import Text.Blaze.Html.Renderer.String
>
> data Page = Home | About | Github
>
> mkUrls :: Page -> [(Text, Text)] -> Text
> mkUrls Home   _ = "/home.html"
> mkUrls About  _ = "/about.html"
> mkUrls Github _ = "https://www.github.com/bollmann"
>
> webPage :: Text -> Text -> HtmlUrl Page
> webPage title content = [hamlet|
>   <html>
>     <head>
>       <title>#{Text.toUpper title}
>     <body>
>       <h1>#{title}
>       <div>Welcome to my Shakespearean Templates page!
>       <hr>
>       <div>Links:
>         <ul>
>           <a href=@{Home}>My Homepage
>           <a href=@{About}>About me
>           <a href=@{Github}>Check out my Github
>       <hr>
>       <div>#{content}
>  |]
>
> main = putStrLn $ renderHtml $
>   webPage "Hello Shakespeare!" "Hello World!" mkUrls

Running this Haskell program, outputs an HTML page as specified by the
Hamlet templating language, embedded through quasi quote
|[hamlet|| .. ||]| in function |webPage|. Hamlet closely
resembles real HTML syntax, but is even more terse: instead of a
closing HTML tag, Hamlet uses indentation to indicate the
span of the tag. Furthermore, Hamlet allows to interpolate
code or identifiers from the Haskell host language when creating an
HTML template. Interpolation of Haskell code into Hamlet is
done by writing |#{ .. }|. In the above example, the HTML page's title
and content are interpolated from Haskell identifiers. Note
particularly how in the webpage's title we uppercase the interpolated
title using Haskell's |Text.toUpper| function \textit{inside} of the
Hamlet language.

In addition to this standard interpolation, Hamlet can also
interpolate links by writing |@{..}|. These links are specified as
values of the |Page| datatype inside the template and the |mkUrls|
render function translates them to real URLs later. Hamlet's
URL interpolation has commonly be phrased as creating ``type-safe
URLs''. One reason is that, just like with normal variable
interpolation, all interpolated links have to exist and be type
correct at compile-time. Hence, as soon as a link's constructor shape
is changed, the compiler statically forces us to update all references
to this link as well. Furthermore, there is only one distinct place in
the code to maintain or update a link's raw URL, thus minimizing the
risk of dead URLs.

For example, suppose we want to add more external links to our web
page. We could model this fact by changing the |Page| data type to

> data Page = Home | About | External ExternalPage
> data ExternalPage = Github | Haskell | Reddit

and, moreover, changing the |mkUrls| renderer function to account for
the new links:

< mkUrls :: Page -> [(Text, Text)] -> Text
< mkUrls Home            _ = "/home.html"
< mkUrls About           _ = "/about.html"
< mkUrls (External page) _ = mkExternalUrls page
<
< mkExternalUrls :: ExternalPage -> Text
< mkExternalUrls Github  = "https://www.github.com"
< mkExternalUrls Haskell = "http://www.haskell.org"
< mkExternalUrls Reddit  = "http://www.reddit.com/r/haskell"

Doing just these changes, will then cause a compile-time error in our
|webPage| template, since we haven't updated the |Github| reference to
our newly adjusted link structure. Hence, the compiler reminds (and in
fact forces) us to update all locations in the code that used the old
|Github| link to now use the new |External Github| (as well as
optionally the |External Haskell|, etc.) links.

%% However, the main reason for calling Hamlet's URLs type-safe is in
%% interplay with the web framework Yesod. On top of Hamlet, Yesod
%% provides yet another DSL for assigning URLs to their corresponding
%% webpage handlers. \todo{shall we mention this (and in this case
%%   elaborate it with two more sentences)??}

Finally, Hamlet allows to use some control constructs like if
conditionals, for loops, and let bindings to embed basic business
logic into a webpage's template. See \cite{shakespeare,yesod} for a
gentle (and much more in-depth) introduction to shakespearean
templates and Yesod.

\section{Template Haskell's Implementation in GHC}

The Template Haskell functionality is implemented by a public Haskell
library as well as a language extension to GHC. The Template Haskell
library, called \texttt{template-haskell}, defines the user-facing API
as described in the previous section. It provides the main module
@Language.Haskell.TH@, which is based on sub modules
\texttt{Language.Haskell.TH.\{Syntax, Lib, Ppr, Quote\}}, respectively.

Module @Language.Haskell.TH.Syntax@ defines the algebraic data types,
the quotation monad @Q@, and the @Lift@ typeclass for
representing Haskell programs as data; module
@Language.Haskell.TH.Lib@ defines the corresponding syntax
construction functions. Furthermore, module @Language.Haskell.TH.Ppr@
provides a pretty printer for displaying Template Haskell object
programs in concrete syntax. Finally, @Language.Haskell.TH.Quote@
defines the quasi quoter datatype for embedding domain specific
languages.

Inside GHC, Template Haskell is implemented by the
\texttt{TemplateHaskell} language extension. This extension's main
purpose is (a) to run meta programs at compile-time through splice
operator |$(..)|; (b) to represent Haskell code as data by enclosing
it in quotation brackets |[|| .. ||]|; and (c) to provide an interface
for reification. The functionality is (mainly) implemented by modules
\texttt{rename/rnSplice.hs}, \texttt{typecheck/TcSplice.hs},
\texttt{deSugar/DsMeta.hs}, and \texttt{hsSyn/Convert.hs},
respectively. Each GHC module is invoked at a different stage during
the compilation of a Haskell program that uses Template Haskell's meta
programming facilities.

The following section highlights how the above features (a) to (c)
fall into the big picture of GHC's compilation process. Simon Marlow
and Simon Peyton Jones provide an excellent general and more thorough
overview of GHC in ``The Glasgow Haskell Compiler''~\cite{aosa}.

To compile a Haskell module @M@ that uses the @TemplateHaskell@
extension, GHC first lexes and parses @M@'s concrete Haskell syntax
into abstract Haskell syntax. Next, GHC's renamer processes @M@'s
abstract syntax, resolving the scopes of the module's identifiers and
connecting them to their binding sites. As part of renaming, feature
(a) is implemented: the evaluation of meta programs. All top-level
splices occurring in the Haskell module @M@ are renamed and then
executed with their results spliced in place of them. In particular,
when the renamer comes across a splice |$(mp)|, it triggers a
subcompilation process of just meta program |mp|. This subcompilation
first typechecks |mp| to ensure that it has type @Q Exp@ (or @Q
[Dec]@, etc.) and thus that it yields a valid Template Haskell object
program. If typechecking succeeds, |mp| is then desugared to an
equivalent, but simpler core expression, and afterwards compiled,
linked, and run. The result is a monadic value of type @Q Exp@ (or @Q
[Dec]@, or the like), which is performed via Template Haskell's |runQ|
function to obtain the generated Template Haskell object program. This
object program is finally converted into real Haskell (abstract)
syntax and spliced in place of the original meta program |$(mp)|. This
concludes the evaluation of meta program |mp|. After splicing in the
meta program's result, the renamer continues its renaming process on
the spliced in result program as if there had never been any splice
|$(mp)|.

Running Template Haskell splices in the renamer and thus before
typechecking the enclosing Haskell module gives rise to the so-called
stage restriction: a top-level splice |$(mp)| may only use imported
and thus already fully typechecked code. The stage restriction is
presumably Template Haskell's most annoying limitation as it requires
a user to separate the definitions of meta programs from their
use-sites in splices into different modules. However, overcoming the
stage restriction is difficult to implement. After all, the code
inside a splice must be successfully typechecked before it can be
run. And typechecking a splice's code coming from the very module
currently being renamed would require evaluation of splices to be run
after typechecking (as in fact was done in the original Template
Haskell implementation \cite{th1}). However, postponing the evaluation
of splices to after the typechecking phase bears other problems, for
example how to rename new identifiers brought into scope by a splice's
execution. Hence, until today the stage restriction has persisted in
the Glasgow Haskell Compiler.

After renaming module @M@, typechecking happens. It ensures that the
composition of @M@'s terms is allowed by its types. With regard to
Template Haskell, the typechecking process is quite simple. Meta
programs are checked in the same manner as regular Haskell code. Their
only distinctive characteristic is to construct a Template Haskell
object program and thus to be of type @Q Exp@, (or @Q [Dec]@, or the
like). While this ensures that a Haskell meta program in fact builds
some sort of a TH expression (or declarations, etc.), it doesn't
enforce the type correctness of the generated object program. This is
because the object program construction in Template Haskell is
untyped, where we don't know whether a built TH expression of type,
say @Exp@, is actually type-correct. To ensure the type-safety of
compile-time generated object programs, these are type checked after
being spliced in as Haskell code. In particular, the spliced in result
programs of all previously during renaming executed meta programs are
now rechecked from scratch.

Interestingly, the contents of quotation brackets are \textit{not}
typechecked except for ensuring that embedded splices (i.e., embedded
invocations of meta programs) are type-safe. Besides checking that
embedded splices correctly produce some value of a Template Haskell
object program, quotation brackets may contain any type-incorrect code
(e.g., |[|| "false" && True ||]| is not rejected). The reason is that
due to sub splices (and particularly splicing in type expressions)
there are several cases where typechecking cannot be performed until
actually executing the sub splice. However, nested splices inside
quotation brackets are not evaluated until the quotation bracket is
run as part of a top-level splice's execution. Hence, typechecking
quotation brackets cannot be done in a generally sensible manner and
is thus not attempted at all. Note that this does not violate type
safety in general since object programs are typechecked from scratch
after having been run and spliced in as Haskell code.

Finally, it is the typechecking pass that provides Template Haskell's
reification feature (c). Using the @Q@ monad's |reify| function in
essence means interacting with GHC's typechecker monad
@TcM@\footnote{The @Q@ monad is essentially a wrapper on top of GHC's
  internal typechecker monad @TcM@. This is accomplished without
  depending on GHC by using a @Quasi@ typeclass for indirection. The
  trick is described in \cite{th2}, \S 10 ``Functoring the Q
  monad''.}. As such, querying an identifier's type, a typeclass'
instances, and other compile-time information by means of |reify|
becomes possible.

After GHC's typechecking pass, desugaring of module @M@'s Haskell code
takes place. The desugaring consists of multiple steps in which the
elaborate Haskell syntax is simplified into GHC's intermediate
language \texttt{Core} (i.e., System F\(\omega\) with
Coercions~\cite{systemfc}). With regard to Template Haskell, splices
have already been eliminated by running them in the renaming stage.
Furthermore Template Haskell object program constructions of data
values (of e.g. type @Exp@, @[Dec]@, or similar) inside monad @Q@ are
desugared just in the same way as is normal do notation. Accordingly,
only feature (b), the desugaring of quotation brackets deserves
special attention: its quoted Haskell expression is rewritten as a
\texttt{Core} expression that, when run, produces a Template Haskell
code fragment equivalent to the quoted Haskell expression. To this
end, splices like |$(e)| inside a quotation bracket are replaced by
their splice bodies |e|. Thus, running the desugared \texttt{Core}
expression of a quotation bracket also evaluates its nested splices to
yield the overall TH object program. Overall, the desugaring achieves
representing Haskell code as corresponding Template Haskell object
programs by translating the former into the latter at the level of
Haskell's intermediate \texttt{Core} language.

The desugared Haskell module @M@ is finally fed into one of several
possible code generators to generate machine code for the architecture
at hand. This concludes the life-cycle of Template Haskell for
compile-time meta programming during the compilation of a Haskell
module @M@.

The GHC modules implementing the \texttt{TemplateHaskell} extension
are (mostly) invoked as part of evaluating a top-level splice |$(mp)|
holding some meta program |mp|. The evaluation is triggered as part of
the renaming pass by module \texttt{rename/RnSplice.hs}. It renames a
top-level splice's body and then calls into module
\texttt{typecheck/TcSplice.hs} for further processing. Module
\texttt{typecheck/TcSplice.hs} first typechecks |mp| to be a valid
meta program and then desugars it to a simpler core
expression. Desugaring hereby involves using module
\texttt{deSugar/DsMeta.hs} for simplifying Template Haskell's
quotation brackets. The desugared meta program is then evaluated by
\texttt{typecheck/TcSplice.hs} and the resulting monadic TH object
program is performed to yield a data value representing the computed
TH object program. This TH object program is finally spliced in as the
result of splice |$(mp)| as real Haskell code. The conversion from
Template Haskell syntax to real Haskell syntax is done by module
\texttt{hsSyn/Convert.hs}. All these steps conclude the evaluation of
meta program |mp| as part of the renaming pass.

\section{Adding Pattern Synonyms Support to Template Haskell}
\label{sec:patsyns}

During this independent study, I added support for the recently added
\texttt{PatternSynonyms} extension to Template Haskell. The details of
this patch are discussed at~\cite{patsyns-patch}. Pattern Synonyms
were introduced in GHC 7.8 and allow to give short names (i.e.,
synonyms) to more complicated patterns. These synonyms can then be
used to match against the underlying patterns. Moreover, in many
cases, the succinct pattern synonym names can also be used as
``smart'' constructors to build the represented, more involved
patterns in an expression context.

Pattern synonyms prove useful (e.g.,) when composing data types from
smaller building blocks.  The following example, due to Conor
McBride\footnote{https://www.reddit.com/r/haskell/comments/1kmods/patternsynonyms\_ghc\_trac/cbqk5t2},
shows how to build a binary tree @Tree a@ from fixpoints, sums, and
products of atomic nodes:

> newtype K a       x = K a
> newtype I         x = I x
> newtype (:+:) f g x = Sum (Either (f x) (g x))
> newtype (:*:) f g x = Prod (f x, g x)
>
> newtype Fix f       = In { unfix :: f (Fix f) }
>
> newtype Tree a = Fix (K a :+: (I :*: I))

This composite construction of @Tree a@ nicely reuses existing
datatypes and their sub structures. However, without pattern synonyms,
both constructing and pattern matching against values of type @Tree a@
becomes verbose and cumbersome. For example, making tree an instance
of @Functor@ is horrendous:

< instance Functor Tree where
<   fmap f (Tree' tree) = Tree' $ go f tree where
<     go f (In (Sum (Left (K x))))
<       = In (Sum (Left (K (f x))))
<     go f (In (Sum (Right (Prod (I l, I r)))))
<       = In (Sum (Right (Prod (I (go f l), I (go f r)))))

Similarly, constructing even simple trees is very tedious. To
alleviate this clumsyness, pattern synonyms can be used to define
@Leaf@ and @Node@ patterns:

> pattern Leaf x   = In (Sum (Left (K x)))
> pattern Node l r = In (Sum (Right (Prod (I l, I r))))

These patterns once and for all fix @Tree a@'s generic internal type
structure and give a shortcut name to pattern match (or construct) a
tree's node or leaf. Using pattern synonyms, defining a @Tree@s
@Functor@ instance again becomes easy to read:

> instance Functor Tree where
>   fmap f (Tree t) = Tree $ go f t where
>     go f (Node l r) = Node (go f l) (go f r)
>     go f (Leaf x)   = Leaf (f x)

%% Pattern synonyms prove useful (e.g.,) when using general recursion
%% schemes for fixpoints of @Functor@s (as suggested by ``sboo'' in
%% comment 11 of ticket \#8761). For example, suppose we have defined a
%% simple data type for representing arithmetic expressions:

%% > data Operation = Add | Multiply
%% > data TreeF a r
%% >   = LitF a               -- values
%% >   | VarF String          -- variables
%% >   | BinF r Operation r   -- compound expressions
%% >   deriving Functor

%% Taking the fixpoint of the @TreeF a@ functor then gives rise to a
%% binary tree:

%% > newtype Fix f = In { unFix :: f (Fix f) }
%% > type Tree a = Fix (TreeF a)

%% Using the fixpoint approach allows to use general recursion schemes
%% such as catamorphisms and anamorphisms to fold or unfold expression
%% trees succinctly and without much
%% boilerplate~\cite{rec-schemes}. However, constructing and pattern
%% matching against values of type @Tree a@ is quite cumbersome. In
%% particular, to define the tree for the arithmetic expression @x * 2 +
%% 1@, we have to write:

%% > exp = In
%% >   BinF (In (BinF
%% >              (In (VarF "x"))
%% >              Multiply
%% >              (In (ValF 2))))
%% >        Add
%% >        (In (ValF 1)))

%% A similar burden is introduced when trying to pattern match against
%% specific values of arithmetic expressions, since all the @In@
%% constructors have to be written out.

%% Pattern synonyms relieve this burden by allowing to name the
%% constructors of the @Tree a@ type succinctly:

%% > pattern Lit x      = In (LitF x)
%% > pattern Var s      = In (VarF s)
%% > pattern Bin l op r = In (BinF l op r)

%% Now, arithmetic expression trees can be created and pattern matched
%% against 

In general, pattern synonyms come in three flavors: unidirectional,
implicitly bidirectional, and explicitly bidirectional pattern
synonyms. Each flavor can further come either as a normal prefix,
infix, or a record pattern synonym. The latter exposes record
selectors to work on the underlying pattern. The different pattern
synonym forms are explained in detail in GHC's users
manual~\cite{ghc-users-guide}.

To add pattern synonyms to Template Haskell, I had to extend the TH
library as well as the GHC internal modules \texttt{hsSyn/Convert.hs},
\texttt{deSugar/DsMeta.hs}, and \texttt{typecheck/TcSplice.hs}. In
Template Haskell's public library, I added syntax constructors as well
as corresponding syntax construction functions to represent pattern
synonyms inside TH object programs. Moreover, I changed the
reification datatype to also take pattern synonyms into account.

Inside GHC, I modified modules \texttt{deSugar/DsMeta.hs} and
\texttt{hsSyn/Convert.hs} to also convert between Haskell's pattern
synonyms and their representation in Template Haskell. In particular,
I extended \texttt{deSugar/DsMeta.hs} to desugar Haskell's pattern
synonyms into a core expression denoting a pattern synonym in Template
Haskell syntax. Similarly, I adjusted \texttt{hsSyn/Convert.hs} to
convert the Template Haskell representation of pattern synonyms into
the corresponding Haskell abstract syntax. Finally, I modified
\texttt{typecheck/TcSplice.hs} to also provide reification of pattern
synonyms, namely to return a pattern synonym's type signature upon
request.

My initial implementation draft was quite straightforward and took
only around two weeks to complete. This was mainly because I could
reuse most of GHC's already existing Template Haskell architecture to
also desugar, convert, and reify pattern synonyms. However, the devil
was then in the detail. In particular, after completing my first
implementation draft, I faced two major problems, which took me around
6 more weeks (on and off) to fully resolve.

The first problem concerned the peculiar types of pattern synonyms. In
general, a pattern synonym's type signature is of the following form:

< pattern P :: forall a1 .. an. CReq
<           => forall b1 .. bm. CProv
<           => t1 -> t2 -> .. -> tn -> t
< pattern P x1 x2 .. xn = <some-pattern>

That is, a pattern synonym's type comes with two forall quantifiers
and two constraint contexts. The first @forall@ quantifier quantifies
over all universially bound type variables and its context @CReq@
denotes these type variables' required constraints. The second
@forall@ quantifier refers to the pattern synonym's existentially
bound type variables and its context @CProv@ refers to those
variable's provided constraints.

Due to their unusual type shapes, I couldn't as easily reuse already
existing machinery for the reification of Haskell types (in
\texttt{typecheck/TcSplice.hs}) and for converting Template Haskell
types to their Haskell analogs (in \texttt{hsSyn/Convert.hs}), as I
had originally thought. Instead I had to special-case the reification
of pattern synonym type signatures as well as their conversion from
Template Haskell syntax to real Haskell syntax.

After resolving this problem, a second major issue concerned the
implementation of record pattern synonyms. Internally in GHC, record
pattern synonyms are modeled with both names for the public record
selectors and (hidden) names for the pattern synonym's internal (right
hand side) variables. However, from a programmer's perspective a
record pattern synonym defines only its record selector
names. Correspondingly, Richard Eisenberg wanted to expose the
intuitive API inside Template Haskell, even though the Haskell AST for
record pattern synonyms internally adds more structure. To expose the
succinct TH API, I had to think more carefully when converting pattern
synonyms in real Haskell ASTs to their corresponding Template Haskell
ASTs and vice versa in \texttt{deSugar/DsMeta.hs} and
\texttt{hsSyn/Convert.hs}, respectively. Essentially a record pattern
synonym's local names had to be forgotten when desugaring them in
\texttt{deSugar/DsMeta.hs} and later, when converting them back to
Haskell syntax in \texttt{hsSyn/Convert.hs} these names had to be
regenerated from scratch. Doing this (slightly) more involved
conversion between Haskell's abstract syntax and Template Haskell
syntax hadn't been needed before, so I had to come up with a design
and the machinery implementing it. In the end, the solution turned out
to be quite small code-wise, but accomplishing it required me to
understand the TH implementation and its various interactions much
better than I had before.

What made the above problem particularly difficult to solve was an
unrelated GHC bug. In particular, once I had added support for record
pattern synonyms, I noticed that quoting and splicing did not work as
expected. Learning about GHC debugging and turning on the debug flags
@-ddump-splices@, @-dddump-rn@, and @-ddump-ds@, revealed the problem:
splicing in Template Haskell record pattern synonyms as Haskell code
somehow broke the link between a record pattern synonym's selector
binder and this selector's usage sites. Digging further into GHC
debugging, I used the trace and debug utilities in
\texttt{utils/Outputable.hs} to put custom trace messages into GHC's
renamer code base. This finally rooted the cause for the incorrect
name resolution of the spliced in pattern synonyms: The newly added
GHC extension \texttt{DuplicateRecordFields} hadn't been made
compatible with Template Haskell. In particular, one invariant of
Template Haskell says that spliced in object programs are already
renamer resolved. However, the \texttt{DuplicateRecordFields}
extension did not respect this invariant and sought to rename spliced
in selectors anyways, thus dissolving the link between selector
binders and their usage sites. As it turned out, not only record
pattern synonym selectors were affected, but in fact any datatype's
record selectors. Hence, fixing the issue not only solved my task of
supporting pattern synonyms in Template Haskell, but also resolved a
regression in GHC 8.0~\cite{patsyns-bugfix}.

To test the ``pattern synonyms'' patch, I wrote a unit test suite
exercising quoting, splicing, and reification of various pattern
synonyms. Parts of the unit tests were reused and originally come from
Rik Steenkamp's patch ``improve printing of pattern
synonyms''~\cite{rdragon-patch}.

\section{Conclusion}

In the course of the last four months, I've explored meta programming
in GHC's Template Haskell extension. To learn about Template Haskell,
I first dived into the underlying theory by
reading~\cite{th1,th2,th3,qq,aosa,yesod,shakespeare}. Second, I
fostered my understanding of meta programming by developing a couple
of toy programs show-casing the features of Template Haskell. Many
examples have been described in Section~\ref{sec:th-review}, a few
more examples can be found at
\url{http://www.github.com/bollmann/th-samples.git}. After getting a
basic understanding of meta programming and the functionality offered
by Template Haskell, I then started studying Template Haskell's
implementation, i.e., the \texttt{template-haskell} library as well as
the \texttt{TemplateHaskell} GHC extension. Besides reading the source
code, I also began looking into current issues with Template Haskell
as mentioned in the GHC bug tracker. In particular, I investigated
tickets \texttt{\#9022}, \texttt{\#11145}, \texttt{\#10707}, and
\texttt{\#9693}. The two former tickets turned out to be already
fixed, so that I could close them easily after adding corresponding
regression tests; investigating the latter two tickets wasn't as
successful unfortunately, as I got overwhelmed by GHC's code base
while trying to understand them. Nonetheless looking into these first
tickets helped me familiarize myself with GHC's development process,
and with submitting patches for review on Phabricator.

Next, I started tackling my bigger task: to also support GHC's
\texttt{PatternSynonym} extension inside of Template Haskell. This
task and its challenges are described in detail in
Section~\ref{sec:patsyns} and took around two months to
complete. During this time I communicated extensively with Richard
Eisenberg, Matthew Pickering, and Ben Gamari, who reviewed and
commented on my patches. My gratitude goes particularly to Richard
Eisenberg, who has relentlessly given feedback on the former drafts of
my patch and whose comments have improved the end quality by a lot. I
think about a third of the total development time was spent discussing
design choices (or strange errors) on Phabricator.

Concluding, I think I've learned a whole lot of new things about
Haskell during this independent study! Besides studying Haskell's meta
programming using Template Haskell, this independent study exposed me
to big Haskell systems, most notably parts of the Glasgow Haskell
Compiler and the \texttt{template-haskell} library. This exposure has
let me \textit{read} significant chunks of Haskell code, permitting me
to see common Haskell paradigms (like Applicatives, Monads, Phantom
Types, etc.) elegantly solve the practical problems at hand. Moreover,
this independent study let me explore various GHC extensions (such as
\texttt{TemplateHaskell}, \texttt{PatternSynonyms},
\texttt{ViewPatterns}, \texttt{TypeFamilies}, \texttt{RankNTypes}) for
the first time. To this end, I think it has enhanced my understanding
of Haskell greatly!

\bibliographystyle{alpha} \bibliography{refs}

\end{document}
