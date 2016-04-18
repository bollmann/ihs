\documentclass{article}
%include polycode.fmt
%options -fglasgow-exts
%format tick = "\,\,\textquotesingle"
%format ticktick = "\,\,\textquotesingle\textquotesingle"

\usepackage{todonotes}
\usepackage[top=2cm,left=4cm,right=4cm,bottom=2cm]{geometry}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{textcomp}

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

%% The central power of Template Haskell lies in the construction of meta
%% programs, that is, programs which construct other programs due to
%% their execution at compile time. To avoid confusion in the sequel, we
%% distinguish between meta programs and the programs they compute. Meta
%% programs are programs that take as their input data other programs,
%% which they manipulate by some algorithmic means. Object programs, on
%% the other hand, are the programs that act like data to the meta
%% programs, i.e., the programs being manipulated by and resulting as
  %% output from the meta programs.

%% Compile-time meta programming has many use cases. For example, it
%% empowers a user to write many, syntactically different, object
%% programs all at once by means of a single meta program. All that is
%% needed is a uniform, algorithmic description to create the different
%% object programs. And the meta program then precisely implements the
%% algorithm to compute all the different object programs as its
%% result. This proves useful for example to avoid writing the same
  %% repetitive, boilerplate code over and over again.

\todo{Finish me!}

Template Haskell (TH) is the standard framework for doing type-safe,
compile-time meta programming in the Glasgow Haskell Compiler
(GHC). It allows writing Haskell meta programs, which are typechecked
and run at compile-time, and which produce Haskell programs as the
results of their execution.

Template Haskell was conceived by Tim Sheard and Simon Peyton Jones in
\cite{th1} by drawing on the ideas of Lisp macros, but in the typed
setting of Haskell. Since then, the original implementation has
evolved quite a bit \cite{th2, qq, th3}. Most notably, in 2007
Geoffrey Mainland added support for quasi quoting \cite{qq}, which
makes the embedding of domain specific languages yet easier.

As it exists today, Template Haskell has two main areas of
application: Haskell code generation and facilitating the embedding of
domain specific languages.

As a code generator, Template Haskell empowers a user to write many,
syntactically different, object programs all at once by means of a
single meta program. All that is needed is a uniform, algorithmic
description to create the different object programs. And the meta
program then precisely implements the algorithm to compute all the
different object programs as its result. This proves useful for
example to avoid writing the same repetitive, boilerplate code over
and over again. To this end, Template Haskell is used (among many
others) in the @aeson@ library to automatically derive a data type's
@ToJSON@ and @FromJSON@ instances for JSON serialization; or in the
@lens@ library to mechanically create a data type's lenses.

As a framework for creating domain specific languages (EDSLs),
Template Haskell allows a user to embed programs written in another
programming language inside a Haskell program. This enables writing
parts of the program in the concrete, domain specific syntax of a
different programming language. It has the benefit to think about --
and to express -- domain specific problems in the language best suited
for the task. In particular, it lets a user focus on their domain
specific problem and removes all additional language burdens induced
by inconvenient syntax, unsuited control constructs, etc. Programs
from the embedded language are parsed and translated into
corresponding (but syntactically heavier) Haskell code at compile-time
by Template Haskell. In this sense, (e.g.,) the shakespearean template
languages from the @shakespeare@ library use Template Haskell at their
core. They expose succinct domain specific languages to build HTML,
CSS, and Javascript code inside of a Haskell based web application.

\todo{finish me! Write about the organization of the following sections.}

\todo[inline]{
  - What is Template Haskell? How did it come about? (Template Haskell
Paper1, Paper2, Quasi-Quote paper), Adoption of TH in real libraries
to solve real-world problems (Yesod's Shakespearean languages!)?

- Even though its called the ugly under the HS extensions, it is the
necessary. A LOT (see reverse dependencies) of packages depend on it.}

\section{Learning Template Haskell by Examples}

In this section, I will review the Template Haskell functionality as
introduced in \cite{th1, th2, qq} to write meta programs. In the
first set of examples I will show-case Template Haskell's potential as
a code generator; in the second set of examples I'll highlight its
facilities to create type-safe embedded domain specific languages
(EDSLs).

To avoid confusion in the sequel, we distinguish between Template
Haskell's compile-time meta programs and the object programs they
generate. Meta programs are programs that compute programs as their
data; they manipulate other programs by some algorithmic means. Object
programs, on the other hand, are the programs that act like data to
the meta programs, i.e., the programs being manipulated by and
resulting as output from the meta programs.

\subsection{Template Haskell as a Code Generator}

As an introductory example, consider Haskell's @Prelude@ function
|curry :: ((a,b) -> c) -> a -> b -> c|, which converts a function
taking a pair to its curried equivalent. Unfortunately, there are no
@Prelude@ functions that provide the same currying functionality for
functions taking arbitrary \(n\)-tuples. Moreover, having to write
more than a few of these functions manually is, while trivial, a very
repetitive and cumbersome task. Instead we wish to generate needed
|curry3|, |curry5|, or |curry8| functions through a single meta
program on demand. Template Haskell let's us do just this. The idea is
to write a meta function |curryN :: Int -> Q Exp| which, given a
number \(n \geq 1\), \textit{constructs the source code} for an
\(n\)-ary |curry| function:

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
hereby generated monadically by function |newName :: String -> Q Name|
to always generate fresh names not used anywhere else. Hence, the
value returned by |curryN| is a monadic computation of type @Q
Exp@. When executed, this monadic computation yields an expression
@Exp@ representing the object program of an \(n\)-ary curry
function. For example, |(curryN 3)| yields a monadic computation,
whose result expression holds an object program of the |curry3|
function of type |((a, b, c) -> d) -> a -> b -> c -> d| in abstract
syntax.

To run a meta program like |curryN| at compile time, Template
Haskell's \textit{splice} operator ``|$|'' is used. When applied to a
@Q Exp@ computation it performs this computation and converts the
resulting object program to real Haskell code. Hence, enclosing a
Haskell meta program by ``|$(..)|'' means to evaluate it and to splice
in the generated Haskell code as the result of the splice. To ensure
type safety, the meta program is type checked before being run at
compile time. Moreover, after splicing in the resulting object program
the entire Haskell module is typechecked again from scratch. For
example, writing |$(curryN 3)| typechecks and then evaluates the meta
function |(curryN 3)| at compile time and puts the resulting object
program |\f x1 x2 x3 -> f (x1, x2, x3)| in place of the splice. After
running all of a Haskell module's meta functions, typechecking
restarts from scratch.

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

< curry1  = \f x1 -> f (x1)
< curry2  = \f x1 x2 -> f (x1, x2)
< curry3  = \f x1 x2 x3 -> f (x1, x2, x3)
< curry4  = \f x1 x2 x3 x4 -> f (x1, x2, x3, x4)
< ...
< curry20 = \f x1 x2 ... x20 -> f (x1, x2, ..., x20)

Note that in this case, |genCurries| returns a list of function
declarations that bind the anonymous lambda abstractions built by
|curryN|. Furthermore, to name the function bindings, we use the
function |mkName :: String -> Name| instead of |newName :: String -> Q
Name|. The reason is that here we want to generate functions |curry1|
to |curry20| with exactly the prescribed names, so they can be
captured and referred to from other parts of the program.

Evaluating Haskell (meta) programs at compile time and splicing in the
generated object programs as regular Haskell code is the first central
building block of Template Haskell. The two other core mechanisms are
exhibited by the implementations of |curryN| and |genCurries|:
algebraic data types and the quotation monad @Q@.

Object programs created by Template Haskell are represented as regular
algebraic data types, describing a program in the form of an abstract
syntax tree. The Template Haskell library provides algebraic data
types @Exp@, @Pat@, @Dec@, and @Type@ to represent Haskell's surface
syntax of expressions, patterns, declarations, and types,
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
construction of object programs is \textit{program reification}, which
allows to query compile-time information during the object program's
construction. We will explain this feature in detail later.

Splicing in object programs with ``|$|'' and building them from
algebraic data types inside the quotation monad @Q@ (almost)
constitutes the functionality of Template Haskell. However,
constructing object programs in terms of their abstract syntax trees
is quite verbose and leads to clumsy meta programs. Therefore the
Template Haskell API also provides two further interfaces to build
object programs more tersely: \textit{syntax construction functions}
and \textit{quotation brackets}.

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
continue. Using syntax construction functions, however, frees us from
explicitly performing monadic program parts when constructing a larger
program. This allows us to hide the monadic construction of
|genCurries|, thus making the code a little shorter:

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

While the syntax constructors work with raw Haskell expressions, the
syntax construction functions expect monadic Haskell expressions. They
construct an object program directly in @Q@, thus allowing the API
consumer to not have to do all the monadic wrapping and unwrapping
manually. For every syntax constructor, there is a corresponding
monadic syntax construction function provided.

%% This gives the programmer the choice to either explicitly construct
%% object programs inside the @Q@ monad or to do the monadic construction
%% implicitly with syntax construction functions.

On top of the syntax construction functions, quotation brackets are a
further shortcut for representing Haskell code. They allow to specify
an object program using just regular Haskell syntax by enclosing it
inside oxford brackets |[|| .. ||]|. That way, object programs can be
specified yet much more succinctly. For example, a meta program
building a Haskell expression for the identity function is still quite
verbose, if expressed as abstract syntax using either ADTs or syntax
construction functions:

> genId :: Q Exp
> genId = do
>   x <- newName "x"
>   lamE [varP x] (varE x)

Using quotation brackets, writing the same meta program can be
abbreviated much further as:

> genId' :: Q Dec
> genId' = [| \x -> x |]

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
Haskell code; in contrast the quotation brackets |[|| .. ||]| turn
real Haskell code into an object program. Consequently, quotation
brackets and the splice operator cancel each other out. The equation
|$([|| e ||]) = e| holds for all expressions \(e\) and similar
equations hold for declarations, and types \cite{th2}.

In addition, there is support for quoting Haskell (value and type)
identifiers as corresponding Template Haskell @Name@s. This allows to
refer to regular Haskell identifiers from within Template Haskell
object programs. For example, writing |`genId| yields a TH @Name@
referring to the |genId| identifier. Similarly, |``Q| gives a @Name@
referring to the @Q@ type identifier.

As a second example that uses both syntax construction functions as
well as quotation brackets, let's consider a meta program |mapN :: Int
-> Q Dec| to build ``generic'' |map| functions at
compile-time. Invoking |$(mapN 1)| should generate the well-known |map
:: (a -> b) -> [a] -> [b]| function; evaluating |$(mapN 2)| should
splice in a binary map function of type |(a -> b -> c) -> [a] -> [b]
-> [c]|, and so on\footnote{Note that \(n\)-ary maps are better
  written using Applicative Functors and @ZipList@s. For understanding
  Template Haskell as a code generator, this example is still useful
  though.}.

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
>                   consPatts = [ [p| $(varP x) : $(varP ys) |] | (x,ys) <- xs `zip` ys ]
>                   apply     = foldl (\g x -> [| $g $(varE x) |])
>                   first = apply (varE f) xs
>                   rest  = apply (varE name) (f:ys)
>               clause argPatts (normalB [| $first : $rest |]) []
>     cl2  = clause (replicate (n+1) wildP) (normalB (conE `[])) []

The implementation of |mapN| is very much in the spirit of meta
function |curryN| from the first example. For instance, evaluating
splice |$(mapN 3)| splices in the following map function at compile
time:

> map3 f (x:xs) (y:ys) (z:zs) = f x y z : map3 f xs ys zs
> map3 _ _      _      _      = []

Nonetheless, meta function |mapN| exhibits a couple of new Template
Haskell features: First, quotation brackets and splices are used in
several places to abbreviate the object program construction. For
example, helper |apply| used to generate |map3|'s body |f x y z : map3
f xs ys zs| exemplifies the use of quotation brackets; it also
highlights how splicing (``|$|'') and quotes (``|[|| .. ||]|'') cancel
each other out. Second, identifier quotes (namely, |`[]|) are used to
create an object program @Name@ that refers to Haskell's built-in list
constructor |[]|. Third, the example shows how all three APIs for
building Template Haskell object programs can be interleaved. The
lowermost verbose API of building a raw data type inside the quotation
monad @Q@ can be abbreviated, where possible, with syntax constructor
functions and quotation brackets.

Lastly, the |mapN| example highlights how Haskell's static scoping is
extended to object programs. The scoping principle for object programs
is just as in normal Haskell: Identifiers are bound to their lexically
enclosing binders in scope, where the object program is
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

The final major Template Haskell feature not yet described is program
\textit{reification}. Briefly, reification allows a meta program to
query compile-time information about other program parts while
constructing the object program. It allows the meta program to inspect
other program pieces to answer questions such as: ``what's this
variable's type?'', ``what are the type class instances of this type
class?'', or ``which constructors does this data type have and and how
do they look like?''. The main use case is to generate boilerplate
code which ``auto-completes'' manually written code. A prime example
is to generically derive type class instances from bare data type
definitions.

Suppose we've defined the following polymorphic data types for
representing potentially erroneous values, lists, and binary trees,
respectively:

> data Result e a = Err e | Ok a
> data List    a = Nil | Cons a (List a)
> data Tree    a = Leaf a | Node (Tree a) a (Tree a)

Moreover, suppose we want to derive @Functor@ instances for all of
these types. Deriving these instances manually is straightforward, but
writing them all out by hand is quite cumbersome. Especially since
writing a @Functor@ instance follows the same pattern across all of
the above types and in fact any type @T a@.

To make a type constructor @T@ an instance of @Functor@, function
|fmap :: (a -> b) -> T a -> T b| needs to be implemented. Its
definition is hereby precisely fixed by parametricity and the functor
laws: By parametricity, all values of type @a@ must be replaced
according to the provided function with values of type
@b@. Furthermore, by the functor laws, all other shapes of the input
value of type @T a@ must be preserved when transforming it to the
output value of type @T b@.

The idea of this algorithm is implemented by meta function
|deriveFunctor :: Name -> Q [Dec]| below. Given the name of a type
constructor (e.g. @Result@, @List@, etc.), it derives the code for
this type constructor's @Functor@ instance.

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
>
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

For example, running the splice |$(deriveFunctor ``Tree)| generates the
following code:

> instance Functor Tree where
>   fmap f (Leaf x)     = Leaf (f x)
>   fmap f (Node l x r) = Node (fmap f l) (f x) (fmap f r)

Meta function |deriveFunctor| hereby shows reification in
action. Calling function |reify :: Name -> Q Info| on the input type
constructor's name yields information about this data type's
definition. It thus learns whether the data type was defined using the
@data@ or @newtype@ keyword, which constructors it defines and what
their shapes are. Based on the learned structure, |deriveFunctor| is
then able to generate a suitable definition of |fmap| and its
different clauses via helper functions |genFmap|, |genFmapClause|, and
|newField|, respectively. The idea is to generate one |fmap| clause
for each of the data type's constructors. And each clause then
transforms its constructor by recursively modifying all of the
constructor's fields of type @a@ through |fmap|'s function @f@, while
retaining all other shapes.

In an analogous manner, a function |deriveFoldable :: Name -> Q [Dec]|
can be written to derive a data type's @Foldable@ instance by
providing function |foldMap :: Monoid m => (a -> m) -> T a ->
m|. Again, |foldMap|'s definition follows directly from a data type's
bare definition, which can be observed by means of
reification\footnote{In fact, the example at
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
expressions are easily defined by an algebraic datatype capturing
their structure, as well as an evaluator checking whether a regular
expression matches some input string\footnote{This example draws on
  Penn's CIS 552 \textit{Advanced Programming} course, specifically
  Homework \#5:
  http://www.seas.upenn.edu/~cis552/current/hw/hw05/Main.html}:

> data RegExp
>   = Char (Set Char)          -- [a], [a-z]; matches a single input character in a given range
>   | Alt RegExp RegExp        -- r1 || r2 (alternation); matches either r1 or r2
>   | Seq RegExp RegExp        -- r1 r2 (concatenation); matches r1 followed by r2
>   | Star RegExp              -- r* (Kleene star); matches r zero or more times
>   | Empty                    -- \(\epsilon\); matches only the empty string
>   | Void                     -- \(\emptyset\); matches nothing (always fails)
>   | Var String               -- a variable holding another regexp (explained later)
>   deriving Show

> match :: RegExp -> String -> Bool
> match r s = nullable (foldl deriv r s)

The evaluator |match| is hereby based on the concepts of
derivatives~\cite{regexps-derivs}: an initial regular expression |r|
matches an input string |s|, if |r| matches the first character of |s|
and its derivative regular expression |(deriv r)| matches the remainder
of |s|:

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
specifying regular expressions in abstract syntax is tedious and
unintuitive. For example, consider defining a regular expression for
checking the wellformedness of email addresses that end in the
top-level domain @.com@. In its usual concrete syntax, such a regular
expression is easily conceived as
@([a-z]|[0-9])*@@([a-z]|[0-9])*.com@, but writing it using the
@RegExp@ dataype is terribly verbose and unintuitive:

> validDotComMail :: RegExp
> validDotComMail = Seq
>   (Star
>     (Alt (Char (fromList "abcdefghijklmnopqrstuvwxyz"))
>          (Char (fromList "0123456789"))))
>   (Seq (Char (fromList "@"))
>     (Seq (Star
>       (Alt (Char (fromList "abcdefghijklmnopqrstuvwxyz"))
>            (Char (fromList "0123456789"))))
>     (Seq (Char (fromList "."))
>     (Seq (Char (fromList "c"))
>     (Seq (Char (fromList "o"))
>          (Char (fromList "m")))))))

Hence, we would like to embed the concrete surface language of regular
expressions inside of the Haskell host language. Template Haskell lets
us do this using quasi quotes and the @QuasiQuotes@ extension. Quasi quotes
let us define a @QuasiQuoter@ to compile a regular expression's
concrete syntax into the above @RegExp@ datatype at compile
time.

> regex :: QuasiQuoter
> regex = QuasiQuoter {
>     quoteExp = unTypeQ . compile
>   , quotePat  = notHandled "patterns"
>   , quoteType = notHandled "types"
>   , quoteDec  = notHandled "declarations"
>   } where notHandled things =
>             error $ things ++ " are not handled by the regex quasiquoter."

> alph


A quasi quoter simply consists of four parsers to parse a raw string
into corresponding abstract Haskell syntax.

\section{Template Haskell's Implementation in GHC}

* @Language.Haskell.TH@ API (TH.hs, TH/Syntax.hs, TH/Lib.hs,
TH/Ppr.hs)

* Offers a small, yet complete AST of Haskell's concrete surface
syntax (much less involved than what's offered by GHC's @HsSyn@).

* Convert.hs:
* DsMeta.hs:
* TcSplice.hs:

\section{Adding Pattern Synonym Support to Template Haskell}

\section{Conclusion}

\bibliographystyle{alpha}
\bibliography{refs}

\end{document}

%% old cruft:

%% To embed a domain specific language with Template Haskell, a
%% \textit{quasi quoter} has to be specified. Formally, a quasi quoter is
%% a value of type @QuasiQuoter@ defined as follows:

%% > data QuasiQuoter = QuasiQuoter {
%% >   quoteExp  :: String -> Q Exp,
%% >   quotePat  :: String -> Q Pat,
%% >   quoteType :: String -> Q Type,
%% >   quoteDec  :: String -> Q Dec
%% > }

%% A quasi quoter thus consists of four parsers which parse strings into
%% abstract Haskell syntax. Its purpose is to parse the embedded domain
%% specific language and to convert it into corresponding Haskell
%% syntax. Having defined a quasi quoter, say |qq|, it can be invoked by
%% writing |[qq|| .. ||]|. Anything inside the quasi quote is treated as
%% part of the embedded domain specific language.

%% As a first example for embedding a different language into a Haskell
%% program, suppose we want to build a simple web application in
%% Haskell. The web application's business logic sits hereby on top of a
%% Haskell webserver which receives and answers client requests: A
%% client's incoming page request is used to lookup the page contents in
%% a database. The page contents are then used to populate an HTML
%% template which is the same accross all of the web application's web
%% pages.

%% Using Template Haskell and its quasiquotes feature, we can embed the
HTML template natively into our web application. 
