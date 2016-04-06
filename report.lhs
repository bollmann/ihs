\documentclass{article}
%include polycode.fmt
%options -fglasgow-exts
\usepackage{todonotes}
\usepackage[top=2cm,left=4cm,right=4cm,bottom=2cm]{geometry}
\usepackage[utf8]{inputenc}

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
  implementation inside GHC to also support the newly added Pattern
  Synonyms feature.}

\section{Introduction}

\todo{Write me!}

- What is Template Haskell? How did it come about? (Template Haskell
Paper1, Paper2, Quasi-Quote paper), Adoption of TH in real libraries
to solve real-world problems (Yesod's Shakespearean languages!)?

- Motivation for TH:
* Automate writing syntactically different, yet somehow similar programs all at once.
  (e.g. generic mapN, zipN, ... functions, ...) -> reduce having to
  repeatedly write the same code.

* Automate writing repetitive/boilerplate code (deriving instances).

* Allow the embedding of domain specific languages.
- type safe regular expressions. (?)
- SubstLang
- much more powerful: type-safe routes/etc. in Yesod.

- Even though its called the ugly under the HS extensions, it is the
necessary. A LOT (see reverse dependencies) of packages depend on it.

- What are the main benefits of TH?
  1. Write many programs using just a single meta program.
  2. EDSLs.

The central power of Template Haskell lies in the construction of meta
programs, that is, programs which construct other programs due to
their execution at compile time. To avoid confusion in the sequel, we
distinguish between meta programs and the programs they compute. Meta
programs are programs that take as their input data other programs,
which they manipulate by some algorithmic means. Object programs, on
the other hand, are the programs that act like data to the meta
programs, i.e., the programs being manipulated by and resulting as
output from the meta programs.

Compile-time meta programming has many use cases. For example, it
empowers a user to write many, syntactically different, object
programs all at once by means of a single meta program. All that is
needed is a uniform, algorithmic description to create the different
object programs. And the meta program then precisely implements the
algorithm to compute all the different object programs as its
result. This proves useful for example to avoid writing the same
repetitive, boilerplate code over and over again.

\section{Learning Template Haskell by Examples}

In this section, I will review the Template Haskell functionality as
introduced in \cite{th1, th2, qq} to write meta programs. In the
first set of examples I will show-case Template Haskell's potential as
a code generator; in the second set of examples I'll highlight its
facilities to create type-safe embedded domain specific languages
(EDSLs).

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
resulting object program to real Haskell code. That is, enclosing a
Haskell meta program with the ``|$|'' operator means to evaluate it
and to splice in the generated Haskell program as the result. To
ensure type safety, the meta program is typechecked before being run
at compile time. For example, writing |$(curryN 3)| evaluates the meta
program of the |curry3| function at compile time and puts the result
|\f x1 x2 x3 -> f (x1, x2, x3)| in place of the splice.

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
to |curry20| with known names, so they can be captured and referred to
from other parts of the program.

Evaluating Haskell code at compile time and splicing in the generated
object programs as regular Haskell code is the first central building
block of Template Haskell. Two further core mechanisms are shown in
the implementations of |curryN| and |genCurries|: algebraic data types
and the quotation monad @Q@.

Object programs created by Template Haskell are represented by regular
algebraic data types in the form of abstract syntax trees. In the
|curryN| example, we represented the generated lambda abstraction as a
Haskell expression with constructors @VarE@, @LamE@, @AppE@, @TupE@,
etc. \todo{should we remove this example?} This Haskell expression
furthermore consisted of pattern expressions for the matched
variables, so we also used @Pat@'s @VarP@ constructor. Similarly, in
the |genCurries| example we represented the generated function
declaration using the @Dec@ data type and used constructors @FunD@,
@Clause@, and @NormalB@ to represent it. In general, the Template
Haskell library provides algebraic data types @Exp@, @Pat@, @Dec@, and
@Type@ to represent Haskell's surface syntax of expressions, patterns,
declarations, and types, respectively. Virtually every concrete
Haskell syntactic construct has a corresponding abstract syntax
constructor in one of the four ADTs. Furthermore, all Haskell
identifiers are represented by the abstract @Name@ data type. By
representing object programs as regular algebraic data types (and thus
as data), normal Haskell can be used as the meta programming language
to build object programs.

Second, TH object programs are built inside the quotation monad
@Q@. This monad is performed by the splice operator ``|$|'' at
compile-time as part of evaluating the meta program. In the examples
so far, the @Q@ monad was only needed to provide fresh identifiers
with function |newName :: String -> Q Name| for the generated Haskell
expressions. The other features that require a monadic construction of
object programs are \textit{program reification} and extending
Haskell's static scoping to the object program level. We will explain
both of these features later.

%% Briefly, program reification allows a meta program to query compile
%% time information about other program parts while constructing an
%% object program. For instance, a meta program asked to automatically
%% derive a typeclass instance based on the definition of a data type
%% needs to know about the data type's value constructors and
%% fields. Precisely this information can be obtained using reification.

Splicing in object programs with ``|$|'' and building them from
algebraic data types inside the quotation monad @Q@ (almost)
constitutes the functionality of Template Haskell. However,
constructing object programs in terms of their abstract syntax trees
is quite verbose and leads to clumsy meta programs. Therefore the
Template Haskell API also provides two further interfaces to build
object programs more conveniently: \textit{syntax construction
  functions} and \textit{quotation brackets}.

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
program. This allows us to write |genCurries| a little more
succinctly:

> genCurries' :: Int -> Q [Dec]
> genCurries' n = sequence [ mkCurryDec i | i <- [1..n] ]
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
syntax construction functions expect Haskell expressions wrapped
inside monad @Q@. They construct an object program directly in @Q@,
thus allowing the API consumer to not have to do all the monadic
wrapping and unwrapping manually.

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

Quotation brackets quote regular Haskell code as their corresponding
object program fragments inside the @Q@ monad. By doing so, they
represent the dual of the already introduced splice operator ``|$|'':
Evaluating a meta program with ``|$|'' splices in the generated object
program as real Haskell code; in contrast the quotation brackets |[||
  .. ||]| turn real Haskell code into an object program. Consequently,
quotation brackets and the splice operator cancel each other out. The
equation |$([|| e ||]) = e| holds for all expressions \(e\) and
similarly for patterns, declarations, and types \cite{th2}.

There are four different kinds of quotation brackets: |[e|| .. ||]|,
|[p|| .. ||]|, |[d|| .. ||]|, and |[t|| .. ||]| for quoting Haskell
expressions, patterns, declarations, and types, respectively. The
quotation bracket |[|| .. ||]| is hereby just another way of writing
|[e|| .. ||]|. Furthermore, there is support for quoting Haskell
identifiers as corresponding Template Haskell @Name@s. For example,
writing |'genId| yields a TH @Name@ referring to the |genId|
identifier. Similarly, |''Q| gives a @Name@ referring to the @Q@ type
identifier. Using the quotation brackets, all of Haskell's concrete
programs can also be represented as object programs in Template
Haskell.

As a further example that uses both syntax construction functions as
well as quotation brackets, let's consider a meta program |mapN :: Int
-> Q Dec| to build ``generic'' |map| functions at
compile-time. Invoking |$(mapN 1)| should generate the well-known |map
:: (a -> b) -> [a] -> [b]| function; evaluating |$(mapN 2)| should
splice in a binary map function of type |(a -> b -> c) -> [a] -> [b]
-> [c]|, and so on\footnote{Note that \(n\)-ary maps are better
  written using Applicative Functors and @ZipList@s. For understanding
  Template Haskell as a code generator, this example is still useful
  though.}.

%format ` = "\; \lq"
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

The implementation of |mapN| is very much in the spirit of function
|curryN| from the first example. For instance, evaluating splice
|$(mapN 3)| splices in the following map function at compile time:

> map3 f (x:xs) (y:ys) (z:zs) = f x y z : map3 f xs ys zs
> map3 _ _      _      _      = []

Nonetheless, meta function |mapN| exhibits a couple of new Template
Haskell features: First, quotation brackets and splices are used in
several places to abbreviate the object program construction by
``lifting'' concrete Haskell syntax into the object program. Function
|apply| (e.g.,) used to generate |map3|'s body |f x y z : map3 f xs ys
zs| exemplifies quotation brackets; it also highlights how splicing
(``|$|'') and quotes ( ``|[|| .. ||]|'') cancel each other
out. Second, identifier quotes (namely, |'[]|) are used to create an
object program name referring to the built-in empty list constructor
|[]|.

Moreover, the example shows how all three APIs (Haskell ADTs and the
quotation monad, syntax construction functions, and quotation
brackets) can be mixed in the construction of the object program.

TODO: Explain extension of static scope to the object level here!

%% Besides giving access to fresh names via function |newName ::
%% String -> Q Name|, the monad's main purpose is to extend Haskell's
%% static scoping discipline to the object programs constructed with
%% Haskell \cite{th1}. The scoping principle is just as in normal
%% Haskell: Identifiers inside an object program are bound to their
%% lexically enclosing binders in scope, when the object program
%% \textit{is defined}. Achieving static scoping is not straightforward
%% due to the interplay of splices |$(..)| and a feature that hasn't been
%% introduced yet: \textit{quotation brackets} |[|| .. ||]|.

which allows splicing in object programs
into real Haskell code at arbitrary locations. And at the splice
point, the names used in the object program might clash with the names
used in the surrounding Haskell program. \todo{should we add an
  example here?} Therefore the @Q@ monad provides the function
|newName :: String -> Q Name| that generates a fresh, non-capturable
name every time it is invoked.

For instance, if we didn't
use a monadic computation

also occur as binders in the surrounding
program. Consider for example the following (illegal) snippet:

< module A where
<
< foo = 42
<
< metaProg :: Q Exp
< metaProg = return x
<

< module B where
<
< \f -> $(metaProg)

> uncurryN :: Int -> Q Exp
> uncurryN n = do
>   f  <- newName "f"
>   xs <- replicateM n (newName "x")
>   let ntup = TupP (map VarP xs)
>       app  = foldl AppE (VarE f) (map VarE xs)
>   return $ LamE [VarP f, ntup] app


\section{Overview of Template Haskell's offered Functionality}

* @Language.Haskell.TH@ API (TH.hs, TH/Syntax.hs, TH/Lib.hs, TH/Ppr.hs)

* Offers a small, yet complete AST of Haskell's concrete surface
syntax (much less involved than what's offered by GHC's @HsSyn@).

* provides means of static and dynamic scope resolution mechanisms. (Q Monad)

* High-level constructs of quotation brackets [| ... |] and splice
operators to construct metaprograms more efficiently.

\section{Template Haskell's Implementation in GHC}

\section{Adding Pattern Synonym Support to Template Haskell}

\section{Conclusion}

\section{Sources}

\bibliographystyle{alpha}
\bibliography{refs}

\end{document}
