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
Paper1, Paper2), Adoption of TH in real libraries to solve real-world
problems (Yesod!)?

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

In this section, I will teach the basic concepts of Template Haskell
to write meta programs. In the first set of examples I will show-case
Template Haskell's potential as a code generator; in the second set of
examples I'll highlight its facilities to create very concise, yet
type-safe embedded domain specific languages (EDSLs).

As an introductory example, consider Haskell's @Prelude@ function
|curry :: ((a,b) -> c) -> a -> b -> c|, which converts a function
taking a pair to its curried equivalent. Unfortunately, there are no
@Prelude@ functions that provide the same currying functionality for
functions taking arbitrary \(n\)-tuples. Moreover, having to write
more than a few of these functions manually is, while trivial, a very
repetitive and cumbersome task. Instead we wish to generate needed
|curry4|, |curry9|, or |curry23| functions through a single meta
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

Given the integer |n|, |curryN| builds the requested \(n\)-ary curry
function in abstract syntax. It returns a lambda abstraction |LamE|
that pattern matches against a function variable |f| and \(n\)
argument variables |x1|, |x2|, ..., |xn| and then applies function |f|
to an \(n\)-tuple expression |(x1, x2, .., xn)| derived from the
pattern matched variables. The names used to represent the function
variable |f| and the arguments |x1| through |xn| are hereby generated
monadically by function |newName| to always generate fresh names that
don't collide with other names. Hence, the value returned (e.g.,) by
|(curryN 3)| is a monadic computation of type |Q Exp|. When executed,
this monadic computation yields an expression |Exp| representing the
object-level function |curry3| of type |(a, b, c) -> d) -> a -> b -> c
-> d| in abstract syntax.

To run the monadic computation returned by |(curryN 3)| and, moreover,
to convert the built object program source code from its abstract
syntax form into real Haskell code, we have to splice it back in. This
is done by Template Haskell via a special \textit{splice} operator,
denoted |$(..)|. Thus, writing |$(curryN 3)| first runs the @Q@
computation and then splices the resulting object program representing
the |curry3| function back in as real Haskell code.

The implementation of |curryN| exhibits the two core mechanisms that
Template Haskell is built on: algebraic data types and the quotation
monad @Q@. Object programs created by Template Haskell are represented
by normal data types in the form of abstract syntax trees. The
Template Haskell library provides the algebraic data types |Exp|,
|Pat|, |Dec|, and |Type| to represent Haskell's surface syntax of
expressions, patterns, declarations, and its types,
respectively. Virtually every concrete Haskell syntactic construct has
a corresponding abstract syntax constructor in one of the four
ADTs. Moreover, meta programs in Template Haskell are built inside the
quotation monad |Q|. This monad's main purpose is to extend Haskell's
lexical scoping to the level of object programs. 


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

%\bibliographstyle{alpha}
\bibliography{refs}

\end{document}
