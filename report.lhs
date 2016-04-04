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

\section{Reviewing Template Haskell by Examples}

In this section, I will review the basic concepts of Template Haskell
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

Given an integer \(n\), meta function |curryN| builds the object
program for an \(n\)-ary curry function in abstract syntax. It returns
a lambda abstraction |LamE| which pattern matches against a function
variable |f| and \(n\) argument variables |x1|, |x2|, ..., |xn| and
then applies function |f| to an \(n\)-tuple expression |(x1, x2, ..,
xn)| derived from the pattern matched variables. The names used to
refer to the variables |f| and |x1| through |xn| are hereby generated
monadically by function |newName :: String -> Q Name| to always
generate fresh names not used anywhere else. Hence, the value returned
(e.g.,) by |(curryN 3)| is a monadic computation of type @Q Exp@. When
executed, this monadic computation yields an expression @Exp@
representing the object function |curry3| of type |((a, b, c) -> d) ->
a -> b -> c -> d| in abstract syntax.

The generated object program's source code can be executed at
compile-time by splicing it in. This is done by Template Haskell via a
special \textit{splice} operator, denoted |$(..)|. Writing |$(curryN
3)| runs the @Q@ computation and converts the resulting object program
holding the |curry3| function to real Haskell code, which is then
spliced in. Thus, at compile-time, |$(curryN 3)| evaluates to the
Haskell expression |\f x1 x2 x3 -> f (x1, x2, x3)|, which precisely
implements the |curry3| function.

To generate function declarations for the first \(n\) curry functions,
we can devise a further meta program on top of |curryN| as follows:

> genCurries :: Int -> Q [Dec]
> genCurries n = sequence [ mkCurry i | i <- [1..n] ]
>   where mkCurry ith = do
>           cury <- curryN ith
>           let name = mkName $ "curry" ++ show ith
>           return $ FunD name [Clause [] (NormalB cury) []]

Running |$(genCurries 20)| will then generate the first 20 curry
functions at compile-time, namely:

< curry1  = \f x1 -> f (x1)
< curry2  = \f x1 x2 -> f (x1, x2)
< curry3  = \f x1 x2 x3 -> f (x1, x2, x3)
< curry4  = \f x1 x2 x3 x4 -> f (x1, x2, x3, x4)
< ...
< curry20 = \f x1 x2 .. x20 -> f (x1, x2, .., x20)

Note that in this case, |genCurries| returns a list of function
declarations to bind the anonymous lambda abstractions. Furthermore,
to name the function bindings, we use function |mkName :: String ->
Name| instead of |newName|. The reason is that here we want to
generate the capturable function names |curry1| to |curry20|.

Splicing in generated object programs as regular Haskell code at
compile-time using the splicing operator |$(..)| is the first central
building block of Template Haskell. The two other core mechanisms are
exhibited by the implementations of |curryN| and |genCurries|:
algebraic data types and the quotation monad @Q@.

Object programs created by Template Haskell are represented by normal
data types in the form of abstract syntax trees. The Template Haskell
library provides algebraic data types @Exp@, @Pat@, @Dec@, and @Type@
to represent Haskell's surface syntax of expressions, patterns,
declarations, and types, respectively. Virtually every concrete
Haskell syntactic construct has a corresponding abstract syntax
constructor in one of the four ADTs. Furthermore, all Haskell
identifiers are represented by the abstract @Name@ data type in
Template Haskell object programs. By representing object programs as
regular algebraic data types (and thus as data), normal Haskell can be
used as the meta programming language to build object programs.

Second, TH object programs are built inside the quotation monad
@Q@. Besides giving access to fresh names via function |newName ::
String -> Q Name|, the monad's main purpose is to extend Haskell's
static scoping discipline to the object programs constructed with
Haskell \cite{th1}. The scoping principle is just as in normal
Haskell: Identifiers inside an object program are bound to their
lexically enclosing binders in scope, when the object program
\textit{is defined}. Achieving static scoping is not straightforward
due to the interplay of splices |$(..)| and a feature that hasn't been
introduced yet: \textit{quotation brackets} |[|| .. ||]|.

Quotation brackets are a shortcut for constructing object programs in
Template Haskell. They allow to specify an object program using just
regular Haskell syntax by enclosing it inside oxford brackets |[||
  .. ||]|. That way, object programs can be specified much more
succinctly. For example, writing a meta program for building an object
program of the identity function is already quite verbose, if
expressed just using ADTs:

> genId :: Q Dec
> genId = do
>   x <- newName "x"
>   return $ LamE [VarP x] (VarE x)

Using quotation brackets, writing the same meta program can be
abbreviated with:

< genId :: Q Dec
< genId = [| \x -> x |]

That is, quotation brackets quote regular Haskell code as a
corresponding Template Haskell object program inside the @Q@
monad. There are four different kinds of quotation brackets: |[e||
  .. ||]|, |[p|| .. ||]|, |[d|| .. ||]|, and |[t|| .. ||]| for quoting
Haskell expressions, patterns, declarations, and types,
respectively. The quotation bracket |[|| .. ||]| is hereby another way
of writing |[e|| .. ||]|. Using the quotation brackets, all of
Haskell's concrete programs can also be represented as object programs
in Template Haskell.



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
< metaProg = return $ 
<
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

%\bibliographstyle{alpha}
\bibliography{refs}

\end{document}
