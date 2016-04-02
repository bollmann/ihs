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

\abstract{In this report, I explore compile-time meta programming in
  Template Haskell (TH) for the Glasgow Haskell Compiler (GHC). I
  motivate use cases for meta programming, explain the Template
  Haskell extension's features on simple toy programs, and give an
  overview of the extension's overall functionality. Furthermore, I
  review Template Haskell's overall implementation in GHC from a
  high-level perspective. Lastly, I describe my experience of
  extending GHC's implementation of Template Haskell to also support
  the newly added Pattern Synonyms feature.}

\section{Introduction}

- What is Template Haskell? How did it come about? (Template Haskell
Paper1, Paper2), Adoption of TH in real libraries to solve real-world
problems (Yesod!)?

- Even though its called the ugly under the HS extensions, it is the
necessary. A LOT (see reverse dependencies) of packages depend on it.

- What are the main benefits of TH?

- Motivations for TH: Embedded Domain Specific Languages (e.g. Yesod's
shakespeare templates)

\todo{Write me!}

\section{Use Cases for Template Haskell}

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

As an introductory example, consider Haskell's @Prelude@ functions
|curry :: ((a,b) -> c) -> a -> b -> c| and |uncurry :: (a -> b -> c)
-> (a,b) -> c|, which convert functions taking a pair to their curried
equivalents and vice versa. Unfortunately, there are no @Prelude@
functions that provide the same currying and uncurrying functionality
for functions taking arbitrary \(n\)-tuples. Moreover, having to write
more than a few of these functions manually is, while trivial, a very
repetitive and cumbersome task. Using GHC's Template Haskell language
extension, however, we can automate this. In particular, we can write
meta functions |curryN :: Int -> Q Exp| and |uncurry :: Int -> Q Exp|
that \textit{construct the code} for currying and uncurrying any
\(n\)-ary tuple functions on demand:

> import Control.Monad
> import Language.Haskell.TH
>
> -- curries a function f :: (t1, t2, ..., tn) -> t to f' :: t1 -> t2 -> ... -> tn -> t.
> curryN :: Int -> Q Exp
> curryN n = do
>   f  <- newName "f"
>   xs <- replicateM n (newName "x")
>   let args = map VarP (f:xs)
>       ntup = TupE (map VarE xs)
>   return $ LamE args (AppE (VarE f) ntup)
>
> -- Uncurries a function f' :: t1 -> t2 -> ... -> tn -> t. to f :: (t1, t2, ..., tn) -> t.
> uncurryN :: Int -> Q Exp
> uncurryN n = do
>   f  <- newName "f"
>   xs <- replicateM n (newName "x")
>   let ntup = TupP (map VarP xs)
>       app  = foldl AppE (VarE f) (map VarE xs)
>   return $ LamE [VarP f, ntup] app

For any \(k \geq 1\) |(curryN k)| then constructs the code for a
function |curryk :: ((t1,t2,..,tk) -> t) -> t1 -> t2 -> .. -> tk ->
t|, while |(uncurryN k)| yields the code for a function |uncurryk ::
(t1 -> t2 -> .. -> tk -> t) -> (t1, t2, .., tk) -> t|.

As a further, slightly more involved, example let's consider for
example the definition of the @Prelude@ function @map@:

< map :: (a -> b) -> [a] -> [b]
< map f []     = []
< map f (x:xs) = f x : map f xs

* Automate writing syntactically different, yet somehow similar programs all at once.
- select the kth element of any n-tuple; write code that does this all at once!
- write code that can generate any mapN function
- Automate writing repetitive/boilerplate code (deriving instances).

* Allow the embedding of domain specific languages.
- type safe regular expressions.
- much more powerful: type-safe routes/etc. in Yesod.

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
