#import "../Packages/global.typ": *

= Introduction

A graphics processing unit (GPU) is a central part of most modern computers, mostly used for image rendering and displaying it to a monitor. This is, of course, not the only kind of computation GPUs can be used for, and through the introduction of programming interfaces such as CUDA @Cuda and later OpenCL @openCL, writing GPU code without knowing shader languages was made possible @cudaBook. One key advantage of using a GPU for computations instead of the Central Processing Unit (CPU) is that the computational power of the GPU is much larger compared to that of the CPU. The reason for this is the utilisation of parallelisation in GPUs @cudaBook. 

== #fut - a Functional Array Programming Language
$fut$ is a functional array programming language that generates GPU code by CUDA and OpenCL and is designed with the focus on compiling to optimised GPU code @Futhark. The language is an ongoing research project but can still be used for non-trivial programs. The foundation of the $fut$ language is that of array manipulation using what is known as second-order array combinators (SOACs) @FutharkPaper. This is based on the work by #cn(<SOACsArticle>), in which some theoretical groundwork for manipulating list/array functions is created @SOACsArticle. This includes the following functions: $map$, $#raw("reduce"), #raw("foldl"), #raw("foldr")$ and $#raw("scan")$. 

The $fut$ semantics of SOACs allow for rewrites of expressions, which helps with optimisation by not only transforming the schedule but also the space @FutharkPaper. $fut$ utilises a transformation of parallelism for optimisation by taking nested parallelism and reorganising it into SOACs nests (that being the outer levels correspond to $map$ operators) @FutharkPaper. $fut$ is syntactically similar to other functional programming languages such as Haskell but focuses less on the expressivity and type systems. 

// The language #fut @Futhark is a functional data-parallel array programming language designed with focus on compiling to optimised graphics processing unit (GPU) code. The language is an ongoing research project but can still be used for non-trivial programs @Futhark. The programs in #fut work with "Second-Order Array Combinators" (SOACs) such as #map, #raw("reduce") and #raw("filter") to handle fusion, streaming, and flattening of parallelism @FutharkPaper.

== The $pi$-calculus - a Process Calculus
// When taking computations and sub-processes into account, one tool for verifying certain features and behaviour are process calculi. 
To help prove aspects of data-parallelism in $fut$, one might look towards process calculi, a tool useful for verifying and proving certain behaviours of systems. In the family of process calculi, the $pi$-calculus is one which can describe concurrent parallel systems. First introduced by #cn(<OG_pi_paper1>) in @OG_pi_paper1 @OG_pi_paper2, the $pi$-calculus is a process calculus in which communication happens by name passing. 
//based on an extension to the calculus of communicating systems (CCS) 

Though the $pi$-calculus is very expressive, extensions and sub-calculi exist which allow for shorter and less cumbersome notation for writing the same process. Take for example the polyadic $pi$-calculus @polyadicPi where multiple names can be sent and received in communication, or the Higher-Order $pi$-calculus (HO$pi$) @hoPi where processes can be communicated. Both have been shown to be encodable in the monadic $pi$-calculus. The polyadic $pi$-calculus by #cn(<polyadicPi>) in @polyadicPi and HO$pi$ by #cn(<hoPi>) in @hoPi. There also exist variations which cannot be expressed in the $pi$-calculus. One such is $b pi$-calculus (a calculus with broadcast derived from the $pi$-calculus), which #cn(<broadPi>) show that no uniform encoding of $b pi$-calculus into the $pi$-calculus exists @broadPi. 
// In the context of $fut$ and GPUs one can think of the different cores doing computations as processes in the $pi$-calculus. 

One of the approaches for proving certain properties of a programming language or process calculus is that of encoding the original to another language or process calculus such as the $pi$-calculus. Translating #fut to the $pi$-calculus would give a data-parallel implementation for free. This would also make it possible to analyse the complexity of data-parallelism in #fut. 

== Translations to the $pi$-calculus
// Introduce translations
One of the most well-known encodings is Milner's encodings of the call-by-value $lambda$-calculus and the lazy $lambda$-calculus to the $pi$-calculus @funcAsProc.
In @continuationsTl, #cn(<continuationsTl>) studies the relationship between the encodings of the call-by-value and call-by-name $lambda$-calculus to $pi$-calculus. The approach taken by Sangiorgi is different than Milner's. In @continuationsTl the encoding is obtained by transforming the $lambda$-calculus into a continuation passing style which is then translated into $"HO"pi$ and lastly into the $pi$-calculus. 

In @ControlTl, #cn(<ControlTl>) introduce a type-preserving translation of the $lambda mu$-calculus (a variation of the $lambda$-calculus with continuation variables) to a subset of the asynchronous $pi$-calculus. 
Another type-preserving encoding can be found in @Amadio, where #cn(<Amadio>) introduce a translation from a concurrent $lambda$-calculus (a variation of the call-by-value $lambda$-calculus extended with parallel composition, restriction, output and input) to the $pi$-calculus. The concurrent $lambda$-calculus is an attempt at capturing the nature of a concurrent functional programming language.

Work regarding encodings of languages to the $pi$-calculus is also prevalent and used for showing or proving properties. #cn(<objTlPi>) gives a translation of two different object-oriented languages, respectively, to illustrate the expressiveness of the $pi$-calculus @objTlPi. A translation of the functional programming language Erlang can be found in @tlErlang. By translating a subset of Erlang known as core Erlang to the asynchronous $pi$-calculus, model checking techniques could possibly be used for verifying correctness properties of communication systems implemented in Erlang @tlErlang. 


// Introduce the translation from butf to epi 
In the work by #cn(<ButfToEpi>), a subset of the $fut$ language (called $butf$) is translated to an extended $pi$-calculus (called $epi$) @ButfToEpi. This translation is then used for an analysis of the complexities of expressions and compared to that of $fut$. As $butf$ is untyped, this allows for writing expressions that logically make no sense; it is for example allowed to use a binary operation on two abstractions. This brings up the question of how one could design a type system for $butf$ to bring the language closer to that of $fut$. That would also restrict the language such that these illogical expressions cannot be valid. The type system of $fut$ has three aspects; simple types, unique types, and sized types. We will in this report introduce $butf$ and $epi$ and extend both with a type system, respectively. The type system we introduce for #butf will try to embody that of the simple types of $fut$ as introduced in @futhark_phdthesis. With the inclusion of a type system we gain static guarantees in regards to the behaviour of a program which a correct translation would preserve. For this we need an updated translation and proofs for the correctness of the translation. 


== Structure of the Report
The remainder of the report is structured as follows:
in @ch:Prelim we introduce the #butf language, #epi, and the translation from #butf to #epi by #cn(<ButfToEpi>) from @ButfToEpi. In @ch:typed_setting we extend #butf with a type system (we call this #btf) and prove the soundness of the type system. This is followed by an extension with a type system to #epi (we call this #tepi), where we also prove the soundness of this type system. In @ch:tlAndCorrect we introduce an updated translation from #btf to #tepi and define and prove the correctness of the translation. Lastly, in @ch:conclusion we conclude the report and discuss future work.
