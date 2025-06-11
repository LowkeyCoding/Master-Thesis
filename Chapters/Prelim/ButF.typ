#import "../../Packages/global.typ": *
#import "../../Figures/Butf.typ": * 

We will in this chapter give an introduction to language #butf, the process calculus #epi and the original translation from #butf to #epi. We will start by introducing $butf$ as seen in @ButfToEpi with a revised semantics. This is followed by an introduction of $epi$ and the translation from $butf$ to $epi$ as seen in @ButfToEpi.

== Basic Untyped #fut <sec:Butf>
In @ButfToEpi, #cn(<ButfToEpi>) introduces a reduced syntax for Futhark without types called Basic Untyped #fut (#butf). #butf is made with the focus on array computations of #fut and while #butf has removed most of the array operations, the core concept of #fut still remains. This makes $butf$ very similar to a $lambda$-calculus extended with arrays, tuples, and binary operations. Though #fut has more array operations than #butf, #cn(<ButfToEpi>) have chosen the operations $map, size$ and $iota$ since they can be used to define other common array operations @ButfToEpi.
// We will in this section give an introduction to the #butf language from @ButfToEpi and later we will introduce a type system.

=== Syntax for #butf

#figure(
  grid(
    columns: 2,
    column-gutter: 1.5em,
    stroke: none,
    $
      e ::=& b \
          & x \
          & [e_1,dots,e_n] \
          & e_1[e_2] \
          & lambda x.e_1 \
          & e_1 e_2 \
          & (e_1, dots, e_n) \
          & ifte(e_1,e_2,e_3)
    $,
    $
      b ::=& n \
          & map \
          & iota \
          & size \
          & bin
    $
  ),
  caption: [#butf syntax @ButfToEpi],
)<fig:butf_syntaxs>

Expressions in #butf is built with the following constructs:
- $b$ which are constants and can either be an integer constant ($n$), an array operation or an arithmetic operation. Array operations are either #map, #iota or #size. 
  - #map takes a tuple containing a function and an array, and returns an array where the function has been applied to each element. 
  - #size takes an array and returns the length of the array.
  - #iota takes an integer and returns an array with length equal to the integer given and with the value of each element equal to its index.
  - The arithmetic operator #bin are the standard arithmetic operations such as $+, -, dot, \/$ and $%$.
- $x$ denotes a variable, $[e_1,dots,e_n]$ an array and $(e_1, dots, e_n)$ a tuple. 
- $e_1[e_2]$ (indexing) returns the value at the location in an array ($e_1$) based on the index ($e_2$). 
- $lambda x.e_1$ (abstraction) introduces a variable $x$ in an expression. 
- $e_1 e_2$ (application) applies expression $e_1$ to the expression $e_2$. 
- The conditional expression takes $e_1$ and if it evaluates to true then we proceed as $e_2$ else we proceed as $e_3$. 

=== Semantics for #butf <sec:butf_semantics>
The operational semantics of #butf is a small-step semantics and is given as a reduction relation ($->$) of the form $e -> e\'$. The semantics we present is a revised semantics to the one introduced in @ButfToEpi. The language #butf is a call-by-value language with values defined as follow.

#definition("Value")[
  We define a value as $v$ in the set of all values $v in cal(V)$, where values are constants, function symbols, arrays and tuples that contain values only, and abstractions: \
  $ v := b | [v_1, dots, v_n] | (v_1, dots, v_n) | lambda x.e $ 
]<def:butfValues>


For the semantics of #butf we will show some of the rules specific to #butf's array operations. The full semantics of #butf can be found in @app:butf_semantics. 

#figure(rect(inset: 20pt, radius: 5%)[#reducedButfSemantics],caption: $butf$ + " semantics", gap:5pt)<fig:reducedButFSemantics>


For indexing we have three rules. #shown(rbutf, "r-index1") is used for evaluation the first sub-expression $e_1$ and #shown(rbutf, "r-index2") for evaluating sub-expression $e_2$. When both sub-expression has fully evaluated to an array of values and an indexing number, respectively, we can use #shown(rbutf, "r-index") to take the final step and get the value at the index. 
//The semantics for binary operation is similar indexing.

//If has three rules: one for evaluating the conditional expression $e_1$, one when evaluating to false and one when true. #shown(rbutf, "r-ift") rule is used when $e_1$ has evaluated and the expression evaluates to a value not equal to 0 and #shown(rbutf, "r-iff") when the value is equal to 0. 

For the array operations the semantic rules reflects the intuition quite well. #shown(rbutf, "r-map") takes a tuple containing a function and an array of evaluated expressions and applies the function to each element. When applying an abstraction we substitute with the value from the abstraction. Substitution in #butf is denoted as ${x |-> y}$ and is read as $x$ is substituted with $y$. The definition for substitution in #butf can be found in @app:butf_defs. #shown(rbutf, "r-iota") takes a number $n$ and returns an array of sequentially increasing elements from 0 to $n-1$. #shown(rbutf, "r-size") takes an array of evaluated expressions and returns a value which corresponds the number of elements in the array. 


