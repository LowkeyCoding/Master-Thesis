#import "../Packages/global.typ": *
#import "../Figures/BtF.typ": *


In this chapter, we introduce typed variations of #butf and #epi, henceforth denoted as #btf and #tepi. We start by introducing a simple type system for #butf, an attempt in adapting the simple type system of #fut introduced in @futhark_phdthesis to #btf. Following this we provide a proof of soundness for #btf. Similarly, for #epi we introduce a type system that handles composite names and prove the soundness of the type system. 
//We will in this chapter introduce typed versions of #butf and #epi henceforth denoted as #btf and #tepi. We will start by introducing a simple type system for #butf based on a revised version of the type system in @butfOrigin. This is then followed by a proof of soundness @th:btf_sound. Then we will introduce a simple type system for #epi that handles composite names and show that it is sound @th:Tepi_Sound.

== Basic Typed #fut <sec:butfTypes>
We extend #butf with a type system inspired by the original type system from @futhark_phdthesis and the simply typed $lambda$-calculus @Church_1940. It should be noted that an original type system for #butf was introduced by #cn(<butfOrigin>) in @butfOrigin but the syntax and semantics for #butf has changed in @ButfToEpi.

=== Types for #btf 
Type judgements are of the form: $Env |- e : tau$, where $Env$ is a type environment, $e$ is a $btf$ expression and $tau$ is a type. Type judgements should be read as: given an environment $Env$, then the expression $e$ has type $tau$. 

#definition("Type environment")[
  An environment $Env$ is partial function from variables to types 
  $
  var harpoon bold(T)
  $
]<def:env>

We have chosen the primitive types of #btf based on the semantics from @ButfToEpi and the #fut documentation @FutharkLangFeat. The primitive types introduced in @FutharkLangFeat are signed and unsigned integers, floating-points, and boolean types. As of now, we have only chosen integers as in @ButfToEpi, but a future extension would be to have floating-point types as well as boolean types. In our case, booleans could have been used in the conditional expression but as seen in @fig:ButFSemantics that is handled by evaluating the value of an integer where 0 is false and everything else is true.

#definition($"Types" bold(T)$)[
#align(center, grid(
  columns: (5em, 5em),
  column-gutter: 20pt,
  $ tau ::=& Int \
       &| [tau] \
       &| (many(tau)) \
       &| tau_1 -> tau_2 \
$,$
"(Integer)" \
"(Array)" \
"(Tuple)" \
"(Abstraction)"
$))
]
// #iwnote[Explain types]

As mentioned earlier the only primitive type we have is $Int$. This simplifies the type system but still allow to show the core of #fut. In addition to the primitive type $Int$ we have two types for handling collections of elements: tuple types $(many(tau))$ and array types $[tau]$. The tuple and array types can be nested meaning they can have an arbitrary depth. Lastly we have the abstraction type which can model higher order functions using tuples. 


=== Syntax and Semantics of #btf
The syntax for #btf is the same as in #butf (#link(<fig:butf_syntaxs>, "Figure 2.1"))  however, the abstraction rule is changed to require a type annotation as it is the only binder construct in #btf. 
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
          & lambda (x: tau).e_1 \
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
  caption: [#btf syntax],
  kind: image
)<fig:btf_syntax>

With the way the syntax of #btf is constructed we have three functions #map, #iota and #size that needs a type to enforce correct usage. The way we solve this is by introducing an implicit type context (@def:icontext). The implicit type context contains the types for the three array functions and is used to extend the type environment (@def:env) as follows $Gamma union sum$.

#definition("Implicit type context")[
$ sum = vec(delim: "{", &map : (tau_1 -> tau_2, [tau_1]) -> [tau_2]\,,&iota : Int -> [Int]\,,&size : [tau] -> Int) $]<def:icontext>

The semantics of #btf is the same as seen in @sec:butf_semantics with a type annotation in abstraction. 

// hvordan typer vi map(size [[tau],[tau]])
// måske kræve map og size er type annoteret.

=== Type rules
To adapt the simple type system of #fut in #btf we took a look at the type rules introduced by #cn(<futhark_phdthesis>) in @futhark_phdthesis. In the cases where we were unable to create similar type rules due to the difference between #btf and #fut we took inspiration from the simply typed $lambda$-calculus. The type rules for #btf can be found in @fig:btfTypRules.
//to the simply typed $lambda$-calculus. #note("some more text")

/* Explain type rules */
#shown(rbtf, "t-if") is an interesting case to look at. We first look at the type of $e_1$ where it must be of type: $Int$, such that it complies with the semantics given in @fig:ButFSemantics. The most interesting part is that we enforce the types of the two branches to be the same. This agrees with what we encountered when we tested conditional branching in the #fut language and the type rule found in @futhark_phdthesis. 

Typing of #shown(rbtf, "t-array") and #shown(rbtf, "t-tuple") look very similar. For #shown(rbtf, "t-array") we require the array to be homogeneous, that being each element of the array must have the same type. In comparison, tuples are heterogeneous, that being we allow each element to have a different type. If we restricted tuples in the same way as array our semantic rule for #map would no longer hold.

In the #shown(rbtf, "t-index") rule we need to type the two expressions. $e_1$ must be typed as an array type of $tau_1$ and $e_2$ as $Int$. The resulting type of index is $tau_1$ - the type of the elements in the array.

In the #shown(rbtf, "t-abs") rule we need to type the abstraction body, the expression $e$ where $x$ has the type $tau_1$. The expression body has the type $tau_2$ if well-typed, giving the abstraction the resulting arrow type $tau_1 -> tau_2$.

In the #shown(rbtf, "t-app") rule, $e_1$ has to be typed as an arrow type $tau_1 -> tau_2$ otherwise $e_1$ is not an abstraction. We then require that $e_2$ is typed as $tau_1$ enforcing that the parameter has to have the correct type. The resulting type of application is the result type of the abstraction $tau_2$

#figure(rect(inset: 20pt, radius: 5%)[#ButFTypeRules],caption: "Type rules of "+ $btf$, gap:5pt)<fig:btfTypRules>

