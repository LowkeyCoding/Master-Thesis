#import "../Packages/global.typ":* 
#import "../Figures/TEpi.typ":*

== Typed #epi <ch:Tepi>
We will in this section extend #epi with a type system (we call it #tepi). In creating a type system for #tepi, different approaches can be taken as many different variations of type systems for the $pi$-calculus exists, including simple types, linear types, and session types @SomeGay. We have chosen to start with designing a simple type system which can act as a base for future extensions.

=== Syntax and Semantics of #tepi
The formation rules of #tepi are a bit different from #epi. First we have removed the labels $all, len$ and $tup$. As these labels are just names to help with readability in the translation and do not have different semantics from $x dot y$ we have removed them. In addition we will restrict composite names to be only on variables and numbers. 
By doing this we can then change the syntax for composite names from $c dot l$ to $c dot T$ and use the type system to restrict composite names to only $x$ and $n$ in the type rules. 
The other difference is the type annotation on the name in restriction and the receive action. 

#figure(
  TEpiSyntax, caption: [Syntax for #tepi]
)<fig:tepi_syntax>

The semantics of #tepi is the same as #epi but with added type annotations as seen in @fig:tepi_syntax.

=== Type System
The type system for #tepi is inspired by the simple type system as introduced by #cn(<SomeGay>) in @SomeGay and elements of the $D pi$ type-system from @DPiCalc to handle composite names. Like in #btf we have the primitive type $Int$ and just like in the simple type system from @SomeGay, we have the channel type which indicate the type of object the channel carries. 
// the type system for $D pi$ from @DPiCalc. 

#definition($#tepi "types"$)[
  $
  &t := Int | ch(many(t)) | pch(n: n) | hh(many(t)) \
  &ell := {t_1,dots,t_n}
  $
]
/*#definition("Composite name type environment")[
  A composite name type environment $CEnv$ is partial function from a pair of a name and a name/number to types
  $
  (cal(N), cal(N) union NN) harpoon cal(bold(T))
  $
]<def:tepi_env2>
*/

To handle communication on composite names we introduce two types: $pch()$ called a location type and $hh(many(t))$ called a pre-channel type. The location type is inspired by @DPiBook as it contains a set of types that can be communicated on. However as we do not have sub-typing as in @DPiBook we use composed names to communicate, where the type of the composed name should match with a type in the the set of types in the location type.  

//and is named to signify there exists other names at the location.H The name location is not a location itself but signifies the handle to the array or tuple process in the translation which is like a location handle

//. The type of the names composed with a location are pre-channel types. This name comes from the fact that these names are not used as channels themselves but has a component (that being the location) which they depend on.

//To handle communication on composite names we have the $(many(T): many(t))$ type that binds a set of $x,n$ to a set of types, thereby restricting the usage of a composite name to the set of $x,n$ on some name $a$. To show an example let us take the handle used from communicating with an array $(nu h: ("all" : t_1, "len": t_2))$ as seen in @sec:tlOfArr. In the example there are two names to communicate on (#all and #len) which both have distinct channel types. This then prevents communication to a handle directly as well as communication on composite names not specified in the type. 
// As seen in the example of a array handle this way of typing it, creates an intuitive representation of composite names. 

The type judgements for #tepi is of the following form: $PEnv |- P$, where $PEnv$ are type environments and $P$ is a #tepi process. The $DEnv$ environment gives us the types of the free variables, names and natural numbers in $P$. The $CEnv$ environment maps the location handle and the composed name or number to a pre-channel type ensuring that each array/tuple location handle has their own typing for the composed name. This then prevents out of bounds indexing as any pair $(h,n)$ where $n$ is greater than the size of the array should not map to a type in the environment $CEnv$.

#definition("Type environment")[
  A type environment $DEnv$ is partial function from free names and variables to types
  $
  cal(N) harpoon cal(bold(T))
  $
]<def:tepi_env>

#definition("Pre-channel type environment")[
  A composite name type environment $CEnv$ is partial function from a pair of a name and a name/number to pre-channel types
  $
  (cal(N), cal(N) union NN) harpoon cal(bold(T))
  $
]<def:tepi_cenv>

//

To use these environments we have defined a simple notation for extending them with a name and its corresponding type (@def:env_exst). When extending with multiple names we may use $DEnv, many(u) : many(t)$ or $CEnv, (many(u),many(n)) : many(t)$.

#definition("Type environment extension")[
  When extending a type environment with a name $u$ or number $n$ and a type $t$ we write $DEnv, u : t$ or $CEnv, (u,n) : t$. 
]<def:env_exst>

In addition we define the well-formed environment as follows.
#definition("Well-formed " + PEnv)[
  The type environments $PEnv$ are well formed, if $PEnv |- P$ and $fv(P) union fn(P) subset.eq dom(DEnv) union dom(CEnv)$.
]<def:well-formed>


We have split the type rules into two parts: type rules for processes and type rules for terms.
#figure(
  TEpiRules, caption: [Type rules for #tepi processes]
)
Type rule #shown(rtepi, "t-par") is typed as usual by typing each process under the environment. #shown(rtepi, "t-if") is typed similarly but we also require the two terms we match to be the same type. For restriction, #shown(rtepi, "t-res"), we require that the continuing process is well-typed with the restricted name added. 

For #shown(rtepi, "t-recv"), we require the name we receive on to be a channel type, and that we can add the received names and their types to the environment and still be well-typed. There is no difference between the type rules of #shown(rtepi, "t-send") and #shown(rtepi, "t-broad"). Like #shown(rtepi, "t-recv"), we require the name we are broadcasting/sending over, to be a channel type. The names we are sending/broadcasting must also be the same type and the continuing process must also be well-typed. 


#figure(
  TEpiTermRules, caption: [Type rules for #tepi terms]
)
We have one look-up rule #shown(rtepi,"t-u"). Remember we use $u$ when we do not differentiate between $x$ and $a$. #shown(rtepi,"t-bin") require the terms for the binary operation to have type $Int$. To handle composite names we have two type rules #shown(rtepi, "t-comp") and #shown(rtepi, "t-comp2"). First we require $u$ to be a location type as we then can look in the $Pi$-environment to see if the composition of the names has a pre-channel type. Then we ensure that the pre-channel type exists in the location type and therefore is valid name in the location.
#include "Proofs/TEpiSoundness.typ"