#import "../Packages/global.typ":* 
= Conclusion <ch:conclusion> 
In this report we have taken a look at the small language #butf which encompasses some of the core aspects of $fut$ and #epi, an extension to the $pi$-calculus extended with broadcasting capabilities and composite names, and the translation of $butf$ to $epi$. We then extended both with a simple type system (called $btf$ and $tepi$, respectively) and introduced an updated translation. 

// henceforth denoted as  #btf and #tepi respectively.

== Results
For the type system for #btf we took inspiration from the simply typed lambda calculus with some of the types based on a simplified Futharks type system, such as arrays and tuple types. As the goal was to attempt to create a type system similar to the simple type system of #fut, we took inspiration from @futhark_phdthesis for the type rules. Since a number of the type rules for #fut is created with unique types, we were unable to capture those exactly with the simple types of #btf. As such, our type rules is mostly similar in those cases with others inspired by the simply typed $lambda$-calculus. 
// In cases where the #btf language was too lacking in expressiveness compared that of #fut (such as lacking aliasing and unique types), we took inspiration from the simply typed $lambda$-calculus. 
To handle typing of array operations we introduced an implicit type context where we could look up the type of $map, iota$ and $size$. We showed that #btf is sound (@th:btf_sound) in regards to the semantics by showing that we can always take a reduction from a well-typed expression that is not a value and still be well-typed after the reduction. 

In the type system for #tepi we introduced a simple type-system with location and pre-channel types to handle composite names. Furthermore we introduce a composite name environment that maps a tuple of names $(x,y)$ to types. This ensures that we can reuse the name $y$ for multiple handles $x$ when translating from #btf to #tepi. This allows for a common interface for accessing arrays and tuples $h dot all$,  $h dot len$,  $h dot n$ and $h dot tup$ without typing collisions simplifying the translation. Furthermore this prevents out of bounds indexing as the pair $(h,n+1)$ should not map to a type in $CEnv$ for any array with the handle $h$ and the length $n$.  
As in #btf we prove that the type system for #tepi is sound (@th:Tepi_Sound) by proving that we can take a reduction from a well-typed process and still be well-typed. 

We then defined an updated translation of #btf to #tepi with some of the constraints of the original translation removed, as they became unnecessary through guarantees of the type-system. Furthermore we have reduced the amount of allowed programs, for example preventing using binary operation on two abstractions by ensuring that the values in binary operations have to be typed as #Int. We then prove type correctness (@th:typeCorrectness) which ensures the translation of any well-typed #btf expression results in a well-typed #tepi expression, with the type of the final output being a channel type $ch(tl(tau))$ where $tl(tau)$ is the translated type of the #btf expression. This is followed by a proof of the behavioural correctness of the translation (@th:correctness) which ensures that there is an operational correspondence between $e$ and $tle(e,o)$ such that $ocp(e, tle(e,o))$. We then argue that (@th:typeCorrectness) and @th:correctness prove @th:CorrectTypedTl such that any given well-typed #btf expression can be translated and stay well-typed in #tepi while preserving the behaviour. This then gives us a data-parallel implementation of #btf in #tepi that ensures the behaviour and typing is correct. This also provides a starting point for extending the type system with sized and unique types from #fut.

// Extend by explaning the type systems. 
// Explain why we have two type environmnets in TEPI 

// Extend soundness part
// For both type systems we prove soundness such that we know that if typing is preserved af a reduction or step and for the case of btf we know that a expression is either a value or can take another reduction. Then for the case of epi we know that we are type safe and therefore there are no transitions from a well typed process such that any type rule conditions do not hold. 

// possible solution to problem
// have location types point at a new environment 
// this environment contains names local to a handle
// therefore we should be able to reuse names

// Possible better solution
// Change CEnv to be a partial map from a name and a name/number to a pre-channel type s.t name, name union number -> type
// we would only have to merge the composition type rules
// and then change translation slightly to build up CEnv when a composit type is used.



== Future Work

There are several directions this work can be extended. Though #btf is a step closer to $fut$ compared to $butf$ by including a type system, there are still many interesting aspects and designs in $fut$ we have not been able to capture. One such could be their unique types or constructs not yet introduced to $btf$/*- objects with this types can only be accessed by one thing(?)*/. Below we will discuss some of the possible directions future work could take.

=== From Array Operations to Functions
Changing the semantics of #btf to allow #size, #iota and #map as abstractions would simplify some programs as the example on #pageRef(<ex:tlMap>). Furthermore it would simplify @th:typeCorrectness as there is a direct correspondence between the typing of array operation types in #btf and the #tepi process where now the type in #tepi is the resulting type of the arrow type in #btf. For example, the type for #size would be ($(Int, [tau]-> Int)$) instead of $Int$.
#let with = raw("with")

=== #with Construct
Introducing the #with construct from #fut would be an interesting path to expand the translation to #tepi. As allowing in place updates without side effects, would require preventing the use of the input array and any aliases of it, in both #btf and #tepi. This problem could be potentially be solved using an environment that contains unique handles  similar to the concept in @CompleteContextYoink where #cn(<CompleteContextYoink>) introduces an environment for names that must be used exactly once. This would require adding an extra condition to communication type rules that ensures the handle is not in the environment. Another interesting solution could be adding uniqueness types from #fut @FutharkLangFeat. Ensuring that either solution works is going to be interesting for the case of @lem:PreserveSub where there are multiple handles in the #tepi translation to the same array where none should be accessible after using #with in the body of the function.


 // This may not be a problem as $x$ should never be used again as e should be well typed and therefore the parametere $x$ should never be accessed after the with construct.

// This problem could be solved using an environment that contains inaccessible handles as similar to the concept @CompleteContextYoink where #cn(<CompleteContextYoink>) introduces an environment for names that must be used exactly once
// In @CompleteContextYoink where #cn(<CompleteContextYoink>) introduces an environment for names that must be used exactly once
=== Sized Types
Introducing sized types as in @size-dep would further align #btf with #fut by ensuring bound checks at the type level. This however would require some degree of polymorphism on the size of arrays at the type level to allow for the implementation of function such as #size, #iota and #map. This could be achieved by using universal quantification as in @size-dep and could look as follows $Env |- map : forall n. (tau_1->tau_2,[tau_1](n))->[tau_2](n)$. This would require introducing a specialization type rule as below where a specific size can be selected for a given universal quantifier though this would require defining substitution on types. 
//This would require defining substitution on types which should be simple.
#align(center, tree(
  label:"(BT-spec)",
  $Env(f) : tau_1 rn(n,x) -> tau_2 rn(n,x)$,
  $n in NN$,
  $Env(f) : forall x. tau_1 -> tau_2$,
))

/* 
=== Linear types

A side effect of adding linear types is that linear types are easily translate able into session types. 
*/

// Future work

// Modify the semantics to allow map,iota,size to be used as abstractions
// This would require that the translation is slightly modified such that the type of the function handle becomes $ch(t_1,ch(t_2))$
// This would also make the argument for type correctness less round about since we can directly from the translation of map derive the type in BtF

// Add sized types to arrays and tuples s.t we can prevent indexing out of bounds and know the exact amount of elements from the type signature.To BtF this would require a limited form of polymorphy to handle map, iota, size therefore we need a type rule to find the specific size... For Tepi  would require minimal changes to the array and tuple type rules in BtF and a small change to the COMPN rule in tepi and the proofs that use those. 

// Implement with construct from futhark to do in-place array operations. This requires that the input array and any alias of the input array is never used after the in place update.   @SANGIORGI1999457