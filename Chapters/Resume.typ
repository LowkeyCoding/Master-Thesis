#import "../Packages/global.typ": * 
\
#heading(text("Summary",size:26pt), outlined: false,numbering: none,level:1)
\ \
This report introduces a typed translation from the language basic typed #fut (#btf), to the process calculus typed extended $pi$-calculus (#tepi). This report extends the work by #cn(<mscButfToEpi>) in which they introduce the language basic untyped #fut (#butf), the process calculus extended $pi$-calculus ($#epi$) and the translation from #butf to #epi. \ 
We start by introducing #butf - a core language based on the functional array programming language #fut which compiles to optimised graphical processing unit (GPU) code. What makes #fut interesting is the addition of arrays in a functional programming language and array operations known as second-order array combinators (SOACs). The semantics of SOACs allow #fut to rewrite expressions which helps with optimisation.\
Next we introduce #epi, which is a process calculus based on the applied $pi$-calculus and extended with broadcasting capabilities and composite names to better handle the array structure for the translation of #butf to #epi. Then we go over the original translation and give some examples which shows translations of #butf expressions. 

To bring #butf closer to #fut we extend it with a type system, incorporating types such integers, arrays, and tuples inspired by Futhark’s simple type system and the simply typed $lambda$-calculus. By introducing a type system we acquire static guarantees and ensure illogical expressions, such as a binary operations on two abstractions, is not allowed. For #btf we introduce a theorem for soundness of the type system which consists of two parts: preservation (types are preserved after a transition step) and progress (expressions are either values or can take a transition step). We then give a proof of the soundness theorem.\
This is followed by introducing a type system for #epi. To handle composite we introduce a location type and pre-channel type which restrict how we combine names through the type rules and by introducing a pre-channel type environment - a type environment to ensure we handle arrays and tuples in the translation correctly. This is followed by a soundness theorem consisting of two parts: subject reduction (types are preserved after a reduction) and type safety (if we are well-typed reduction errors can not occur). For type safety we introduce an #wrong predicate and its reduction rules, and give the proof for soundness. 

Lastly we give a typed translation from #btf to #tepi and show previous examples updated with the new translation. To prove the correctness of the translation we introduce theorems about type correctness and behavioral correctness.\ 
Type correctness ensures that every well-typed #btf expression translates to a well-typed #tepi process, with the type carried by the output channel type mirroring the type of the expression. Behavioral correctness ensures the translation behaves similar to #btf on the observable output after an important reduction. For this we introduce an operational correspondence that relates #btf expressions and #tepi processes. Together, these results provide a type-preserving translation of #btf to #tepi.

We conclude the report and discuss future work which includes ideas for possible improvements in the semantics, extending #btf with a new construct from #fut called #raw("with"), and introducing sized types to #btf.



// Introduction
// This research bridges functional array programming and concurrent process models by establishing a formally verified compilation path from Futhark—a functional language for GPU parallelism—to an extended π-calculus. Prior work translated an untyped Futhark subset (ButF) to a broadcast-enabled π-calculus (Eπ), but lacked static guarantees. We close this gap by introducing type systems for both languages, enabling rigorous verification of behavior preservation and correctness. This foundation supports compiling data-parallel array operations to concurrent processes while ensuring semantic fidelity.

// Core Contributions
// We designed BtF, a typed extension of ButF, incorporating base types, arrays, and tuples inspired by Futhark’s simple type system. Key constraints—such as enforcing integer operands in binary operations—eliminate illogical programs. For the target, we developed TEπ, augmenting Eπ with location types, pre-channel types, and a composite name environment. This environment maps tuples of names (x,y) to types, enabling safe reuse of names during translation.

// Type soundness was proven for both languages. For BtF, reductions preserve well-typedness: any reducible non-value expression transitions to another well-typed term. Similarly, well-typed TEπ processes remain well-typed after reduction. These guarantees ensure runtime safety in their respective execution models.

// A novel type-directed translation from BtF to TEπ was defined, leveraging type information to relax constraints from the original untyped translation. Type correctness ensures that every well-typed BtF expression compiles to a well-typed TEπ process, with the output channel type ch(⟦τ⟧) mirroring the source type τ. Behavioral correctness establishes an operational correspondence between source expressions and their compiled processes, guaranteeing equivalent observable behavior. Together, these results provide a faithful, type-preserving implementation of BtF in TEπ.

// Methodology
// Small-step operational semantics defined evaluation for both languages. Type soundness used progress and preservation theorems, while translation correctness combined type induction and bisimulation techniques. The composite name environment—a core innovation—resolved name reuse challenges by tracking type associations for tuples of names, allowing multiple handles for a single resource.

// Future Work
// Three directions were identified. First, reinterpreting array operations (size, iota, map) as abstractions would simplify typing and enable polymorphism. Second, Futhark’s with construct for in-place updates could be integrated using uniqueness types or linear environments to prevent aliasing. Third, sized types (e.g., [τ](n)) would align BtF closer to Futhark, requiring universal quantification for operations like map : ∀n. (τ₁→τ₂, [τ₁](n)) → [τ₂](n).

// Conclusion
// This work delivers the first end-to-end typed compilation from a Futhark-like language to the π-calculus, verified via formal proofs. By bridging GPU-oriented array programming with concurrent process models, it enables rigorous analysis of data-parallel behavior. The framework also lays groundwork for integrating advanced Futhark features (e.g., uniqueness/sized types), advancing verified compilation for parallel systems.
