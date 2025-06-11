#import "../../Packages/global.typ": *
#import "../../Figures/wrong.typ": *

#let rwrongn(x) = shown(rwrong, x)
#let repin(x) = shown(repi, x)
#let tepin(x) = shown(rtepi, x)

== Soundness of #tepi
Before giving the soundness theorem of #tepi we will introduce a #wrong predicate. The #wrong predicate is a process that should only be reached in case there is a type mismatch.
//or for composite names, using a combinations of names not allowed by the type rules.
In @fig_subset_of_wrong, a subset of the reductions rules for the #wrong predicate can be found. For all the rules see @app:wrong_proc.

#figure(grid(
  columns: 2,
  column-gutter: 2em,
  row-gutter: 2em,
  
  showr(rwrong, "rw-broad"),
  showr(rwrong, "rw-recv"),
  grid.cell(colspan:2,showr(rwrong, "rw-match")),
)
,caption: [Subset of the #wrong predicate rules])<fig_subset_of_wrong>

#rwrongn("rw-broad") can go to #wrong in the case that the channel type and the type of the terms being sent does not match. #rwrongn("rw-recv") is similar as we can go to #wrong if the type of variables received do not match with type the channel type carries.
#rwrongn("rw-match") can go to #wrong if the type of the terms being matched is not the same. 
// For binary operations we can go to #wrong by #rwrongn("rw-bin1") or #rwrongn("rw-bin2") if the type of one of the terms is not $Int$.


// For composite names there are three cases where we can go to the #wrong process. The first case is that the type $c$ is not a composite type. The second case is that $c$ is not a channel name or variable. In the last case the type of $c$ is correct but the name of the term is not a variable or number.


=== Soundness Theorem
With the #wrong predicate introduced we can now give the soundness theorem for #tepi.

#theorem($"Soundness of " #tepi$)[
  Let $P$ be a #tepi process then
  1. (Subject reduction) if $PEnv |- P$ and $P -> P'$ then $PEnv |- P'$
  2. (Type safety) if $PEnv |- P$ then $P arrow.r.not wrong$
]<th:Tepi_Sound>

For @th:Tepi_Sound we have two parts that needs to be proven. Subject reduction states that if a process $P$ is well-typed in an environment and can reduce to $P'$ then $P'$ is also well-typed. Type safety states that if a process $P$ is well-typed it can never reduce to #wrong. 

=== Proof of lemmas
Before we start the proof of @th:Tepi_Sound we need to define some lemmas which will help in the proof.

#lemma("Weakening of terms")[
  If $PEnv |- T : t$ then $DEnv, u : t_u, CEnv |- T : t$ given any type $t_u$ and a $u$ such that $u in.not dom(DEnv)$.
]<lem:weak_tepi_t>

#lemma("Weakening of processes")[
  If $PEnv |- P$ then $DEnv, u : t_u, CEnv |- P$ given any type $t_u$ and a $u$ such that $u in.not dom(DEnv)$.
]<lem:weak_tepi_p>

#lemma("Strengthening of terms")[
  If $DEnv, u : t_u, CEnv |- T : t$ then $PEnv |- T:t$ given any type $t_u$ and a $u$ such that $u in.not dom(DEnv)$.
]<lem:stronk_tepi_t>

#lemma("Strengthening of processes")[
  If $DEnv, u : t_u, CEnv |- P$ then $PEnv |- P$ given any type $t_u$ and a $u$ such that $u in.not dom(DEnv)$.
]<lem:stronk_tepi_p>
@lem:weak_tepi_t to @lem:stronk_tepi_p states that we can add and remove names from the type environment where some name $u$ is not used in some process $P$. This is used to prove @lem:type_cong as in structural congruence we have the ability to extend the scope, add and remove restrictions. The full proof of all the lemmas can be found in @app:proof_tepi_weak_t to @app:proof_tepi_strengt.
#lemma("Type preservation under structural congruence")[
  Let $P$ and $Q$ be #tepi processes.
  1. If $PEnv |- P$ and $P == Q$ then $PEnv |- Q$
  2. If $PEnv |- Q$ and $Q == P$ then $PEnv |- P$
]<lem:type_cong>

@lem:type_cong states that types are preserved under structural congruence. This lemma is necessary for proving subject reduction in @th:Tepi_Sound. The full proof can be found in @app:proof_type_cong.

/*#lemma("Type preservation under substitution of channels")[
  If $PEnv |- c dot T : ch(t)$, $PEnv |- T_u : t_u$ and $PEnv |-  T'_u : t_u$  such that $PEnv |- T rn(T_u,T_u') : t$
]<lem:tepi_subst_c>*/

#lemma("Type preservation under substitution of processes")[
  Let $PEnv |- P$ be a well-typed #tepi process and $PEnv |-  T_u : t_u$, $PEnv |-  T'_u : t_u$, then $PEnv |- P rn(T_u, T'_u)$
]<lem:tepi_subst_p>

#lemma("Type preservation under substitution of terms")[
  If $PEnv |- T : t$, $PEnv |- T_u : t_u$ and $PEnv |-  T'_u : t_u$ such that $PEnv |- T rn(T_u,T_u') : t$
]<lem:tepi_subst_t>


The last two lemmas, @lem:tepi_subst_p and @lem:tepi_subst_t, states that types are preserved under substitution.


=== Proving Soundness
Just as the proof for @th:btf_sound, we have split the proof into two parts; one for subject reduction and one for type safety. As the whole proof is quite long we will in this section only showcase some of the cases for the proof. The full proof of subject reduction and type safety can be found in @app:proof_subject and @app:proof_type_safe, respectively.
==== Proof of Subject Reduction
//For the first part of proving @th:Tepi_Sound we need to prove subject reduction. We will go through some of the cases for the proof. The full proof can be found in @app:proof_subject.

We will prove subject reduction by induction in the rule for concluding $P -> P'$.

#case(of: repin("r-com"))[
    By our assumption we know that $PEnv |- send(c, many(T)).P$ and $PEnv |- receive(c,many(x) : many(t)).Q$ by the application of #tepin("t-par"). By #repin("r-com") we have $send(c,many(T)).P|receive(c,many(x)).Q -t P | Q rn(many(x),many(T))$ and must show that $PEnv |- P | Q rn(many(x),many(T))$. 
    
    Then by #tepin("t-send") we have that $c: ch(many(t))$ and $many(T) : many(t)$, and by #tepin("t-recv") we have that $c : ch(many(t))$ and $DEnv, many(x) : many(t), CEnv |- Q$. 
    By using @lem:tepi_subst_p we have that $DEnv, many(x): many(t), CEnv |- Q rn(many(x),many(T))$, and by @lem:stronk_tepi_p we have $PEnv |- Q rn(many(x),many(T))$. We can therefore conclude $PEnv |- P | Q rn(many(x),many(T))$ by #tepin("t-par").
  ]

  #case(of: repin("r-then"))[
    By our assumption we know $PEnv |- [T_1 bow T_2]P\,Q$ by #tepin("t-if") and $[T_1 bow T_2]P\,Q -t P$ by #repin("r-then"). We must then show $PEnv |- P$. This follows immediately by #tepin("t-if") as $PEnv |- [T_1 bow T_2]P\,Q$ is only correct if $PEnv |- P$.
  ]
  #case(of: repin("r-else"))[
    By our assumption we know $PEnv |- [T_1 bow T_2]P\,Q$ by #tepin("t-if") and $[T_1 bow T_2]P\,Q -t P$ by #repin("r-else"). We must then show $PEnv |- Q$. This follows immediately by #tepin("t-if") as $PEnv |- [T_1 bow T_2]P\,Q$ is only correct if $PEnv |- Q$.
  ]

==== Proof of Type Safety
//For the second part of proving @th:Tepi_Sound we need to prove type safety. We will go through some of the cases for the proof. The full proof can be found in @app:proof_type_safe.

We prove type safety by induction in the type rules.

#case(of: tepin("t-broad"))[
    By our assumption we have that $PEnv |- broad(c,many(T)) . P$ and must prove that $broad(c,many(T)) . P rnb wrong$. By inspecting #rwrongn("rw-broad") we can see that $broad(c,many(T)) . P -b wrong$ only if $c : ch(many(t_1))$, $many(T) : many(t_2)$ where $many(t_1) eq.not many(t_2)$. This contradicts the type rule for broadcast, that states $c : ch(many(t))$ and $many(T) : many(t)$ meaning it must hold that $many(t_1) = many(t_2)$ for broadcast to be well-typed and therefore $P arrow.r.not wrong$.
  ]
  #case(of: tepin("t-recv"))[
    By our assumption we have that $PEnv |- receive(c, many(x) : many(t)).P$ and must prove that $receive(c, many(x) : many(t)).P rnt wrong$. By inspecting #rwrongn("rw-send") we can see that $receive(c, many(x) : many(t)).P -t wrong$ if $c: ch(many(t_1))$ and $many(x): many(t_2)$ where $many(t_1) eq.not many(t_2)$. This contradicts #tepin("t-recv") as for send to be well-typed $c : ch(many(t))$ and $many(x) : many(t)$, and therefore it must be that $t_1 = t_2$. We can therefore conclude $P arrow.r.not wrong$.
  ]
  #case(of: tepin("t-if"))[
    By our assumption we have that $PEnv |- [T_1 bow T_2]P,Q$ and must prove that $ [T_1 bow T_2]P,Q rnt wrong$. By inspecting #rwrongn("rw-match") we can see that $[T_1 bow T_2]P,Q -t wrong$ if $T_1: t_1$, $T_2 : t_2$ and $t_1 eq.not t_2$. This contradicts #tepin("t-if") as $T_1 : t$ and $T_2 : t$, that being $t_1 = t_2$ for match to be well-typed and therefore $P arrow.r.not wrong$
  ]

  