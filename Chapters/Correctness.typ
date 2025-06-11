#import "../Packages/global.typ": *


== Correctness of the Translation //from #btf to #tepi
As we have now shown the translation of #btf to #tepi, the next important step is to show that the translation is correct. But before we get to the proof we will need to define what a correct translation is. Our approach to define and prove correctness is similar to @ButfToEpi, that being by an operational correspondence, with a few changes brought forth by the type systems.

=== Defining Bisimulation
We have some important definitions we need before we can define operational correspondence. One of the main parts of operational correspondence is the notion of bisimilarity - more specifically in our case, a barbed congruence. A barb, as introduced by #cn(<BarbedBi>) in @BarbedBi, is a predicate $barb("",alpha)$ such that $P attach(arrow.long, t: alpha)$ that being $P$ can perform some observable action $alpha$. In our case $alpha$ is either an input ($a$), output ($overline(a)$) or a broadcast ($overline(a)#h(-0.1pt):#h(-0.1pt)$).

For our definition of barbed bisimulation, we have the notion of multiple important and administrative reductions. The definition we give is the same as seen in @ButfToEpi.

#definition("Multiple important and administrative transitions")[
  The transition $=s$ is defined for labels $s in {circle.small, circle.small.filled}$ as follows:
  $ 
  =s = cases(
    s = circle.small\, attach(arrow.long, t: circle.small, tr: *),  
    s = circle.small.filled\,attach(arrow.long,  tr: *, t:circle.small) -i
 )
  $
]<def:MultiTrans>

Another important definition we introduce is the complete context. This approach of constricting contexts is inspired by #cn(<CompleteContextYoink>), @CompleteContextYoink.
#definition("Complete context")[
  Let $PEnv |- P$ and $C[dot]$ be a context with a hole with $fn(C[dot]) union fv(C[dot])=cal(M)$, then we say $C$ is a complete context if $exists DEnv',CEnv' $ s.t $DEnv',CEnv' |- C[P]$ where $dom(DEnv'\,CEnv') = cal(M)$.
]<def:compContext>

Now we can finally give the definition of Weak Administrative Barbed Bisimulation (WABB). The definition of WABB is similar to the one seen in @ButfToEpi.

#definition("Weak Administrative Barbed Bisimulation")[
  Suppose $PEnv |- P,Q$ and let $cal(R)$ be symmetric relation over processes. Then $cal(R)$ is called a Weak Administrative Barbed Bisimulation if for whenever $rel(P,Q)$ the following holds:
  1. If $P -i P'$ then $Q =i Q'$ and $rel(P',Q')$
  2. If $P -a P'$ then $Q =a Q'$ and $rel(P',Q')$
  3. For each prefix $alpha$, $barb(P,alpha)$ implies $barb(Q =a,alpha)$
  4. For all complete contexts $C$, $rel(C(P), C(Q))$
  // then $bi(e,e')$
  We write $bim(P, Q)$ if there exist a weak administrative barbed bisimulation $cal(R)$ such that $rel(P,Q)$.
]<def:Wabb>

The definition of a complete context (@def:compContext) is necessary in the definition of WABB. Let us imagine we defined WABB without a complete context and just allowed a relation on every context filled with well-typed processes. We would then be able to relate two process that by themselves are well-typed, but put in a context are ill-typed. The complete context restricts the contexts such that we only look at contexts that is also well-typed when the hole is filled with a well-typed process. 
//The use of administrative and important reductions from @def:MultiTrans is necessary for it be considered a weak Barbed Bisimulation 
//similar to what can be seen in a weak bisimilarity in CCS where an action can be matched using an arbitrary number of silent transition preceeding and following the action.

=== Defining Correctness

With the definition of WABB we can start defining correctness of the translation. We have two requirements for the translation. The first requirement is the correctness of types is preserved after translation. This gives us the following theorem.
// Start vi ud med den tomme PI - skal vi have krav til den?
#theorem($"Typed correctness"$)[
  Let $e$ be a #btf expression. \
  1. (Soundness) If $Env |- e : tau$ then $tle(e,o) = (PEnv, P)$ where $PEnv |- P$ and $DEnv(o) = ch(tl(tau))$. \
  2. (Completeness) If $tle(e,o) = (PEnv, P)$, $PEnv |- P$ and there exists $DEnv(o) : ch(t)$ with $t = tl(tau)$ then $Env |- e : tau$.
  We then say that $tok(e,tle(e,o))$ if the typed translation is sound and complete.
  // 2. $forall x in fv(e). PEnv(x) = tl(Env(x))$. 
  // $tl(Env) |- tl(e) : tl(tau)$
  // hvis oversættelse af e kan types og output har typen t og t = tl(tau) så kan e types under tau. 
]<th:typeCorrectness>


The second requirements is the behaviour is preserved after the translation. The second part is achieved by the notion of operational correspondence which is inspired by #cn(<Amadio>), @Amadio. Our definition of operational correspondence is similar to the one as seen in @ButfToEpi with the addition of requiring that expressions and processes must be well-typed. 

#definition($"Operational Correspondence" $)[
  Let $Env |- e : tau$ be a well-typed #btf expression, $PEnv |- P$ a well-typed #tepi process and $R$ be non-symmetric binary relation between an expression and a process. Then $R$ is an administrative operational correspondence if $forall(e,P) in R$ the following holds:
  1. If $e -> e'$ then $exists P'$ such that $P =i Q$, $ bim(Q,P')$ and $orel(e', P')$
  2. If $P =i P'$ then $exists e', Q$ such that $e -> e'$, $bim(Q, P')$ and $orel(e', Q)$ 
  We say that $ocp(e,P)$ if there exists an operational correspondence relation $R$ such that $orel(e,P)$.
]<def:opcor>

From the definition of operational correspondence we have two conditions. Condition 1 achieves soundness by guaranteeing that reductions of #btf expression $e$ can be matched by a sequence of one or more reductions in the corresponding #tepi process $P$. Condition 2 achieves completeness by ensuring that $e$ can always evolve to some $e'$ given that $P$ has any important reduction and that the evolved expression $e'$ is in an operational correspondence with some $Q$, and that $P'$ and $Q$ are WABB. The later part is important for ensuring the operational correspondence after a reduction. For the behavioural correctness we get the following theorem.
// This gives us the main theorem for correctness.
#theorem("Behavioural correctness")[
  Let $e$ be a well-typed #btf expression and $o$ be a fresh name then $ocp(e, tle(e,o))$.
]<th:correctness>

@th:correctness states that a #btf expression and the translation of the expression is in an operational correspondence and in the proof we will show this. In the proof we will denote condition 1 as soundness and condition 2 as completeness. 
To help prove @th:correctness we need some lemmas as seen in @ButfToEpi.

//Another important part of defining correctness of the typed translation is that the translation of types are correct. This gives us the following theorem.
//which states that when translating a #btf expression the type of expression matches the type of the output channel. 
// Since there is no one to one correspondence of types between expressions and processes we must instead ensure the translations of types are matching.



/*
#inote[
  We might want to add administrative types such that we can show that given zero or more administrative types the type signatures are equivalent. \
  Theorems and lemmas need to be rewritten in a mathematical language.
]
*/



#lemma("Program behaviour")[
  For any $PEnv |- P$, complete context $C$ and \ $s in {circle.small, circle.small.filled}$, then if there exists a $PEnv |- Q$ s.t $C[P] -s Q$, then one of the following holds:
  1. Only $C$ reduces, therefore $Q = C'[P]$ s.t $C[null] -s C'[null]$.
  2. Only $P$ reduces, therefore $Q = C[P']$ s.t $P -s P'$.
  3. $C$ and $P$ interact, therefore $Q = C'[P']$ and there exists an $O$ s.t \ $C[P] == (nu many(a) : many(t_a)).(O | P)$, $O | P -s O' | P'$ and $C[P] -s C'[P']$.
]<lem:prgBehave>

@lem:prgBehave states three different cases in which processes can reduce when within a context. In the first case only the context reduces. In the second only the process within the context reduces. In the last case an interaction occurs and as such both the context and process reduces. This lemma is useful for simplifying the proofs for some of the later lemmas.


#lemma("Preservation of substitution")[ let $Env |- e_1 : tau$ and $Env |- e_2 : tau$ be well-typed #btf expression and $e_2 in cal(V)$ then
  1. If $e_2$ is a number then $bim(tle(e_1,o) rn(x,n), tle(e_1{x |-> n},o))$ for some $o$
  2. If $e_2$ is an abstraction, tuple or array then $bim((nu h : t) . (Q | tle(e_1,o) rn(x,h)), tle(e_1 {x |-> e_2},o))$ for some $o$, where $tle(e_2,o) | receive(o,x : t).P =i (nu h: t) . (Q | P rn(x,h))$ and $t = tl(tau)$.
]<lem:PreserveSub>

@lem:PreserveSub is necessary in proving @th:correctness, more specifically application. As in the application we have two expression $e_1 e_2$ with the first being an abstraction. We need to know if we can substitute in with the value from the second expression. This is necessary for us argue that the translation after reductions can be matched with application in $btf$ after the transition step. 

The next two lemmas will be necessary to show that processes that are finished in the translation can be removed without any other processes being affected. First, @lem:GarbageProc states that processes bisimilar to the $null$ processes will always be bisimilar even after possible reductions. Second, @lem:GarbageCollect states that we can remove theses processes without affecting other processes.

#lemma("Garbage processes")[
  For any $PEnv |- P$ then if $bim(P,null)$ and there exists $P'$ such that $P attach(arrow.double.long, t: s, tr: *) P'$ then $forall alpha . P' adown(alpha)$ and $bim(P', null)$.
]<lem:GarbageProc>

#lemma("Garbage collection")[
  For any complete context $C$ and any $PEnv |- P$ where $bim(P, null)$, then for all $PEnv |- Q$ it holds that $bim(P | Q,Q)$. 
]<lem:GarbageCollect>

@lem:tvoo is necessary if we want to know if there is an observable action after some administrative reductions. This will useful in the proof for behavioral correctness to argue for the bisimilarity of two processes. @lem:teoo states that if a translated expression after some reductions eventually outputs on $o$ then $e$ is a value. 

#lemma("Translated value has observable output")[
  If $Env |- e : tau$ and $e in cal(V)$  then there exists an $PEnv |- P$, s.t $tle(e,o) =a P$ and $barb(P, overline(o))$.
]<lem:tvoo>

#lemma("Translated expression has observable ouput")[  
  There exists $Env |- e : tau$ and $PEnv |- P$ s.t $tle(e,o) =a P$ and $barb(P, overline(o))$ then it holds that $e in cal(V)$.
 ]<lem:teoo>


From the two theorems about correctness of the translation we get following corollary which states that any given well-typed #btf expression can be translated and stay well-typed in #tepi while preserving the behaviour from $btf$.
 #corollary("Correctness of the typed translation")[
   Given a well-typed #btf expression $Env |- e: tau$ and a fresh $o$ then $ocp(e,tle(e,o))$ and $tok(e,tle(e,o))$
 ]<th:CorrectTypedTl>

#include "Proofs/Correctness.typ"
