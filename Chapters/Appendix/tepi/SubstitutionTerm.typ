#import "../../../Packages/global.typ": *
#let epi(x) = shown(repi, x)
#let tepi(x) = shown(rtepi, x)

== Proof of Lemma 3.9 <app:proof_tepi_sub_t>

#proof(of: <lem:tepi_subst_t>)[
  #case(of: tepi("t-n"))[
    Then $T = n$. Then from the @def:sub-epi-t we get the substitution $n rn(T_u,T'_u)=n$ and applying #tepi("t-n") preserves the typing $PEnv |- n : Int$.
  ] 
  #case(of: tepi("t-u"))[
    Then $T = u$ and from #tepi("t-u") we get that $PEnv(u) = t$. Then from @def:sub-epi-t we get two cases:
    #case(of: $u = T_u$)[
      From the substitution we get that $u rn(T_u, T'_u) = T_u'$ and $u = T_u$ therefore $DEnv(T_u) = t$ and since $PEnv |- T'_u : t_u$ we get that $t = t_u$. Then since $PEnv |- T_u : t_u$ we get that $PEnv(T_u) = t$. Therefore applying #tepi("t-u") preserves the typing $PEnv |- u rn(T_u, T'_u) : t$.
    ]
    #case(of: "otherwise")[
      From the substitution we get that $u rn(T_u, T'_u) = u$ and applying #tepi("t-u") preserves the typing $PEnv |- u : t$ and therefore $PEnv |- u rn(T_u, T'_u) : t$ preservers the typing.
    ]
  ]
  #case(of: tepi("t-bin"))[
    Then $T = T_1 bin T_2$, where $PEnv |- T_1 : Int$,$PEnv |- T_2 : Int$ and $t = Int$. Then from @def:sub-epi-t we get that $(T_1 bin T_2) rn(T_u,T'_u) = T_1 rn(T_u,T'_u) bin T_2 rn(T_u,T'_u)$. Then from the inductive hypothesis we get that $PEnv |- T_1 rn(T_u,T'_u): Int$ and $PEnv |- T_2 rn(T_u,T'_u) : Int$. Therefore, applying #tepi("t-bin") preservers the typing $PEnv |- (T_1 bin T_2) rn(T_u,T'_u) : Int$.
  ]
  // Minor detail this is neither a process nor a term
  #case(of: tepi("t-comp"))[
    Then $T = c dot T'$ and as $T'$ can be typed with either #tepi("t-comp") and #tepi("t-comp2") depending on wether $T'$ is $x$ or $n$. Then from @def:sub-epi-c we get substitution on both $c$ and $T$ therefore we can apply it component wise s.t we get $c' = c rn(T_u,T'_u)$ and $T' = T rn(T_u,T'_u)$ from the induction hypothesis we get that $PEnv(c') : pch()$ and $DEnv(c', T') : hh(many(t))$. Since, the types $pch()$ and $hh(many(t))$ are preserved after substitution then $hh(many(t)) in pch()$ holds. Therefore, applying #tepi("t-comp") or #tepi("t-comp2") preserves the typing $PEnv |- (c dot T) rn(T_u,T'_u) : ch(t)$.
    // Then $T = c dot T'$ and as $T'$ can be typed with either #tepi("t-comp") and #tepi("t-comp2") depending on wether $T'$ is $x$ or $n$. Therefore we get that $(DEnv,u:t_u)(c) = pch()$, $CEnv(c,T') = hh(t)$, $hh(t) in pch()$ and  $DEnv,u:t_u,CEnv |- c dot T' : ch(t)$. Then as $u$ is not in the environment by @def:well-formed and by @def:tepi_cenv we know that the type of $T'$ depends on the handle $c$ then $c eq.not u$ and $T' eq.not u$. Therefore applying #tepi("t-comp") or #tepi("t-comp2") preserves the typing $PEnv |- T : ch(t)$.
  ]
]