#import "../../../Packages/global.typ": *
#let epi(x) = shown(repi, x)
#let tepin(x) = shown(rtepi, x)

== Proof of Lemma 3.4 <app:proof_tepi_weak_t>

#proof(of: <lem:weak_tepi_t>)[
  #case(of: $n$)[
    Then $T = n$, and from #tepin("t-n") we get that $PEnv |- T : Int$. Then from @def:fnt and @def:fvt we get that $fn(T) union fv(T) = emptyset$. Therefore adding $u : t_u$ to $DEnv$ and applying #tepin("t-n") preserves the typing $DEnv,u : t_u, CEnv |- T : Int$. 
  ]
  #case(of: $u$)[
    Then $T = u'$, and from #tepin("t-u") we get that $PEnv |- T : t$ and $DEnv(u') = t$. Since $u in.not dom(DEnv)$, then $(DEnv,u:t_u,CEnv)(u') = t$ therefore applying #tepin("t-u") preserves the typing $DEnv, u :t_u, CEnv |- T : t$.
  ]
  #case(of: $T_1 bin T_2$)[
    Then $T = T_1 bin T_2$, and from #tepin("t-bin") we get that $PEnv |- T : Int$, $PEnv |- T_1 : Int$ and $PEnv |- T_2 : Int$. Then from the induction hypothesis we get that $DEnv, u:t_u, CEnv |- T_1 : Int$ and $DEnv, u:t_u, PEnv |- T_2 : Int$. Therefore applying #tepin("t-u") preserves the typing $DEnv, u : t_u, CEnv |- T : Int$.
  ]
  #case(of: $c dot T$)[
   Then $T = c dot T'$ and as $T'$ can be typed with either #tepin("t-comp") and #tepin("t-comp2") depending on wether $T'$ is $x$ or $n$. Therefore we get that $DEnv(c) = pch()$, $CEnv(c,T') = hh(t)$, $hh(t) in pch()$ and  $DEnv,CEnv |- c dot T' : ch(t)$. Therefore applying #tepin("t-comp") or #tepin("t-comp2") preserves the typing $DEnv,u : t_u,CEnv |- c dot T' : ch(t)$. Then as $u$ is not in the environment by @def:well-formed and by @def:tepi_cenv we know that the type of $T'$ depends on the handle $c$ then $c eq.not u$ and $T' eq.not u$. Therefore applying #tepin("t-comp") or #tepin("t-comp2") with $u$ in the environment preserves the typing $DEnv,u:t_u,CEnv |- T : ch(t)$.
    // Then $T = c dot T'$ and as $T'$ can be typed with either #tepi("t-comp") and #tepi("t-comp2") depending on wether $T'$ is $x$ or $n$. Therefore we get that $(DEnv,u:t_u)(c) = pch()$, $CEnv(c,T') = hh(t)$, $hh(t) in pch()$ and  $DEnv,u:t_u,CEnv |- c dot T' : ch(t)$. Then as $u$ is not in the environment by @def:well-formed and by @def:tepi_cenv we know that the type of $T'$ depends on the handle $c$ then $c eq.not u$ and $T' eq.not u$. Therefore applying #tepi("t-comp") or #tepi("t-comp2") preserves the typing $PEnv |- T : ch(t)$.
  ]
]