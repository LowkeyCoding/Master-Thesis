#import "../../../Packages/global.typ": * 
#let epi(x) = shown(repi, x)
#let tepi(x) = shown(rtepi, x)

== Proof of Lemma 3.6 <app:proof_tepi_strengt_t>

#proof(of:<lem:stronk_tepi_t>)[
  #case(of: $n$)[
    Then $T = n$ and from #tepi("t-n") we get that $DEnv,u:t_u, CEnv |- T : Int$. Then from @def:fnt and @def:fvt we get that $fn(T) union fv(T) = emptyset$. From @def:well-formed we can derive $u in.not fn(P) union fv(P)$. Therefore applying #tepi("t-n") without $u$ in the environment preserves the typing $PEnv |- T : Int$.
  ] // fix
  #case(of: $u$)[
    Then $T =  u'$ and from #tepi("t-u") we get that $DEnv,u:t_u, CEnv |- T : t$ and $(DEnv,u:t_u, CEnv)(u') = t$. 
    #case(of: $u' eq.not u$)[
      Then as $u in.not dom(DEnv)$ and $u' in dom(DEnv)$ we get that $DEnv(T) : t$. Therefore applying #tepi("t-u") without $u$ in the environment preserves the typing $PEnv |- T : t$.
    ]
    #case(of: $u' eq u$)[
      contradicts $u in.not dom(DEnv)$.
    ]
  ]
  #case(of: $T_1 bin T_2$)[
    Then $T = T_1 union T_2$ and from #tepi("t-bin") we get that $DEnv,u : t_u, CEnv |- T : Int$, $DEnv,u : t_u, CEnv |- T_1 : Int$ and  $DEnv,u : t_u, CEnv |- T_2 : Int$. Then using the inductive hypothesis we get that $PEnv |- T_1 : Int$ and $PEnv |- T_2 : Int$. Therefore applying #tepi("t-bin") preserves the typing $PEnv |- T : Int$.
  ]
  #case(of: $c dot T$)[
    Then $T = c dot T'$ and as $T'$ can be typed with either #tepi("t-comp") and #tepi("t-comp2") depending on wether $T'$ is $x$ or $n$. Therefore we get that $(DEnv,u:t_u)(c) = pch()$, $CEnv(c,T') = hh(t)$, $hh(t) in pch()$ and  $DEnv,u:t_u,CEnv |- c dot T' : ch(t)$. Then as $u$ is not in the environment by @def:well-formed and by @def:tepi_cenv we know that the type of $T'$ depends on the handle $c$ then $c eq.not u$ and $T' eq.not u$. Therefore applying #tepi("t-comp") or #tepi("t-comp2") preserves the typing $PEnv |- T : ch(t)$.
  ]
]