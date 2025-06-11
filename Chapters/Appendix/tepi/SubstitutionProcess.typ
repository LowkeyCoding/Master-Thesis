#import "../../../Packages/global.typ": *
#let epi(x) = shown(repi, x)
#let tepi(x) = shown(rtepi, x)
// RN(y,x) x is replaced by y
== Proof of Lemma 3.10 <app:proof_tepi_sub>
#proof(of: <lem:tepi_subst_p>)[
  #case(of: tepi("t-nil"))[
    Then $P = null$. Then from the @def:sub-epi-p we get the substitution $P rn(T_u,T'_u)=null$ and using #tepi("t-nil") we get that $PEnv |- P$.
  ] 
  #case(of: tepi("t-par"))[
    Then $P = Q | R$. Then using @def:sub-epi-p we get that $P rn(T_u,T'_u) = Q rn(T_u,T'_u) | R rn(T_u,T'_u)$. Then using the inductive hypothesis we get that $PEnv |- Q rn(T_u,T'_u)$ and $PEnv |- R rn(T_u,T'_u)$. Therefore, applying #tepi("t-par") preserves the typing $PEnv |- P rn(T_u,T'_u)$. 
  ] 
  #case(of: tepi("t-rep"))[
    Then $P = !Q$. Then from @def:sub-epi-p we get that $P rn(T_u,T'_u) = !(Q rn(T_u,T'_u))$. Then using the inductive hypothesis we get that $PEnv |- Q rn(T_u,T'_u)$.
    Therefore, applying #tepi("t-rep") preserves the typing $PEnv |- P rn(T_u,T'_u)$. 
  ] 
  // case
  #case(of: tepi("t-res"))[
    Then $P = (nu a : t) Q$. Then from @def:sub-epi-p we get two cases: 
    #case(of: $a in.not fn(T_1) union fn(T_2)$)[
      Then using the inductive hypothesis we get that $DEnv, a : t, CEnv tack |- Q rn(T_u,T'_u)$. Therefore, when applying #tepi("t-res") we get that $PEnv |- (nu a : t) Q rn(T_u,T'_u)$.
    ]
    #case(of: $a in.not fn(T_1) union fn(T_2)$)[
      From @def:sub-epi-p we get that $b in.not fn(T_u) union fn(T_u') union fn(Q)$, $(nu b : t) Q' rn(T''_u, T'''_u)$ and where $T''_u = T_u rn(a,b)$, $T'''_u = T'_u$ and $Q' = Q rn(a,b)$. Then by induction hypothesis we have $DEnv, b : t, CEnv tack Q rn(a,b)$ and the typing of $Q'$ is preserved and by @lem:tepi_subst_t the typing is preserved for $T''$ and $T'''$ s.t $DEnv, b : t, CEnv tack T'' : t_u$ and $DEnv, b : t, CEnv tack T''' : t_u$. Then first case of @def:sub-epi-p applies as $b in.not fn(T''_u) union fn(T'''_u)$ therefore, using the induction hypothesis $DEnv, b : t, CEnv tack Q'$,$DEnv, b : t, CEnv tack T''_u : t_u$ and $DEnv, b : t, CEnv tack T'''_u : t_u, $ . Then, when applying #tepi("t-res") preserves the typing $PEnv |- (nu b : t) Q' rn(T''_u,T'''_u)$.
    ]
  ]
  
  #case(of: tepi("t-send"))[
    Then $P = send(c, many(T)).Q$. Then from @def:sub-epi-p we get that $(send(c, many(T)).Q) rn(T_u,T'_u) = overline(c) rn(T_u,T'_u) angle.l many(T) rn(T_u,T'_u) angle.r .Q rn(T_u,T'_u)$. Then using the inductive hypothesis we get that $PEnv tack overline(c) rn(T_u,T'_u)$, $PEnv |- Q rn(T_u,T'_u)$, and $PEnv |- many(T) rn(T_u,T'_u)$. Then, when applying #tepi("t-send") preserves the typing $PEnv |- send(c, many(T)).Q) rn(T_u,T'_u)$.
  ] 
  #case(of: tepi("t-broad"))[
    Then $P = broad(c, many(T)).Q$. Then from @def:sub-epi-p we get that $(broad(c, many(T)).Q) rn(u_1,u_2) = overline(c) rn(u_1,u_2) angle.l many(T) rn(u_1,u_2) angle.r .Q rn(u_1,u_2)$. Then using the inductive hypothesis we get that $PEnv tack overline(c) rn(T_u,T'_u)$, $PEnv |- Q rn(T_u,T'_u)$, and $PEnv |- many(T) rn(T_u,T'_u)$. Then, when applying #tepi("t-broad") preserves the typing $PEnv |- broad(c, many(T)).Q) rn(u_1,u_2)$. 
  ] 
  #case(of: tepi("t-recv"))[
    Then $P = c(many(x) : many(t)).Q$. Then from @def:sub-epi-p we get two cases: 
    #case(of: $many(x) sect fv(T_1) union fv(T_2) eq emptyset$)[
      From @def:sub-epi-p we get that $(c(many(x) : many(t)).Q) rn(T_u,T'_u) = receive(c rn(T_u,T'_u), many(x) : many(t)).Q rn(T_u,T'_u)$. Then using the inductive hypothesis we get that $DEnv,many(x):,many(t),CEnv tack c rn(T_u,T'_u) : ch(many(t))$,$DEnv,many(x):,many(t),CEnv tack Q rn(T_u,T'_u)$. Therefore, applying #tepi("t-recv") preserves the typing $PEnv tack c(many(x) : many(t)).Q rn(T_u,T'_u)$
    ]
    #case(of: $many(x) sect fv(T_1) union fv(T_2) eq.not emptyset$)[
      From @def:sub-epi-p we get that $many(y) in.not fn(T_u) union fn(T_u') union fn(Q)$, $receive(c, many(y) : many(t)).Q'$ and where $T''_u = T_u rn(many(x),many(y))$, $T'''_u = T'_u rn(many(x),many(y))$ and $Q' = Q rn(many(x),many(y))$. Then by induction hypothesis we have $DEnv, many(y) : many(t), CEnv tack Q rn(many(x),many(y))$ and the typing of $Q'$ is preserved and by @lem:tepi_subst_t the typing is preserved for $T''$ and $T'''$ s.t $DEnv, many(y) : many(t), CEnv tack T'' : t_u$ and $DEnv, many(y) : many(t), CEnv tack T''' : t_u$. Then first case of @def:sub-epi-p applies as $b in.not fn(T''_u) union fn(T'''_u)$ therefore, using the induction hypothesis $DEnv, many(y) : many(t) tack c rn(T''_u,T'''_u) : ch(many(t))$, $DEnv, many(y) : many(t), CEnv tack Q' rn(T''_u,T'''_u)$. Therefore, applying #tepi("t-recv") preserves the typing $PEnv tack (c(many(y) : many(t)).Q) rn(T''_u,T'''_u)$
    ]
  ] 
  #case(of: tepi("t-if"))[
    Then $P = [T_1 bow T_2]Q,R$ and from #tepi("t-if") we get that $PEnv |- T_1 : t$, $PEnv |- T_2: t$, $PEnv |- Q$ and $PEnv |- R$. Then from @def:sub-epi-p we get that $P rn(T_u,T'_u) = [T_1 rn(T_u,T'_u) bow T_2 rn(T_u,T'_u)]Q rn(T_u,T'_u), R rn(T_u,T'_u)$. Then from @lem:tepi_subst_t we get that $PEnv |- T_1 rn(T_u,T'_u) : t$ and $PEnv |- T_2 rn(T_u,T'_u) : t$. Then by the induction hypothesis we get that $PEnv |- Q rn(T_u,T'_u)$ and $PEnv |- R rn(T_u,T'_u)$.
    Therefore, applying #tepi("t-if") preserves the typing $PEnv |- ([T_1 bow T_2]Q,R) rn(T_u,T'_u)$
  ] 
]
