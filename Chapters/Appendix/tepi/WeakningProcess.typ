#import "../../../Packages/global.typ": *
#let epi(x) = shown(repi, x)
#let tepi(x) = shown(rtepi, x)

== Proof of Lemma 3.5 <app:proof_tepi_weak>

#proof(of: <lem:weak_tepi_p>)[
  By induction on derivation of  $PEnv |- P$
  #case(of: $null$)[
    Then $P = null$ and by #tepi("t-nil") we get that $PEnv |- null$ holds for any $PEnv$ as $null$ is not dependent on the environment.
  ] // ok
  #case(of: $P | Q$)[
    Then $P = Q | R$ and by #tepi("t-par") we get that if $PEnv |- P$, then $PEnv |- Q$ and $PEnv |- R$. Then using the induction hypothesis we get that $DEnv,u : t_u, CEnv |- R$ and $DEnv,u : t_u, CEnv |- Q$. Therefore applying #tepi("t-par") gives us  $DEnv,u : t_u, CEnv |- Q | R$ preserving that $P$ is well-typed.
  ] // ok
  #case(of: $!P$)[
    Then $P = !Q$ and by #tepi("t-rep") we get that if $PEnv |- !Q$, then $PEnv |- Q$. Then using the induction hypothesis we get that $DEnv,u:t_u,CEnv |- Q$. Therefore applying #tepi("t-rep") gives us $DEnv,u:t_u, CEnv |- !Q$ preserving that $P$ is well-typed.
  ] // ok
  #case(of: $(nu a: t).P$)[
     Then $P = (nu a: t).Q$ and by #tepi("t-res") we get that if $PEnv |- P$, then $DEnv, a: t,CEnv |- Q$. Then using the induction hypothesis we get that $DEnv,a: t, u:t_u, CEnv |- Q$. Therefore applying #tepi("t-res") gives us $DEnv,u:t_u, CEnv |- (nu a: t).Q$ preserving that $P$ is well-typed.
  ] // maybe look at other ways of showing a != u
  #case(of: $send(c, many(T)).P$)[
    Then $P = send(c, many(T)).Q$ and by #tepi("t-send") we get that if $PEnv |- P$, then $PEnv |- c: ch(many(t))$, $PEnv |- many(T) : many(t)$ and $PEnv |- Q$. Then using the inductive hypothesis we get that $DEnv,u:t_u,CEnv |- Q$. Then by @lem:weak_tepi_t we get that we can weaken the terms and the channel s.t $DEnv,u:t_u,CEnv |- c: ch(many(t))$ and $DEnv, u:t_u,CEnv |- many(T) : many(t)$. Therefore applying #tepi("t-send") gives us $PEnv,u:t_u |- send(c, many(T)).Q$ preserving that $P$ is well-typed..
  ] // ok
  #case(of: $receive(c, many(x): many(t)).Q$)[
    Then $P = c(many(x),many(t)).Q$ and by #tepi("t-recv") we get that if $PEnv |- P$, then $PEnv |- c: ch(many(t))$ and $DEnv,many(x):many(t), CEnv |- Q$. From @def:well-formed we can derive that $u in.not fn(P) union fv(P)$. Since $PEnv$ only contains free variables/names therefore $u$ is a new free variable or name. Then by the induction hypothesis we get that $DEnv' = DEnv,many(x) : many(t),u : t_u$, $DEnv',CEnv |- Q$. Therefore applying #tepi("t-recv") gives us $DEnv,u:t,CEnv |- c(many(x),many(t)).Q$ preserving that $P$ is well-typed..
  ] // fix
  #case(of: $broad(c,many(T)).P$)[
    Then $P = broad(c, many(T)).Q$ and by #tepi("t-broad") we get that if $PEnv |- P$, then $PEnv |- c: ch(many(t))$, $PEnv |- many(T) : many(t)$ and $PEnv |- Q$. Then using the inductive hypothesis we get that $PEnv,u:t_u |- Q$. Then by @lem:weak_tepi_t we get that we can weaken the terms and the channel s.t $PEnv,u:t_u |- c: ch(many(t))$ and $DEnv, u:t_u, CEnv |- many(T) : many(t)$. Therefore applying #tepi("t-send") gives us $DEnv,u:t_u,CEnv |- broad(c, many(T)).Q$ preserving that $P$ is well-typed.
  ]
  #case(of: $[T_1 bow T_2]P,Q$)[
    Then $P = [T_1 bow T_2]Q,R$ and by #tepi("t-if") we get that if $PEnv |- P$, then $PEnv |- T_1 : t$,$PEnv |- T_2 : t$, $PEnv |- Q$ and $PEnv |- R$. Then using the inductive hypothesis we get that $DEnv,u:t,CEnv |- Q$ and $PEnv,u:t |- R$. Then using @lem:weak_tepi_t we get that we can weaken the terms s.t $DEnv,u:t,CEnv |- T_1 : t$, $DEnv,u:t,CEnv |- T_2 : t$ Therefore applying #tepi("t-if") we get that $DEnv,u:t,CEnv |- [T_1 bow T_2]Q,R$ preserving that $P$ is well-typed.
  ]
]