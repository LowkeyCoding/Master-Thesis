#import "../../../Packages/global.typ": * 
#let epi(x) = shown(repi, x)
#let tepi(x) = shown(rtepi, x)


== Proof of Lemma 3.7 <app:proof_tepi_strengt>

#proof(of:<lem:stronk_tepi_p>)[
  #case(of: $null$)[
    Using #tepi("t-nil") we get that $DEnv,u :t, CEnv |- null$ holds for any $PEnv$ as $null$ is not dependent on the environment.
  ]
  #case(of: $P | Q$)[
    Then $P = Q | R$ and by #tepi("t-par") we get that if $DEnv, u : t_u, CEnv |- P$, then $DEnv,u : t_u, CEnv |- Q$ and $DEnv,u : t_u, CEnv |- R$. Then from the induction hypothesis we have that $DEnv,u : t_u, CEnv |- Q$ and $DEnv,u : t_u, CEnv |- R$. Therefore applying #tepi("t-par") gives us $PEnv |- Q | R$ preserving that $P$ is well-typed.
  ]
  #case(of: $!P$)[
    Then $P = !Q$ and by #tepi("t-rep") we get that if $DEnv, u : t_u, CEnv |- P$, then $DEnv, u : t_u, CEnv |- Q$. Then from the inductive hypothesis we have that $PEnv |- P$. Therefore applying #tepi("t-rep") gives us $PEnv |- !Q$ preserving that $P$ is well-typed.
  ]
  #case(of: $(nu a: t).P$)[
    Then $P = (nu a : t).Q$ and by #tepi("t-res") we get that if $DEnv, u : t_u, CEnv |- P$, then $DEnv, u : t_u, a : t, CEnv |- Q$. From the induction hypothesis we get that $DEnv,a:t, CEnv |- Q$ and that $u in.not dom(DEnv\,a:t)$ therefore $u != a$. Therefore applying #tepi("t-res") gives us $DEnv,u:t_u, CEnv |- (nu a : t).Q$ preserving that $P$ is well-typed.
  ] // maybe okay?
  
  #case(of: $send(c, many(T)).P$)[
    Then $P = send(c, many(T).Q)$ and by #tepi("t-send") we get that if $DEnv, u : t_u, CEnv |- P$, then $DEnv, u : t_u, CEnv |- c : ch(many(t))$, $DEnv, u : t_u, CEnv |- many(T) : many(t)$ and $DEnv, u : t_u, CEnv |- Q$. Then from the inductive hypothesis we have that $PEnv |- Q$. Then using @lem:stronk_tepi_t we can strengthen the terms and channel s.t $PEnv |- c : ch(many(t))$, $PEnv |- many(T) : many(t)$. Therefore applying #tepi("t-send") gives us $PEnv |- send(c,many(T)).Q$ preserving that $P$ is well-typed.
  ] // ok
  
  #case(of: $c(many(x):many(t)).Q$)[
    Then $P = c(many(x):many(t)).Q$ by and #tepi("t-recv") we get that if $DEnv, u : t_u, CEnv |- P$, then $DEnv, u : t_u, CEnv |- c: "ch"(many(t))$ and $DEnv, u : t_u,many(x):many(t), CEnv |- Q$. Then from the inductive hypothesis we get that $DEnv,many(x):many(t), CEnv |- Q$ and that $u in.not dom(DEnv\,a:t)$ therefore $u != a$. Then using @lem:weak_tepi_t we can strengthen the channel s.t $PEnv |- c: "ch"(many(t))$. Therefore applying #tepi("t-recv") gives us $PEnv |- c(many(x):many(t)).Q$ preserving that $P$ is well-typed.
  ] 
  
  #case(of: $broad(c,many(T)).P$)[
    Then $P = broad(c, many(T).Q)$ and by #tepi("t-broad") we get that if $DEnv, u : t_u, CEnv |- P$, then $DEnv, u : t_u, CEnv |- c : ch(many(t))$, $DEnv, u : t_u, CEnv |- many(T) : many(t)$ and $DEnv, u : t_u, CEnv |- Q$. Then from the inductive hypothesis we have that $PEnv |- Q$. Then from @lem:stronk_tepi_t we can strengthen the terms and channel s.t $PEnv |- c : ch(many(t))$, $PEnv |- many(T) : many(t)$. Therefore applying #tepi("t-broad") gives us $PEnv |- broad(c,many(T)).Q$ preserving that $P$ is well-typed.
  ] // ok
  
  #case(of: $[T_1 bow T_2]P,Q$)[
    Then $P = [T_1 bow T_2]Q,R$ and by #tepi("t-if") we get that if $DEnv, u : t_u, CEnv |- P$, then $DEnv, u : t_u, CEnv |- T_1 : t$, $DEnv, u : t_u, CEnv |- T_2 : t$, $DEnv, u : t_u, CEnv |- Q$ and $DEnv, u : t_u, CEnv |- R$. Then from the inductive hypothesis we have that $PEnv |- Q$ and $PEnv |- R$. Then from @lem:stronk_tepi_t we can strengthen the terms s.t $PEnv |- T_1 : t$ and $PEnv |- T_2 : t$. Therefore applying #tepi("t-if") gives us $PEnv |- [T_1 bow T_2]Q,R$ preserving that $P$ is well-typed.
  ] // ok
]