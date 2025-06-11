#import "../../../Packages/global.typ": * 

#let rwrongn(x) = shown(rwrong, x)
#let tepin(x) = shown(rtepi, x)

== Proof of Theorem 3.2 - type safety <app:proof_type_safe>

#proof(of: "Type safety of processes")[
  We prove type safety by induction in the type rules.

  #case(of: tepin("t-nil"))[
    Trivial as for #tepin("t-nil") $P arrow.r.not wrong$
  ]
  #case(of: tepin("t-send"))[
    By our assumption we have that $PEnv |- send(c,many(T)) . P$ and must prove that $send(c,many(T)) . P rnt wrong$. By inspecting #rwrongn("rw-send") we can see that $send(c,many(T)) . P -t wrong$ only if $c : ch(many(t_1))$, $many(T) : many(t_2)$ where $many(t_1) eq.not many(t_2)$. This contradicts the type rule for send, that states $c : ch(many(t))$ and $many(T) : many(t)$ meaning it must hold that $many(t_1) = many(t_2)$ for send to be well-typed and therefore $P arrow.r.not wrong$.
  ]
  #case(of: tepin("t-broad"))[
    By our assumption we have that $PEnv |- broad(c,many(T)) . P$ and must prove that $broad(c,many(T)) . P rnb wrong$. By inspecting #rwrongn("rw-broad") we can see that $broad(c,many(T)) . P -b wrong$ only if $c : ch(many(t_1))$, $many(T) : many(t_2)$ where $many(t_1) eq.not many(t_2)$. This contradicts the type rule for broadcast, that states $c : ch(many(t))$ and $many(T) : many(t)$ meaning it must hold that $many(t_1) = many(t_2)$ for broadcast to be well-typed and therefore $P arrow.r.not wrong$.
  ]
  #case(of: tepin("t-recv"))[
    By our assumption we have that $PEnv |- receive(c, many(x) : many(t)).P$ and must prove that $receive(c, many(x) : many(t)).P rnt wrong$. By inspecting #rwrongn("rw-recv") we can see that $receive(c, many(x) : many(t)).P -t wrong$ if $c: ch(many(t_1))$ and $many(x): many(t_2)$ where $many(t_1) eq.not many(t_2)$. This contradicts #tepin("t-recv") as for receive to be well-typed $c : ch(many(t))$ and $many(x) : many(t)$, and therefore it must be that $t_1 = t_2$. We can therefore conclude $P arrow.r.not wrong$.
  ]
  #case(of: tepin("t-if"))[
    By our assumption we have that $PEnv |- [T_1 bow T_2]P,Q$ and must prove that $ [T_1 bow T_2]P,Q rnt wrong$. By inspecting #rwrongn("rw-match") we can see that $[T_1 bow T_2]P,Q -t wrong$ if $T_1: t_1$, $T_2 : t_2$ and $t_1 eq.not t_2$. This contradicts #tepin("t-if") as $T_1 : t$ and $T_2 : t$, that being $t_1 = t_2$ for match to be well-typed and therefore $P arrow.r.not wrong$
  ]
  #case(of: tepin("t-par"))[
    By our assumption we have that $PEnv |- P | Q$ and must prove that $P | Q rnt wrong$. We have two cases where we can go to the #wrong process.
    #case(of: rwrongn("rw-par1"))[
      By inspecting #rwrongn("rw-par1") we can see that $P | Q -t wrong$ if $P -t wrong$. Since $PEnv |- P | Q$ we have that $PEnv |- P$ by #tepin("t-par"), and by our induction hypothesis we have $P rnt wrong$ and therefore we have a contradiction.
    ]
    #case(of: rwrongn("rw-par2"))[
      By inspecting #rwrongn("rw-par2") we can see that $P | Q -t wrong$ if $Q -t wrong$. Since $PEnv |- P | Q$ we have that $PEnv |- Q$ by #tepin("t-par"), and by our induction hypothesis we have $Q rnt wrong$ and therefore we have a contradiction.
    ]
  ]
  #case(of: tepin("t-res"))[
    By our assumption we have that $PEnv |- (nu a : t ). P$ and must prove that $(nu a : t ). P rnq wrong$. Since $PEnv |- (nu a :t ). P$ we have that $PEnv, a : t |- P$ by #tepin("t-par"), and by our induction hypothesis we have $P rnt wrong$ and therefore we have a contradiction.
  ]
  #case(of: tepin("t-rep"))[
    By our assumption we have that $PEnv |- ! P$ and must prove that $! P rnt wrong$. Since $PEnv |- ! P$ we have that $PEnv |- P$ by #tepin("t-par"), and by our induction hypothesis we have $P rnt wrong$ and therefore we have a contradiction.
  ]
]

#proof(of: "Type safety of terms")[
  #case(of: tepin("t-n"))[
    Trivial as for #tepin("t-n") $P arrow.r.not wrong$
  ]
  #case(of: tepin("t-u"))[
    Trivial as for #tepin("t-u") $P arrow.r.not wrong$
  ]
  #case(of: tepin("t-bin"))[
    By our assumption we have that $PEnv |- T_1 bin T_2$ and must prove that $T_1 bin T_2 rnt wrong$. We have two cases where we can go to the #wrong process.
    #case(of: rwrongn("rw-bin1"))[
      By inspecting #rwrongn("rw-bin1") we can see that $T_1 bin T_2 -t wrong$ if $T_1 :t$ and $t eq.not Int$. This contradicts #tepin("t-bin") as for binary operation to be well-typed the type of $T_1$ must be $Int$. Therefore $P arrow.r.not wrong$
    ]
    #case(of: rwrongn("rw-bin2"))[
      By inspecting #rwrongn("rw-bin2") we can see that $T_1 bin T_2 -t wrong$ if $T_2 :t$ and $t eq.not Int$. This contradicts #tepin("t-bin") as for binary operation to be well-typed the type of $T_2$ must be $Int$. Therefore $P arrow.r.not wrong$
    ]
  ]
  #case(of: tepin("t-comp"))[
    By our assumption we have that $PEnv |- u dot x$ and must prove that $u dot x rnt wrong$. We have three cases where we can go to the #wrong process. 
    #case(of: rwrongn("rw-comp1"))[
      By inspecting #rwrongn("rw-comp1") we can see that $u dot x -t wrong$ if $u$ is not a location type. This contradicts #tepin("t-comp") as for a composite name to be well-typed $u$ must be a location type. Therefore $P arrow.r.not wrong$.
    ]
    #case(of: rwrongn("rw-comp2"))[
      By inspecting #rwrongn("rw-comp2") we can see that $u dot x -t wrong$ if $CEnv(u,x) != hh(many(t))$. This contradicts #tepin("t-comp") as for a composite name to be well-typed we have $DEnv(x) = hh(many(t))$. Therefore $P arrow.r.not wrong$.
    ]
    #case(of: rwrongn("rw-comp3"))[
       By inspecting #rwrongn("rw-comp3") we can see that $u dot x -t wrong$ if $hh(many(t)) in.not pch()$. This contradicts #tepin("t-comp") as for a composite name to be well-typed we have $hh(many(t)) in pch()$. Therefore $P arrow.r.not wrong$.
    ]
  ]
  #case(of: tepin("t-comp2"))[
    By our assumption we have that $PEnv |- u dot x$ and must prove that $u dot x rnt wrong$. We have three cases where we can go to the #wrong process. 
    #case(of: rwrongn("rw-comp4"))[
      By inspecting #rwrongn("rw-comp4") we can see that $u dot n -t wrong$ if $u$ is not a location type. This contradicts #tepin("t-comp2") as for a composite name to be well-typed $u$ must be a location type. Therefore $P arrow.r.not wrong$.
    ]
    #case(of: rwrongn("rw-comp5"))[
      By inspecting #rwrongn("rw-comp5") we can see that $u dot n -t wrong$ if $CEnv(u, n) != hh(many(t))$. This contradicts #tepin("t-comp2") as for a composite name to be well-typed we have $CEnv(u,n) = hh(many(t))$. Therefore $P arrow.r.not wrong$.
    ]
    #case(of: rwrongn("rw-comp6"))[
       By inspecting #rwrongn("rw-comp6") we can see that $u dot n -t wrong$ if $hh(many(t)) in.not pch()$. This contradicts #tepin("t-comp2") as for a composite name to be well-typed we have $hh(many(t)) in pch()$. Therefore $P arrow.r.not wrong$.
    ]
  ]
]

