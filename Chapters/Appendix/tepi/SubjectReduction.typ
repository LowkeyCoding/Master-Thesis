#import "../../../Packages/global.typ": * 

#let repin(x) = shown(repi, x)
#let tepin(x) = shown(rtepi, x)

== Proof of Theorem 3.2 - subject reduction  <app:proof_subject>

#proof(of: "Proof of subject reduction")[
  We will prove subject reduction by induction in the rule for concluding $P -> P'$.

  #case(of: repin("r-com"))[
    By our assumption we know that $PEnv |- send(c, many(T)).P$ and $PEnv |- receive(c,many(x) : many(t)).Q$ by the application of #tepin("t-par"). By #repin("r-com") we have $send(c,many(T)).P|receive(c,many(x)).Q -t P | Q rn(many(x),many(T))$ and must show that $PEnv |- P | Q rn(many(x),many(T))$. 
    
    Then by #tepin("t-send") we have that $c: ch(many(t))$ and $many(T) : many(t)$, and by #tepin("t-recv") we have that $c : ch(many(t))$ and $DEnv, many(x) : many(t), CEnv |- Q$. 
    By using @lem:tepi_subst_p we have that $DEnv, many(x): many(t), CEnv |- Q rn(many(x),many(T))$, and by @lem:stronk_tepi_p we have $PEnv |- Q rn(many(x),many(T))$. We can therefore conclude $PEnv |- P | Q rn(many(x),many(T))$ by #tepin("t-par").
    
  ]
  #case(of: repin("r-broad"))[
    By our assumption we know that $PEnv |- broad(c, many(T)) . Q$, $PEnv |- receive(c,many(x_1) : many(t)).P_1$, ..., $PEnv |- receive(c,many(x_n) : many(t)).P_n$ given multiple applications of #tepin("t-par"). By #repin("r-broad") we have $broad(c,many(T)).Q |receive(c,many(x_1)).P_1|dots|receive(c,many(x_n)).P_n -b Q | P_1 rn(many(x_1),many(T)) | dots | P_n rn(x_n,many(T))$ and must show that $PEnv |- Q | P_1 rn(many(x_1),many(T)) | dots | P_n rn(x_n,many(T))$. 
    
    Then by #tepin("t-broad") we have that $c: ch(many(t))$ and $many(T) : many(t)$, and by #tepin("t-recv") we have that $c : ch(many(t))$ and $DEnv, many(x_i) : many(t), CEnv |- P_i$ for all $i in {1,...,n}$. By using @lem:tepi_subst_p we have that $DEnv, many(x_i): many(t), CEnv |- P_i rn(many(x_i),many(T))$ for all $i in {1,...,n}$, and by @lem:stronk_tepi_p we have $PEnv |- P_i rn(many(x_i), many(T))$ for all $i in {1,...,n}$. We can therefore conclude $PEnv |- Q | P_1 rn(many(x_1),many(T)) | ... | P_n rn(many(x_n),many(T))$ by multiple applications of #tepin("t-par").
  ]
  #case(of: repin("r-par"))[
    By our assumption we know that $PEnv |- P | Q$ and given application of #tepin("t-par") we know $PEnv |- P$ and $PEnv |- Q$. Given #shown(repi, "r-par") we know that $P | Q -t P' | Q$ and must show that $PEnv |- P' | Q$. By induction we get that $PEnv |- P -t P'$ and thereby also for $PEnv |- P'$. By #tepin("t-par") we then have $PEnv |- P' | Q$. 
  ]
  #case(of: repin("r-bpar"))[
    The proof is similar to #repin("r-par").
  ]
  #case(of: repin("r-res1"))[
    By our assumption we know that $PEnv |- (nu a : t) . P$ and by #tepin("t-res") we have $DEnv, a:t,CEnv |- P$, and given #shown(repi, "r-res1") we know that $(nu a:t).P -q (nu a:t).P'$. We must then show $PEnv |- (nu a: t). P'$. Then by induction and given #tepin("t-res") we have $DEnv, a:t, CEnv |- P'$.
  ]
  #case(of: repin("r-res2"))[
    The proof is similar to #repin("r-res1").
  ]
  #case(of: repin("r-then"))[
    By our assumption we know $PEnv |- [T_1 bow T_2]P\,Q$ by #tepin("t-if") and $[T_1 bow T_2]P\,Q -t P$ by #repin("r-then"). We must then show $PEnv |- P$. This follows immediately by #tepin("t-if") as $PEnv |- [T_1 bow T_2]P\,Q$ is only correct if $PEnv |- P$.
  ]
  #case(of: repin("r-else"))[
    By our assumption we know $PEnv |- [T_1 bow T_2]P\,Q$ by #tepin("t-if") and $[T_1 bow T_2]P\,Q -t Q$ by #repin("r-else"). We must then show $PEnv |- Q$. This follows immediately by #tepin("t-if") as $PEnv |- [T_1 bow T_2]P\,Q$ is only correct if $PEnv |- Q$.
  ]
  #case(of: repin("r-struct"))[
    By our assumption we know that $PEnv |- P$ and $P -q P'$, and by @lem:type_cong we have that $PEnv |- Q$. By induction we have that $PEnv |- Q'$ and by @lem:type_cong we get $PEnv |- P'$
  ]
]