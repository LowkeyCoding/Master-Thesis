#import "../../../Packages/global.typ": *
#let rscn(x) = shown(rstructcong, x)
#let tepin(x) = shown(rtepi, x)

#import "../../../Figures/Epi.typ": *

== Proof of Lemma 3.8 <app:proof_type_cong>


#proof(of: <lem:type_cong>)[
  We prove @lem:type_cong by induction in the structural congruence rules. 

  #case(of: rscn("screname"))[
    Trivial as by $alpha$-conversion we only change bound names and in $PEnv$ we only find free names, variables and numbers.
  ]
  #case(of: rscn("scparn"))[
    $underbracket(P, "1") == underbracket(P | null, "2") $
    #case(of: "1" )[
      By our inductive hypothesis we have that $PEnv |- P$. By #tepin("t-par") and #tepin("t-nil") we have $PEnv |- P | null$.  
    ]
    #case(of: "2" )[
      By our inductive hypothesis we have that $PEnv |- P | null$. Then by #tepin("t-par") we have $PEnv |- P$.
      
    ]
  ]
  #case(of: rscn("scpara"))[
    $underbracket(P | (Q | R), "1") == underbracket((P | Q) | R, "2") $
    #case(of: "1" )[
      By our inductive hypothesis we have that $PEnv |- P | (Q | R)$. Then by two applications of #tepin("t-par") we have $PEnv |- P$, $PEnv |- Q$ and $PEnv |- R$. Then we have $PEnv |- (P | Q) | R$ by two applications of #tepin("t-par").
    ]
    #case(of: "2" )[
      Similar to the first case.
    ]
  ]
  // HERE
  #case(of: rscn("scparb"))[
    $underbracket(P | Q, "1") == underbracket(Q | P, "2") $
    #case(of: "1" )[
      By our inductive hypothesis we have that $PEnv |- P | Q$. By #tepin("t-par") we have $PEnv |- P$ and $PEnv |- Q$. Then we have $PEnv |- Q | P$ by #tepin("t-par").
    ]
    #case(of: "2" )[
      Similar to the first case.
    ]
  ]
  #case(of: rscn("screpli"))[
    $underbracket(! P, "1") == underbracket(P | ! P, "2") $
    #case(of: "1" )[
      By our inductive hypothesis we have that $PEnv |- !P$. By #tepin("t-rep") we that $PEnv |- P$. Using #tepin("t-par") we have $PEnv |- P | ! P$.
      
    ]
    #case(of: "2" )[
      By our inductive hypothesis we have that $PEnv |- (P | ! P$. By #tepin("t-rep") we that $PEnv |- P$.
      
    ]
  ]
  #case(of: rscn("scnewn"))[
    $underbracket((nu a : t). null, "1") == underbracket(null, "2") $
    #case(of: "1" )[
      By our inductive hypothesis we have that $PEnv |- (nu a : t) . null$. By #tepin("t-res") we have that $DEnv, a : t, CEnv |- null$ for some $t$. We can then prove $PEnv |- 0$ using @lem:stronk_tepi_p  as it states that we can remove names from the #null process and still be well-typed. 
    ]
    #case(of: "2" )[
      By our inductive hypothesis we have that $PEnv |- null$. Using @lem:weak_tepi_p we can show that $DEnv, a : t, CEnv |- null$ and using #tepin("t-res") show that $PEnv |- (nu a : t) . null$ is still well-typed.
    ]
  ]
  #case(of: rscn("scnewa"))[
    $underbracket((nu a : t_1) . (nu b : t_2) . P, "1") == underbracket((nu b : t_2) . (nu a : t_1). P, "2") $
    #case(of: "1" )[
      By our inductive hypothesis we have that $PEnv |- nu a . nu b . P$. By applying #tepin("t-res") twice and we get $DEnv,a : tau_1,b : tau_2, CEnv tack P$ and $DEnv,b : tau_2,a : tau_1, CEnv tack P$ as the order is irrelevant $(nu a : t_1) . (nu b : t_2) . P$ is still well-typed. 
    ]
    #case(of: "2" )[
      Similar to the first case.
    ]
  ]
  #case(of: rscn("scnewb"))[
    $underbracket(P | (nu a : t) . Q, "1") == underbracket((nu a : t). (P | Q), "2") $
    #case(of: "1" )[
      By our inductive hypothesis we have that $PEnv |- P | nu a.Q$ and by #tepin("t-par") we have $PEnv |- P$ and $PEnv |- (nu a: t).Q$. The premise $PEnv |- (nu a: t).Q$ must be concluded with #tepin("t-res") giving us $DEnv,a:t, CEnv |- Q$. Then from the premise of #rscn("scnewb") we have $a in.not "fv"(P) union "fn"(P)$. Then using @lem:weak_tepi_p we get that $DEnv, a : t, CEnv |- P$ when $a in.not "dom"(DEnv)$. Therefore, if $a in.not "dom"(DEnv)$ it must hold that $DEnv, a : t, CEnv |- P$.
      
    ]
    #case(of: "2" )[
      By our inductive hypothesis we have that $(nu a : t). (P | Q)$. By @lem:stronk_tepi_p we have $PEnv |- P$ from $DEnv, a : t, CEnv |- P$. We can then apply #tepin("t-res") on Q and #tepin("t-par").
      
    ]
  ]
]