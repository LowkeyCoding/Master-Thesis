#import "../../../Packages/global.typ": *

#let rbtfn(x) = shown(rbutf, x)
#let repin(x) = shown(repi, x)
#let radmnn(x) = shown(radmn,x)
#let ts_e(x) = $#showf(sttrans_e, x) = #showt(sttrans_e, x)$
#let ts_l(x) = $#showf(sttrans_l, x) = #showt(sttrans_l, x)$

== Proof of Lemma 4.4 <app:proof_GarbageCollect>

#proof(of: <lem:GarbageCollect>)[
  Let $R$ be a relation $R = {(C[P | Q], C[Q]) | P,Q in cal(P), C in cal(C), bim(P, null)}$. Then by @lem:GarbageProc if $bim(P, null)$ then $P adown(alpha)$ therefore since $bim(P, null)$ it holds that when $barb(P | Q, alpha)$ then $P adown(alpha)$ and $barb(Q, alpha)$.
  We then prove that $R$ is a @def:Wabb.
  #case(of: "(1) and (2)")[
    By @def:Wabb condition (1) and (2) if $C[P|Q] -s O$ then $C[Q] =s O'$ s.t $(O,O') in R$. By @lem:prgBehave $O$ is one of the following three cases.
    #case(of:$C "reduces alone"$)[
      Then $O = C'[P | Q]$. Here $C[Q]$ can follow by $C[Q] -s C'[Q]$.
    ]
    #case(of:$P | Q "reduces alone"$)[
      Then $O = C[R]$, where $R = P | Q -s R$. Since by @lem:GarbageProc we have $P adown(alpha)$, then either $P$ or $Q$ reduces alone.
      #case(of: $R = P' | Q$)[
        Then $P -s P'$, and because $bim(P, null)$, $s = circle.small$. Therefore $C[Q]$ can follow with no reductions as by  @lem:GarbageProc $bim(P', null)$ and $(C[P' | Q], C[Q]) in R$
      ]
      #case(of: $R = P | Q'$)[
        Then $Q -s Q'$, $C[Q] -s C[Q']$ and $(C[P | Q'],C[Q']) in R$
      ]
    ]
    #case(of:$P | Q "and" C "reduces"$)[
      Then $exists R$ s.t $R in C$ and $R | P | Q -s S' | P | Q'$ as by @lem:GarbageProc we have $P adown(alpha)$ and therefore $P$ can not communicate with $S$. Therefore we have that $S | Q -s S' | Q'$ and then $C[Q] -s C'[Q']$.
    ] 
  ]
  #case(of: "(3)")[
    By the selection of $R$ it holds.
  ]
  #case(of: "(4)")[
    If $barb(C[P | Q],alpha)$ then $barb(Q =a, alpha)$. By @lem:GarbageProc then $P adown(alpha)$, $barb(Q, alpha)$ and by @lem:prgBehave $O$ is one of the following cases.
    #case(of:$C "reduces alone"$)[
      Then $O = C'[P | Q]$. Here $C[Q]$ can follow by $C[Q] -s C'[Q]$.
    ]
    #case(of:$Q "reduces alone"$)[
      Then $O = C[Q']$ where $Q -s Q'$ and $C[P | Q] -s C[P | Q']$. 
    ]
    #case(of:$Q "and" C "reduces"$)[
      Follows the same argumentation as (1) and (2).
    ] 
  ]
]