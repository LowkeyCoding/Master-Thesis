#import "../../../Packages/global.typ": *

#let rbtfn(x) = shown(rbutf, x)
#let repin(x) = shown(repi, x)
#let radmnn(x) = shown(radmn,x)
#let ts_e(x) = $#showf(sttrans_e, x) = #showt(sttrans_e, x)$
#let ts_l(x) = $#showf(sttrans_l, x) = #showt(sttrans_l, x)$

== Proof of Lemma 4.3 <app:proof_GarbageProc>

#proof(of: <lem:GarbageProc>)[
  We use $attach(tr:n,-s)$ to denote $n$ reductions of the form $-s$ then using induction on $n$.
  #case(of: $n = 0$)[
    In this case no reduction has occured and therefore $P' = P$ and we must show that $P adown(alpha)$ for any prefix.
    We show this by contradiction and therefore assume there exists an $alpha$ s.t $barb(P,alpha)$. From the assumption of $bim(P, null)$ we have that $(P, null) in R$ and by the condition (4) of @def:Wabb then it must hold that $null =a barb(,alpha)$. However, since there are no reductions from $null$ therefore $null -s #h(-1em)\/ #h(0.5em)$ and $null  adown(alpha)$.
  ]
  #case(of: $n > 0$)[
    From the induction hypothesis we have $P attach(tr:n-1,-s) P^(n-1)$ then $forall alpha. P^(n-1) adown(alpha)$ and $bim(P^(n-1), null)$. Then we we will show that $P^(n-1) -s P'$ then $forall alpha. P' adown(alpha)$ and $bim(P^', null)$. Since $bim(P^(n-1), null)$ we know that there exist and $R$ s.t $(P^(n-1), null) in R$ and $R$ is a @def:Wabb. Since $null -i#h(-1em)\/ #h(0.5em)$, then $P -i #h(-1em)\/ #h(0.5em)$ therefore $P^(n-1) -a P'$. Then because $(P^(n-1),null) in R$, then $(P', null) in R$, and therefore $bim(P',null)$ and $forall alpha. P adown(alpha)$
  ]
]
