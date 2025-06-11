#import "../../../Packages/global.typ": *

#let rbtfn(x) = shown(rbutf, x)
#let repin(x) = shown(repi, x)
#let radmnn(x) = shown(radmn,x)
#let ts_e(x) = $#showf(sttrans_e, x) = #showt(sttrans_e, x)$
#let ts_l(x) = $#showf(sttrans_l, x) = #showt(sttrans_l, x)$

== Proof of Lemma 4.6

#proof(of: <lem:teoo>)[
  By inspection of the translation in @ch:TransBtfTEpi we have that the constructs ${x,n,lambda x:tau .e, (e_1,dots,e_n), [e_1,dots,e_n]}$ only contain administrative transitions. Then by induction on $cal(D)(e)$ we get two cases: 
  #case(of: $cal(D)(e) = 0$)[
    Then $e in {n,x, lambda x: tau .e}$ and by @def:butfValues we have that $e in cal(V)$. Then as $e in cal(V)$ we have by @lem:tvoo that $tle(e,o) =a P$ and $barb(P,overline(o))$.
  ]
  #case(of: $cal(D) > 0$)[
    Then $e in {(e_1,dots,e_n), [e_1,dots,e_n]}$ and $cal(D)(e) = max_(i in {0,dots,n})(cal(D)(e_i))+1$ where $e_i in {x,n,lambda x:tau .e, (e_1,dots,e_n), [e_1,dots,e_n]}$. Then as $e_i$ does not contain constructs with important transitions then $e$ must contain fully evaluated expressions and therefore by @def:butfValues $e in cal(V)$ and therefore by @lem:tvoo that $tle(e,o) =a P$ and $barb(P,overline(o))$.
  ]
]