#import "../../../Packages/global.typ": *

#let rbtfn(x) = shown(rbutf, x)
#let repin(x) = shown(repi, x)
#let radmnn(x) = shown(radmn,x)
#let ts_e(x) = $#showf(sttrans_e, x) = #showt(sttrans_e, x)$
#let ts_l(x) = $#showf(sttrans_l, x) = #showt(sttrans_l, x)$

== Proof of Lemma 4.5 <app:proof_tvoo>
Before we can prove @lem:tvoo we need to know the depth of an expression $e$.
#definition("Depth of expression")[
  Let $cal(D)(e)$ denote the depth of $e$.
  $
    cal(D)(n) &= 0 \
    cal(D)(lambda x.e) &= 0 \
    cal(D)((e_1,dots,e_n)) &= max_(i in {0,dots,n})(cal(D)(e_i)) + 1 \
    cal(D)([e_1,dots,e_n]) &= max_(i in {1,dots,n})(cal(D)(e_i)) + 1 \
    cal(D)(ifte(e_1,e_2,e_3)) &= max_(i in {1,dots,3})(cal(D)(e_i)) + 1  \
    cal(D)(e_1 bin e_2) &= max_(i in {1,dots,2})(cal(D)(e_i)) + 1 \
    cal(D)(size e_1) &= cal(D)(e_1) + 1\
    cal(D)(iota e_1) &= cal(D)(e_1) + 1\
    cal(D)(map e_1) &= cal(D)(e_1) + 1\
  $
]<def:depth>

#proof(of: <lem:tvoo>)[
  We prove this on induction on the depth $cal(D)(e)$ where $e in cal(V)$. 
  As per  #radmnn("r-admn") any $-t$ is an administrative reduction.
  #case(of: $cal(D)(e) = 0$)[
    From @def:depth, we get that $e$ must be either a number or abstraction.
    #case(of: $n$)[
      From @h3:ts_expr #ts_e("num") can immediately send $n$ on $o$ and therefore $barb(tl(n)_o, overline(o))$
    ]
    #case(of: $x$)[
      From @h3:ts_expr #ts_e("var") can immediately send $x$ on $o$ and therefore $barb(tl(x)_o, overline(o))$
    ]
    #case(of: $lambda x.e$)[
      From @h3:ts_expr #ts_e("lambda") can send the handle $h$ on $o$ by going under restriction and the parallel composition therefore $barb(#showt(sttrans_e, "lambda"), overline(o))$
    ]
  ]
  #case(of: $cal(D)(e) > 0$)[
    Since $cal(D)(e) > 0$ then $e$ must be either a tuple or array. From @def:depth we get that the depth for tuple and array is $cal(D)(e) = max_(i in {0,dots,n})(cal(D)(e_i)) + 1$. Since $e$ is a value on the form $(e_1,dots e_n)$ or $[e_1,dots,e_n]$, then each $e_i$ we have that for all $e_1,dots,e_n$ $forall i in {1,dots,n}$ where $cal(D)(e_i) < cal(D)(e)$. Then by the induction hypothesis we have that $tl(e_i)o_i =a P_i$ where $barb(P_i, overline(o)_i)$
    #case(of: $(e_1,dots e_n)$)[
       From @h3:ts_expr we get the translation for array $#showf(sttrans_l, "array")$ is 
       $ #showt(sttrans_l, "array",strip:false) $ Then by repeated application of #repin("r-res1") followed by #repin("r-com") therefore $q = tau$ as communication reduction is a $tau$ reduction. This then results in the following process $P = (product_(i=1)^(n) Pcell(h, i-1, v_i) | send(h dot len, n) | send(o, h))$ and as it was reached using only administrative reductions we have that $#showf(sttrans_l, "array") =a P$. Then because $P$ can send the handle $h$ on $o$ by going under the parallel composition we have that $barb(P, overline(o))$
    ]
    #case(of: $[e_1,dots e_n]$)[
      From @h3:ts_expr we get the translation for tuple $#showf(sttrans_l, "tuple")$ is 
       $ #showt(sttrans_l, "tuple",strip:false) $ Then by repeated application of #repin("r-res1") followed by #repin("r-com") therefore $q = tau$ as communication reduction is a $tau$ reduction. This then results in the following process $P = nu h . (repl send(h dot tup,v_1\, dots\, v_n) | send(o,h) )$ and as it was reached using only administrative reductions we have that $#showf(sttrans_l, "tuple") =a P$. Then by going under restriction, and using structural congruence to swap $repl send(h dot tup,v_1\, dots\, v_n)$ and $send(o,h)$ in the parallel composition and then going under it, we have that $P$ can send $h$ on $o$. Therefore we have that $barb(P, overline(o))$.
    ]
  ]
]