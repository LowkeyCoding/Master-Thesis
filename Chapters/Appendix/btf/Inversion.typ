#import "../../../Packages/global.typ": *

#let rubn(x) = shown(rbutf, x)
#let rbn(x) = shown(rbtf, x)

== Proof of Lemma 3.1 <app:proof_btf_inversion>

#proof(of: <lem:CanForm>)[
  We prove @lem:CanForm by inspection of the type rules.

  #case(of: $tau = Int$)[
    In the case that $tau = Int$ the only rule that gives a value this type is #rbn("t-int")
  ]
  #case(of: $tau = tau_1 -> tau_2$)[
    In the case that $tau_1 -> tau_2$ the only rule that gives a value this type is #rbn("t-abs")
  ]
  #case(of: $tau = [tau]$)[
    In the case that $tau = [tau]$ the only rule that gives a value this type is #rbn("t-array")
  ]
  #case(of: $tau = (many(tau))$)[
    In the case that $tau = (many(tau))$ the only rule that gives a value this type is #rbn("t-tuple")
  ]
]