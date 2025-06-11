#import "../../../Packages/global.typ": *

#let rubn(x) = shown(rbutf, x)
#let rbn(x) = shown(rbtf, x)

== Proof of Lemma 3.2 <app:proof_btf_weak>

#proof(of: <lem:btf_weak>)[
  By induction on the depth of the derivation of $Env |- e : tau$ 
  #case(of: rbn("t-int"))[
    Then $e = n$ and $tau = Int$. Therefore by #rbn("t-int") we have $Env,x:tau'|- n : Int$.
  ]
  #case(of: rbn("t-var"))[
    Then $e = y$ and $y : tau in "dom"(Env)$. Since $x in.not "dom"(Env)$, we have that $x eq.not y$. Therefore we get $y in "dom"(Env,x:tau')$ and from #rbn("t-var") we have $Env,x:tau' |- y : tau$.
  ]
  #case(of: rbn("t-bin"))[
    Then $e = e_1 bin e_2$ and $Env |- e_1 : Int$ and $Env |- e_2 : Int$ and $tau = Int$. Therefore using the inductive hypothesis we have $Env,x : tau' |- e_1 : Int$ and $Env,x : tau' |- e_2 : Int$ and from #rbn("t-bin") we get $Env,x : tau' |-e_1 bin e_2 : tau$.
  ]
  #case(of: rbn("t-if"))[
    Then $e = ifte(e_1,e_2,e_3)$ and $Env |- e_1 : Int$ and $Env |- e_2 : tau$ and $Env |- e_3 : tau$. From the induction hypothesis we have that $Env,x:tau' |- e_1 : Int$ and $Env,x:tau' |- e_2 : tau$ and $Env,x:tau' |- e_2 : tau$. Therefore, from #rbn("t-if") we have $Env,x:tau' |- ifte(e_1,e_2,e_3) : tau$.
  ]
  #case(of: rbn("t-array"))[
    Then $e = [e_1, dots, e_n]$ and $forall i in {1,dots,n}. Env |- e_i = tau_1$ and $tau = [tau_1]$. From the inductive hypothesis we have that $forall i in {1,dots,n}. Env,x:tau' |- e_i : tau_1$ and from #rbn("t-array") we get $Env,x:tau'|- [e_1,dots,e_n] : [tau_1]$  
  ]
  #case(of: rbn("t-tuple"))[
    Then $e = (e_1, dots, e_n)$ and $forall i in {1,dots,n}. Env |- e_i = tau_i$ and $tau = (tau_1,dots,tau_n)$. From the inductive hypothesis we have that $forall i in {1,dots,n}. Env,x:tau' |- e_i : tau_i$ and from #rbn("t-tuple") we get $Env,x:tau'|- (e_1,dots,e_n) : (tau_1,dots,tau_n)$
  ]
  #case(of: rbn("t-index"))[
    Then $e = e_1[e_2]$ and $Env |- e_1 : [tau]$ and $Env |- e_2 : Int$. Therefore using the inductive hypothesis we have $Env,x : tau' |- e_1 : [tau]$ and $Env,x : tau' |- e_2 : Int$ and from #rbn("t-index") we get $Env,x : tau' |- e_1[e_2] : tau$.
  ]
  #case(of: rbn("t-abs"))[
    Then $e = lambda y : tau_1.e_1$ and $tau = tau_1 -> tau_2$ and $Env, y: tau_1 |- e_1 : tau_2$ we assume $x eq.not y$ renaming $y$ if needed. Because $x in.not "dom"(Env)$ it must hold that $x in.not "dom"(Env, y: tau_1)$. Therefore using the inductive hypothesis we get $Env, y: tau_1,x : tau' |- e_1 : tau_2$ and from #rbn("t-abs") we get $Env,x : tau' |- lambda y : tau_1.e_1 : tau_1 -> tau_2$.
  ]
  #case(of: rbn("t-app"))[
    Then $e = e_1 e_2$ and $Env |- e_1 : tau_1 -> tau$ and $Env |- e_2 : tau_1$. Therefore using the inductive hypothesis we have $Env,x : tau' |- e_1 : tau_1 -> tau$ and $Env,x : tau' |- e_2 : tau_1$ and from #rbn("t-app") we get $Env,x : tau' |- e_1 e_2 : tau$.
  ]
]