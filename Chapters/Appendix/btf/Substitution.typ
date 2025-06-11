#import "../../../Packages/global.typ": *

#let rubn(x) = shown(rbutf, x)
#let rbn(x) = shown(rbtf, x)

== Proof of Lemma 3.3 <app:proof_btf_sub>

#proof(of: <lem:btf_sub>)[
  By induction on derivations of $Env, x: tau |- e : tau'$.
  #case(of: rbn("t-int"))[
    Then $e = n$ and $tau' = Int$. Then from $n{x |-> s} :tau'$ the preservation of under substitution is immediately obvious. 
  ]
  #case(of: rbn("t-var"))[
    Then $e = y$ and $y : tau' in Env,(x:tau)$. For #rbn("t-var") there are two sub cases depending on whether $e$ is $x$ or another variable . 
    #case(of: $y = x$)[
      Then we get $y{ x |-> s} = s$ from @def:sub-butf. From the inductive hypothesis we then get that $Env |- s : tau$.
    ]
    #case(of: $y eq.not x$)[
      Then we get $y{ x |-> s} = y$ from @def:sub-butf, and as the expression remains unchanged the preservation of types is immediately obvious.
    ]
  ]
  #case(of: rbn("t-bin"))[
    Then $e = e_1 bin e_2$ and $Env (x : tau) |- e_1 : Int$ and $Env (x : tau) |- e_2 : Int$. Using the inductive hypothesis we have that $Env |- e_1{x |-> s} : Int$ and $Env |- e_2{x |-> s} : Int$. Then using #rbn("t-bin") we get $Env |- e_1{x |-> s} bin e_2{x |-> s} : Int$; therefore the type is preserved under substitution.
  ]
  #case(of: rbn("t-if"))[
    Then $e = ifte(e_1,e_2,e_3)$ and $Env, (x: tau) |- e_1 : Int$ and $Env, (x: tau) |- e_2 : tau'$ and and $Env, (x: tau) |- e_3 : tau'$. Using the inductive hypothesis we have that $Env |- e_1{x |-> s} : Int$ and $Env |- e_2{x |-> s} : tau'$ and $Env |- e_3{x |-> s} : tau'$. Then using #rbn("t-if") we get $Env |- ifte(e_1{x |-> s},e_2{x |-> s},e_3{x |-> s}) : tau'$; therefore the type is preserved under substitution.
  ]
  #case(of: rbn("t-array"))[
    Then $e = [e_1, dots, e_n]$ and $forall i in {1 dots n}. Env (x: tau) |- e_i : tau_1$ and $tau' = [tau_1]$. Using the inductive hypothesis we have that $forall i in {1 dots n}. Env |- e_i{x |-> s} : tau_1$. Then using #rbn("t-array") we get $Env |- [e_1{x |-> s}, dots, e_n {x |-> s}]: [tau_1]$; therefore the type is preserved under substitution.
  ]
  #case(of: rbn("t-tuple"))[
    Then $e = (e_1, dots, e_n)$ and $forall i in {1 dots n}. Env (x: tau) |- e_i : tau_i$ and $tau' = (tau_1, dots, tau_n)$. Using the inductive hypothesis we have that $forall i in {1 dots n}. Env |- e_i{x |-> s} : tau_1i$. Then using #rbn("t-array") we get $Env |- (e_1 {x |-> s}, dots, e_n {x |-> s}): (tau_1, dots, tau_i)$; therefore the type is preserved under substitution.
  ]
  #case(of: rbn("t-index"))[
    Then $e = e_1[e_2]$ and $Env (x: tau) |- e_1 : [tau']$ and  $Env (x: tau) |- e_2 : Int$. Using the inductive hypothesis we have that $Env |- e_1{x |-> s} : [tau']$ and $Env |- e_2{x |-> s}: Int$. The using #rbn("t-index") we get $Env |- e_1{x |-> s}[e_2{x |-> s}] : tau'$; therefore the type is preserved under substitution.
  ]
  #case(of: rbn("t-abs"))[
    Then $e = lambda (y: tau_1).e_1$, $tau' = tau_1 -> tau_2$ and $Env,x : tau,y :tau_1 |- e_1 : tau_2$ since $Env |- s: tau$ by @lem:btf_weak we have $Env, y: tau_1 |- s : tau$, then using the inductive hypothesis we have $Env, y: tau_1 |- e_1{x |-> s}: tau_2$. Therefore from #rbn("t-abs") we get $Env |- lambda (y: tau_1).e_1{x |-> s} :tau_1 -> tau_2$. As we can assume $y != x$ from @lem:btf_weak and from @def:sub-butf we have that $e{x|->s} = lambda (y: tau_1).e_1{x |-> s}$, therefore the type is preserved under substitution.
   ]
  #case(of: rbn("t-app"))[
    Then $e = e_1 e_2$ and $Env,x:tau' |- e_1 : tau_1 -> tau$ and $Env,x:tau' |- e_2 : tau_1$. Then using the inductive hypothesis we  have $Env |- e_1 {x |-> s} :tau_1 -> tau$ and $Env |- e_2 {x |-> s} : tau_1$. Therefore using #rbn("t-app") we get $Env |- e_1{x |-> s} e_2{x |-> s} : tau$. Because we have $e{x |-> s} = e_1{x |-> s} e_2{x |-> s}$ from @def:sub-butf, therefore the type is preserved under substitution.
  ]

]