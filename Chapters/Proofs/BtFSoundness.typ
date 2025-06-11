#import "../../Packages/global.typ": *
#let rubn(x) = shown(rbutf, x)
#let rbn(x) = shown(rbtf, x)

== Soundness of #btf
With the type system introduced, one of the properties of the type system we want is that of soundness. For this we give the following theorem.

#theorem("Soundness of " + $btf$)[
  Let $e$ be a #btf expression then
  1. (Preservation) if $Env |- e : tau$ and $e -> e\'$ then $Env |- e' : tau$
  2. (Progress) if $|- e: tau$ then $e = v in cV$ or $exists e'. e -> e'$
]<th:btf_sound>

The soundness theorem consists of two parts: preservation and progress. Preservation states that if we are well-typed and can take a transition step then the resulting expression is also well-typed. Progress states that either the expression is a value or there exists an $e'$ we can reach after taking a transition step.

=== #btf Lemmas
To help prove @th:btf_sound we need formulate the following lemmas.
@lem:CanForm is necessary for connecting values and types.
@lem:btf_weak states that we can add a new fresh variable to the type environment without conflicts.
@lem:btf_sub states that substitution of variables are type preserving. The full proof of all the lemmas can be found in @app:proof_btf_inversion to @app:proof_btf_sub.

#lemma("Inversion")[
  If $|- v: tau$ then
  1. if $tau = Int$ then $v$ is a constant.
  2. if $tau = tau_1 -> tau_2$ then $v$ is an abstraction.
  3. if $tau = [tau]$ then $v$ is an array of values.
  4. if $tau = (many(tau))$ then $v$ is a tuple of values.
]<lem:CanForm>


#lemma("Weakening")[
  If $Env|- e : tau$ and $x in.not "dom"(Env)$, then $Env, x: tau' |- e : tau$
]<lem:btf_weak>

#lemma("Preservation of types under substitution")[
  If $Env, x: tau |- e : tau' $ and $Env |- s : tau$, then $Env |- e{x |-> s} : tau'$
]<lem:btf_sub>

=== Proving Soundness

We have split the proof of @th:btf_sound into two parts; one for preservation and one for progress. As the whole proof is quite long we will in this section only showcase some of the cases for the proof. The full proof of preservation and progress can be found in @app:proof_pres and @app:proof_prog, respectively. 

==== Proof of Preservation 
//For the first part of proving @th:btf_sound we need to prove preservation. We will showcase the cases for #rbn("t-if") and #rbn("t-app")

We will prove preservation by induction on the derivation of $Env |- e : tau$ using case analysis on the last rule in the derivation.

#case(of: rbn("t-if"))[
    Then $e = ifte(e_1,e_2,e_3)$ and $e_1: Int$ and $e_2: tau$ and $e_3: tau$.  By assuming $e -> e'$ exists, we then derive the following applicable reduction rules: 
    #case(of: rubn("r-ift"))[
      then $e' = e_2$ and from the typing of $e_2$ we get $Env |- e' : tau$.
    ]
    #case(of: rubn("r-iff"))[
      then $e' = e_3$ and from the typing of $e_3$ we get $Env |- e' : tau$.
    ]
    #case(of: rubn("r-if"))[
      then we get $e' = ifte(e'_1,e_2,e_3)$, where $e_1 -> e'_1$. Using the inductive hypothesis we get that $Env |- e'_1 : Int$, therefore using #rbn("t-if") we get $Env |- e' : tau$.
    ]
  ]

#case(of: rbn("t-app"))[
    Then $e = e_1 e_2$, and $Env |- e_1 : tau_1 -> tau$ and $Env |- e_2 : tau_1$.  By assuming $e -> e'$ exists, and using case analysis we derive the following applicable reduction rules: 
    #case(of: $dots$)[
    ]
    #case(of: rubn("r-abs"))[
      Then $e_1 = lambda (x: tau_2).e_3$ and $e_2 = v$ and $e' = e_3{x |-> v}$. Because $Env |- e_1 : tau_1 -> tau$ and $e_1 = lambda (x: tau_2).e_3$ by inspection of the type rules it must hold that $tau_1 = tau_2$ giving us $Env |- lambda (x: tau_1).e_3: tau_1 -> tau $. Then by inspection the derivation must end with #rbn("t-abs") giving us $Env, (x : tau_1) e_3 : tau$. Then because $Env |- e_2 : tau_1$ and $e_2 = v$ it must hold that $Env |- v : tau_1$. Therefore, using the @lem:btf_sub we have that $Env |- e_3{x |-> v} : tau$.
    ]
     #case(of: $dots$)[
    ]
  ]

==== Proof of Progress
//For the second part of proving @th:btf_sound we need to prove progress. We will show some of the cases for the proof.

We will prove progress by induction on the typing derivation of $|- e: tau$ (the empty environment).
#case(of: rbn("t-if"))[
    We know from #rbn("t-if") that $e_1$ has type $Int$.
    By the inductive hypothesis we know that either $e_1 in cV$ or $exists e'_1 . e_1 -> e'_1$. This gives us two cases:
    - $e_1 in.not cV$
    - $e_1 in cV$
    #case(of: $e_1 in.not cV$)[
      In the case that $e_1 in.not cV$ then by our inductive hypothesis $e_1 -> e'_1$. We can then apply #rubn("r-if").
      We can see that given the premise we can take the step $ifte(e_1, e_2, e_3) -> ifte(e'_1, e_2, e_3)$ and therefore progress holds. 
    ]
    #case(of: $e_1 in cV$)[
      In the case that $e_1 in cV$ then it must be number (that is the only value of type $Int$ by proof of @lem:CanForm). In that case one of the two following rules applies: #rubn("r-ift") or #rubn("r-iff").

      First case we apply #rubn("r-ift") where given the premise $e$ can take the step $ifte(e_1, e_2, e_3) -> e_2$ and therefore progress holds. 

      Second case we apply #rubn("r-iff") where given the premise $e$ can take the step $ifte(e_1, e_2, e_3) -> e_3$ and therefore progress holds. 
    ]
  ]

#case(of: rbn("t-app") )[
    We know by #rbn("t-app") that $e_1$ has type $tau_1 -> tau_2$.
    By the induction hypothesis we know that $e_1 in cV$ or $exists e'_1 . e_1 -> e'_1$ and $e_2 in cV$ or $exists e'_2 . e_2 -> e'_2 $. That gives us four cases: 
      - $e_1, e_2 in.not cV$
      - $e_1, e_2 in cV$
      - $e_1 in cV$ and $e_2 in.not cV$
      - $e_2 in cV$ and $e_1 in.not cV$.
    #case(of: $e_1, e_2 in.not cV$)[
      In the case that $e_1$ and $e_2$ are not values then by our inductive hypothesis $e_1 -> e'_1$ and $e_2 -> e'_2$. If $e_1$ takes a step then #rubn("r-app1") applies. 
      From #rubn("r-app1") we have that given the premise we can take the step $e_1 e_2 -> e'_1 e_2$ and therefore progress holds. 
        
      if $e_2$ takes a step then #rubn("r-app2") applies.
      From #rubn("r-app2") we have that given the premise we can take the step $e_1 e_2 -> e_1 e'_2$ and therefore progress holds. 
    ]
    #case(of: $e_1 in.not cV$)[
      In the case that $e_1$ is not a value then by our inductive hypothesis it can take a step. Then the rule #rubn("r-app1") applies. 
      From #rubn("r-app1") we have that given the premise we can take the step $e_1 e_2 -> e'_1 e_2$ and therefore progress holds. 
      ]
    #case(of: $e_2 in.not cV$)[
      In the case that $e_2$ is not a value then by our inductive hypothesis it can take a step. Then the rule #rubn("r-app2") applies. 
      From #rubn("r-app2") we have that given the premise we can take the step $e_1 e_2 -> e_1 e'_2$ and therefore progress holds. 
    ]
    #case(of: $e_1, e_2 in cV$)[
      In the last case both $e_1$ and $e_2$ are values. As $e_1$ must be an arrow type (by our type rule) - then abstraction applies (as that is the only value that has type $tau_1 -> tau_2$ from proof of @lem:CanForm) and we can use #rubn("r-abs") to take a step.
    ]
  ]


