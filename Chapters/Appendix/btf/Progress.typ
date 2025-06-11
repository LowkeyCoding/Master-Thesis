#import "../../../Packages/global.typ": *

#let rubn(x) = shown(rbutf, x)
#let rbn(x) = shown(rbtf, x)

== Proof of Theorem 3.1 - progress <app:proof_prog>

#proof(of: "progress")[
  We will prove progress by induction on the typing derivation of $|- e: tau$ (the empty environment). We will go over each type rule and show that progress holds: either $e$ is a value or it can take a step $e -> e'$. //Values are defined in @def:butfValues, and just to remind, are the following: constants and function symbols, arrays, tuples, and abstractions. 
  
  #case(of: rbn("t-int") )[
    Trivial as $n$ is a value and therefore progress holds.
    ]

  #case(of: rbn("t-var") )[
     We cannot type #rbn("t-var") under the empty environment. We would have that $x: tau$ under $Env$ but that contradicts our inductive hypothesis.
  ]

  #case(of: rbn("t-abs") )[
    The case of #rbn("t-abs") is trivial as abstraction is a value and therefore progress holds.
  ]

  #case(of: rbn("t-app") )[
    We know by #rbn("t-app") that $e_1$ has type $tau_1 -> tau_2$.
    By the induction hypothesis we know that $e_1 in cV$ or $exists e'_1 . e_1 -> e'_1$ and $e_2 in cV$ or $exists e'_2 . e_2 -> e'_2 $. That gives us four cases: 
      /*- $e_1, e_2 in.not cV$
      - $e_1, e_2 in cV$
      - $e_1 in cV$ and $e_2 in.not cV$
      - $e_2 in cV$ and $e_1 in.not cV$.*/
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

  #case(of: rbn("t-bin") )[
    We know from #rbn("t-bin") that $e_1$ and $e_2$ has type $Int$.
    By the induction hypothesis we know that $e_1 in cV$ or $exists e'_1 . e_1 -> e'_1$ and $e_2 in cV$ or $exists e'_2 . e_2 -> e'_2$. This gives us the following cases:
    // - $e_1, e_2 in.not cV$
    // - $e_1 in cV$ and $e_2 in.not cV$ (and the symmetric case)
    // - $e_1, e_2 in cV$
    #case(of: $e_1, e_2 in.not cV$)[
      In the case that $e_1, e_2 in.not cV$ the by our inductive hypothesis we know that $e_1 -> e'_1$ and $e_2 -> e'_2$. If $e_1$ take a step then #rubn("r-bin1") applies.
      From #rubn("r-bin1") we have that given the premise we can take the step $e_1 bin e_2 -> e'_1 bin e_2$ and therefore progress applies.

      If $e_2$ take a step then #rubn("r-bin2") applies.
      From #rubn("r-bin2") we have that given the premise we can take the step $e_1 bin e_2 -> e_1 bin e'_2$ and therefore progress applies.
    ]
    #case(of: $e_1 in.not cV$)[
      In the case that $e_1 in.not cV$ then by our inductive hypothesis $e_1$ can take a step and then #rubn("r-bin1") applies.
      From #rubn("r-bin1") we have that given the premise we can take the step $e_1 bin e_2 -> e'_1 bin e_2$ and therefore progress applies.
    ]
    #case(of: $e_2 in.not cV$)[
      In the case that $e_2 in.not cV$ then by our inductive hypothesis $e_2$ can take a step and then #rubn("r-bin2") applies.
      From #rubn("r-bin2") we have that given the premise we can take the step $e_1 bin e_2 -> e_1 bin e'_2$ and therefore progress applies.
    ]
    #case(of: $e_1,e_2 in cV$)[
      In the last case both $e_1$ and $e_2$ are values. Both values must be numbers (that is the only value of type $Int$ by proof of @lem:CanForm). In that case #rubn("r-bin") applies and given the premise $e$ can take a step and therefore progress applies.
    ]
  ]


  #case(of: rbn("t-if"))[
    We know from #rbn("t-if") that $e_1$ has type $Int$.
    By the inductive hypothesis we know that either $e_1 in cV$ or $exists e'_1 . e_1 -> e'_1$. This gives us two cases:
    // - $e_1 in.not cV$
    // - $e_1 in cV$
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


  #case(of: rbn("t-array") )[
    In the case of #rbn("t-array") we have $n$ number of expressions. Then by our inductive hypothesis, for $i in {1, ..., n}$, we know that $e_i in cV$ or $exists e'_i . e_i -> e'_i$. We will take a look at two cases:
    // - $exists i. e_i in.not cV$
    // - $forall i. e_i in cV$
    #case(of: $exists i. e_i in.not cV$)[
      In the case that $exists i. e_i in.not cV$ we know that from our inductive hypothesis $e_i -> e'_i$. In that case we can apply the rule #rubn("r-array").
      from #rubn("r-array") we have that given the premise we take the step $[e_1, dots, e_i, dots, e_n] -> [e_1, dots, e'_i, dots e_n]$ and therefore progress holds.
    ]
    #case(of: $forall i. e_i in cV$)[
      In the case that $forall i. e_i in cV$ then all sub-expressions are values. Then progress holds as arrays where all sub-expressions are values is in #cV
    ]
  ]


  #case(of: rbn("t-tuple") )[
    The case of #rbn("t-tuple") is similar to #rbn("t-array") as we have $n$ number of expressions. Then by our inductive hypothesis, for $i in {1, ..., n}$, we know that $e_i in cV$ or $exists e'_i . e_i -> e'_i$. We will take a look at two cases:
      // - $exists i. e_i in.not cV$
      // - $forall i. e_i in cV$
      #case(of: $exists i. e_i in.not cV$)[
        In the case that $exists i. e_i in.not cV$ then by our inductive hypothesis there must exist an $e'_i$ such that $e_i -> e'_i$. We can then apply the rule #rubn("r-tuple").
        From #rubn("r-tuple") we have that if the premise holds we can take the step $(e_1, dots, e_i, dots, e_n) -> (e_1, dots, e'_i, dots e_n)$ and therefore progress holds. 
      ]
      #case(of: $forall i. e_i in cV$)[
        In the case that $forall i. e_i in cV$ then all sub expressions are values. Then progress holds as tuples where all sub-expressions are values is in #cV.
      ]
  ]

  #case(of: rbn("t-index") )[
    We know from #rbn("t-index") that $e_1$ has type $[tau]$ and $e_2$ has type $Int$.
    By our inductive hypothesis we know that $e_1 in cV$ or $exists e'_1 . e_1 -> e'_1$ and $e_2 in cV$ or $exists e'_2 . e_2 -> e'_2$. That gives us four cases: 
        // - $e_1, e_2 in.not cV$
        // - $e_1 in cV$ and $e_2 in.not cV$
        // - $e_2 in cV$ and $e_1 in.not cV$.
        // - $e_1, e_2 in cV$
  #case(of: $e_1, e_2 in.not cV$)[
        In the case that $e_1, e_2 in.not cV$ then by our inductive hypothesis we know that $e_1$ and $e_2$ can take a step. If $e_1$ takes a step then #rubn("r-index1") applies.
        From #rubn("r-index1") we have that given the premise we can take the step $e_1 [e_2] -> e'_1 [e_2]$ and therefore progress holds.

        If $e_2$ take a step then #rubn("r-index2") applies.
        From #rubn("r-index2") we have that given the premise we can take the step $e_1 [e_2] -> e_1 [e'_2]$ and therefore progress holds.
      ]
      #case(of: $e_1 in.not cV$)[
        In the case that $e_1 in.not cV$ then by our inductive hypothesis $e_1$ can take a step and then #rubn("r-index1") applies.
        From #rubn("r-index1") we have that given the premise we can take the step $e_1 [e_2] -> e'_1 [e_2]$ and therefore progress holds.
      ]
      #case(of: $e_2 in.not cV$)[
        In the case that $e_2 in.not cV$ then by our inductive hypothesis $e_2$ can take a step and then #rubn("r-index2") applies.
        From #rubn("r-index2") we have that given the premise we can take the step $e_1 [e_2] -> e_1 [e'_2]$ and therefore progress holds.
      ]
      #case(of: $e_1,e_2 in cV$)[
        In the last case both $e_1$ and $e_2$ are values. $e_1$ must be an array (that is the only value of type $[tau]$ by proof of @lem:CanForm) and $e_2$ must be a number (that is the only value of type $Int$ by proof of @lem:CanForm). In that case #rubn("r-index") applies. 
        We can see that given the premise then $e$ can take a step and therefore progress holds.
      ]
  ]
      
]

  /*
  #case(of: rbn("t-if") )[
    For #rbn("t-if") we have the following type rule: 
    
    #showr(rbtf, "t-if")
    
    By our inductive hypothesis we know that $e_1 in cV$ or $exists e'_1 . e_1 -> e'_1$. 
    
    The two expressions $e_2$ and $e_3$ can be independently evaluated after a step with either #rubn("r-ift") or #rubn("r-iff"). This step is only depending on $e_1$ and as such we will only look at the cases:
      - $e_1 in.not cV$
      - $e_1 in cV$
    #case(of: $e_1 in.not cV$)[
      In the cases no expressions are values then by our inductive hypothesis the expressions must take a step.
      In the case of $e_1$ we can apply one of the following rules: #rubn("r-ift"), #rubn("r-iff"), #rubn("r-bin"), #rubn("r-app1"), #rubn("r-app2") or #rubn("r-abs").

      Let us start by looking at rule #rubn("r-ift").
      $ showr(rbutf, "r-ift") $
      We can see from #rubn("r-ift") that given the premise then we can take the step $ifte(e_1, e_2, e_3) -> e_2$ and therefore progress holds. 

      If we look at rule #rubn("r-iff").
      $ showr(rbutf, "r-iff") $
      We can see that given the premise we can take the step $ifte(e_1, e_2, e_3) -> e_3$ and therefore progress holds. 


      If we look at rule #rubn("r-bin").
      $ showr(rbutf, "r-bin") $
      From #rubn("r-bin") we can see that given the premise holds we can take the step $e_1 bin e_2 -> v_3$ and therefore progress holds.

      If we look at rule #rubn("r-app1").
      $ showr(rbutf, "r-app1") $
      From #rubn("r-app1") we have that given the premise we can take the step $e_1 e_2 -> e'_1 e_2$ and therefore progress holds.

      If we look at rule #rubn("r-app2").
      $ showr(rbutf, "r-app2") $
      From #rubn("r-app2") we have that given the premise we can take the step $e_1 e_2 -> e_1 e'_2$ and therefore progress holds.

      If we look at rule #rubn("r-abs").
      $ showr(rbutf, "r-abs") $
      From #rubn("r-abs") rule we can see that we can take the step $(lambda x . e) v -> e{x |-> v}$ and therefore progress holds.

      
    ]
    #case(of: $e_1 in cV$)[
      In the case $e_1 in cV$ it must be evaluated to a number and $n in cV$. From there on two rules applies depending on the value of $e_1$: #rubn("r-ift") or #rubn("r-iff"). 
    ]

    #case(of: $e_2 in cV$)[
      In the case of $e_2 in cV$ then by our inductive hypothesis $e_1$ and $e_3$ must take a step. In the case of $e_1$ one of the following rules applies: #rubn("r-ift"), #rubn("r-iff"), #rubn("r-bin"), #rubn("r-app1"), #rubn("r-app2") or #rubn("r-abs"). We can then take a step like shown in case 1. In the case of $e_2$ then #rubn("r-ift") or #rubn("r-iff") applies.
        
      The case of $e_3 in cV$ is symmetrical to this.
    ]
    #case(of: $e_1,e_2 in cV$)[
      In the case of $e_1,e_2 in cV$ then by our inductive hypothesis $e_3$ must take a step and then #rubn("r-ift") or #rubn("r-iff") applies

      The case of $e_1,e_3 in cV$ is symmetrical to this.
    ]
    #case(of: $e_2,e_3 in cV$)[
      In the case of $e_2,e_3 in cV$ then by our inductive hypothesis $e_1$ must take a step and then one of following rules applies:#rubn("r-ift"), #rubn("r-iff"), #rubn("r-bin"), #rubn("r-app1"), #rubn("r-app2") or #rubn("r-abs").
    ]
    #case(of: $e_1,e_2, e_3 in cV$)[
        
    ]
  ]
*/