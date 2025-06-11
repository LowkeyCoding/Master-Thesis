#import "../../../Packages/global.typ": *
#let rubn(x) = shown(rbutf, x)
#let rbn(x) = shown(rbtf, x)
//To prove type preservation we have to introduce two lemmas @lm:weak and @lm:pts. We introduce @lm:weak to show that we can introduce an $x$ and still be able to type an expression that does not contain $x$. construct in @lm:pts where $x$ is not in the context. We introduce @lm:pts to ensure that types are preserved under substitution we use this to ensure the type is preserved for $rubn("r-abs")$ and $rubn("r-map")$ constructs.

== Proof of Theorem 3.1 - preservation <app:proof_pres>

#proof(of: "preservation")[
  Induction on the derivation of $Env |- e : tau$ using case analysis on the last rule in the derivation.
  #case(of: rbn("t-int"))[
    Then $e = n$, and by inspection of the reduction rules there exists no $e'$ such that $n -> e'$ making the preservation immediately obvious.
  ]
  #case(of: rbn("t-var"))[
    Then $e = x$, and by inspection of the reduction rules there exists no $e'$ such that $x -> e'$ making the preservation immediately obvious.
  ]
  #case(of: rbn("t-bin"))[
    Then $e = e_1 bin e_2$ and $tau = Int$ and $Env |- bin : Int -> Int -> Int$ and $Env |- e_1 : Int$ and $Env |- e_2 : Int$. By assuming $e -> e'$ exists, we derive the following reduction rules:
    #case(of: rubn("r-bin1"))[
      then $e' = e'_1 bin e_2$, where $e_1 -> e'_1$. Using the induction hypothesis we get that $Env |- e'_1 : Int$ therefore, using #rbn("t-bin") we get that $Env |- e' : tau$.
    ]
    #case(of: rubn("r-bin2"))[
      then $e' = e_1 bin e'_2$, where $e_2 -> e'_2$. Using the induction hypothesis we get that $Env |- e'_2 : Int$ therefore, using #rbn("t-bin") we get that $Env |- e' : tau$.
    ]
    #case(of: rubn("r-bin"))[
      then $e' = v_3$ and from the typing of $bin$ we get that $Env |- e' : tau$.
    ]
  ]
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
  #case(of: rbn("t-array"))[
    Then $e = [e_1,dots,e_n]$ and $forall i in {1,dots,n}. Env |- e_i : tau_1$ and $tau = [tau_1]$. By assuming $e -> e'$ exists, we then derive that #rubn("r-array") is the only applicable reduction rule. Therefore $e' = [e_1,dots,e'_i,dots,e_n]$. Using the inductive hypothesis we get that $Env |- e'_1 : tau_1$, using #rbn("t-array") we get $Env |- e' : tau$.
  ]
  #case(of: rbn("t-tuple"))[
    Then $e = (e_1,dots,e_n)$ and $forall i in {1,dots,n}. Env |- e_i : tau_i$ and $tau = (t_1,dots,t_n)$. By assuming $e -> e'$ exists, we then derive that #rubn("r-tuple") is the only applicable reduction rule. Therefore $e' = (e_1,dots,e'_i,dots,e_n)$. Using the inductive hypothesis we get that $Env |- e'_1 : tau_1$, using #rbn("t-tuple") we get $Env |- e' : tau$.
  ]
  #case(of: rbn("t-index"))[
    Then $e = e_1[e_2]$ and $Env |- e_1 : [tau]$ and $Env |- e_2 : Int$. By assuming $e -> e'$ exists, we then derive the following reduction rules: 
    #case(of: rubn("r-index1"))[
      then $e' = e'_1[e_2]$, where $e_1 -> e'_1$. Using the inductive hypothesis we get that $Env |- e'_1 : [tau]$, therefore using #rbn("t-index") we get $Env |- e' : tau$.
    ]
    #case(of: rubn("r-index2"))[
      then $e' = e_1[e'_2]$, where $e_2 -> e'_2$. Using the inductive hypothesis we get that $Env |- e'_2 : Int$, therefore using #rbn("t-index") we get $Env |- e' : tau$.
    ]
    #case(of: rubn("r-index"))[
      then $e' = v_i$, using @lem:CanForm we get that $e_1 = [v_1,dots,v_n]$. Then using #rbn("t-array") we get that $forall i in {1,dots,n}. Env |- v_i : tau$ and therefore we get that $Env |- v_i : tau$.
    ]
    
  ]

  #case(of: rbn("t-abs"))[
    Then $e = lambda (x: tau).e$, and by inspection of the reduction rules there exists no $e'$ such that $lambda (x: tau).e -> e'$ making the preservation immediately obvious.
  ]
  #case(of: rbn("t-app"))[
    Then $e = e_1 e_2$, and $Env |- e_1 : tau_1 -> tau$ and $Env |- e_2 : tau_1$.  By assuming $e -> e'$ exists, and using case analysis we derive the following applicable reduction rules: 
    #case(of: rubn("r-app1"))[
      Then $e' = e'_1 e_2$ and $e_1 -> e'_1$. Using the induction hypothesis we have that $Env |- e'_1 : tau_1 -> tau$. Therefore, using #rbn("t-app") we get $Env |- e'_1 e_2 : tau$.
    ]
    #case(of: rubn("r-app2"))[
      Then $e' = e_1 e'_2$ and $e_2 -> e'_2$. Using the induction hypothesis we have that $Env |- e'_2 : tau_1 $. Therefore, using #rbn("t-app") we get $Env |- e_1 e'_2 : tau$.
    ]
    #case(of: rubn("r-abs"))[
      Then $e_1 = lambda (x: tau_2).e_3$ and $e_2 = v$ and $e' = e_3{x |-> v}$. Because $Env |- e_1 : tau_1 -> tau$ and $e_1 = lambda (x: tau_2).e_3$ by inspection of the type rules it must hold that $tau_1 = tau_2$ giving us $Env |- lambda (x: tau_1).e_3: tau_1 -> tau $. Then by inspection the derivation must end with #rbn("t-abs") giving us $Env, (x : tau_1) e_3 : tau$. Then because $Env |- e_2 : tau_1$ and $e_2 = v$ it must hold that $Env |- v : tau_1$. Therefore, using the @lem:btf_sub we have that $Env |- e_3{x |-> v} : tau$.
    ]
    #case(of: rubn("r-map"))[
      Then $e_1 = map$ for $e_2$ there are two cases that apply:
      #case(of: $e_2 in.not cV$)[
        the case for #rubn("r-app2") applies.
      ]
      #case(of: $e_2 in cV$)[
        using @lem:CanForm we get that $e_2 = (lambda (x:tau_1):e_3,[v_1, dots, v_n])$  then we get that $e' = [e_3{x |-> v_1},dots,e_3{x |-> v_n}]$.
        Then from @def:icontext we have that $Env |- map : (Int -> Int, [Int]) -> [Int]$ then by inspection of the type rules we have that $tau = [Int]$ and $tau_1 = Int$. Then by inspection the derivation must end with #rbn("t-array") giving us $Env |- [v_1,dots,v_n] : tau$ and $forall i in {1,dots,n}. Env |- v_i : Int$. Therefore using @lem:btf_sub we have that $Env |- [e{x |-> v_1},dots,e{x |-> v_n}] : tau$.
      ]
    ]
    #case(of: rubn("r-iota"))[
      Then $e_1 = iota$ for $e_2$ there are two cases that apply:
      #case(of: $e_2 in.not cV$)[
        the case for #rubn("r-app2") applies.
      ]
      #case(of: $e_2 in cV$)[
        using @lem:CanForm we get that $e_2 = n$, then we get that $e' = [v_1,dots,v_n]$. Then from @def:icontext we have that $Env |- iota : Int -> [Int]$ then by inspection of the type rules we have that $tau = [Int]$ and $tau_1 = Int$. Then using #rbn("t-array") we get that $Env |- e' : tau$.
      ]
    ]
    #case(of: rubn("r-size"))[
      Then $e_1 = size$ for $e_2$ there are two cases that apply:
      #case(of: $e_2 in.not cV$)[
        the case for #rubn("r-app2") applies.
      ]
      #case(of: $e_2 in cV$)[
        using @lem:CanForm we get that $e_2 = [v_1,dots,v_n]$ then we get that $e' = n$. Then from @def:icontext we have that $Env |- size : [Int] -> Int$ then by inspection of the type rules we have that $tau = Int$ and $tau_1 = [Int]$. Then using #rbn("t-int") we get that $Env |- e' : tau$.
      ]
    ]
  ]
]




  
/*  Assuming $Env |- e : tau$ and there exists a transition $e -> e'$ we show that $Env |- e'$ using induction on the type derivations of $e -> e'$.

  #case(of: rubn("r-array"))[
    In this case we have that $e = [e_1, dots ,e_i, dots, e_n]$ and $e' = [e_1, dots ,e'_i, dots, e_n]$ and $tau = [tau']$. From the derivation we have that there exists a transition $e_i -> e'_i$ where $1 <= i <= n$ and we a assume that our induction hypothesis holds for derivations, then $Env |- e_i : tau'$ and $Env |- e'_i : tau'$. Therefor from the premise of the only array type rule #rbn("t-array") we get that $forall i in {1,dots,n} Env |- e_i : tau'$ and as the type of $e_i$ is preserved after the transition $e_i -> e'_i$ then $Env |- e' : tau$ and the type is preserved.
  ]

  #case(of: rubn("r-tuple"))[
    In this case we have that $e = (e_1, dots ,e_i, dots, e_n)$ and $e' = (e_1, dots ,e'_i, dots, e_n)$ and $tau = (tau_1, dots, tau_i, dots , tau_n)$. From the derivation we have that there exists a transition $e_i -> e'_i$ where $1 <= i <= n$ and we a assume that our induction hypothesis holds for derivations, then $Env |- e_i : tau_i$ and $Env |- e'_i : tau_i$. Therefor from the premise of the only tuple type rule #rbn("t-tuple") we get that $forall i in {1,dots,n} Env |- e_i : tau_i$ and as the type of $e_i$ is preserved after the transition $e_i -> e'_i$ then $Env |- e' : tau$ and the type is preserved.
  ]
  #case(of: rubn("r-index1"))[
    
  ]
  #case(of: rubn("r-index2"))[
    
  ]
  #case(of: rubn("r-index"))[
    In this case we have that $e = e_1[e_2]$ and $e' = v_i$ under the assumption $Env |- e: tau$ we have the following derivations $Env |- [v_0,dots,v_n] : [tau]$ and $Env |- i : Int$ where $1 <= i <= n$. From the premise of #rbn("t-array") we get that $forall j in {1,dots,n} Env |- v_j : tau$ therefore it must hold that $Env |- e' : tau$ and the type is preserved. 
  ]

  #case(of: rubn("r-abs"))[
    In this case we have that $e = (lambda (x: tau').e_1)v$ and $e' = e_1 rn(v,x)$ under the assumption $Env |- e: tau$ we have the following derivations $Env |- lambda (x: tau')e_1 : tau' -> tau$ and $Env |- v : tau'$. For abstraction there is only one type rule #rbn("t-abs"), where from the premise we know that $Env, (x: tau') |- e_1 : tau$. Then as $Env |- v : tau'$ and $Env, x:tau' |- e_1 : tau$ #wnote[we have that both $v,x : tau'$ and preserving the type after the substitution $e_1 rn(v,x)$ therefore it must hold that $ Env |- e_1 rn(v,x) : tau$ and the type is preserved after #rubn("r-abs")][Use substitution lemma]. 
  ]

  #case(of: rubn("r-app1"))[
    In this case we have that $e = e_1 e_2$ and $e' = e'_1 e_2$ under the assumption $Env |- e: tau$ we have the following derivations $Env |- e_1: tau' -> tau$ and $Env |- e_2 : tau'$. From the derivation we have that there exists a transition $e_1 -> e'_1$ and under the assumption that our induction hypothesis holds for derivations then $Env |- e'_1 : tau' -> tau$. Therefore since the type of $e_1$ is preserved after the step $e_1 -> e'_1$ then it must hold that $ Env |- e'_1 e_2 : tau$ and the type is preserved.
  ]

  #case(of: rubn("r-app2"))[
    In this case we have that $e = e_1 e_2$ and $e' = e_1 e'_2$ under the assumption $Env |- e: tau$ we have the following derivations $Env |- e_1: tau' -> tau$ and $Env |- e_2 : tau'$. From the derivation we have that there exists a transition $e_2 -> e'_2$ and under the assumption that our induction hypothesis holds for derivations then $Env |- e'_2 : tau'$. Therefore since the type of $e_2$ is preserved after the step $e_2 -> e'_2$ then it must hold that $ Env |- e_1 e'_2 : tau$ and the type is preserved.
  ]
  #wnote[
  #case(of: rubn("r-if"))[
    
  ]
  #case(of: rubn("r-ift") )[
    In this case we have that $e = ifte(e_1,e_2,e_3)$ and $e' = e_2$ under the assumption $Env |- e: tau$ we have the following derivations $Env |-  e_1 : Int$, $Env |- e_2 : tau$, $Env |- e_3 : tau$. Since $Env |- e : tau$ and $Env |- e': tau$ we have that the type is preserved
  ]
  
  #case(of: rubn("r-iff") )[
    In this case we have that $e = ifte(e_1,e_2,e_3)$ and $e' = e_3$ under the assumption $Env |- e: tau$ we have the following derivations $Env |-  e_1 : Int$, $Env |- e_2 : tau$, $Env |- e_3 : tau$. Since $Env |- e : tau$ and $Env |- e': tau$ we have that the type is preserved
  ]][update]
  
  #case(of: rubn("r-map") )[
    In this case we have that $e = map (lambda x.e, [v_1, dots,v_n])$ and $e' = [e{x map v_1},dots,e{x map v_n}]$ under the assumption $Env |- e: [tau]$ we have the following derivations $Env |- map : (tau' -> tau, [tau']) -> tau$ and $Env |- (lambda x.e, [v_1, dots,v_n]) : (tau' -> tau, [tau'])$. From the case of #rubn("r-abs") we know that abstractions preserves types therefore it must hold that applying the abstraction to each element in the array that the type is preserved such that $Env |- e' : [tau']$
  ]
  #case(of: rubn("r-bin1"))[
    
  ]
  #case(of: rubn("r-bin2"))[
    
  ]
  #case(of: rubn("r-bin") )[
    In this case we have that $e = e_1 bin e_2$ and $e' = v_3$ and $tau = Int$. From #rbn("t-bin") we have that $e'$ has the type $Int$ as binary operations $Env |- bin : Int -> Int -> Int$ takes two $Int$'s as input a and produces a new $Int$. Therefore we have the type judgements $Env |- e_1 bin e_2 : Int$ and $Env |- e' : Int$ where the type is preserved after the step $e_1 bin e_2 -> n_3$.
  ]

  #case(of: rubn("r-iota") )[
    In this case we have that $e = iota n$ and $e' = [0,1,dots,n-1]$ under the assumption $Env |- e: [tau]$ we have the following derivations $Env |- size : Int -> [Int]$ and $Env |- [0,1,dots,n-1] : [Int]$. From the case of #rubn("r-abs") we know that abstractions preserves types therefore it must hold that it must hold that applying $iota$ to $n$ preserves the type such that $Env |- e': [tau]$. 
  ]

  #case(of: rubn("r-size") )[
    In this case we have that $e = size [v_1, dots, v_n]$ and $e' = n$ under the assumption $Env |- e: tau$ we have the following derivations $Env |- size : [Int] -> Int$ and $Env |- n : Int$. From the case of #rubn("r-abs") we know that abstractions preserves types therefore it must hold that applying $size$ to $n$ preserves the type such that $Env |- e': tau$. 
  ]

  #case(of: "Consistency")[ 
  
     * No Type * In this case we have that $e = ...$ and $e' = ...$ under the assumption $Env |- e: [tau]$ we have the following derivations $dots$.
     
     * Type * In this case we have that $e = dots$ and $e' = dots$ and $tau = dots$.
    
  ]*/
