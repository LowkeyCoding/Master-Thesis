#import "../../../Packages/global.typ": *

== Proof of Lemma 4.2

Before we start the proof of @lem:PreserveSub we first need some important definitions. We have taken the same approach to prove @lem:PreserveSub as #cn(<ButfToEpi>) and therefore the approach for the proof will be similar to the one seen in @ButfToEpi.

First we have the definition $U$ which is the building blocks for the translation. By this we mean that for any $Env |- e: tau$ there should exist a process $P$ and output channel $o$ such that $tle(e,o) == P$ and that $P$ is in the set of all possible $U$. As we know that $e$ is well typed then by the proof of @th:typeCorrectness we know that $P$ is well-typed and therefore we will denote the types in some of the building blocks by $t$.

#definition($"Building blocks" U$)[
  We define the set of translation building blocks $U$ as follows.
  $
  U = &receive(o,v : t).U | receive(h, v : t_1 \, o : t_2).U | ! receive(h, v : t_1 \, o : t_2).U | receive(h dot n, v : t).U | receive(h dot len, n : t).U | \
  &receive(h dot tup, v_1 : t_1 \, dots \, v_n : t_n).U | receive(h dot all, c : t).U | !receive(h dot all, c : t).U | broad(h dot all, c).U | \
  &receive(c, n : t_1 \, v : t_2).U | !receive(c, n : t_1 \, v : t_2).U | receive(d, \_ : t).U | [n != 0]U,U | U|U | (nu a : t).U | \
  &send(o,v) | send(h, v \, o) | send(h dot n, n \, v) | !send(h dot n, n \, v) | send(h dot len, n) | send(h dot tup, v_1\, dots \, v_n) | \
  &! send(h dot tup, v_1\, dots \, v_n) | send(c, n \, v) | send(d, 0 : t) | Prepeat(n, c, d) | null 
  $
  we denote the set of all possible $U$ as $cal(U)$.
]

In the translation we have 4 categories of channels $o in Omega$, $h in Lambda$, $d in Kappa$, $c in Psi$ and $cal(A) = Omega union Lambda union Kappa union Psi$ where $a in cal(A)$. We denote $cal(P) = {P_1,dots,P_n}$ as a set of processes in $U$ where $forall i in {1..n} . barb(P_i, h)$, and therefore $cal(P) subset.eq cal(U)$. We denote $cal(Q) = {Q_1, dots, Q_n}$ as the set of processes s.t for some $Q_i in cal(Q)$, $Q_i$ communicates over $h_i$ instead of $h$. 

#definition($"Client function" f$)[
  We create a function that partially maps from sub processes to the powerset of processes
  $f: cal(Q) harpoon PP(cal(P))$
]

This function takes a sub-process $Q$ and then returns the processes $Q$ communicates with, that being $Q$'s clients. Next we define a new relation $R$ that relates processes with a single handle for communication with a $Q$ to processes with multiple handles for communication with multiple $Q$'s. In this relation $C$ is a complete context (see @def:compContext).

#definition($"Relation" R$)[
  $
  R = &{(C[(nu h : t_h) . (nu cal(A) : many(t_a)) . ( Q | limits(product)_(P_i in cal(P)) P_i | U)], \ &C[(nu h_1 : t_h_1) . space dots space .(nu h_n : t_h_n) . (nu cal(A) : many(t_a)) . (limits(product)_(Q_i in cal(Q)) | limits(product)_(Q_j in cal(Q)) limits(product)_(P_i in f(Q_j)) P_i rn(h_j,h) | U ) ]) | \
  &U adown(h)  "and" forall i in {1 dots n}. U adown(h_i) "and"
  (union.big_(Q_i in cal(Q)) f(Q_i)) = cal(P) "and" \
  &forall Q_i,Q_j. where i != j "then" f(Q_i) sect f(Q_j) = emptyset "and"
  forall a in cal(A). (nu a : t_a).U adown(a)
}
  $
]

This brings us to the proof of @lem:PreserveSub which states that for two well-typed #btf expressions and their 

// NOTES:
// Q : is a fully evaluated abstraction, tuple or array
// Q_i : is the fully evaluated sub procceses of Q
// h_i : is the handles used to communicate the result of sub proccesses of Q. {h dot i, h dot len, h dot all, h dot tup,h}


// For this relation we require that the handle $h$ is not observable in $U$, . The requirement $forall Q_i,Q_j. where i != j "then" f(Q_i) sect f(Q_j) = emptyset$ ensures that there is no overlap in when communication with $P_i$ happens. 
 
#proof(of: <lem:PreserveSub>)[
  In order to prove @lem:PreserveSub we have to prove that independent of what value $e_1$ is that $bim(tle(e_1,o) rn(h,x), tle(e_1 {x |-> e_2},o))$ by showing that $R$ is a WABB and therefore closed under @def:Wabb. We do this by matching the transitions for each translated expression and showing that the new pair is in $R$.
  #case(of: $e_2 "is an integer"$)[
    When $e_2$ is a number we have from the translation that $tle(n,o) = send(o,n)$ where $n : Int$, $o : ch(Int)$ and $x : Int$. As $x$ is a variable the substitution is on translations of $x$ in $e_1$. Therefore we show that $bim(tle(x,o) rn(x,n), tle(x { x |-> n},o))$. Then we have the translation for $x$ is $tle(x,o) = send(o,x)$ and $tle(x { x |-> n},o) = send(o,n)$. We then have that $send(o,x) rn(x,n) = send(o,n)$ and since $bim(send(o,n),send(o,n))$ then $bim(send(o,x) rn(x,n), tle(x { x |-> n},o))$.
  ]

  #case(of: $e_2 "is an abstraction, tuple or array"$)[
    For the process $tle(e_1 {x |-> e_2},o)$ there can be different variations of processes from the translation of $e_2$. In this case a handle is used for communication with the translation of $e_2$. 
    #case(of: $"1. " C[S] -> C'[S]$)[
      In this case we have an internal reduction in the context of the form $C[S] -> C'[S]$ where $S = (nu h : t_h) . (nu cal(A) : t_a) . ( Q | limits(product)_(P_i in cal(P)) P_i | U)$ s.t $C$ can take the transition without $S$ and behaves like $C[null] -> C'[null]$. Therefore we can use $C'$ on the right side of the pair since it is not dependent on the process in the context. Furthermore since the restrictions on the relation only are on the inner process of the context the new pair is in $R$. 
    ] 
    #case(of: $"2. " U -> U'$)[
      In this case we have an internal transition inside $U$ s.t $U -> U'$ and since $U$ is the same on the left and right side of the pair there is a matching transition per @def:Wabb. However to show that $U'$ is allowed in $R$ we have to prove the following holds $U' adown(h)$, $forall i in {1 dots n}. U' adown(h_i)$ and $forall a in cal(A). (nu a : t_a).U' adown(a)$. To prove the first condition $U' adown(h)$ we destruct $U'$ into it's components $U' = U_1 | dots | U_n$. Then to prove $U' adown(h)$ we have to construct a $U''$ as from the building blocks of $U$ we have that there can exists a $U_i$ of the form $U_i in.not {!U,(nu a : t_a).U, [n != 0]U,U, null}$ s.t that $barb(U_i,h)$ and therefore $barb(U',h)$ which is not allowed in $R$. However we can construct a new $U''$ and $cal(P)'$ s.t $U'' adown(h)$ and $(limits(union.big)_(Q_i in cal(Q)) f(Q_i)) = cal(P)'$. We construct $cal(P')$ as $cal(P)$ and the set of all sub-processes of $U'$ where $barb(U_i,h)$ then we construct $U''$ as the all the sub-processes of $U'$ where $U_i adown(h)$ in parallel composition. Then as $U'' adown(h)$ and all of new exposed clients of $cal(Q)$ has been moved to $cal(P')$ we have $(limits(union.big)_(Q_i in cal(Q)) f(Q_i)) = cal(P)'$. 
      
      Then for the second condition $forall i in {1 dots n}. U'' adown(h_i)$ we use that on both sides of the pair $U$ is the same. Then as we are only able to observer communication $h_i$ after substituting $h$ we know from the construction of $U''$ above that $U'' adown(h)$. Therefore we can only observe communication on $h_i$ outside of $U''$ and therefore the condition $forall i in {1 dots n}. U'' adown(h_i)$ holds.

      Then for the case of $forall a in cal(A). (nu a : t_a).U'' adown(a)$ we can use structural congruence to move out all restrictions and therefore we have that the new pair is in $R$. $ (&C[(nu h : t_h) . (nu cal(A) : many(t_a)) . ( Q | limits(product)_(P'_i in cal(P')) P'_i | U'')],\ &C[(nu h_1 : t_h_1) . space dots space .(nu h_n : t_h_n) . (nu cal(A) : many(t_a)) . (limits(product)_(Q_i in cal(Q)) | limits(product)_(Q_j in cal(Q)) limits(product)_(P'_i in f(Q_j)) P'_i rn(h_j,h) | U'' ) ]) $ 

      
     // $U' adown(h) "and" forall a in cal(A). (nu a : t_a).U adown(a)$. For the condition $forall a in cal(A). (nu a : t_a).U adown(a)$ we look
      
      
      
      //We then destruct $U'$ into it's components $U' = U_1 | dots | U_n$ then we  at the building blocks of $U$. When some $U_i$ is not of the form $U_i in.not {!U, [n != 0]U,U, null}$ we can have that there exist and $U_i$ s.t $barb(U_i,h)$ or $forall a in cal(A).barb((nu a : t_a).U_i',a)$ and therefore $barb(U',h)$ or $barb(U',a)$ which is not allowed in $R$. However by constructing a new $U''$ and $cal(P')$ s.t $U'' adown(h)$ and $forall a in cal(A). U'' adown(a)$ using structural congruence we show that we can rewrite the process without changing behaviour s.t it is still WABB and in $R$. We construct $cal(P')$ by moving all sub-process $U_i$ in $U'$ where we observe a channel $h$ or $a in cal(A)$ using structural congruence s.t on $U'' adown(h)$ and $forall a in cal(A). U'' adown(a)$. Then since we only make use of structural congruence $U' == U''$ and therefore pair is still in $R$. // The only change needed is to not move all communications on $a$ into P and let U do that internally.
      
      //In this case we have an internal communication in $U_1$ such that $U_1 -> U_2$ where $U_1 = U$. During this internal communication there is the case where $barb(U_2,h)$ s.t $U_2 = U_3 | dots | U_n$ and there $exists U_i in {U_3, dots, U_n}. U_i = h(o : t_1,v : t_2).U_lambda_i$ or $exists U_i in {U_3, dots, U_n}. h_j(o : t_1,v : t_2).U_lambda_j$ which is not allowed in $R$ by the condition $U adown(h)$ and $forall j in {1,dots,n}.U adown(h_j)$. \
      //Then we denote $U_"app"$ as the set of all $U_i in {U_3, dots, U_n}$ where $barb(U_i,h)$ and then $U_"ok" = {U_3, dots, U_n} - U_"app"$. Then using repeated application of structural congruence on $(nu h : t_h) . (nu cal(A) : t_a) . ( Q | limits(product)_(P_i in cal(P)) P_i | U_2)$ we transform it to $(nu h : t_h) . (nu cal(A) : t_a) . ( Q | limits(product)_(P_i in cal(P) union U_"app") P_i | U_"ok")$. Then because we have moved the cases where $barb(U_i,h)$ out of the new $U$ the condition $U adown(h)$ holds in $R$. Then since we only make use of structural congruence it can be matched on the right side using structural congruence and the pair is still in $R$.
    ]
    #case(of: $"3. "Q |P_i -> Q' | P'_i$)[
      For this case we consider the different forms of $e_2$ and $Q$ where $e_2$ is either an abstraction, tuple or array.
       #case(of: $e_2 = lambda (x : t) . e_lambda$)[
        Then $Q = !receive(h,x\,r).tle(e_lambda,r)$ and as $P_i$ communicates with $Q$ on $h$ it has the following form $P_i = !send(h,x\,r).S$ where $S$ is some continuation of $P_i$. Then we have the transition to $Q | P -> tle(e_lambda,r) | S$ in the right pair we can match this by using $P_i rn(h_j,h)$ where $P_i in f(Q_j)$ s.t $barb(Q_j,h_j)$. 
        After the communication $S$ is uncovered and a $tle(e_lambda,r)$ is spawned and added to $U' = U union tle(e_lambda,r) union S$. However as it is possible that $barb(tle(e_lambda,r),h)$ and $barb(S,h)$ we use structural congruence as in the second case to find a $U''$ and $P'$ s.t $U'' adown(h)$ and then the following holds:
        $ Q | limits(product)_(P_i in cal(P)) P_i | U -> Q | limits(product)_(P_i in cal(P')) P_i | U'' $ 
        //On the right side we can then match the transition using $P_i rn(h_j,h)$ where $P_i in f(Q_j)$ s.t $barb(Q_j,h_j)$.
        Therefore the pair after the transition is still in $R$. 
      ] 
      #case(of: $e_2 = (e_(2,1), dots , e_(2,n))$)[
        Then $Q = ! send(h dot tup, T_1\, dots \, T_n) | send(o,h)$ and as $P_i$ communicates with $Q$ on $h$ it has the following form $P_i = receive(h dot tup, v_1 : t_1\,dots\, v_n : t_n).S$ where $S$ is some continuation of $P_i$. Then using the same argument for the case of abstraction with $U' = U union S$.  
      ]
      #case(of: $e_2 = [e_(2,1), dots , e_(2,n)]$)[
        Then $Q = limits(product)_(i in 1..n) (!receive(h dot all, r).send(r, T_i) | send(h dot i, T_i)) | send(o,h)$ and as $P_i$ communicates with $Q$ on $h$ it has one of the following forms where $S$ is some continuation of $P_i$. $ P_i in {receive(h dot i, v : t).S, send(h dot all, h_x).!receive(h_x, i : Int\, v : t).S, receive(h dot len, v : Int).S} $ Then using the same argument for the case of abstraction with $U' = U union S$.  
       ]
    ]
    Next we look at the right side of the pair in the relation.
    1. In this case we have an internal communication in the context $C$. The proof follows the same argument as in case 1 above.
    2. In this case we have an internal communication in $U$. The proof follows the same argument as in case 2 above. 
    3. For this case we consider the different forms of Q, that being $e_1$ is either an abstraction, tuple or array. The proof follows the same argument as in case 3 above communicating on some $h_j$ instead.
  ]
  #case(of: $"The pair" (tle(e_1,o) rn(h,x),tle(e_1{x |-> e_2 },o))$)[
    
    Lastly we show that $R$ is closed under @def:Wabb when on the form of the pair.
    $ ((nu h : t).(Q | tle(e_1,o) rn(h,x)),tle(e_1{x |-> e_2},o)) $
    In $e_1$ there exist $n$ usages of $x$ where each usage in $tle(e_1,o)$ is replaced with $send(o_1,x),dots,send(o_n,x)$ where $forall i in {1,dots,n}. send(o_i,x) in cal(U)$. Then in $e_1{x |-> e_2}$ each use of $x$ is replaced with the full expression $e_2$ s.t in $tle(e_1,o)$ each $x$ is on the form $forall i in {1,dots,n}. tle(e_i,o_i) = (nu h : tau).(Q | send(o_i,h_i))$ where $tle(e_i,o_i) in cal(U)$. Therefore $tle(e_1 {x |- e_2},o)  = tle(e_2,o_1) | dots | tle(e_2,o_n) | S$ and $tle(e_1,o) rn(h,x) = send(o_1,h)| dots |send(o_n,h) | S$ where $S$ is the rest of $tle(e_2,o)$. We start by showing we can match transitions.

    #case(of: "WABB")[
      We start by expanding the translation of $tle(e_1{x |-> e_2},o) = Q_1 | send(o_1,h_1) | dots | Q_n | send(o_n,h_n) | S$ and $tle(e_1,o) rn(x,h) = Q | send(o_1, h) | dots | send(o_n, h) | S$. The by inspection of the translation we have that $forall i in {1,dots,n}. (Q == Q_i)$ as $Q$ and $Q_i$ are both translations of $e_2$ with different handles and therefore we can apply the structural congruence rule for alpha conversion. Furthermore from the translation we have that for each $Q | dots |send(o_i,h)$ on the left side of the pair there is a corresponding $Q_i | send(o_i,h_i)$ on the right side and as $e_2 in cal(V)$ we no there are no further important transitions. Then as $S$ is the same on both sides of the pair we can match any internal transition of $S$. // Highlight that e_1 is a fully evaluated expression and therefore there are no importnat transitions inside we have to match. 
    ]
    Then we show that for the left and right side of the pair that the conditions for $R$ is fulfilled.
    // Fix left and right side
    #case(of: "Left side")[
      Then for the left side we show that we can transform the form of the translation s.t it fulfills that $U adown(h)$  and $forall a in cal(A). (nu a : t_a).U adown(a)$. To do this we first find a $U$, $Q$ and $cal(P)$ s.t we can transform the process $W_1 = (nu h : t).(nu cal(A) : t_a).(Q' | send(o_1,h)| dots |send(o_n,h) | S)$ to the following process.
      $ (nu h : t) . (nu cal(A) : t_a) . ( Q | limits(product)_(P_i in cal(P)) P_i | U)  $
      
      The first step is to abuse that all bindings of names are unique and therefore we can move out all bindings using structural congruence s.t we have the process on the following form.
  
      $ W_1 == (nu h : t).(nu cal(A) : many(t_a)).(Q' | send(o_1,h)| dots |send(o_n,h) | S) $
  
      Then for every sub-process in $S$ we check if $barb(S_i, h)$ and when it is the case add it to $cal(P)$ and otherwise to $U$ and then we add $Q'|send(o_1,h)| dots |send(o_n,h)$ to $Q$. Therefore we have that $U adown(h)$ and $forall a in cal(A). (nu a : t_a).U adown(a)$, and by the construction of $U$ we have not added any process that communicates on $h$ and as all restrictions have been moved to the top of the process. Therefore we can reconstruct $W_1$ using $U$ and $cal(P)$ s.t we have the following process.
      $ (nu h : t) . (nu cal(A) : t_a) . ( Q | limits(product)_(P_i in cal(P)) P_i | U)  $
    ]

    #case(of:"Right side")[
      Then for the right side we show that we can transform the form of the translation s.t it fulfills that $forall i in {1 dots n}. U' adown(h_i)$, $(union.big_(Q_i in cal(Q)) f(Q_i)) = cal(P)$, $forall Q_i,Q_j. where i != j "then" f(Q_i) sect f(Q_j) = emptyset$ and $forall a in cal(A). (nu a : t_a).U adown(a)$ To do this we first find a $U$, $cal(Q)$ and $cal(P)$ s.t we can transform the process $W_2 = (nu h_1 : t).(Q_1 | send(o_1,h_1)) | dots | (nu h_n : t).(Q_n | send(o_n,h_n)) | S$ to the following process. 
      $ (nu h_1 : t_h_1) . space dots space .(nu h_n : t_h_n) . (nu cal(A) : t_a) . (limits(product)_(Q_i in cal(Q)) | limits(product)_(Q_j in cal(Q)) limits(product)_(P_i in f(Q_j)) P_i rn(h_j,h) | U ) $ 
      The first step is to abuse that all bindings of names are unique and therefore we can move them to start of the process s.t we have the process on the following form.
      $ W_1 ==  (nu h_1 : t).dots.(nu h_n : t).(Q_1 | send(o_1,h_1)) | dots | (Q_n | send(o_n,h_n)) | S $ Then for every sub-process in $S$ we check if $barb(S_i, h)$ and if it is the case we add it to $cal(P)$ and otherwise $U$. Then we construct $cal(Q) = {Q_1| send(o_1,h_1) ,dots,Q_n| send(o_n,h_n)}$. Therefore we have that $forall i in {1 dots n}. U adown(h_i)$ and $(limits(union.big)_(Q_i in cal(Q)) f(Q_i)) = cal(P)$ holds as all clients of $cal(Q)$ has been moved to $cal(P)$ and $forall Q_i,Q_j. where i != j "then" f(Q_i) sect f(Q_j) = emptyset$ holds as each $P_i in cal(P)$ receives their handle through some $o_i$ specific to each instance of the translation of $e_2$. Lastly $forall a in cal(A). (nu a : t_a).U adown(a)$ as all restrictions have been moved to the top of the process.
      
     //Then for the right side $R_2$  of the pair we have to find a $U$, $cal(Q)$ and $cal(P)$ s.t it is structurally congruent with $R_1$.
      //$ R_1 = (nu h_1 : t_h_1) . space dots space .(nu h_n : t_h_n) . (nu cal(A) : t_a) . (limits(product)_(Q_i in cal(Q)) | limits(product)_(Q_j in cal(Q)) limits(product)_(P_i in f(Q_j)) P_i rn(h_j,h) | U ),  $ 
      //$ R_2 == (nu h_1 : t).(Q_1 | send(o_1,h_1)) | dots | (nu h_n : t).(Q_n | send(o_n,h_n)) | S $
      //The first step is to abuse that all bindings of names are unique and therefore we can move them to start of the process s.t the following holds.
      //$ R_2 == (nu h_1 : t).dots.(nu h_n : t).(Q_1 | send(o_1,h_1)) | dots | (Q_n | send(o_n,h_n)) | S $
      //Then for every sub-process in $S$ we check if $barb(S_i, h)$ and when it is the case add it to $cal(P)$ and $U$ otherwise. Furthermore we add $send(o_1,h_1)| dots |send(o_n,h_n)$ to $U$ as $forall i in {1,dots,n}. send(o_i,h) adown(h_i)$. Then we add ${Q_1,dots,Q_n}$ to $cal(Q)$ s.t it is on the form as $R_1$ 
    ]
   // Then we have to show that we can match transitions between the left and right side of the pair. We do this by inspection of $L_2$ and $R_2$ where we observer that for each $send(o_i,h)$ on the left side there is a corresponding $Q_i | send(o_i,h_i)$ where $Q_i$ is the translation of $e_1$ after an important transition with the handle $h_i$. Then as $Q$ on the left side is the translation of $e_1$ after an important transition aswell we have that $Q == Q_i$ after alpha conversion. Therefore as we can handle each  transition on the left side on the form $send(o_i,h)$ with a $Q_i | send(o_i,h_i)$ on the right side and as $S$ is the same on both sides we can match any transition on the $L_2$ with one in $R_2$. 
    Therefore as the pair $(W_1,W_2)$ fulfills the conditions for $R$ and $R$ is closed under @def:Wabb with the pair it must hold for this case.
    //Then since $tle(e_2,o) rn(h,x) in cal(U)$ and $tle(e_2 {x |- e_1},o) in cal(U)$ and the pair can match the pair $(L_2,R_2) in R$ using structural congruence.
  ]
]

