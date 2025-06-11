#import "../../../Packages/global.typ": *

#let rbtfn(x) = shown(rbutf, x)
#let repin(x) = shown(repi, x)
#let radmnn(x) = shown(radmn,x)
#let ts_e(x) = $#showf(sttrans_e, x) = #showt(sttrans_e, x)$
#let ts_l(x) = $#showf(sttrans_l, x) = #showt(sttrans_l, x)$

== Proof of Theorem 4.2 <app:behaveCorrect>

#proof(of: <th:correctness>)[
  Let $cal(B)$ be the set of all #btf programs and let $R$ be the following relation $R={(e,tle(e,o)) | e in cal(B), o "fresh"}$. We show that $R$ is an administrative operational correspondences. As per @def:opcor we only consider pairs where $e -> e'$ and where $tle(e,o)$ contains $circle.small.filled$. 
  #case(of: "Array")[
    For arrays we have $e = [e_1, ... , e_n]$ and must prove that the two parts of operational correspondence hold.
    #case(of: "Soundness")[
      For the first part we have that if $e -> e'$ then there is a $P'$ such that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$. From the rule #rbtfn("r-array") we know there must exist an $i$ such that $e_i -> e'_i$. The translation $tle(e,o)$ contains $(nu o_i : t_i). (tle(e_i,o_i))$. By our assumption that $(e, tle(e,o)) in R$ we have that $(e_i, tle(e_i,o_i)) in R$. Then it follows that we have $tle(e_i,o_i) =i Q$ and that $bim(Q, tle(e'_i,o_i))$. 
      
      //Then we select $P'$ to be $tle(e',o)$ where the sub-process $tle(e_i,o_i)$ is replaced by $Q$. We then have that when $tle(e_i,o_i)$ is unguarded we know that $tle(e,o) =i P$ and $bim(P, P')$.
      
      We let the subprocess $tle(e_i,o_i)$ in $tle(e,o)$ be replaced by $Q$. We then have that when $tle(e_i,o_i)$ is unguarded we know that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$.
    ]
    #case(of: "Completeness")[
      If $tle(e,o) =i P'$, then $bim(P',tle(e',o))$ where $e -> e'$. However as the translation of #rbtfn("r-array") on #pageRef(<h3:ts_arr_tup>) contains no $circle.small.filled$ then the important reduction must be in one of the elements of $e$. Then by our assumption that $tle(e,o) =i P'$ there must exist an $i$ s.t in the sub-process $tle(e_i,o_i)$ the important reduction occurs. As $(e_i, tle(e_i,o_i)) in R$ we know that $tle(e_i,o_i) =i Q$ for any $Q$ and $e'_i$ where $bim(Q,tle(e_i,o_i))$ and $e_i -> e'_i$. 
      
      Then we select $e'$ to be $e$ where $e_i$ is replaced by $e'_i$. Therefore $bim(P',tle(e',o))$ as only administrative transitions has been taken.
    ]
  ]
  #case(of: "Tuple")[
    For tuples we have $e = (e_1, ... , e_n)$ and must prove that the two parts of operational correspondence hold.
    #case(of: "Soundness")[
      For the first part we have that if $e -> e'$ then there is a $P'$ such that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$. From the rule #rbtfn("r-tuple") we know there must exist an $i$ such that $e_i -> e'_i$. The translation $tle(e,o)$ contains $(nu o_i : t_i). (tle(e_i,o_i))$. By our assumption that $(e, tle(e,o)) in R$ we have that $(e_i, tle(e_i,o_i)) in R$. Then it follows that we have $tle(e_i,o_i) =i Q$ and that $bim(Q, tle(e'_i,o_i))$. 
      
      We let the subprocess $tle(e_i,o_i)$ in $tle(e,o)$ be replaced by $Q$. We then have that when $tle(e_i,o_i)$ is unguarded we know that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$.
    ]
    #case(of: "Completeness")[
      For the second part we have that if $tle(e,o) =i P'$ then there is an $e'$ such that $e -> e'$ and $bim(P', tle(e',o))$. However as the translation of #rbtfn("r-tuple") on #pageRef(<h3:ts_arr_tup>) contains no $circle.small.filled$ then the important reduction must be in one of the elements of $e$. Then by our assumption that $tle(e,o) =i P'$ there must exist an $i$ such that in the sub-process $tle(e_i,o_i)$ the important reduction occurs. As we have that $(e_i, tle(e_i,o_i)) in R$ we know that $tle(e_i,o_i) =i Q$ for any $Q$ and $e'_i$ where $bim(Q,tle(e_i,o_i))$ and $e_i -> e'_i$. 
      
      Then we select $e'$ to be $e$ where $e_i$ is replaced by $e'_i$. Therefore we have $bim(P',tle(e',o))$ as only administrative transitions has been taken.
    ]
  ]
  #case(of: "Indexing")[
    For indexing we have $e = e_1[e_2]$ and must prove that the two parts of operational correspondence hold.
    #case(of: "Soundness")[
      For the first part we have that if $e -> e'$ then there is a $P'$ such that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$. For indexing we have three rules for $e$ to take a step: #rbtfn("r-index"), #rbtfn("r-index1") and #rbtfn("r-index2"). The two rules, #rbtfn("r-index1") and #rbtfn("r-index2"), are used for evaluating each sub-expression. By our assumption that $(e, tle(e,o)) in R$ we have that $(e_1, tle(e_1,o_1)) in R$, and then if $e_1[e_2] -> e'_1[e_2]$ we have $tle(e_1,o_1) =i tle(e'_1,o_1)$ and $bim(tle(e_1,o_1), tle(e'_1,o_1))$. We have that when $tle(e_1,o_1)$ is unguarded we know that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$. The same holds for $e_2$.

      For the last rule #rbtfn("r-index") we have that if $v_1[v_2] -> v_3$ then a corresponding operation exists. By #rbtfn("r-index") we have $v_1$ being an array of size $n$ and $v_2$ being a integer with a value of at most $n$. By @lem:tvoo we have that the translation of two expression have observable action on their respective $o$ channel and these are administrative reductions. Then from the third case of @lem:prgBehave we have $(nu h:t_h).(Q_h | receive(h dot i, v :t) . circle.small.filled send(o,v),null)$ where $t_h = (i: ch(t_1), all : ch(t_1), len : ch(Int))$ with $t_1 = (i : Int, v : t)$ and $Q_h$ is the leftovers from the reduced array ($tle(e_1,o_1)$) and index ($tle(e_2,o_2)$). Using @lem:GarbageCollect we can remove $Q_h$ and then we have $tle(e,o) =i P'$ and $bim(tle(e',o), P')$. 
      //From #rbtfn("r-index") we know that $i in {1,dots,n}$ and therefore $i > 0$ ensuring that $h dot i$ is observable. Thereby we have that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$.
    ]
    #case(of: "Completeness")[
      If $tle(e,o) =i P'$, then $bim(P',tle(e',o))$ where $e -> e'$. From the translation of #rbtfn("r-index") in @h3:ts_expr there are three possible locations for important reductions $tle(e_1,o_1),tle(e_2,o_2)$ and by the index check. Therefore we get two sub-cases one for where the important reduction is in the sub-processes and one where it is before the output of the value.  
      
      Then because $tle(e,o) =i P'$ there must exist an $i$ where $i in {1,2}$ s.t in the sub-process $tle(e_i,o_i)$ the important reduction occurs. We assume that exists some $(e_j, tle(e_j,o_j)) in R$ and from that assumption we have that $tle(e_j,o_j) =i Q$ for any $Q$ and $e'_j$ where $bim(Q,tle(e_i,o_i))$ and $e_j -> e'_j$. Then we select $e'$ to be $e$ where $e_i$ is replaced by $e'_i$. Therefore $bim(P,tle(e',o))$ as only administrative transitions has been taken.
      
      Then because $tle(e,o) =i P'$ there must be a process listening on $h dot i$ and this is the only case when the array and index is fully reduced. We have that we can only listen on $h dot i$ if the array size is larger or equal to $i$. Therefore $e -> e'$ by #rbtfn("r-index") and $bim(P', tle(e',o))$.
    ]
  ]
  #case(of: "Binop")[
    /*
    The proof for Binop follows the same structure as Index.
    */
    For Binop we have $e = e_1 bin e_2$ and must prove that the two parts of operational correspondence hold.
    #case(of: "Soundness")[
      For the first part we have that if $e -> e'$ then there is a $P'$ such that $tle(e,o) =i P'$ and $bim(tle(e',o), P')$. 

      Just like indexing we have three rules for $e$ to take a step: #rbtfn("r-bin"), #rbtfn("r-bin1") and #rbtfn("r-bin2"). The two rules, #rbtfn("r-bin1") and #rbtfn("r-bin2"), are used for evaluating each sub-expression. By our assumption that $(e, tle(e,o)) in R$ we have that $(e_1, tle(e_1,o_1)) in R$, and then if $e_1 bin e_2 -> e'_1 bin e_2$ we have $tle(e_1,o_1) =i tle(e'_1,o_1)$ and $bim(tle(e_1,o_1), tle(e'_1,o_1))$. We have that when $tle(e_1,o_1)$ is unguarded we know that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$. The same holds for $e_2$.

      For the last rule #rbtfn("r-bin") we have that if $v_1 bin v_2 -> v_3$. By @lem:tvoo we have that the two sub-expressions will output on their respective channel after som administrative reductions. On the important reduction we have that $-i send(o, v_1 bin v_2)$ and thereby we have $tle(e,o) =i P'$ and $bim(tle(e',o), P')$. 
    ]
    #case(of: "Completeness")[
      For the second part we have that if $tle(e,o) =i P'$ then there is an $e'$ such that $e -> e'$ and $bim(P', tle(e',o))$. We have three cases: one where the important reduction happens in $tle(e_1,o_1)$, one where it happens in $tle(e_2,o_2)$ or where it happens on the communication on $o$. 

      First case the $=i$ transition happens inside $tle(e_1,o_1)$. We let $e' = e'_1 bin e_2$ where $e_1 -> e'_1$. By our assumption that $(e, tle(e,o) in R)$ we have that $(e_1, tle(e_1,o_1)) in R$ which means we know that $bim(P', tle(e',o))$. The same argument follows for the second case where $=i$ happens in $tle(e_2,o_2)$.

      In the last case we have that we receive on $o_1$ and $o_2$ and therefore by @lem:teoo we know that both $e_1$ and $e_2$ must be values. We then select $e' = v_3$ and then we have $bim(P', tle(e',o))$. 
    ]
  ]
  #case(of: "Application")[
    For application we have $e = e_1 e_2$ and must prove that the two parts of operational correspondence hold. 
    #case(of: "Soundness")[
      For the first part we have that if $e -> e'$ then there is a $P'$ such that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$. There are two cases for when $e -> e'$: One when the sub-expressions can take a step and one when they cannot. 

      For the first case we have that there are two application rules for the sub-expressions $e_1$ and $e_2$ to take a step: #rbtfn("r-app1") and #rbtfn("r-app2"). By our assumption that $(e, tle(e,o)) in R$ we have that $(e_1, tle(e_1,o)) in R$. The same holds for $e_2$. When $tle(e_1,o_1)$ and $tle(e_2,o_2)$ is unguarded we know that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$.

      For the second case we have that neither $e_1 $ and $e_2$ cannot take a step and by @lem:teoo we know that $e_1$ and $e_2$ must be values and therefore must be on the form $e_1 = lambda (x : tau_1).e_lambda$ and $e_2 = v$. In this case we can take a step with #rbtfn("r-abs") and this can be matched in the translation of application. As this case is more complicated we will show how the translation will match this. First the two sub-expression is evaluated and this will give us the process on the following form:

      $ (nu o_1 : ch(tl(tau_1 -> tau_2))) . (nu o_2 : ch(tl(tau_1))) . \
      (underbracket( (nu h : tl(tau_1 -> tau_2)) . (send(o,h) | repl receive(h, x : tl(tau_1)\,r : ch(tl(tau_2))) . tle(e_lambda,r)) , tle(e_1,o_1)) \
      | underbracket((nu v : tl(tau_1)) . send(o_2, v) | S, tle(e_2,o_2)) 
      | receive(o_1,h : tl(tau_1 -> tau_2)) . receive(o_2, v : tl(tau_1)). circle.small.filled send(h, v\, o)) $

      As the translation of $e_1$ is an abstraction it is substituted with the translation of abstraction. The translation of $e_2$ is substituted with a value ready to be sent on $o_2$ in parallel with a processes $S$ that maintains the value. To not confuse the reader, the expression in the translation of abstraction has been renamed to $e_lambda$. After communication on $o_1$ and $o_2$ happens the application will be on the following form:

      $ (nu h : tl(tau_1 -> tau_2)) . (nu v : tl(tau_1)) . 
       
       underbracket( repl receive(h, x : tl(tau_1)\,r : ch(tl(tau_2))) . tle(e_lambda,r), "Abstraction") | S | circle.small.filled send(h, v\, o) $

       Now we can send on the function handle $h$ and thus proceed to $tle(e_lambda,r)$ where $r$ is the return channel substituted with the output channel $o$ and value $v$. We denote this as the process $H$ which then corresponds to $H = tle(e_lambda,o)rn(x,v)$. By @lem:PreserveSub we have that this corresponds to $e_lambda {v |-> x}$ which is our $e'$. Thereby we have the $tle(e,o) =i P'$ and $bim(P', tle(e',o))$.
    ]
    #case(of: "Completeness")[
      For the second part we have that if $tle(e,o) =i P'$ then there is an $e'$ such that $e -> e'$ and $bim(P', tle(e',o))$. We have two cases: first if the important transition happens in either $tle(e_1,o_1)$ or $tle(e_2,o_2)$, or second when sending on the handle $h$.

      In the first case we can select $e'$ to be either $e'_1 e_2$ or $e_1 e'_2$ depending on where the important transition happens and then by one of the two application rules we have $e -> e'$.

      In the second case both $tle(e_1,o_1)$ and $tle(e_2,o_2)$ can send on their respective $o$ after some administrative reductions. By @lem:teoo we know that $e_1$ and $e_2$ are values and as such no important transition exists in those. We know that $tle(e_1,o_1)$ is an abstraction and therefore by #rbtfn("r-abs") we have that $e -> e'$.
    ]
  ]
  #case(of: "Conditional")[
    For conditional we have $e = ifte(e_1,e_2,e_3)$ and must prove that the two parts of operational correspondence hold.
    #case(of: "Soundness")[
      For the first part we have that if $e -> e'$ then there is a $P'$ such that $tle(e,o) =i P'$ and $bim(tle(e',o), P')$. We have three rules for conditionals: #rbtfn("r-if"), #rbtfn("r-ift") and #rbtfn("r-iff"). 
      
      We start by looking at the case for evaluating $e_1$. By our assumption that $(e, tle(e,o)) in R$ we have that $(e_1, tle(e_1,o_1)) in R$ and then if $ifte(e_1,e_2,e_3) -> ifte(e'_1,e_2,e_3)$ by #rbtfn("r-if") we have $tle(e_1,o_1) =i tle(e'_1,o_1)$ and $bim(tle(e_1,o_1), tle(e'_1,o_1))$. We then have that when $tle(e_1,o_1)$ is unguarded we know that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$.

      When $e_1$ has evaluated and a value has been sent on $o_1$ we have one of two possible reductions left. Since $e_1 arrow.not$ we know by @lem:teoo that $e_1$ is a value and then we have either $[n eq.not 0] . tle(e_2,o), tle(e_3,o) -i tle(e_2,o)$ (which can be matched using #rbtfn("r-ift")) or $-i tle(e_3,o)$ (which can be matched using #rbtfn("r-iff")). We then have $tle(e,o) =i P'$ $bim(P', tle(e',o))$. 
    ]
    #case(of: "Completeness")[
      For the second part we have that if $tle(e,o) =i P'$ then there is a $e'$ such that $e -> e'$ and $bim(P', tle(e',o))$. We have two cases to look at.

      First case the $=i$ transition happens inside $tle(e_1,o_1)$. We let $e' = ifte(e'_1,e_2,e_3)$ where $e_1 -> e'_1$. By our assumption that $(e, tle(e,o) in R)$ we have that $(e_1, tle(e_1,o_1)) in R$ which means we know that $bim(P', tle(e',o))$. 

      For the second case we have received values on $o_1$ and therefore by @lem:teoo we know that $e_1$ must be a value. We can then select $e'$ to be either $e_2$ or $e_3$. Depending on how the match concludes we have that either $-i tle(e_2,o_2)$ or $-i tle(e_3,o)$ and given our assumption that $(e, tle(e,o) in R)$ we have that ${(e_2, tle(e_2,o)), (e_3, tle(e_3,o))} subset.eq R$ and then we have $bim(P', tle(e',o))$. 
    ]
  ]
  #case(of: "Map")[
    For map we have $e = map e_1$ and must prove that the two parts of operational correspondence hold. 
    #case(of: "Soundness")[
      For the first part we have that if $e -> e'$ then there is a $P'$ such that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$. 

      For the first case we have that $e_1$ has not yet been evaluated to a tuple. We can then use #rbtfn("r-app2") to take a step. 

      $ #showr(rbutf, "r-app2") $
      
      As #map is a variation of application we can use #rbtfn("r-app2"). By our assumption that $(e, tle(e,o)) in R$ we have that $(e_1, tle(e_1,o_1)) in R$. When $tle(e_1,o_1)$ is unguarded we know that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$.

      For the second case we have that by #rbtfn("r-map") we can take a step and therefore $e_1$ is the tuple $(lambda x.e_lambda, [v_1,...,v_n])$. As this is one of the more complicated cases we will show how this is matched in the translation. First have that $e' = [e_lambda  {x |-> v_1}, ..., e_lambda {x |-> v_n}]$ from #rbtfn("r-map"). From the translation we have:
      
      $ (nu o_1 : ch(t_1)) . (nu h_1 : tl([tau_2])) . tle(e_1,o_1) | 
    receive(o_1, h_2 : t_1) . underbracket(receive(h_2 dot tup, f : tl(tau_1 -> tau_2)\,h_3 : tl([tau_1])),(lambda x.e_lambda, [v_1,...,v_n])). $

    Here we receive the tuple after the unguarded $tle(e_1,o_1)$. Only administrative reductions has happened so far. Next we receive the length of the input array and the values located at each index.
    
    $ underbracket(receive(h_3 dot len, n : Int), "Input array length") . underbracket((nu h_4 : ch(Int\, tl(tau_1)) ) . 
    broad(h_3 dot all,h_4), forall (n,v) in [v_1,...,v_n]) . (nu r_1 : ch(Int) ) . (nu d : ch(Int) ). $

    Next, using #Prepeat, we apply the abstraction to each value and pass it to the #Pcell process to create the new array. Again only administrative reduction has happened. Only when the #Prepeat process has finished will we receive on $d$ which is an important reduction. 
    
      $
    (Prepeat(n,r_1,d) | repl underbracket(receive(h_4, i : Int \,v_1 : tl(tau_1)), "Index & argument") . 
    underbracket(( nu r_2 : ch(tl(tau_2)) ). send(f, v_1\,r_2) . receive(r_2,v_2 : tl(tau_2)), lambda x.e_lambda v_i) \ 
    . receive(r_1, \_ : Int) . Pcell(h_1,i ,v_2, tl(tau_2)) | 
    circle.small.filled receive(d,\_: Int) . send(o, h_1) | repl send(h_1 dot len,n) ) $

    This is our $P'$ and as we output the new updated array we have that $bim(P', tle(e',o))$.
    
    ]
    #case(of: "Completeness")[
      For the second part we have that if $tle(e,o) =i P'$ then there is a $e'$ such that $e -> e'$ and $bim(P', tle(e',o))$.

      We know that $P'$ has received on $circle.filled.small receive(d, \_ : Int)$, and as we are well-typed we know that 
      $tle(e_1,o_1)$ where $ o_1 : ch(@{ch(ch(t_1\,ch(t_2))\,@{ch(Int\, t_1),ch(t_1),ch(Int)})} = tl(((tau_1 -> tau_2), [tau_1]))) $
      
      Then on $P'$ we observe $barb(P', o)$ where $o : ch(@{ch(Int\, t_2),ch(t_2),ch(Int)})$ and $@{ch(Int\, t_2),ch(t_2),ch(Int)} = tl([tau_2])$.
      Therefore $e$ is of the form $map (lambda x.e_lambda, [v_1,dots,v_n])$ and from the observation on $P'$ we have that $lambda x.e_lambda$ is applied to each element of $[v_1,dots,v_n]$.
      

      We set $e' = [e_lambda {x |-> v_1}, ..., e_lambda {x |-> v_n}]$ and we know that $e -> e'$ by #rbtfn("r-map"). Then we have $bim(P', tle(e',o))$.
    ]
  ]
  #case(of: "Iota")[
    For Iota we have $e = iota e_1$ and must prove that the two parts of operational correspondence hold. 
    
    #case(of:"Soundness")[
      For the first part we have that if $e -> e'$ then there is a $P'$ such that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$. 

      Just like #map we have two cases. The first case follows the same argument as #map. 

      For the second case we can take a step by #rbtfn("r-iota") and therefore $e_1$ is an number. Thereby $e' = [0,1,...,n-1]$. Just like #map we will go through the translation. First we create some restriction for the channels the communication will happen on.

      $
      underbracket((nu o_1 : ch(tl(Int))),"Input number") . underbracket((nu r : ch(Int)) . (nu d : ch(Int) ), Prepeat "Process") . \ underbracket((nu h : pch(ch(Int\, Int)\,ch(Int) \, ch(Int))),"Output array") . $

      Next we receive the value on $o_1$ after some administrative reductions. Then the #Prepeat process is started to create the array with each value being its index. Only when the #Prepeat process has finished will we receive on $d$ which is an important reduction.
      
    $
    (tle(e_1,o_1) |  receive(o_1,n : tl(Int)) . (Prepeat(n,r,d) |  repl receive(r, i : Int) .  Pcell(h,i,i) |  circle.small.filled receive(d,  \_ : Int) . \ send(o,h) | send(h . len, n : Int) ))
      $

      We then have our $P'$ and as we output the new array we have that $bim(P', tle(e',o))$.
      
    ]
    #case(of:"Completeness")[
      For the second part we have that if $tle(e,o) =i P'$ then there is a $e'$ such that $e -> e'$ and $bim(P', tle(e',o))$.

      We know that $P'$ has received on $circle.filled.small receive(d, \_ : Int)$, and as we have received on $o_1$ an $n : Int$, $e$ must be a value on the form $n$ after some administrative reductions by @lem:tvoo. We then select $e' = [0,1...,n-1]$ and by #rbtfn("r-iota") we have that $e -> e'$ and $bim(P', tle(e',o))$. 
    ]
  ]
  #case(of: "Size")[
    For Size we have $e = size e_1$ and must prove that the two parts of operational correspondence hold. 
    
    #case(of:"Soundness")[
      For the first part we have that if $e -> e'$ then there is a $P'$ such that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$. 

      Just like #map we have two cases. The first case follows the same argument as #map.

      For the second case we can take a step by #rbtfn("r-size") and therefore $e_1$ is an array. Thereby $e' = n$. In the translation we receive the array handle on $o_1$ and by @lem:tvoo we have that the sub-expression will output on its respective channel after som administrative reductions. We then receive the length of the array on $h dot len$ as $n$ followed by the important reduction and then our $P' = send(n,o)$. We then have that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$.
    ]
    #case(of:"Completeness")[
      For the second part we have that if $tle(e,o) =i P'$ then there is a $e'$ such that $e -> e'$ and $bim(P', tle(e',o))$.

      We have that $P' = send(o,n)$. We know that $P'$ has received on $o_1$ and given we are well-typed that $o_1 : ch(pch(ch(Int\, tl(tau)), ch(tl(tau)), ch(Int))) = tl([tau])$. Therefore $e$ is on the following form: $[v_1,...,v_n]$. We then select $e' = n$ and by #rbtfn("r-size") we have that $e -> e'$ and $bim(P', tle(e',o))$. 
    ]
  ]
]