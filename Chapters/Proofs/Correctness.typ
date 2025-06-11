#import "../../Packages/global.typ": *

#let rbtfn(x) = shown(rbutf, x)
#let btfn(x) = shown(rbtf, x)
#let repin(x) = shown(repi, x)
#let tepin(x) = shown(rtepi, x)
#let radmnn(x) = shown(radmn,x)
#let ts_e(x) = $#showf(sttrans_e, x) = #showt(sttrans_e, x)$
#let ts_l(x) = $#showf(sttrans_l, x) = #showt(sttrans_l, x)$


=== Proof of Correctness
For the corollary to hold we must prove the two theorems: @th:typeCorrectness and @th:correctness. 

We start with a subset of the proof of @th:typeCorrectness. The full proof can be found in @app:typeCorrect. 

#proof(of: <th:typeCorrectness>)[
  We prove soundness by induction on the rules used for concluding $e$ is well-typed, and for completeness we prove it by induction on the structure of $e$.
  #case(of: "Application")[
    For application we have $e = e_1 e_2$ and must prove the soundness and completeness of the translation.
    #case(of: "Soundness")[
      From the #btfn("t-app") rule we know that $e : tau_2$. From inspection of the translation we have an $h : tl(tau_1 -> tau_2) = ch(tl(tau_1)\,ch(tl(tau_2)))$. From the translation we see that we send $v,o$ on $h$ and from that we then have $v: tl(tau_1)$ and $o : ch(tl(tau_2))$. Therefore soundness hold.
    ]
    #case(of: "Completeness")[
      We have that $e = lambda (x :tau_1).e_1$ and $tle(e,o) = (PEnv, P)$ where 
      
      $ P =  (nu h : tl(tau_1 -> tau_2)) . ( send(o,h) |  repl receive(h, x : tl(tau_1)\,r : ch(tl(tau_2))) . tle(e_1,r)) $
      
      We assume that $DEnv(o) = ch(t)$ where $t = tl(tau)$. By inspection of the translation we have that $send(o,h)$ where $h : tl(tau_1 -> tau_2)$ which implies $tau = tau_1 -> tau_2$. Then by the induction hypothesis we get that $tle(e_1,o) = (DEnv',CEnv, P')$ where $DEnv' = DEnv,h: tl(tau_1 -> tau_2),x: tl(tau_1),r:ch(tl(tau_2))$, s.t $Env,x: tau_1 tack e_1 : tau_2$. Therefore by #btfn("t-abs") we get that $Env tack lambda (x :tau_1).e_1 : tau_1 -> tau_2$. 
    ]
  ]
]

For @th:correctness we will show the proof of behavioral correctness for application. The full proof of @th:correctness can be found in @app:behaveCorrect.

#proof(of: <th:correctness>)[
  Let $cal(B)$ be the set of all #btf programs and let $R$ be the the following relation $R={(e,tle(e,o)) | e in cal(B), o "fresh"}$. We show that $R$ is an administrative operational correspondences. As per @def:opcor we only consider pairs where $e -> e'$ and where $tle(e,o)$ contains $circle.small.filled$. 
  #case(of: "Application")[
    For application we have $e = e_1 e_2$ and must prove that the two parts of operational correspondence hold. 
    #case(of: "Soundness")[
      For the first part we have that if $e -> e'$ then there is a $P'$ such that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$. There are two cases for when $e -> e'$: One when the sub-expressions can take a step and one when they cannot. 

      For the first case we have that there are two application rules for the sub-expressions $e_1$ and $e_2$ to take a step: #rbtfn("r-app1") and #rbtfn("r-app2"). By our assumption that $(e, tle(e,o)) in R$ we have that $(e_1, tle(e_1,o_1)) in R$. The same holds for $e_2$. When $tle(e_1,o_1)$ and $tle(e_2,o_2)$ is unguarded we know that $tle(e,o) =i P'$ and $bim(P', tle(e',o))$.

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
]
