#import "../../../Packages/global.typ": *

#let rbtfn(x) = shown(rbutf, x)
#let btfn(x) = shown(rbtf, x)
#let repin(x) = shown(repi, x)
#let tepin(x) = shown(rtepi, x)
#let radmnn(x) = shown(radmn,x)
#let ts_e(x) = $#showf(sttrans_e, x) = #showt(sttrans_e, x)$
#let ts_l(x) = $#showf(sttrans_l, x) = #showt(sttrans_l, x)$


== Proof of Theorem 4.1 <app:typeCorrect>
#proof(of: "Soundness")[
  We prove this by induction in the rules used for concluding $e$ is well-typed.
  #case(of: btfn("t-var"))[
    From the #btfn("t-var") rule we know that $e : tau$. From inspection of the translation we have $send(o, x)$ and by the type rules #tepin("t-send") and #tepin("t-u") we have that $o : ch(t)$ where $t = DEnv (x)$. 
    Then we have that $tl(Env) = PEnv$ and $Env(x) : tau$ therefore $DEnv(x) = tl(tau)$ and then it must be that $o : ch(tl(tau))$.
  ]
  #case(of: btfn("t-int"))[
    From the #btfn("t-int") rule we know that $e : Int$. From inspection of the translation we have $send(o,n)$ and by the type rules #tepin("t-send") and #tepin("t-n") we have that $o : ch(t) where t = Int$. By the translation of types we have $tl(Int) = Int$. Therefore $o : ch(tl(tau))$.
    
  ]
  #case(of: btfn("t-abs"))[
    From the #btfn("t-abs") rule we know that $e : (tau_1 -> tau_2)$. From inspection of the translation we have $send(o, h)$ and by the type rule #tepin("t-send") we have $o : ch(t)$ where $t$ is the type of the object we are sending on $o$. From the translation we can see that $h : tl(tau_1 -> tau_2)$. Therefore it must be that $o : ch(tl(tau_1 -> tau_2))$. 
    
  ]
  #case(of: btfn("t-app"))[
    From the #btfn("t-app") rule we know that $e : tau_2$. From inspection of the translation we have an $h : tl(tau_1 -> tau_2) = ch(tl(tau_1)\,ch(tl(tau_2)))$. From the translation we see that we send $v,o$ on $h$ and from that we then have $v: tl(tau_1)$ and $o : ch(tl(tau_2))$. Therefore soundness hold.
    
  ]
  #case(of: btfn("t-index"))[
    From the #btfn("t-index") rule we know that $e : tau$. From inspection of the translation we have $send(o, v)$ and by the type rule #tepin("t-send") we have $o : ch(t)$ where $t$ is the type of the object we are sending on $o$. From the translation we can see that $v : tl(tau)$. Therefore it must be that $o : ch(tl(tau))$. 
     
  ]
  #case(of: btfn("t-bin"))[
     From the #btfn("t-bin") rule we know that $e : Int$. From inspection of the translation we have $send(o, v_1 bin v_2)$ and by the type rule #tepin("t-send") we have $o : ch(t)$ where $t$ is the type of the object we are sending on $o$. From #tepin("t-bin") we have the type of $v_1 bin v_2 : Int$. By the translation of types we have $tl(Int) = Int$. Therefore $o : ch(tl(tau))$.
  ]
  #case(of: btfn("t-if"))[
     From the #btfn("t-if") rule we know that $e : tau$ where both sub-expressions $e_2$ and $e_3$ is of type $tau$. From the induction hypothesis we get that from $tle(e_2, o)$ and $tle(e_3, o)$ that $PEnv(o) = ch(tl(tau))$.  Therefore soundness hold. //From inspection of the translation we have $send(o,?)$ and by the type rule #tepin("t-send") we have $o : ch(t)$ where $t$ is the type of what we are sending on $o$. 
    
  ]
  #case(of: btfn("t-array"))[
    From the #btfn("t-array") rule we know that $e : [tau]$. From inspection of the translation we have $send(o, h)$ and by the type rule #tepin("t-send") we have $o : ch(t)$ where $t$ is the type of the object we are sending on $o$. From the translation we can see that $h : tl([tau])$. Therefore it must be that $o : ch(tl([tau]))$. 
    
  ]
  #case(of: btfn("t-tuple"))[
    From the #btfn("t-tuple") rule we know that $e : (tau_1, ..., tau_n)$. From inspection of the translation we have $send(o, h)$ and by the type rule #tepin("t-send") we have $o : ch(t)$ where $t$ is the type of the object we are sending on $o$. From the translation we can see that $h : tl((tau_1, ..., tau_n))$. Therefore it must be that $o : ch(tl((tau_1, ..., tau_n)))$. 
     
  ]
]

#proof(of: "Completeness")[
  We prove this by induction in the structure of $e$.
  #case(of: $e = x$)[
    We have that $tle(e,o) = (PEnv,P)$ where $P = send(o,x)$. We assume that $DEnv(o) = ch(t)$ where $t = tl(tau)$, therefore we must have that $DEnv tack x : t$. By inspection of the translation of #btf type environment @fig:tlOfBtfTypEnv we have that $DEnv, x : t$ implies $Env, x : tau$ and therefore $Env |- x : tau$. 
    //From the translation we have $send(o,x)$ and $Env tack x : tau$. By #tepin("t-send") we have that $o: ch(t)$ with $t$ being $tl(tau)$. Therefore this trivially hold.
  ]
  #case(of: $e = n$)[
    We have that $tle(e,o) = (PEnv,P)$ where $P = send(o,n)$. We assume that $DEnv(o) = ch(t)$ where $t = tl(tau)$, therefore we must have that $DEnv tack n : t$ and by #tepin("t-n") we have that $t = Int$.
    By inspection of the translation of #btf type environment @fig:tlOfBtfTypEnv and types @fig:tlOfBtfTyp we have that $DEnv, n : Int$ implies $Env, n : Int$ and therefore $Env |- n : Int$. 
    //From the translation we have $send(o,n)$ and $Env tack n : Int$. By #tepin("t-send") and #tepin("t-n") we have that $o: ch(Int)$ with $t$ being $tl(Int)$. Therefore this trivially hold.//translation of types we have that $tl(Int) = Int$. Therefor we must be able to type $e$ under $Int$ for completeness to hold. From #btfn("t-int") we have that $n: Int$ and therefore completeness must hold.
  ]
  #case(of: $e = lambda (x :tau_1).e_1$)[
    We have that $tle(e,o) = (PEnv, P)$ where 
    
    $ P =  (nu h : tl(tau_1 -> tau_2)) . ( send(o,h) |  repl receive(h, x : tl(tau_1)\,r : ch(tl(tau_2))) . tle(e_1,r)) $
    
    We assume that $DEnv(o) = ch(t)$ where $t = tl(tau)$. By inspection of the translation we have that $send(o,h)$ where $h : tl(tau_1 -> tau_2)$ which implies $tau = tau_1 -> tau_2$. Then by the induction hypothesis we get that $tle(e_1,o) = (DEnv',CEnv, P')$ where $DEnv' = DEnv,h: tl(tau_1 -> tau_2),x: tl(tau_1),r:ch(tl(tau_2))$, s.t $Env,x: tau_1 tack e_1 : tau_2$. Therefore by #btfn("t-abs") we get that $Env tack lambda (x :tau_1).e_1 : tau_1 -> tau_2$. 
    
    //From #tepin("t-send") we have that $o: ch(t)$ with $t$ being the type of $h$, and from #tepin("t-u") we have that $h: ch(tl(tau_1)\,ch(tl(tau_2)))$. From the translation of types we have that $ch(tl(tau_1)\,ch(tl(tau_2))) = tl(tau_1 -> tau_2)$. Therefore we must be able to type $e$ under $tau_1 -> tau_2$ for completeness to hold. From #btfn("t-abs") we have that $e: tau_1 -> tau_2$ and therefore completeness must hold.
    
  ]
  #case(of: $e = e_1 e_2$)[ 
    We have that $tle(e,o) = (PEnv, P)$ where 
    
    $ P =  (nu o_1 : ch(tl(tau_1 -> tau_2))) . (nu o_2 : ch(tl(tau_1))) .  (tle(e_1,o_1) | tle(e_2,o_2) | \ receive(o_1,h : tl(tau_1 -> tau_2)) . receive(o_2, v : tl(tau_1)). circle.small.filled send(h, v\, o)) $
    We assume that $DEnv(o) = ch(t)$ where $t = tl(tau)$. By inspection of the translation we have that $send(h,v\,o)$ where $h : tl(tau_1 -> tau_2)$. By inspection of the translation of #btf types @fig:tlOfBtfTyp we have that $h : ch(tl(tau_1), ch(tl(tau_2)))$ this then implies that $o : ch(tl(tau_2))$ and $tau = tau_2$. Then by the induction hypothesis we get that $tle(e_1,o_1) = (DEnv',CEnv',P')$ where $DEnv(o_1) = ch(tl(tau_1->tau_2))$ s.t $Env' tack e_1 : tau_1 -> tau_2$ and $tle(e_2,o_2) = (DEnv'',CEnv'',P'')$ where $DEnv(o_2) = ch(tl(tau_1))$ s.t $Env' tack e_2 : tau_1$. Therefore by #btfn("t-app") we get that $Env tack e_1 e_2 : tau_2$
  // From the translation we have that $send(h, v\,o)$, with $Env tack e_1 : tau_1 -> tau_2$ and $Env tack e_2 : tau_1$. We then know that $h$ is handle to an abstraction where we forward the return channel $o$. Then from the translation of #rbtfn("r-abs") we get that $r : ch(tau_2)$ which is our $o$ that $o: ch(tau_2)$. Therefore we must be able to type $e$ under $tau_2$ for completeness to hold. From #btfn("t-app") we have that $e: tau_2$ and therefore completeness must hold.

  ]
  #case(of: $e = e_1[e_2]$)[
    We have that $tle(e,o) = (Delta, Pi, P)$ where 
    $
    P = (nu o_1 : ch(tl([tau]))) . (nu o_2 : ch(tl(tau))) . tle(e_1,o_1) | tle(e_2,o_2) | receive(o_1, h : tl([tau])) . \ receive(o_2, i : tl(Int)) . receive(h dot i, v : tl(tau)) . circle.small.filled send(o, v)
    $
    
    We assume that $DEnv(o) = ch(t)$ where $t = tl(tau)$. By the induction hypothesis we get that $tle(e_1,o_1) = (DEnv_1,CEnv_1,P_1)$ and $tle(e_2,o_2) = (DEnv_2,CEnv_2,P_2)$ where $DEnv(o_1) = ch(tl([tau]))$ and $DEnv(o_2) = ch(tl(Int))$ s.t $Env tack e_1 : [tau]$ and $Env tack e_2 : Int$. If $P$ is well-typed we get the following well-typed sub-process $h dot i(v : tl(tau)) . circle.small.filled send(o,v)$ and thereby we know the type of the object $o$ carries. From this we get that $t = tl(tau)$ and by #btfn("t-index") we get that $Env |- e_1[e_2] : tau$.

    
    // From the translation we have $send(o,v)$. By #tepin("t-send") we have that $o: ch(t)$ with $t$ being the type of $v$, and from the binding of $v$ we have $v: tl(tau)$. Therefore we must be able to type $e$ under $tau$ for completeness to hold. From #btfn("t-index") we have that $e: tau$ and therefore completeness must hold.
    
  ]
  #case(of: $e = ifte(e_1,e_2,e_3)$)[ 
     We have that $tle(e,o) = (PEnv, P)$ where 
    
    $ P = (nu o_1 : ch(tl(Int))) .  (tle(e_1, o_1) |  receive(o_1, n : tl(Int)) .  circle.small.filled [n eq.not 0] tle(e_2,o), tle(e_3,o)) $ 
    We assume that $DEnv(o) = ch(t)$ where $t = tl(tau)$.
    Then if $P$ is well-typed we also have the following subprocess being well-typed $[n != 0]tle(e_2,o),tle(e_3,o)$ in which both branches outputs on the channel $o$. Then by the induction hypothesis we get that $tle(e_1,o_1) = (DEnv_1,CEnv_1,P_1)$ where $DEnv(o_1) = ch(tl(Int))$ s.t $Env tack e_1 : Int$ and $tle(e_2,o) = (DEnv_2,CEnv_2,P_2)$, $tle(e_3,o) = (DEnv_3,CEnv_3,P_3)$ where $DEnv(o) = ch(tl(tau))$ s.t $Env tack e_2 : tau$ and $Env tack e_3 : tau$. Therefore by #btfn("t-if") we get that $Env tack ifte(e_1,e_2,e_3) : tau$.
    
  // From the translation we have $[n != 0]tle(e_2,o),tle(e_3,o)$ with $Env tack e_2 : tau$ and $Env tack e_3 : tau$. Then by the induction hypothesis we have that $tle(e_2,o)$ where $o : ch(tl(tau))$ and $tle(e_3,o)$ where $o : ch(tl(tau))$. Therefore this trivially hold.
  ]
  
  #case(of: $e = e_1 bin e_2$)[
    We have that $tle(e,o) = (PEnv, P)$ where 
    $ P = (nu o_1 : ch(tl(Int))) . (nu o_2 : ch(tl(Int))) .  (tle(e_1,o_1) | tle(e_2,o_2) |  receive(o_1, v_1 : tl(Int)). \ receive(o_2, v_2 : tl(Int)) .circle.small.filled send(o, v_1 bin v_2) ) $ 
    We assume that $DEnv(o) = ch(t)$ where $t = tl(tau)$. By the induction hypothesis we get that $tle(e_1,o_1) = (DEnv_1,CEnv_1,P_1)$ and $tle(e_2,o_2) = (DEnv_2,CEnv_2,P_2)$ where $DEnv(o_1) = ch(tl(Int))$ and $DEnv(o_2) = ch(tl(Int))$ s.t $Env tack e_1 : Int$ and $Env tack e_2 : Int$. Then by inspection of the translation we have that $send(o, v_1 bin v_2)$ and by #tepin("t-bin") we have that $DEnv,v_1:Int,v_2:Int,CEnv tack v_1 bin v_2 : Int$ which implies $tau = Int$. Therefore by #btfn("t-bin") we get that $Env tack e_1 bin e_2: Int$.
    //From the translation we have $send(o, v_1 bin  v_2)$ and by #tepin("t-send") we have that $o: ch(t)$ with $t$ being the type of $v_1 bin v_2$. From #tepin("t-bin") we have that $v_1 bin v_2: Int$. from the translation of types we have that $tl(Int) = Int$ and therefore we must be able to type $e$ under $Int$ for completeness to hold. From #btfn("t-bin") we have that $e: Int$ and therefore completeness must hold.
    
  ]
  #case(of: $e = [e_1, dots, e_n]$)[
    We have that $tle(e,o) = (PEnv, P)$ where
    
    $ P = (nu o_1 : ch(tlt(tau,e_1))). dots . (nu o_n : ch(tlt(tau,e_n))) . (nu h : tlt([tau], e)) . \ (product_(i=1)^(n) tle(e_i,o_i) | receive(o_1,v_1 : tlt(tau, e_1)). dots . receive(o_n,v_n : tlt(tau,e_n)) . \ (product_(i=1)^(n) Pcell(h, i-1, v_i, tlt(tau,e_i)) | send(h dot len, n) | send(o, h) )) $

    We assume that $DEnv(o) = ch(t)$ where $t = tl(tau)$. By the induction hypothesis we get that $forall i in 1..n . tle(e_i,o_i) = (DEnv_i,CEnv_i,P_i)$ where $DEnv(o_i) = ch(tl(tau_1))$ such that $Env tack e_i : tau_1$. If $P$ is well-typed the following sub-process in the translation must be well-typed as well: $send(o,h)$. From the restriction $(nu h : tl([tau_1]))$ we get the type of the object that $o$ carries. From this we get that $t = tl([tau_1])$. We must therefore have that $Env |- e : [tau_1]$ and by #btfn("t-array") we get that $Env |-  [e_1, dots, e_n] : [tau_1]$.
    
    //From the translation of arrays we have $send(o,h)$ and by #tepin("t-send") we have that $o: ch(t)$ with $t$ being the type of $h$. From the restriction on $h$ we have that $h: pch(ch(Int\, tl(tau))\, ch(tl(tau))\, ch(Int)) = tl([tau])$. Therefore we must be able to type $e$ under $[tau]$ for completeness   to hold. From #btfn("t-array") we have that $e: [tau]$ and therefore completeness must hold.
    
  ]
  #case(of: $e = (e_1, dots, e_n)$)[
    We have that $tle(e,o) = (PEnv, P)$ where
    
    $ P = (nu o_1 : ch(tlt(tau_1,e_1))) . dots . (nu o_n : ch(tlt(tau_n,e_n)))  . \ (product_(i=1)^(n) tle(e_i,o_i) | receive(o_1,v_1 : tlt(tau_1,e_1)). space dots space . receive(o_n,v_n : tlt(tau_n,e_n)) . \ nu (h : tlt((tau_1,dots,tau_n), e)) . (repl send(h dot tup,v_1\, dots\, v_n) | send(o,h) )) $

    We assume that $DEnv(o) = ch(t)$ where $t = tl(tau)$. By the induction hypothesis we get that $forall i in 1..n . tle(e_i,o_i) = (DEnv_i,CEnv_i,P_i)$ where $DEnv(o_i) = ch(tl(tau_i))$ such that $Env tack e_i : tau_i$. If $P$ is well-typed the following sub-process in the translation must also be well-typed: $send(o,h)$. From the restriction $(nu h : tl((tau_1 , dots , tau_n)))$ we get the type of the object that $o$ carries. From this we get that $t = tl((tau_1 , dots , tau_n))$. We must therefore have that $Env |- e : (tau_1 , dots , tau_n)$ and by #btfn("t-tuple") we get that $Env |-  (e_1, dots, e_n) : (tau_1 , dots , tau_n)$.
    
    //From the translation of tuples we have $send(o,h)$ and by #tepin("t-send") we have that $o: ch(t)$ with $t$ being the type of $h$. From the restriction on $h$ we have that $h: pch(ch(tl(tau_1)\,dots\,tl(tau_n))) = tl((tau_1, ..., tau_n))$. Therefore we must be able to type $e$ under $(tau_1, ..., tau_n)$ for completeness to hold. From #btfn("t-tuple") we have that $e: (tau_1, ..., tau_n)$ and therefore completeness must hold.
  ]
  #case(of: $e = size e_1$)[
    We have that $tle(e, o) = (PEnv, P)$ where
    $ P = (nu o_1 : ch(tl([tau_1]))) . (tle(e_1,o_1) | \ receive(o_1,h : tl([tau_1])) .  receive(h dot len, n : Int) . circle.small.filled send(o, n)) $ 
    We assume that $DEnv(o) = ch(t)$ where $t = tl(tau)$. By the induction hypothesis we get that $tle(e_1,o_1) = (DEnv_1,CEnv_1,P_1)$ where $DEnv(o_1) = ch(tl([tau_1]))$ s.t $Env tack e_1 : [tau_1]$. Then if $P$ is well-typed the following sub-process from the translation must be well-typed: $receive(h dot len, n : Int) . circle.small.filled send(o, n))$. From this we know the type of object that $o$ carries from which we get that $t = Int$ and therefore we must have that $Env |- e : Int$. From @def:icontext we get the type of $size : [tau_1] -> Int$ and by #btfn("t-app") we get that $Env tack size e_1 : Int$.
    
    //By the binding $receive(h dot len , n : Int)$ we get that $n : Int$ and from #tepin("t-send") and #tepin("t-n") we have that $o: ch(Int)$. From the translation of types we have that $tl(Int) = Int$. Therefor we must be able to type $e$ under $Int$ for completeness to hold. By the definition of $Env$ we have that the initial environment is $Env union sum$ where $sum(size): Int$. 
  ]
  #case(of: $e = iota e_1$)[
    We have that $tle(e, o) = (PEnv, P)$ where

    $ P = (nu o_1 : ch(tl(Int))) . (nu r : ch(Int)) . (nu d : ch(Int) ) . \
    (nu h : pch(ch(Int\, Int)\,ch(Int) \, ch(Int))) . \
    (tle(e_1,o_1) |  receive(o_1,n : tl(Int)) . (Prepeat(n,r,d) | \ repl receive(r, i : Int) .  Pcell(h,i,i) |  circle.small.filled receive(d,  \_ : Int) . \ send(o,h) | send(h . len, n : Int) )) $

    We assume that $DEnv(o) = ch(t)$ where $t = tl(tau)$. By the induction hypothesis we that $tle(e_1,o_1) = (DEnv_1, CEnv_1, P_1)$ where $DEnv(o_1) = ch(Int)$ such that $Env |- e_1 : Int$. Then if $P$ is well-typed the following sub-process is also well-typed: $send(o,h)$. From the restriction $(nu h :pch(ch(Int\, Int)\,ch(Int) \, ch(Int)))$ which is the type of the object that $o$ carries. From the translation of types know that $pch(ch(Int\, Int)\,ch(Int) \, ch(Int)) = tl([Int])$ and we must therefore have $Env |- e : [Int]$. From @def:icontext we get the type of $iota : Int -> [Int]$ and by #btfn("t-app") we get that $Env tack iota e_1 : [Int]$.
    
    //From the translation we have $send(o,h)$ and by #tepin("t-send") we have that $o: ch(t)$ with $t$ being the type of $h$. From the restriction on $h$ we have $h: pch(ch(Int\, Int)\,ch(Int) \, ch(Int))$. From the translation of types we have $pch(ch(Int\, Int)\,ch(Int) \, ch(Int)) = tl([tau])$ where $tl(tau) = Int$. Therefor we must be able to type $e$ under $[Int]$ for completeness to hold. By the definition of $Env$ we have that the initial environment is $Env union sum$ where $sum(iota): [Int]$.
    
  ]
  #case(of: $e = map e_1$)[
    We have that $tle(e, o) = (PEnv, P)$ where
    
    $ P = (nu o_1 : ch(tl((tau_1 -> tau_2, [tau_1]))) ) . (nu h_1 : tl([tau_2]) ) . (tl(e_1)_o_1 |  \ 
    receive(o_1, h_2 : tl((tau_1 -> tau_2, [tau_1]))) . receive(h_2 dot tup, f : tl(tau_1 -> tau_2)\,h_3 : tl([tau_1])) . \
    receive(h_3 dot len, n : Int) . (nu h_4 : ch(Int\, tl(tau_1)) ) . \
    broad(h_3 dot all,h_4) . (nu r_1 : ch(Int) ) . (nu d : ch(Int) ). \
    (Prepeat(n,r_1,d) | repl receive(h_4, i : Int \,v_1 : tl(tau_1)) . \
    ( nu r_2 : ch(tl(tau_2)) ). send(f, v_1\,r_2) . receive(r_2,v_2 : tl(tau_2)) \ 
    . receive(r_1, \_ : Int) . Pcell(h_1,i ,v_2, tl(tau_2)) | \
    circle.small.filled receive(d,\_: Int) . send(o, h_1) | repl send(h_1 dot len,n) ) ) $

    We assume that $DEnv(o) = ch(t)$ where $t = tl(tau)$. By the induction hypothesis we that $tle(e_1,o_1) = (DEnv_1, CEnv_1, P_1)$ where $DEnv(o_1) = ch(tl((tau_1 -> tau_2, [tau_1])))$ such that $Env |- e_1 : (tau_1 -> tau_2, [tau_1])$. Then if $P$ is well-typed the following sub-process must well-typed: $send(o,h_1)$. From the restriction we get $(nu h_1: tl([tau_2]))$ which is the type of the object that $o$ carries and therefore we must have that $Env |- e : [tau_2]$. From @def:icontext we get the type of $map : (tau_1 -> tau_2, [tau_1]) -> [tau_2]$ and by #btfn("t-app") we get that $Env tack map e_1 : [tau_2]$.

    
    //From the translation we have $send(o,h_1)$ and by #tepin("t-send") we have that $o: ch(t)$ with $t$ being the type of $h_1$. From the restriction on $h_1$ we have that $h_1 : tl([tau_2])$. Therefor we must be able to type $e$ under $[tau_2]$ for completeness to hold. By the definition of $Env$ we have that the initial environment is $Env union sum$ where $sum(map): [tau_2]$. 
  ]
]
