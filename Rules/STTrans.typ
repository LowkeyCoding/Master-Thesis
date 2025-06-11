#import "../Packages/shorthands.typ":*

#let sttrans_l = (
    /*array: (
    from: $tle([e_1, dots, e_n],o)$,
    to: $(nu len_h : hh(Int)). \ (nu o_1 : ch(tlt(tau,e_1))). dots . (nu o_n : ch(tlt(tau,e_n))) . (nu h : tlt([tau], e)) . \ (product_(i=1)^(n) tle(e_i,o_i) | receive(o_1,v_1 : tlt(tau, e_1)). dots . receive(o_n,v_n : tlt(tau,e_n)) . \ (product_(i=1)^(n) Pcell(h, i-1, v_i, tlt(tau,e_i)) | send(h dot len_h, n) | send(o, h) )) $,
    where: $&where \ &Env tack [e_1, dots, e_n] : [tau]  \ & forall i in {1,dots,n}.Env tack e_i : tau$
  ),*/
  tuple: (
    from: $tle((e_1, dots, e_n),o)$,
    to: $(nu o_1 : ch(tlt(tau_1,e_1))) . dots . (nu o_n : ch(tlt(tau_n,e_n)))  . \ (product_(i=1)^(n) tle(e_i,o_i) | receive(o_1,v_1 : tlt(tau_1,e_1)). space dots space . receive(o_n,v_n : tlt(tau_n,e_n)) . \ (nu h : tlt((tau_1,dots,tau_n), e)) . (repl send(h dot tup,v_1\, dots\, v_n) | send(o,h) ))$,
    where: $&where \ &Env tack (e_1, dots, e_n) : (tau_1,dots,tau_n) \ & forall i in {1,dots,n}.Env tack e_i : tau_i \ & CEnv = (CEnv_1 union dots union CEnv_n) \ &, (h,tup) : hh(tl(tau_1),dots,tl(tau_n))$
  ),
  array: (
    from: $tle([e_1, dots, e_n],o)$,
     to: $(nu o_1 : ch(tlt(tau,e_1))). dots . (nu o_n : ch(tlt(tau,e_n))) . (nu h : tlt([tau], e)) . \ (product_(i=1)^(n) tle(e_i,o_i) | receive(o_1,v_1 : tlt(tau, e_1)). dots . receive(o_n,v_n : tlt(tau,e_n)) . \ (product_(i=1)^(n) Pcell(h, i-1, v_i, tlt(tau,e_i)) | send(h dot len, n) | send(o, h) )) $,
    where: $&where \ &Env tack [e_1, dots, e_n] : [tau]  \ & forall i in {1,dots,n}.Env tack e_i : tau \ & CEnv = (CEnv_1 union dots union CEnv_n) \ & ,(h,len) : hh(Int) \ & , (h,all) : hh(ch(Int\, tau)) \ & ,(h,1) : hh(tl(tau)) \ &#h(3.1em) dots.v \ & ,(h,n) : hh(tl(tau))$
  )
)
#let sttrans_o = (
  size: (
    from: $tle(size, o)$,
    to: //$(nu h : ch(I) . ( send(o,h) | \ repl receive(h, x : tl(tau_1)\,r : ch(tl(tau_2))) . tle(e_1,r))$,
    $(nu o_1 : ch(tl([tau]))) . (tle(e_1,o_1) | \ receive(o_1,h : tl([tau])) .  receive(h dot len, n : Int) . circle.small.filled send(o, n))$,
    where: $&where \ &Env tack size e_1 : Int \ &Env tack e_1 : [tau]$
  ),
  itoa: (
    from: $tle(iota e_1,o)$,
    to: $(nu o_1 : ch(tl(Int))) . (nu r : ch(Int)) . (nu d : ch(Int) ) . \
    (nu h : pch(hh(Int\, Int)\,hh(Int))) . \
    (tle(e_1,o_1) |  receive(o_1,n : tl(Int)) . (Prepeat(n,r,d) | \ repl receive(r, i : Int) .  Pcell(h,i,i,Int) |  circle.small.filled receive(d,  \_ : Int) . \ send(o,h) | send(h dot len, n) ))$,
    where: $&where \ &Env tack iota e_1 : [Int] \ &Env tack e_1 : Int$
  ),
  // o_1: receive args
  // h_1: out array
  // h_2: tuple handle
  // h_3: in array
  // h_4: in array value handle
  // r_1: repeater reciever
  // r_2: function return channel
  // v_1: in array value
  // v_2: out array value
  map: (
    from: $tle(map e_1,o)$,
    to: $
    (nu o_1 : ch(t_1) ) . (nu h_1 : tl([tau_2]) ) . (tl(e_1)_o_1 |  \ 
    receive(o_1, h_2 : t_1) . receive(h_2 dot tup, f : tl(tau_1 -> tau_2)\,h_3 : tl([tau_1])) . \
    receive(h_3 dot len, n : Int) . (nu h_4 : ch(Int\, tl(tau_1)) ) . \
    broad(h_3 dot all,h_4) . (nu r_1 : ch(Int) ) . (nu d : ch(Int) ). \
    (Prepeat(n,r_1,d) | repl receive(h_4, i : Int \,v_1 : tl(tau_1)) . \
    ( nu r_2 : ch(tl(tau_2)) ). send(f, v_1\,r_2) . receive(r_2,v_2 : tl(tau_2)) \ 
    . receive(r_1, \_ : Int) . Pcell(h_1,i ,v_2, tl(tau_2)) | \
    circle.small.filled receive(d,\_: Int) . send(o, h_1) | repl send(h_1 dot len,n) ) )$,
    where: $&where \ &Env tack e_1 : (tau_1 -> tau_2, [tau_1]) \ &t_1 = tl((tau_1 -> tau_2, [tau_1]))$ 
  ),
)

#let sttrans_t = (
  t-int: (
    from: $tl(Int)$,
    to: $Int$,
    where: $$
  ),
  t-array: (
    from: $tl([tau])$,
    to: $pch(n: n, hh(Int, tl(tau)), hh(tl(tau)), hh(Int))$,
    where:$$
  ),
  t-tuple: (
    from: $tl((tau_1,dots, tau_n))$,
    to: $pch(n: n, hh(tl(tau_1),dots,tl(tau_n)))$,
    where:$$
  ),
  t-abs: (
    from: $tl(tau_1 -> tau_2)$,
    to: $ch(tl(tau_1)\, ch(tl(tau_2)))$,
    where: $$
  ),
)

#let sttrans_te = (
  te-empty: (
    from: $tl(emptyset)$,
    to: $emptyset$,
    where: $$,
  ),
  te-env: (
    from: $tl(#[$Env, x : tau$])$,
    to: $tl(Env), x : tl(tau)$,
    where: $$,
  )
)

#let sttrans_e = (
  var: (
    from: $tle(x,o)$,
    to: $send(o,x)$,
    where: $where Env |- x : tau$
  ),
  num: (
    from: $tle(n,o)$,
    to: $send(o,n)$,
    where: $where Env |- n : Int$
  ),
  lambda: (
    from: $tle(lambda (x : tau_1) . e_1,o)$,
    to: $(nu h : tl(tau_1 -> tau_2)) . ( send(o,h) | \ repl receive(h, x : tl(tau_1)\,r : ch(tl(tau_2))) . tle(e_1,r))$,
    where: $&where \ &Env tack lambda (x : tau_1) . e : tau_1 -> tau_2 \ &Env tack e : tau_2$ 
  ),
  app: (
    from: $tle(e_1 e_2,o)$,
    to: $(nu o_1 : ch(tl(tau_1 -> tau_2))) . (nu o_2 : ch(tl(tau_1))) . \ (tle(e_1,o_1) | tle(e_2,o_2) | \ receive(o_1,h : tl(tau_1 -> tau_2)) . receive(o_2, v : tl(tau_1)). circle.small.filled send(h, v\, o))$,
    where: $&where \ &Env tack e_1 : tau_1 -> tau_2 \ &Env tack e_2 : tau_1$
  ),
  index: (
    from: $tle(e_1[e_2],o)$,
    to: $(nu o_1 : ch(tl([tau]))) . ( nu o_2 : ch(tl(Int))) . \  (tle(e_1,o_1) | tle(e_2,o_2) | receive(o_1, h : tl([tau])) . \ receive(o_2, i : tl(Int)) .  receive(h dot i,  v : tl(tau)) . circle.small.filled  send(o, v)))$,
    where: $&where \ &Env tack e_1 : [tau] \ &Env tack e_2 : Int $
  ),
  ifte: (
    from: $tle(ifte(e_1,e_2,e_3),o)$,
    to: $(nu o_1 : ch(tl(Int))) .  (tle(e_1, o_1) | \ receive(o_1, n : tl(Int)) .  circle.small.filled [n eq.not 0] tle(e_2,o), tle(e_3,o))$,
    where: $&where \ &Env tack e_1 : Int \ &Env tack e_2 : tau \ &Env tack e_3 : tau$
  ),
  bin: (
    from: $tle(e_1 bin e_2,o)$,
    to: $(nu o_1 : ch(tl(Int))) . (nu o_2 : ch(tl(Int))) . \ (tle(e_1,o_1) | tle(e_2,o_2) |  receive(o_1, v_1 : tl(Int)). \ receive(o_2, v_2 : tl(Int)) .circle.small.filled send(o, v_1 bin v_2) )$,
    where: $&where \ &Env tack e_1 : Int \ &Env tack e_2 : Int$
  ),
)