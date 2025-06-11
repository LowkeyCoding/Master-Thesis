#import "../../Packages/global.typ": *

= Proof of @lem:uniq <app:proof_uniq>

#proof(of:<lem:uniq>)[
  We proceed by using structural induction on $P$.
  #case(of: $null$)[
    Then $fn(null) = fv(null) = bn(null) = bv(null) = emptyset$.
    Therefore all intersections are trivially empty.
  ]
  #case(of: $a$)[
    Then $fn(a) = {a},fv(a) = bn(a) = bv(a) = emptyset$. Since $fn(a) = {a}$ is the only function with a set containing an element all intersections are trivially empty.
  ]
  #case(of: $x$)[
    Then $fv(x) = {x},fn(x) = bn(x) = bv(x) = emptyset$. Since $fv(x) = {x}$ is the only function with a set containing an element all intersections are trivially empty.
  ]
  #case(of: $P | Q$)[
    Then $P = Q | R$ and $
      fn(P) &= fn(Q) union fn(R) \
      fv(P) &= fv(Q) union fv(R) \
      bn(P) &= bn(Q) union bn(R) \
      bv(P) &= bv(Q) union bv(R)
    $ and from our inductive hypothesis we can derive that $f_1(Q) sect f_2(Q) = emptyset$ and $f_1(R) sect f_2(R) = emptyset$. As names and variables are disjoint and unions preserve disjointness we get that $(f_1(Q) union f_1(R)) sect (f_2(Q) union f_2(R)) = emptyset$
    
  ]
  #case(of: $nu a. P$)[
    Then $P = nu a. Q$ and $
      fn(P) &= fn(Q) \\ {a} \
      fv(P) &= fv(Q) \
      bn(P) &= {a} union bn(Q) \
      bv(P) &= bv(Q)
    $ and from our inductive hypothesis we can derive that $f_1(Q) sect f_2(Q)$. From this we get three cases:
    #case(of: $f_1 = "fn and" f_2 = "bn"$)[
      Then $f_1(nu a. Q)$ removes a name $a$ and $f_2(nu a. Q)$ adds a name $a$ to the sets. Therefore it holds that $(f_1(P) \\ {a}) sect( f_2(P) union {a}) = emptyset$.
    ]
    #case(of: $f_1 = "fv and" f_2 = "bv"$)[
      Disjointness holds for $Q$ such that $f_1(Q) sect f_2(Q) = emptyset$.
    ]
    #case(of: $(f_1,f_2) in {("fn","fv"),("bn","bv")}$)[
       Names and variables are disjoint therefore, $f_1(nu a. Q) union f_2(nu a. Q) = emptyset$
    ]
    
  ]
  #case(of: $c(many(x)).P$)[
    Then $P = c(many(x)).Q$ and $
      fn(P) &= fn(c) union fn(Q) \
      fv(P) &= fv(c) union (fn(Q) \\ many(x)) \
      bn(P) &= bn(Q) \
      bv(P) &=  bv(Q)
    $ and from our inductive hypothesis we can derive that $f_1(Q) sect f_2(Q)$. From this we get three cases:
    #case(of: $f_1 = "fv and" f_2 = "bv"$)[
      Then $f_1(P)$ removes a name $a$ and $f_2(P)$ adds a name $a$ to the sets. Therefore it holds that $(f_1(Q) \\ many(x)) sect (many(x) union f_2(Q)) = emptyset$.
    ]
    #case(of: $f_1 = "fn and" f_2 = "bn"$)[
      Disjointness holds for $P$ such that $f_1(P) sect f_2(P) = emptyset$.
    ]
    #case(of: $(f_1,f_2) in {("fn","fv"),("bn","bv")}$)[
       Names and variables are disjoint therefore, $f_1(P) union f_2(P) = emptyset$
    ]
  ]
  #case(of: $send(c,many(T)).P$)[
    Then $P = send(c,many(T)).Q$ and $
      fn(P) &= fn(c) union fn(many(T)) union fn(Q) \
      fv(P) &= fv(c) union fv(many(T)) union fv(Q)) \
      bn(P) &= bn(Q) \
      bv(P) &=  bv(Q)
    $ Follows from the inductive hypothesis and the disjointness of names/variables in $overline(c),many(T),Q$
  ]
  #case(of: $broad(c,many(T)).P$)[
    Similar to send.
  ]
  #case(of: $[T_1 bow T_2]P,Q$)[
    Then $P = [T_1 bow T_2]Q,R$ and $
      fn(P) &= fn(T_1) union fn(T_2) union fn(Q) union fn(R) \
      fv(P) &= fv(T_1) union fv(T_2) union fv(Q) union fv(R) \
      bn(P) &= bn(Q) union bn(R) \
      bv(P) &=  bv(Q) union bv(R) 
    $ Follows from the inductive hypothesis and the disjointness of names/variables in $T_1,T_2,Q,R$
  ]
]

