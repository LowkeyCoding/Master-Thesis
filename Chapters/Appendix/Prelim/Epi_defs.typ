#import "../../../Packages/global.typ": *

== #epi Definitions <app:epi_defs>
#grid(
  columns: 2,
  [#definition("Free names of channels")[
    $
      fn(a) &= {a} \
      fn(x) &= emptyset \
      fn(a dot l) &= {a} \
      fn(x dot l) &= emptyset \
    $
]<def:fnc>],
  [#definition("Free names of terms and channels")[
  $
    fn(n) &= emptyset \
    fn(a) &= {a} \
    fn(x) &= emptyset \
    fn(T_1 bin T_2) &= fn(T_1) union fn(T_2) \
  $
]<def:fnt>]
)




#definition("Free names of processes")[
  $ 
    fn(null) &= emptyset  \
    fn(P | Q) &= fn(P) union fn(Q) \
    fn(!P) &= fn(P) \
    fn(nu a.P) &= fn(P) \\ {a} \
    fn(send(c,many(T)).P) &= fn(c) union fn(T) union fn(P) \
    fn(broad(c,many(T)).P) &= fn(c) union fn(T) union fn(P) \
    fn(receive(c,many(x))) &= fn(c) union fn(P) \
    fn([T_1 bow T_2]P\,Q) &= fn(T_1) union fn(T_2) union fn(P) union fn(Q) \
  $
]<def:fnp>


#grid(
  columns: 2,
  [
    #definition("Free variables of labels")[
  $
     fv(n) &= emptyset \
     fv(x) &= {x} \
     fv(all) &= emptyset \
     fv(len) &= emptyset \
     fv(tup) &= emptyset
  $
]<def:fvl>
  ],
  [
    #definition("Free variables of channels")[
    $
      fv(a) &= emptyset \
      fv(x) &= {x} \
      fv(a dot l) &= fv(l) \
      fv(x dot l) &= {x} union fv(l) \
    $
]<def:fvc>
  ],
  grid.cell(colspan: 2, align: center)[#box(width:50%,[#definition("Free variables of terms")[
  $
    fv(n) &= emptyset \
    fv(a) &= emptyset \
    fv(x) &= {x} \
    fv(T_1 bin T_2) &= fv(T_1) union fv(T_2) \
  $
]<def:fvt>])
]
)






#definition("Freee variables of processes")[
  $ 
    fv(null) &= emptyset  \
    fv(P | Q) &= fv(P) union fv(Q) \
    fv(!P) &= fv(P) \
    fv(nu a.P) &= fv(P) \
    fv(send(c,many(T)).P) &= fv(c) union fv(T) union fv(P) \
    fv(broad(c,many(T)).P) &= fv(c) union fv(T) union fv(P) \
    fv(receive(c,many(x))) &= fv(c) union fv(P) \
    fv([T_1 bow T_2]P\,Q) &= fv(T_1) union fv(T_2) union fv(P) union fv(Q) \
  $
]<def:fvp>

#definition("Bound names of processes")[
  $
    bn(null) &= emptyset  \
    bn(P | Q) &= bn(P) union bn(Q) \
    bn(!P) &= bn(P) \
    bn(nu a.P) &= {a} union bn(P) \
    bn(send(c,many(T)).P) &= bn(P) \
    bn(broad(c,many(T)).P) &= bn(P) \
    bn(receive(c,many(x))) &= bn(P) \
    bn([T_1 bow T_2]P\,Q) &= bn(P) union bn(Q) \
  $
]<def:bnp>

#definition("Bound variables of processes")[
  $
    bv(null) &= emptyset  \
    bv(P | Q) &= bv(P) union bv(Q) \
    bv(!P) &= bv(P) \
    bv(nu a.P) &= bv(P) \
    bv(send(c,many(T)).P) &= bv(P) \
    bv(broad(c,many(T)).P) &= bv(P) \
    bv(receive(c,many(x))) &= many(x) union bv(P) \
    bv([T_1 bow T_2]P\,Q) &= bv(P) union bv(Q) \
  $
]<def:bvp>

#grid(
  columns: 2,
  [
    #definition("Substitution of labels")[
  $
     n rn(T_1,T_2)&= n \
     x rn(T_1,T_2)&= cases(
        T_2 &"if" x=T_1,
        x &"otherwise"
      ) \
     all rn(T_1,T_2) &= all \
     len rn(T_1,T_2) &= len \
     tup rn(T_1,T_2) &= tup
  $
]<def:sub-epi-l>
  ],
  [
    #definition("Substitution of channels")[
      $
      a rn(T_1,T_2)&= cases(
        T_2 &"if" a=T_1,
        a &"otherwise"
      ) \
      x rn(T_1,T_2)&= cases(
        T_2 &"if" x=T_1,
        x &"otherwise"
      ) \
      (a dot T) rn(T_1,T_2)&=   cases(
        T_2 dot (T rn(T_1,T_2)) &"if" a = T_1,
        a dot (T rn(T_1,T_2)) &"otherwise"
      )  \
      (x dot T') rn(T_1,T_2)&=  cases(
        T_2 dot (T rn(T_1,T_2)) &"if" x = T_1,
        x dot (T rn(T_1,T_2)) &"otherwise"
      ) \
    $
]<def:sub-epi-c>
  ],
  grid.cell(colspan: 2, align: center)[#box(width:50%,[#definition("Substitution of terms and channels")[
    $
    n rn(T_1,T_2) &= n \
    a rn(T_1,T_2) &= cases(
        T_2 &"if" a=T_1,
        a &"otherwise"
      ) \
    x rn(T_1,T_2)&= cases(
        T_2 &"if" x=T_1,
        x &"otherwise"
      ) \
    (T_3 bin T_4) rn(T_1,T_2) &= T_3 rn(T_1,T_2) bin T_4 rn(T_1,T_2) \
  $
]<def:sub-epi-t>])
]
)






#definition("Substitution of processes")[
  #grid(
    columns: (auto,1em,auto,),
    align: (right,center,left,),
    column-gutter: 0.5em,
    row-gutter: 1em,
    $null rn(T_1,T_2)$,$=$,$null$,
    $(P | Q) rn(T_1,T_2)$,$=$,$P rn(T_1,T_2) | Q rn(T_1,T_2)$,
    $!P rn(T_1,T_2)$, $=$,$!(P rn(T_1,T_2))$,
    $(nu a. P) rn(T_1,T_2)$, $=$, $cases(&nu a. (P rn(T_1,T_2)) &#h(1em) "if" a in.not fn(T_1) union fn(T_2),
    &nu b. (P rn(a,b) rn(T'_1 ,T'_2)) &#h(1em) "otherwise where" b in.not f_n)$,
    $$,$$,$where f_n =fn(T_1) union fn(T_2) union fn(P)\ T'_1 = T_1 rn(a,b) "and" T'_2 = T_2 rn(a,b)$,
    $(send(c,many(T)).P) rn(T_1,T_2)$,$=$,$(overline(c) rn(T_1,T_2)) angle.l (many(T)rn(T_1,T_2)) angle.r .(P rn(T_1,T_2))$,
    $(broad(c,many(T)).P) rn(T_1,T_2)$,$=$,$(overline(c)#h(-0.1pt):#h(-0.1pt) rn(T_1,T_2)) (angle.l many(T) rn(T_1,T_2) angle.r) .(P rn(T_1,T_2))$,
    $(c(many(x)).P) rn(T_1,T_2)$,$=$,$cases(
      &c rn(T_1,T_2)(many(x)).P rn(T_1,T_2) &#h(1em) "if" many(x) sect fv(T_1) union fv(T_2) = emptyset,
      &c rn(T'_1,T'_2)(many(y)).P rn(many(x),many(y)) rn(T'_1,T'_2) &#h(1em)"otherwise where" many(y) sect f_v = emptyset)$,
      $$,$$,$&where f_v = (fv(T_1) union fv(T_2) union fv(P)) \ & T'_1 = T_1 rn(many(x),many(y)) "and" T'_2 = T_2 rn(many(x),many(y))$,
      $([T_1 bow T_2]P,Q) rn(T_1,T_2)$,$=$,$bow T_2 rn(T_1,T_2)]P rn(T_1,T_2), Q rn(T_1,T_2)$
    )
]<def:sub-epi-p>
