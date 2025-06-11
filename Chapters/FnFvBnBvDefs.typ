#import "../Packages/global.typ": *

#definition("Free names of channels")[
    $
      fn(a) &= {a} \
      fn(x) &= emptyset \
      fn(a dot l) &= {a} \
      fn(x dot l) &= emptyset \
    $
]<def:fnc>

#definition("Free names of terms")[
  $
    fn(n) &= emptyset \
    fn(a) &= {a} \
    fn(x) &= emptyset \
    fn(T_1 bin T_2) &= fn(T_1) union fn(T_2) \
  $
]<def:fnt>

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

#definition("Free variables of labels")[
  $
     fv(n) &= emptyset \
     fv(x) &= {x} \
     fv(all) &= emptyset \
     fv(len) &= emptyset \
     fv(tup) &= emptyset
  $
]<def:fvl>

#definition("Free variables of channels")[
    $
      fv(a) &= emptyset \
      fv(x) &= {x} \
      fv(a dot l) &= fv(l) \
      fv(x dot l) &= {x} union fv(l) \
    $
]<def:fvc>

#definition("Free variables of terms")[
  $
    fv(n) &= emptyset \
    fv(a) &= emptyset \
    fv(x) &= {x} \
    fv(T_1 bin T_2) &= fv(T_1) union fv(T_2) \
  $
]<def:fvt>

#definition("Freee variables of processes")[
  $ 
    fv(null) &= emptyset  \
    fv(P | Q) &= fv(P) union fv(Q) \
    fv(!P) &= fv(P) \
    fv(nu a.P) &= fn(P) \
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

/*#lemma("Uniquness of bound/free variables and names")[
  Given a #epi process $P$ and two functions $f_1,f_2 in {"fn","fv","bn","bv"}$ where $f_1 eq.not f_2$ then $f_1(P) sect f_2(P) = emptyset$
]<lem:uniq>*/
