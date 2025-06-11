#import "../Packages/tree.typ":*
#import "../Packages/shorthands.typ":*
#let rtepi = (
  t-nil: (
    name: "ET-Nil",
    tree: tree(
      label: "(ET-Nil) ",
      $PEnv |- null$
    )
  ),
  t-par: (
    name: "ET-Par",
    tree: tree(
      label: "(ET-Par) ",
      $PEnv |- P | Q$,
      $PEnv |- P$,
      $PEnv |- Q$
    )
  ),
  t-rep: (
    name: "ET-Rep",
    tree: tree(
      label: "(ET-Rep) ",
      $PEnv |- repl P$,
      $PEnv |- P$,
    )
  ),
  t-res: (
    name: "ET-Res",
    tree: tree(
      label: "(ET-Res) ",
      $PEnv |- (nu a: t).P$,
      $DEnv,a:t,CEnv |- P$
    )
  ),
  t-recv: (
    name: "ET-Recv",
    tree: tree(
      label: "(ET-Recv) ",
      $PEnv |- receive(c,  many(x) : t).P $,
      $PEnv |- c : ch(many(t))$,
      $DEnv, many(x) : t, CEnv |- P$,
    )
  ),
  t-send: (
    name : "ET-Send",
    tree: tree(
    label: "(ET-Send) ",
      $PEnv |- send(c, many(T)).P$,
      $PEnv |- c : ch(many(t))$,
      $PEnv |- many(T) : t$,
      $PEnv |- P$
    )
  ),
  t-broad: (
    name: "ET-Broad",
    tree: tree(
      label: "(ET-Broad) ",
      $PEnv |- broad(c, many(T)).P$,
      $PEnv |- c : ch(many(t))$,
      $PEnv |- many(T) : t$,
      $PEnv |- P$
    )
  ),
  t-com: (
    name: "ET-Com",
    tree: tree(
      label: "(ET-Com) ",
      $PEnv |- send(c, many(T)).P | receive(c,many(x) : many(t)).Q$,
      $PEnv |-many(T) : many(t)$,
      
    )
  ),
  t-comb: (
    name: "ET-BCom",
    tree: tree(
      label: "(ET-BCom) ",
      $PEnv |- broad(c,many(T)).Q | receive(c,x_1 : many(t)).P_1 | dots | receive(c,x_n : many(t)).P_n$,
      $PEnv |- many(T) : many(t)$,
    )
  ),
  t-if: (
    name: "ET-Match",
    tree:  tree(
      label: "(ET-Match) ",
      $PEnv |- [T_1 bow T_2]P\,Q$,
      $PEnv |- T_1 : t$,
      $PEnv |- T_2 : t$,
      $PEnv |- P$,
      $PEnv |- Q$,
    )
  ),
  t-comp: (
    name: "ET-Compx",
    tree: tree(
      label: "(ET-Compx) ",
      $PEnv |- u dot x: ch(many(t))$,
      $DEnv |- u : pch(n:i)$,
      $CEnv(u,x) = hh(many(t))$,
      $hh(many(t)) in ell$,
    )
  ),
  t-comp3: (
    name: "ET-Compn",
    tree: tree(
      label: "(ET-Compn) ",
      $PEnv |- u dot n: ch(many(t))$,
      $DEnv |- u : pch(n:i)$,
      $CEnv(n) = hh(many(t))$,
      $hh(many(t)) in ell$,
    )
  ),
  t-comp2: (
    name: "ET-Compn",
    tree: tree(
      label: "(ET-Compn) ",
      $PEnv |- u dot n: ch(many(t))$,
      $DEnv |- u : pch(n:i)$,
      $CEnv(u, n) = hh(many(t))$,
      $hh(many(t)) in ell$,
    )
  ),
  t-bin: (
    name: "ET-Bin",
    tree: tree(
      label: "(ET-Bin) ",
      $PEnv |- T_1 bin T_2 : Int$,
      $PEnv |- T_1 : Int$,
      $PEnv |- T_2 : Int$
    )
  ),
  t-n:(
    name: "ET-N",
    tree: tree(
      label: "(ET-N)",
      $PEnv |- n : Int$
    )
  ),
  t-index:(
    name: "ET-Index",
    tree: tree(
      label: "(ET-Index)",
      $PEnv |- n : t$,
      $CEnv(n) = t$
    )
  ),
  t-u:(
    name: "ET-U",
    tree: tree(
      label: "(ET-U)",
      $PEnv |- u : t$,
      $DEnv (u) = t$
    )
  ),
  s-refl:(
     name: "S-Refl",
    tree: tree(
      label: "(S-Refl)",
      $t lt.eq t'$,
    )
  ),
  s-trans:(
     name: "S-Trans",
    tree: tree(
      label: "(S-Trans)",
      $t lt.eq t''$,
      $t lt.eq t'$,
      $t' lt.eq t''$
    )
  ),
  s-many:(
    name: "S-Many",
    tree: tree(
      label: "(S-Many)",
      $ch(many(t)) lt.eq ch(tp)$,
      $forall i. t_i lt.eq t'_i$
    )
  ),
  s-pre:(
    name: "S-Pre",
    tree: tree(
      label: "(S-Pre)",
      $ch(many(t)) lt.eq pch(tp)$,
      $exists i.ch(many(t)) lt.eq t'_i$
    )
  ),
  s-uwrap:(
    name: "S-UWrap",
    tree: tree(
      label: "(S-UWrap)",
      $tp lt.eq pch(tp)$
    )
  ),
  
)