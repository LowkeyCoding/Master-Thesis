#import "../Packages/tree.typ": *
#import "../Packages/shorthands.typ": *

#let rwrong = (
  rw-send: (
    name: "ER-Send",
    tree: tree(
      label: "(ER-Send) ",
      $PEnv |- send(c,many(T)).P -t wrong$,
      $DEnv (c) = ch(many(t_1))$,
      $PEnv |- many(T) : many(t_2)$,
      $many(t_1) eq.not many(t_2)$
    )
  ),  
  rw-broad: (
    name: "ER-Broad",
    tree: tree(
      label: "(ER-Broad)",
      $PEnv |- broad(c,many(T)).P attach(arrow.long, tl: [] , tr:[], t: :c) wrong$,
      $DEnv (c) = ch(many(t_1))$,
      $PEnv |- many(T) : many(t_2)$,
      $many(t_1) eq.not many(t_2)$
    )
  ),  
  rw-recv: (
    name: "ER-Recv",
    tree: tree(
      label: "(ER-Recv)",
      $PEnv |- receive(c, many(x) : many(t_2)) .P -t wrong$,
      $DEnv (c) = ch(many(t_1))$,
      
      $many(t_1) eq.not many(t_2)$
    )
  ),
  rw-par1: (
    name: "ER-Par1",
    tree: tree(
      label: "(ER-Par1)",
      $PEnv |- P | Q -t wrong$,
      $PEnv |- P -t wrong$,
    )
  ), 
  rw-par2: (
    name: "ER-Par2",
    tree: tree(
      label: "(ER-Par2)",
      $PEnv |- P | Q -t wrong$,
      $PEnv |- Q -t wrong$,
    )
  ), 
   rw-rep: (
    name: "ER-Rep",
    tree: tree(
      label: "(ER-Rep) ",
      $PEnv |- ! P -t wrong$,
      $PEnv |- P -t wrong$,
    )
  ),
  rw-res: (
    name: "ER-Res",
    tree: tree(
      label: "(ER-Res) ",
      $PEnv |- (nu a:t).P -q wrong$,
      $P -q wrong ("temp")$,
    )
  ),
  rw-match: (
    name: "ER-Match",
    tree: tree(
      label: "(ER-Match) ",
      $PEnv |- [T_1 bow T_2]P,Q -t wrong$,
      $PEnv |- T_1: t_1$,
      $PEnv |- T_2: t_2$,
      $t_1 eq.not t_2$
    )
  ),
  rw-bin1: (
    name: "ER-Bin1",
    tree: tree(
      label: "(ER-Bin1) ",
      $PEnv |- T_1 bin T_2 -t wrong$,
      $PEnv |- T_1 : t $,
      $t eq.not Int$,
    )
  ),
  rw-bin2: (
    name: "ER-Bin2",
    tree: tree(
      label: "(ER-Bin2) ",
      $PEnv |- T_1 bin T_2 -t wrong$,
      $PEnv |- T_2 : t$,
      $t eq.not Int$,
    )
  ),
  rw-comp1: (
    name: "ER-Compx1",
    tree: tree(
      label: "(ER-Compx1) ",
      $PEnv |- u dot x -t wrong$,
      $DEnv (u) eq.not pch()$,
    )
  ),
  rw-comp2: (
    name: "ER-Compx2",
    tree: tree(
      label: "(ER-Compx2) ",
      $PEnv |- u dot x -t wrong$,
      $DEnv (u) eq pch()$,
      $CEnv (u,x) eq.not hh(many(t))$,
    )
  ),
  rw-comp3: (
    name: "ER-Compx3",
    tree: tree(
      label: "(ER-Compx3) ",
      $PEnv |- u dot x -t wrong$,
      $DEnv (u) eq pch()$,
      $CEnv (u,x) = hh(many(t))$,
      $hh(many(t)) in.not ell$,
    )
  ),
  rw-comp4: (
    name: "ER-Compn1",
    tree: tree(
      label: "(ER-Compn1) ",
      $PEnv |- u dot n -t wrong$,
      $DEnv (u) eq.not pch()$,
    )
  ),
  rw-comp5: (
    name: "ER-Compn2",
    tree: tree(
      label: "(ER-Compn2) ",
      $PEnv |- u dot x -t wrong$,
      $DEnv (u) eq pch()$,
      $CEnv (u,n) eq.not hh(many(t))$,
    )
  ),
  rw-comp6: (
    name: "ER-Compn3",
    tree: tree(
      label: "(ER-Compn3) ",
      $PEnv |- u dot n -t wrong$,
      $DEnv (u) eq pch()$,
      $CEnv (u,n) = hh(many(t))$,
      $hh(many(t)) in.not ell$,
    )
  ),
)

