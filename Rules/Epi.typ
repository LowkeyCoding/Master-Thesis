#import "../Packages/tree.typ":*
#import "../Packages/shorthands.typ":*

#let repi = (
  r-com: (
    name: "E-Com",
    tree: tree(
      label: "(E-Com) ",
      $send(c,many(T)).P|receive(c,many(x)).Q -t P | Q rn(many(x),many(T))$
    )
  ),
  r-par: (
    name: "E-Par",
    tree: tree(
      label: "(E-Par1) ",
      $P | Q -t P' | Q$,
      $P -t P'$,
    )
  ),
  r-bpar: (
    name: "E-Par2",
    tree: tree(
      label: "(E-Par2) ",
      $P | Q -b P' | Q$,
      $c in.not Q$,
      $P -b P'$,
    )
  ),
  r-res1: (
    name: "E-Res1",
    tree: tree(
      label: "(E-Res1) ",
      $nu a.P -q nu a.P'$,
      $P -q P'$,
      $q eq.not :a$,
    )
  ),
  r-res2: (
    name: "E-Res2",
    tree: tree(
      label: "(E-Res2) ",
      $nu a.P -t nu a.P'$,
      $P -b P'$,
      $a in c$,
    )
  ),
  r-struct: (
    name: "E-Struct",
    tree: tree(
      label: "(E-Struct) ",
      $P -q P' quad$,
      $P == Q quad$,
      $Q -q Q'$,
      $P' == Q'$,
    )
  ),
  r-else: (
    name: "E-Else",
    tree: tree(
      where: $"if" T_1 bow.not T_2$,
      label: "(E-Else) ",
      $[T_1 bow T_2]P\,Q -t Q$
    )
  ),
  r-then: (
    name: "E-Then",
    tree: tree(
      where: $"if" T_1  bow T_2$,
      label: "(E-Then) ",
      $[T_1 bow T_2]P\,Q -t P $
    )
  ),
  r-broad: (
    name: "E-Broad",
    tree: tree(label: "(E-Broad) ",
     $ broad(c,many(T)).Q |receive(c,many(x_1)).P_1|dots|receive(c,many(x_n)).P_n -b  Q | P_1 rn(many(x_1),many(T)) | dots | P_n rn(many(x_n),many(T))$
    )
  )
)