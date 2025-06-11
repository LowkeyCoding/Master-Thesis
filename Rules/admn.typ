#import "../Packages/tree.typ":*
#import "../Packages/shorthands.typ":*

#let radmn = (
  r-admn: (
    name: "Adm",
    tree: tree(
      label: "(Admn) ",
      $P -a P' $,
      $P -t P'$
    )
  ),
   r-nonadmn: (
    name: "NonAdmn",
    tree: tree(
      label: "(NonAdm) ",
      $circle.small.filled P -i P' $,
      $P -> P'$
    )
  ),
   r-both: (
    name: "Both",
    tree: tree(
      label: "(Both) ",
      $P -> P'$,
      $P attach(arrow.long, t: s) P'$,
      $s in {circle.small, circle.small.filled}$
    )
  ),
)