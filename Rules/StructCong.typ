#import "../Packages/shorthands.typ":*

#let rstructcong = (
  screname: (
    name: "Rename",
    tree: $P == P' "by" alpha"-conversion"$
  ),
  scparn: (
    name: $"Par-"null$,
    tree: $P | null == P$
  ),
  scpara: (
    name: "Par-A",
    tree: $P |(Q | R) == (P | Q) | R$
  ),
  scparb: (
    name: "Par-B",
    tree: $P | Q == Q | P $
  ),
  screpli: (
    name: "Replicate",
    tree: $!P == P | !P$
  ),
  scnewn: (
    name: $"New-"null$,
    tree: $nu a.null == null$
  ),
  scnewa: (
    name: "New-A",
    tree: $nu a. nu b.P == nu b.nu a.P$
  ),
  scnewb: (
    name: "New-B",
    tree: $ P | nu a.Q == nu a.(P | Q) \
           & "when" a in.not fv(P) union fn(P)$
  ),
)