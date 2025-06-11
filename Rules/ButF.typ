#import "../Packages/tree.typ":*
#import "../Packages/shorthands.typ":*

#let rbutf = (
  r-array: (
    name: "B-Array",
    tree: tree(
      label:"(B-Array) ",
      $[e_1, dots, e_i, dots, e_n] -> [e_1, dots, e'_i, dots e_n]$,
      //$e_i -> e_i\'$,
      $exists i in {1, dots, n}. e_i -> e'_i$,
    )
  ),
  r-tuple: (
    name: "B-Tuple",
    tree: tree(
      label: "(B-Tuple) ",
      $(e_1, dots, e_i, dots, e_n) -> (e_1, dots, e'_i, dots e_n)$,
      $exists i in {1, dots, n}. e_i -> e'_i$,
    )
  ),
  r-index1: (
    name: "B-Index1",
    tree: tree(
      label: "(B-Index1) ",
      $e_1[e_2] -> e'_1[e_2]$,
      $e_1 -> e'_1$,
    )
  ),
  r-index2: (
    name: "B-Index2",
    tree: tree(
      label: "(B-Index2) ",
      $e_1[e_2] -> e_1[e'_2]$,
      $e_2 -> e'_2$,
    )
  ),
  r-index: (
    name: "B-Index",
    tree: tree(
      label: "(B-Index) ",
      $[v_1, ..., v_n][i] -> v_i$,
      $forall i in {1, dots, n}$
    )
  ),
  r-abs: (
    name: "B-Abs",
    tree: tree(
      label: "(B-Abs) ",
       $(lambda x.e) v -> e{x |-> v}$
    )
  ),
  r-app1: (
    name: "B-App1",
    tree: tree(
      label: "(B-App1) ",
      $e_1 e_2 -> e'_1 e_2$,
      $e_1 -> e'_1$,
    )
  ),
  r-app2: (
    name: "B-App2",
    tree: tree(
      label: "(B-App2) ",
      $e_1 e_2 -> e_1  e'_2$,
      $e_2 -> e'_2$,
    )
  ),
  r-if: (
    name: "B-If",
    tree: tree(
      label: "(B-If) ",
      $ifte(e_1, e_2, e_3) -> ifte(e'_1, e_2, e_3)$,
      $e_1 -> e'_1$,
    )
  ),
  r-ift: (
    name: "B-Ift",
    tree: tree(
      label: "(B-Ift) ",
      $ifte(v, e_2, e_3) -> e_2$,
      $v eq.not 0$,
    )
  ),
  r-iff: (
    name: "B-Iff",
    tree: tree(
      label: "(B-Iff) ",
      $ifte(v, e_2, e_3) -> e_3$,
      $v eq 0$,
    )
  ),
  r-bin1: (
    name: "B-Bin1",
    tree: tree(
      label: "(B-Bin1) ",
      $e_1 bin e_2 -> e'_1 bin e_2$,
      $e_1 -> e'_1$,
    )
  ),
  r-bin2: (
    name: "B-Bin2",
    tree: tree(
      label: "(B-Bin2) ",
      $e_1 bin e_2 -> e_1 bin e'_2$,
      $e_2 -> e'_2$,
    )
  ),
  r-bin: (
    name: "B-Bin",
    tree: tree(
      label: "(B-Bin) ",
      $v_1 bin v_2 -> v_3$,
      $v_3 = v_1 bin v_2$
    )
  ),
  r-map: (
    name: "B-Map",
    tree: tree(
      label: "(B-Map) ",
      $map(lambda x.e,[v_1, dots, v_n]) ->  [e{x |-> v_1}, dots, e{x |-> v_n}]$
    )
  ),
  r-iota: (
    name: "B-Iota",
    tree: tree(
      label: "(B-Iota) ",
      $iota n -> [0, 1, dots, n-1]$
    )
  ),
  r-size: (
    name: "B-Size",
    tree: tree(
      label: "(B-Size) ",
      $size [v_1, dots, v_n] -> n$
    )
  ),
)