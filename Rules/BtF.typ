#import "../Packages/tree.typ":*
#import "../Packages/shorthands.typ":*

#let rbtf = (
  t-int: (
    name: "BT-Int",
    tree: tree(
      label: "(BT-Int) ",
      $Env |- n : Int$
    )
  ),
  t-var: (
    name: "BT-Var",
    tree: tree(
      label: "(BT-Var) ",
      $Env |- x : tau$,
      $Env (x) = tau$
    )
  ),
  t-bin: (
    name: "BT-Bin",
    tree: tree(
      label: "(BT-Bin) ",
      $Env |- e_1 bin e_2 : Int$,
      $Env |- e_1 : Int$,
      $Env |- e_2 : Int$,
      $Env |- bin : Int -> Int -> Int$,
    )
  ),
  t-if: (
    name: "BT-If",
    tree: tree(
      label: "(BT-If)",
      $Env |- ifte(e_1,e_2,e_3) : tau$,
      $Env |- e_1 : Int$,
      $Env |- e_2 : tau$,
      $Env |- e_3 : tau$
    )
  ),
  t-array: (
    name: "BT-Array",
    tree: tree(
      label: "(BT-Array)",
      $Env |- [e_1, dots, e_n]: [tau]$,
      $forall i in {1, dots, n} Env |- e_i : tau$,
    )
  ),
  t-tuple: (
    name: "BT-Tuple",
    tree: tree(
      label: "(BT-Tuple)",
      $Env |- (e_1, dots, e_n): (tau_1, dots, tau_n)$,$forall i in {1, dots, n} #h(0.5em) Env |- e_i : tau_i$
    )
  ),
  t-index: (
    name: "BT-Index",
    tree: tree(
      label: "(BT-Index)",
      $Env |- e_1[e_2] : tau$,
      $Env |- e_1 : [tau]$,
      $Env |- e_2 : Int$
    )
  ),
  t-abs: (
    name: "BT-Abs",
    tree: tree(
      label: "(BT-Abs)",
      $Env |- (lambda x:tau_1). e: tau_1 -> tau_2$,
      $Env,(x: tau_1) |- e : tau_2$
    )
  ),
  t-app: (
    name: "BT-App",
    tree: tree(
      label: "(BT-App)",
      $Env |- e_1 e_2 : tau_2$,
      $Env |- e_1: tau_1 -> tau_2$,
      $Env |- e_2: tau_1$
    )
  )
)