#import "../Packages/global.typ":*

#let EpiSyntax = {
    grid(
    columns: 3,
    column-gutter: 1.5em,
    row-gutter: 1.5em,
    align: top + right,
    stroke: 0pt,
    $ P,Q,R, dots ::=& null \
       & P | Q \
       & repl P \
       & A.P \
       & circle.small.filled P \
       & nu a.P\
       &[T_1 bow T_2] P, Q 
    $,
    $ A ::= & send(c, many(T)) \ 
       & receive(c, many(x)) \
       & broad(c, many(T)) 
      $
    ,
    $ c ::=& a \
        & x \
        & x dot l \
        & a dot l 
     $,
    $
      l ::=& n \
        & x \
        & all \
        & len \
        & tup
    $,$
      T ::=& n \
        &a \
        &x \
        &T dot.circle T 
    $
  )
}
#let TEpiSyntax = {
    grid(
    columns: 2,
    column-gutter: 1.5em,
    row-gutter: 1.5em,
    stroke: 0pt,
    $ P,Q,R, dots ::=& null \
       & P | Q \
       & repl P \
       & A.P \
       & (nu a: t).P \
       &[T_1 bow T_2] P, Q \
       & Sbranch(c^p, {l_1:P_1, dots l_n:P_n}) \
       & choice(c^p, l.P)
    $,
    $ A ::= & ssend(c, T_1:t_1\, dots\,T_n:t_n) \ 
       & sreceive(c^p, x_1^p_1\, dots\,x_n^p_n  ) \
       & sbroad(c,  T_1:t_1\, dots\,T_n:t_n) 
      $
    ,
    $ c ::=& a \
        & x 
     $,$
      T ::=& n \
        &a \
        &x \
        &T dot.circle T 
    $
  )
}

// #let EpiStructCong = {
//   grid(
//     columns: (5em, 10em, 5em, 10em),
//     column-gutter: (1em, 3em,1em,),
//     $ &"(Rename)" \ 
//       &"(Par-"null")" \
//       &"(Par-A)" \
//       &"(Par-B)" 
//     $,
//     $
//       &P == P' \
//       &P | null == P \
//       &P |(Q | R) == (P | Q) | R\
//       &P | Q == Q | P 
//     $,
//     $ 
//       &"(Replicate)" \
//       &"(New-"null")" \
//       &"(New-A)" \
//       &"(New-B)"
//     $,
//     $
//       & !P == P | !P \
//       & nu x.null == null \
//       & nu x. nu y.P == nu y.nu x.P \
//       & P | nu x.Q == nu x.(P | Q) \
//       &  "when" x in.not "fv"(P) union "fn"(P)
//     $
//   )
// }

#let StructCong = {
  grid(
    columns: (5em, 10em, 5em, 10em),
    column-gutter: (1em, 3em,1em,),
    $ 
      & shown(rstructcong ,"screname") \
      & shown(rstructcong ,"scparn") \
      & shown(rstructcong ,"scpara") \
      & shown(rstructcong ,"scparb") 
    $,
    $
      & showr(rstructcong ,"screname") \
      & showr(rstructcong ,"scparn") \
      & showr(rstructcong ,"scpara") \
      & showr(rstructcong ,"scparb") 
    $,
    $ 
      & shown(rstructcong ,"screpli") \
      & shown(rstructcong ,"scnewn") \
      & shown(rstructcong ,"scnewa") \
      & shown(rstructcong ,"scnewb") 
    $,
    $
      & showr(rstructcong ,"screpli") \
      & showr(rstructcong ,"scnewn") \
      & showr(rstructcong ,"scnewa") \
      & showr(rstructcong ,"scnewb") 
    $
  )
}


#let EpiRed = {grid(
    columns: 2,
    column-gutter: 2em,
    row-gutter: 2em,
    align: top + left,
    grid.cell(colspan: 2, align: center)[#showr(repi, "r-com")],
    grid.cell(colspan: 2, align: center)[#showr(repi, "r-broad")],
    showr(repi, "r-par"),
    showr(repi, "r-bpar"),
    showr(repi, "r-res1"),
    showr(repi, "r-res2"),
    showr(repi, "r-then"),
    showr(repi, "r-else"),
    grid.cell(colspan: 2, align: center)[#showr(repi, "r-struct")]
  )}