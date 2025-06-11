#import "../Packages/global.typ": *

#let TEpiRules = {
  grid(
    columns: 2,
    column-gutter: 1em,
    row-gutter: 2em,
    align: bottom + left,
    showr(rtepi, "t-nil"),
    showr(rtepi, "t-par"),
    showr(rtepi, "t-rep"),
    showr(rtepi, "t-res"),
    showr(rtepi, "t-send"),
    showr(rtepi, "t-recv"),
    showr(rtepi, "t-broad"),
    // showr(rtepi, "t-com"),
    // showr(rtepi, "t-comb"),
    // {},
    showr(rtepi, "t-if"),
  )
}

#let TEpiTermRules = {
  grid(
    columns: 2,
    column-gutter: 1em,
    row-gutter: 2em,
    align: bottom + center, 
    
    showr(rtepi, "t-n"),
    //showr(rtepi, "t-index"),
    showr(rtepi, "t-u"),
    showr(rtepi, "t-bin"),
    showr(rtepi, "t-comp"),
    grid.cell(colspan:2,showr(rtepi, "t-comp2")),
    //showr(rtepi, "t-comp3"),
  )
}

#let TEpiSyntax = {
    grid(
    columns: 2,
    column-gutter: 1.5em,
    row-gutter: 1.5em,
    align:top + left,
    stroke: 0pt,
    $ P,Q,R, dots ::=& null \
       & P | Q \
       & repl P \
       & A.P \
       & circle.small.filled P \
       & (nu a: t).P\
       &[T_1 bow T_2] P, Q 
    $,
    $ A ::= & send(c, many(T)) \ 
       & receive(c, many(x) : many(t)) \
       & broad(c, many(T)) 
      $
    ,
    $ c ::=& a \
        & x \
        & c dot T
     $,$
      T ::=& n \
        &a \
        &x \
        &T dot.circle T 
    $
  )
}