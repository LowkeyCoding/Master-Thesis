#import "../Packages/global.typ": *

#let ButFSemantics = {
  grid(
    columns: 2,
    column-gutter: 2em,
    row-gutter: 2em,
    align: bottom + left,
    grid.cell(colspan: 2, align: center)[#showr(rbutf, "r-array")],
    grid.cell(colspan: 2, align: center)[#showr(rbutf, "r-tuple")],
    showr(rbutf, "r-index1"),
    showr(rbutf, "r-index2"),
    showr(rbutf, "r-index"),
    showr(rbutf, "r-abs"),
    showr(rbutf, "r-app1"),
    showr(rbutf, "r-app2"),
    grid.cell(colspan: 2, align: center)[#showr(rbutf, "r-if")],
    showr(rbutf, "r-ift"),
    showr(rbutf, "r-iff"),
    showr(rbutf, "r-bin1"),
    showr(rbutf, "r-bin2"),
    showr(rbutf, "r-bin"),
    showr(rbutf, "r-iota"),
    grid.cell(colspan: 2, align: center)[#showr(rbutf, "r-size")],
    grid.cell(colspan: 2, align: center)[#showr(rbutf, "r-map")],

  ) 
}

#let reducedButfSemantics = {
  grid(
    columns: 2,
    column-gutter: 2em,
    row-gutter: 2em,
    align: bottom + left,  

    showr(rbutf, "r-index1"),
    showr(rbutf, "r-index2"),
    showr(rbutf, "r-index"),
    showr(rbutf, "r-iota"),
    grid.cell(colspan: 2, align: center)[#showr(rbutf, "r-size")],
    grid.cell(colspan: 2, align: center)[#showr(rbutf, "r-map")],
  )
}