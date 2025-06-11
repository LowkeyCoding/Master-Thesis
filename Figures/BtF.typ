#import "../Packages/global.typ": * 


#let ButFTypeRules = {
grid(
  columns: 2,
  column-gutter: 1em,
  row-gutter: 2em,
  align: bottom + left,
  showr(rbtf, "t-int"),
  showr(rbtf, "t-var"),
  showr(rbtf, "t-bin"),
  showr(rbtf, "t-if"),
  showr(rbtf, "t-array"),
  showr(rbtf, "t-tuple"),
  showr(rbtf, "t-index"),
  showr(rbtf, "t-abs"),
  grid.cell(colspan:2,align:center,showr(rbtf, "t-app")),
)

}
