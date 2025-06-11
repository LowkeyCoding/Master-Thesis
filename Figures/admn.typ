#import "../Packages/global.typ": *

#let EpiAdmRed = {
  grid(
    columns: 3,
    column-gutter: 1em,
    row-gutter: 2em,
    align: bottom + center, 
    
    showr(radmn, "r-admn"),
    showr(radmn, "r-nonadmn"),
    showr(radmn, "r-both"),
  )
}