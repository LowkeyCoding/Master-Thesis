#import "@preview/curryst:0.5.0": rule, prooftree
#let tree(where:none, ..arguments) = {
  if where != none {
    grid(
      columns: 2,
      column-gutter: 1em,
        prooftree.with(vertical-spacing: 0.4em)(rule(..arguments)),
        where
    )
  } else {
    prooftree.with(vertical-spacing: 0.4em)(rule(..arguments))
  }
}