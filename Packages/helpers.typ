#import "@preview/drafting:0.2.1": *
#import "Yoinks/theorems.typ": *
#import "Yoinks/colorbox.typ": *
#import "Yoinks/equate.typ": * 


#let showr = (r,rn) => r.at(rn).at("tree")
#let shown = (r,rn) => "(" + r.at(rn).at("name") +")"
#let dive
#let clean_ts(body) = if body.has("children") { body.children.filter(it => it != linebreak()).map(it => if it.has("body") {clean_ts(it.body)} else {if it == [:] {$#h(0.25em)it #h(0.25em)$} else {$it$}}).join()} else { body }
#let showf = (r,rn) => r.at(rn).at("from")
#let showt = (r,rn, strip: true) => if strip {clean_ts(r.at(rn).at("to").body)} else {r.at(rn).at("to").body}
#let showw = (r,rn) => clean_ts(r.at(rn).at("where").body)


#let translation-grid-s(r) = align(center,grid(
  columns: (auto,auto,auto),
  align: (right,center,left),
  column-gutter: 0.5em,
  row-gutter: 1.5em,
  ..for rn in r.keys() {
    (
      r.at(rn).at("from"),
      $=$,
      r.at(rn).at("to"),
   )
  }
))
#let translation-grid(r) = {
grid(
  columns: (auto,auto,7fr,4fr),
  align: (right,center,left,left),
  column-gutter: 0.5em,
  row-gutter: 1.5em,
  ..for rn in r.keys() {
    (
      r.at(rn).at("from"),
      $=$,
      r.at(rn).at("to"),
      r.at(rn).at("where")
   )
  }
)}
#let translation-grid-v(r) = {
  
  grid(
  columns: (auto,auto,1fr),
  align: (right,center,left,right),
  column-gutter: 0.5em,
  row-gutter: 1.5em,
  ..for rn in r.keys() {
    (
      r.at(rn).at("from"),
      $=$,
      block[#r.at(rn).at("to") \
      #r.at(rn).at("where")]
   )
  }
)}


#let cn(name) = {
  show regex("[A-Z]\. "): v => []
  show regex(",.*$"): v => [ et. al]
  [#cite(name, form: "author")]
}

#let definition = thmbox(
  "definition",
  "Definition",
  base: "heading",
  base_level: 1,
  // take only the first level from the base
  // stroke: rgb("#000000") + 1pt
)

#let example = thmbox(
  "example",
  "Example",
  base: "heading",
  base_level: 1,
)

#let get_ch() = context int(counter(heading).get())
#let theorem = thmbox(
  "theorem",
  "Theorem",
  base: "heading",
  base_level: 1,
  stroke: rgb("#000000") + 1pt
)

#let lemma = thmbox(
  "lemma",
  "Lemma",
  base: "heading",
  base_level: 1,
  stroke: rgb("#000000") + 1pt
)

#let corollary = thmbox(
  "corollary",
  "Corollary",
  base: "heading",
  base_level: 1,
  stroke: rgb("#000000") + 1pt
)


#let enote = {
  let rect(stroke: none, fill: none, width: 0pt, content) = {
    set text(0.9em)
    colorbox(
      color: "red",
      radius: 2pt,
      width: width
    )[#content]
  }
  
  margin-note.with(rect: rect, stroke: red)
}



#let wnote = {
  let rect(stroke: none, fill: none, width: 0pt, content) = {
    set text(0.9em)
    colorbox(
      color: "orange",
      radius: 2pt,
      width: width
    )[#content]
  }
  
  margin-note.with(rect: rect, stroke: orange)
}

#let qnote(content) = {
  let rect(stroke: none, fill: none, width: 0pt, content) = {
    set text(0.9em)
    colorbox(
      color: "purple",
      radius: 2pt,
      width: width
    )[#content]
  }
  
  margin-note.with(rect: rect, stroke: orange)
}

#let note = {
  let rect(stroke: none, fill: none, width: 0pt, content) = {
    set text(0.9em)
    colorbox(
      color: "gray",
      radius: 2pt,
      width: width
    )[#content]
  }
  
  margin-note.with(rect: rect, stroke: gray)
}

#let ienote(content) = {
    colorbox(
      color: "red",
      radius: 2pt,
      width: auto
    )[#content]
}



#let iwnote(content) = {
    colorbox(
      color: "orange",
      radius: 2pt,
      width: auto
    )[#content]
}

#let inote(content) = {
    colorbox(
      color: "gray",
      radius: 2pt,
      width: auto
    )[#content]
}

#let iqnote(content) = {
    colorbox(
      color: "purple",
      radius: 2pt,
      width: auto
    )[#content]
}

#let eqn = (body) => {
  set math.equation(numbering: "(1.1)")
  equate(breakable: true, sub-numbering: true, number-mode: "line")[#body]
}
#let eqr = (ref) => equate(ref)

#let tref = label => context{
    
    let it = query(label).last()
    let thms = query(selector(<meta:thmenvcounter>).after(it.location()))
    let number = thmcounters.at(thms.first().location()).at("latest")
    [#it.supplement #numbering(it.numbering, ..number)]
}
