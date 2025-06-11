#import "Packages/global.typ": *
#import "@preview/i-figured:0.2.4": *
// #set text(lang: "gb")
// #set-page-properties(margin-left: 2.5cm)
#set par(justify: true)
#set heading(numbering: "1.1")
#show: thmrules
#show: ligatures

/*
#show heading.where(level: 1): h => {
    pagebreak(weak: true) 
    set text(size: 24pt)
    [#counter(heading).display() #h.body \ ]
    v(1em, weak: true)
}
*/

#show heading: it => {
  v(0.05cm)
  it
  v(0.05cm)
}

#include "Chapters/Resume.typ"

#import "Setup/template.typ": *
#import "Packages/global.typ": *

// #include "Chapters/Resume.typ"

#import "Chapters/abstract.typ": abstract
// Take a look at the file `template.typ` in the file panel
// to customize this template and discover how it works.
#show: project.with(
  meta: (
    title: "A Type Safe Translation of a Functional Array Language to a Process Calculus",
    theme: "Semantics and type systems",
    project_period: "Spring Semester 2025",
    project_group: "cs-25-sv-10-01",
    participants: (
      (name: "Daniel Vang Kleist", email: "dkleis20@student.aau.dk"),
      (name: "Loke Walsted", email: "lwalst20@student.aau.dk"),
    ),
    supervisor: (
      (name: "Hans Hüttel", email: "hans@cs.aau.dk"),
    ),
    date: datetime.today().display()
  ),
  // Insert your abstract after the colon, wrapped in brackets.
  // Example: `abstract: [This is my abstract...]`
  abstract: abstract,
  department: "Computer Science",
)

// Modify Equation references
// Equation 1 -> (1)
#show ref: it => {
  let eq = math.equation
  let el = it.element
  if el != none and el.func() == eq {
    // Override equation references.
    link(el.location(),numbering(
      el.numbering,
      ..counter(eq).at(el.location())
    ))
  } else {
    // Other references as usual.
    it
  }
}

/*#set ref(supplement: it => {
  if it.func() == heading and it.depth == 1 {
    "Chapter"
  } else {
    it.supplement
  }
})*/



/*
#set par.line(
  numbering: n => text(red)[#n]
)
*/

// Ensure that inline equations dont overlap with the lines above and below.
// The other alternative is scaling however that makes it harder to read.
#show math.equation.where(block: false): it => {
  //set text(bottom-edge: "bounds")
  //block(breakable:false,it)
  //map.with(x:true)
  context map_state.update(move(raw("map")))
  context tup_state.update(move(raw("tup")))
  text(bottom-edge: "bounds",it)
  context tup_state.update(raw("tup"))
  context map_state.update(raw("map"))
}

#let holllllllllup = counter("kkljdskljskjldsdskjlkidj")
#set heading(supplement: "Chapter")
#show heading.where(level: 1): it => {
  let kinds = query(figure).map(fig => fig.kind).dedup()
  for kind in kinds {
    counter(figure.where(kind: kind)).update(0)
  }
  it
}
// Remove numbering from ==== sections
#show heading.where(level: 4): it =>[
    #block(it.body)
]

#set figure(kind: image, numbering: num => context str(counter(heading).get().at(0)) + "." + str(num))

// Insert Chapters here
#include "Chapters/Introduction.typ"

= Preliminaries <ch:Prelim>
#include "Chapters/Prelim/ButF.typ"
#include "Chapters/Prelim/Epi.typ"
#include "Chapters/Prelim/Translation.typ"

= A Typed Setting <ch:typed_setting>
#include "Chapters/BtF.typ"
#include "Chapters/Proofs/BtFSoundness.typ"
#include "Chapters/TEpi.typ"
// TEpi soundness
= Translation and Correctness <ch:tlAndCorrect>
#include "Chapters/TranslationBtfTEpi.typ"
#include "Chapters/Correctness.typ"
#include "Chapters/Conclusion.typ"

// Typed translation
// TELpi 
// TELpi soundness
// BltF 
// BltF soundness 
// Linear Typed translation

//
#bibliography("Bibliography.bib")<pageend>
#pagebreak(weak: true)
#set page(numbering: "I")
#set heading(numbering: "A.1", supplement: "Appendix")
#counter(page).update(1)
#counter(heading).update(0)
#thmcounters.update((
    "counters": ("heading": ()),
    "latest": ()
  ))

// Insert Appendix here
// #show: appendix 

//#include "Chapters/Appendix/Proof_lemma_1.typ"

// Butf
= Appendix for Preliminaries 
#include "Chapters/Appendix/Prelim/Butf_defs.typ"
#include "Chapters/Appendix/Prelim/Butf_semantics.typ"
#include "Chapters/Appendix/Prelim/Epi_defs.typ"


// btf
= Proofs About the Type System for #btf

#include "Chapters/Appendix/btf/Inversion.typ"
#include "Chapters/Appendix/btf/Weakening.typ"
#include "Chapters/Appendix/btf/Substitution.typ"
#include "Chapters/Appendix/btf/Preservation.typ"
#include "Chapters/Appendix/btf/Progress.typ"

// tepi
#include "Chapters/Appendix/WrongProc.typ"

= Proofs About the Type System for #tepi

#include "Chapters/Appendix/tepi/WeakningTerm.typ"
#include "Chapters/Appendix/tepi/WeakningProcess.typ"
#include "Chapters/Appendix/tepi/StrengtheningTerm.typ"
#include "Chapters/Appendix/tepi/StrengtheningProcess.typ"
#include "Chapters/Appendix/tepi/TypeCong.typ"
#include "Chapters/Appendix/tepi/SubstitutionTerm.typ"
#include "Chapters/Appendix/tepi/SubstitutionProcess.typ"
#include "Chapters/Appendix/tepi/SubjectReduction.typ"
#include "Chapters/Appendix/tepi/TypeSafety.typ"

// Correctness
= Proofs for the Translation of #btf to #tepi

#include "Chapters/Appendix/trans/prgBehave.typ"
#include "Chapters/Appendix/trans/PreserveSub.typ"
#include "Chapters/Appendix/trans/GarbageProcess.typ"
#include "Chapters/Appendix/trans/GarbageCollect.typ"
#include "Chapters/Appendix/trans/tvoo.typ"
#include "Chapters/Appendix/trans/teoo.typ"

#include "Chapters/Appendix/trans/TypeCorrectness.typ"
#include "Chapters/Appendix/trans/BehaveCorrectness.typ"


