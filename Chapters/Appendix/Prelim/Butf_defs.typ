#import "../../../Packages/global.typ": *

== #butf Definitions <app:butf_defs>
#definition("Free variables of " + butf)[
  #grid(
    columns: (auto, 1em,auto),
    align: (right,center,left),
    column-gutter: 0.5em,
    row-gutter: 1em,
    $"FV"(x)$, $=$, ${x}$,
    $"FV"(lambda x. e)$, $=$, $"FV"(e)\\ {x}$, 
    $"FV"(e_1 e_2)$, $=$, $"FV"(e_1) union "FV"(e_2)$, 
    $"FV"(e_1 bin e_2)$, $=$, $"FV"(e_1) union "FV"(e_2)$, 
    $"FV"([e_1,dots,e_n])$, $=$, $"FV"(e_1) union dots union "FV"(e_n)$, 
    $"FV"((e_1,dots,e_n))$, $=$, $"FV"(e_1) union dots union "FV"(e_n)$, 
    $"FV"(ifte(e_1,e_2,e_3))$, $=$, $"FV"(e_1) union "FV"(e_2)union "FV"(e_3)$, 
    $"FV"(map e_1)$, $=$, $"FV"(e_1)$, 
    $"FV"(iota e_1)$, $=$, $"FV"(e_1)$, 
    $"FV"(size e_1)$, $=$, $"FV"(e_1)$, 
  )
]


#definition("Substitution of " + butf)[
  #grid(
    columns: (auto, 1em,auto,auto),
    align: (right,center,left,left),
    column-gutter: (0.5em,0.5em,1em),
    row-gutter: 1em,
    $x{x |-> s}$,$=$,$s$,$$,
    $y{x |-> s}$,$=$,$y$,$"if" y eq.not x$,
    $(lambda y.e_1){x |-> s}$,$=$,$lambda y.e_1{x |-> s}$,$"if" y eq.not x "and" y in.not "FV"(s)$,
    $(e_1 e_2){x |-> s}$,$=$,$e_1{x |-> s} space e_2{x |-> s}$,$$,
    $(e_1 bin e_2){x |-> s}$,$=$,$e_1{x |-> s} bin e_2{x |-> s}$,$$,
    $e_1[e_2]{x |-> s}$,$=$,$e_1{x |-> s}[e_2{x |-> s}]$,$$,
    $[e_1,dots,e_n]{x |-> s}$,$=$,$[e_1{x |-> s},dots,e_n {x |-> s}]$,$$,
    $(e_1,dots,e_n){x |-> s}$,$=$,$(e_1{x |-> s},dots,e_n {x |-> s})$,$$,
    $ifte(e_1,e_2,e_3){x |-> s}$,$=$,$ifte(e_1{x |-> s}, \ e_2{x |-> s},e_3{x |-> s})$,$$,
    $(map e) {x |-> s}$,$=$,$map (e{x |-> s})$,$$,
    $(iota e) {x |-> s}$,$=$,$iota (e{x |-> s})$,$$,
    $(size e) {x |-> s}$,$=$,$size (e{x |-> s})$,$$,
  )

]<def:sub-butf>