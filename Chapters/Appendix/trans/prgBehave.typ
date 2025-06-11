#import "../../../Packages/global.typ": *

#let rbtfn(x) = shown(rbutf, x)
#let repin(x) = shown(repi, x)
#let radmnn(x) = shown(radmn,x)
#let ts_e(x) = $#showf(sttrans_e, x) = #showt(sttrans_e, x)$
#let ts_l(x) = $#showf(sttrans_l, x) = #showt(sttrans_l, x)$

== Proof of Lemma 4.1 <app:proof_prgBehave>

#proof(of: <lem:prgBehave>)[
  We prove this using the cases where $P$ appears in $C[P]$ unguarded or guarded.
  #case(of: $P "is guarded"$)[
    If $P$ is guarded in $C[P]$ then only $C$ can reduce and the first case applies.   
  ]
  #case(of: $P "is unguared"$)[
    If $P$ is unguarded in $C[P]$ then it has to be behind a combination of $!,nu a, Q |$ in C. Using structural congruence we can construct the following two cases
    $ C[P] == nu many(a).(O | P) "or" C[P] == !(nu many(a).(O | P)) $
    Further using structural congruence we can show that we can transform the second case into the form of the first. 
    $ &!(nu many(a).(O | P)) &== \ 
      &!(nu many(a).(O | P)) | many(b).(O | P) &==\
      &!(nu many(b).(!(nu many(a).(O | P)) | O | P)) & = \
      &!nu many(b).(O' | P) "where" O' ==  !(nu many(a).(O | P))
    $
    Therfore we get that $Q$ is one of the following three cases.
    #case(of: $nu many(a).(O | P')$)[
      As $Q == nu many(a).(O | P')$ we have that $P -s P'$ and since only $P$ reduces we have that $Q == C[P']$. Since, we have $C[P']$ and $P -s P'$ case (2) applies. 
    ]
    #case(of: $nu many(a).(O' | P)$)[
      As $Q == nu many(a).(O' | P)$ we have that $O -s O'$ and since only $O$ reduces we have that $Q == C'[P]$ where $C'[dot] = nu many(a).(O' | dot)$. Since no reduction on $P$ occurs from the reduction $C[P] -s C'[P]$ we can conclude that the context can take the same reduction with the inactive process s.t $C[null] -s C[null]$. Then, as we have $C'[P]$,$O -s O'$ and $C[null] -s C[null]$ case (1) applies.
    ]
    #case(of: $nu many(a).(O' | P')$)[
      As $Q == nu many(a).(O' | P')$ we have that both $O$ and $P$ reduces and that $Q == C'[P']$. Then as both $O$ and $P$ are reduced in a single step it must be either a #repin("r-com") or #repin("r-broad"). Therefore there must $exists b$ s.t $barb(O, b)$ and $barb(P,b)$ then we have that $O | P -s = O' | P'$, and $C[P] -s C'[P']$. Then, we have $C[P']$,$O | P -s = O' | P'$ and $C[P] -s C'[P']$ and therefore case (3) applies.
    ]
  ]
]
