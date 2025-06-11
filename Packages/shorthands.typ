#import "@preview/quick-maths:0.1.0": shorthands
#let epi = [E$pi$]
#let tepi = [TE$pi$]
#let null = $bold(0)$
#let butf = "ButF"
#let btf = "BtF"


#let bow = symbol(
  "⋈",
  ("not", "⧓"),
)

#let pageRef(x) = {link(x, "page " + context counter(page).at(x).at(0))}

#let map_state = state("map", raw("map"))
#let tup_state = state("tup", raw("tup"))
// [#bow #h(-0.9em)\/]
#let an = "and"
#let where = "where"
#let map = context map_state.get()
#let iota = raw("iota")
#let size = raw("size")
#let bin = $dot.circle$
#let all = raw("all")
#let len = raw("len")
#let tup = context tup_state.get()
#let end = raw("end")
#let fut = "Futhark"
#let cong = "structural congruence"
#let Prepeat = math.italic("Repeat")
#let Pcell = math.italic("Cell")
#let imp = $circle.small.filled$


#let ligatures = shorthands.with(
  ($>|$, math.angle.r),
  ($|<$, math.angle.l),
  ($|-$, math.tack),
  ($|>$, math.gt.tri),
  ($*$, math.dot),
  ($[=$, math.subset.eq.sq),
  ($=]$, math.supset.eq.sq),
  ($==$, math.equiv),
  ($||$, $|$),
  ($|-$, math.tack.r),
  ($-t$, math.attach(math.arrow.long, tl: [], tr: [], t: math.tau)),
  ($-b$, math.attach(math.arrow.long, tl: [], tr: [], t: $:c$)),
  ($-q$, math.attach(math.arrow.long, tl: [], tr: [], t: $q$)),
  ($⧓$, [#bow #h(-0.5em)\/#h(0.5em)]),
  ($=a$, math.attach(math.stretch(math.arrow.double, size: 1.1em), tl: [], tr: [], t:$circle.small$)),
  ($-a$, math.attach(math.arrow.long, tl: [], tr: [], t:$circle.small$)), 
  ($=i$, math.attach(math.stretch(math.arrow.double, size: 1.1em), tl: [], tr: [], t:$circle.small.filled$)),
  ($-i$, math.attach(math.arrow.long, tl: [], tr: [], t:$circle.small.filled$)), 
  ($=s$, math.attach(math.stretch(math.arrow.double, size: 1.1em), tl: [], tr: [], t:$s$)), 
  ($-s$, math.attach(math.arrow.long, tl: [], tr: [], t:$s$)), 
)
/* butf types */
#let ep = $epsilon$
#let Env = $Gamma$
#let Int = $bold("Int")$
#let Hole = $sigma$
/* butf notation */
#let ifte(e1,e2,e3) = $#raw("if") #e1 #raw("then") #e2 #raw("else") #e3$
#let cV = $cal(V)$
#let adown(x) = [$attach(br: #x,arrow.b #h(-0.46em)#rotate(30deg)[#text(size:6pt,baseline: -2pt,weight: "extrabold","/")])$]

/* Epi notation */
#let ch(..x) = $"ch"(#x.pos().join(","))$
#let loc(x) = $"loc"(#x)$
#let rn(y,x) = ${attach(slash,tl:#x,br:#y)}$
#let send(x,y) = $overline(#x) angle.l #y angle.r$
#let broad(x,y) = $overline(#x)#h(-0.1pt):#h(-0.1pt)angle.l #y angle.r$
#let many(x) = $attach(tr:"",t: arrow, tl:"", #x)$
#let manyt(x) = $attach(tr:"",t: tilde, tl:"", #x)$
#let receive(x,y) = $#x (#y)$
#let Schoice(x,y) = $#x triangle.stroked.l #y$
#let Sbranch(x,y) = $#x triangle.stroked.r #y$
#let var = $bold("Var")$
#let tl(x) = $bracket.l.double #x bracket.r.double$
#let tlt(x,e) = $bracket.l.double #x bracket.r.double$
#let sp = {h(0.15em)}
#let pp = $#raw("+")$
#let mp = $#raw("-")$
#let repl = $!$
#let choice(..content) = {$plus.circle$ + math.cases(..content)
}
#let fn(x) = $"fn"(#x)$
#let bn(x) = $"bn"(#x)$
#let fv(x) = $"fv"(#x)$
#let bv(x) = $"bv"(#x)$
#let dom(x) = $"dom"(#x)$
#let wrong = $#math.italic("error")$
#let CEnv = $Pi$
#let DEnv = $Delta$
#let PEnv = $DEnv, CEnv$
#let ssend(x,y) = $#x^mp ! angle.l #y angle.r$
#let sbroad(x,y) = $#x^pp ! angle.l #y angle.r$
#let sreceive(x,y) = $#x (#y)$
#let tp = $attach(t:arrow,tl:"",tr:"",attach(tr:prime,t))$
#let pch(n: 0,..args) = {
  let t = args.pos()
  if(t.len() == 0){
    $@ell$
  } else{
   $@{#t.join(",")}$ 
  }
}
#let hh(..args) = {
  $"pch"(#args.pos().join(","))$
}
#let tle(x,o) = $bracket.l.double #x bracket.r.double^(Env)_(#o)$


/* not steps */
#let rnt = $attach(arrow.not, tl: [] , tr: [], t: tau)$
#let rnb = $attach(arrow.not, tl: [], tr: [], t: :c)$
#let rnq = $attach(arrow.not, tl: [], tr: [], t:q)$

// correctness
#let rel(x,y) = $#x #sp cal(R) #sp #y$
#let orel(x,y) = $#x #sp R #sp #y$
#let bi(x,y) = $ #x limits(approx)^circle.small.filled #y $
#let barb(x,y) = $#x attach(arrow.b, br:#y)$
#let bim(x,y) = $#x attach(approx, t: dot, br: alpha) #y$
#let ocp(x,y) = $#x attach(gt.lt, br: "ok") #y$
#let tok(x,y) = $#x #move(dy:0.125em,$succ$) #h(-0.5em) #move(dy:-0.125em,$prec$) #h(0.25em) #y$