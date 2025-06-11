#import "../../Packages/global.typ": *
#import "../../Figures/Epi.typ": *
#import "../../Figures/admn.typ": *

#let rscn(x) = shown(rstructcong, x)

== Extended $pi$-calculus <ch:epi>
The Extended $pi$-calculus ($epi$) is a process calculus based on the applied $pi$-calculus @appliedPi extended with broadcast and composite names @mscButfToEpi. First introduced in @butfOrigin, #cn(<butfOrigin>) looks at extending the pi-calculus to capture constructs and concepts of $fut$ in the later introduced translation. Broadcast is added by #cn(<butfOrigin>) to prevent other communication from occurring when translating the #map construct from $butf$ and composite names is introduced to capture how some constructs are related, such as elements in arrays.

=== Syntax for #epi <sec:epiSyntax>
#figure(
  EpiSyntax,
  caption: [#epi Syntax @ButfToEpi],
  kind: image
)
The syntax for the #epi is split into different formation rules where $P,Q,R,dots$ are processes, $A$ are actions, $c$ are channels, and $T$ are terms. We denote names with lowercase letters and use specific letters to differentiate between them: $a$ being a channel name, $x$ being a variable, $n$ being a number and $u$ when we do not differentiate between $a$ and $x$. We assume variables and names are distinct. 
$null$ is the inactive process that being a process which cannot reduce further. We will sometimes leave out the trailing inactive process and write $P$ instead of $P.null$. Parallel composition $P | Q$ consists of two processes in parallel and replication $! P$ constructs an unbounded number of the process $P$. The process $circle.small.filled P$ is used to denote an important step which is used in the translation.
#epi also includes the match construct $[T_1 bow T_2]P,Q$ where $bow in {<,>,<=,>=,=,eq.not}$ and should be read as: when $T_1 bow T_2$ evaluates to true it proceeds as $P$, otherwise $Q$. 
Restriction of a name to a process ($nu a . P$) is limited to only channel names. There are three actions in #epi:
- Send ($send(c, many(T))$) that sends a list of terms $many(T)$ on the channel $c$.
- Receive ($receive(c,many(x))$) which receives a list of terms and binds it to $many(x)$ on the channel $c$.
- Broadcast ($broad(c, many(T))$) that sends $many(T)$ to everyone that listens on the channel $c$ simultaneously.
Restriction and input acts as a binder for names to processes. Channels in #epi can be either channel names or variables $a$, and $x$ respectively; additionally both names and variables can be composed with a label $a dot l$. Labels are used in @ButfToEpi to select specific behaviour of channels e.g. $receive("arr" dot len, x)$ will get the length of an array where $receive("arr" dot all, x)$ will get all the elements of $"arr"$. The idea of composite names comes from @polyadicNames, though one key difference is that the composition of names introduced by #cn(<polyadicNames>) allow composite names of arity $k$ where in #epi it is restricted to an arity of two. Terms can be either $n in NN$, channel names, variables or binary operations where $bin in {+,-,dot,\/, % }$ @ButfToEpi.

=== Semantics for #epi

The semantics of #epi is in the style of a labelled reduction semantics similar to that of the reduction semantics for the $pi$-calculus. The structural congruence relation is defined as usual @butfOrigin. 
//We define the free variables and names, and bound variables and names as follows where $rn(T_1,T_2)$ means substitute $T_1$ with $T_2$.



#figure(rect(inset: 20pt, radius: 5%)[#StructCong],caption: "Structural congruence rules", gap:5pt)<fig:EpiCong>

The structural congruence rules given are quite common for most $pi$-calculi and allow for rewrites of processes. #rscn("scparn"), #rscn("scpara") and #rscn("scparb") allow for restructuring parallel composition. #rscn("scnewn") show that a restriction on the inactive process is inconsequential and #rscn("scnewa") that the order of restrictions can be swapped. #rscn("scnewb") show that the scope of a restriction can be moved to encompass a parallel process or the other way around, remove said process from the restriction. 

#figure(
  rect(inset: 20pt, radius: 5%)[#EpiRed],
  caption: [Labelled reduction rules for #epi], gap:5pt
)<fig:EpiRed>

The semantics for #epi can be seen in  @fig:EpiRed. It is similar to the one for the monadic $pi$-calculus introduced by #cn(<funcAsProc>) in @funcAsProc, however to handle broadcast a labelled reduction semantic is introduced to ensure that broadcast is handled before the process can continue. In the reduction rules for communication and broadcast, when communication occur we substitute the names $many(x)$ with the received value $many(T)$ denoted as $rn(many(x),many(T))$. The substitution rules for #epi can be found in @app:epi_defs. For the labelled semantic three arrow types are introduced: $-t$, $-b$, and $-q$. The reduction $-t$ is the regular reduction as seen in the $pi$-calculus. The $-b$ reduction is the broadcast reduction which ensures that all parallel receivers on a broadcast channel receives the broadcasted value. Lastly, $-q$ can be either a $-t$ or $-b$ reduction @butfOrigin.

#figure(
  EpiAdmRed, caption: [labelled semantics for important and administrative reductions as seen in @ButfToEpi]
)

In addition to the labelled reduction semantics, a labelled semantics for administrative and important reductions is given in @ButfToEpi. These two types of reductions are used in the translation from #butf to #epi and will be important when we define the correctness of our typed translation in @ch:tlAndCorrect.
//An important reduction in one process is a reduction that must be matched in the other. 

