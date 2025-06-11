#import "../../Packages/global.typ": * 

== Translation of #butf to #epi <ch:transButfEpi>
We will now introduce the translation from #butf to #epi by #cn(<ButfToEpi>), @ButfToEpi. This will be used to give a general understanding of the original translation and will be used when we compare the new translation from #btf to #tepi introduced in @ch:TransBtfTEpi. 

For a translation of a #butf expression $e$ to the corresponding #epi process, the notation $tl(e)$ will be used for the translated #epi process. The notation $tl(e)_o$ is used when specifying an output channel (that being the channel $o$) as parameter for a translated process that is used such that we can communicate with that process, as seen in @ButfToEpi. This approach originates from the work by #cn(<funcAsProc>) where two translations to the $pi$-calculus is shown: one of the lazy $lambda$-calculus and one of the call-by-value $lambda$-calculus @funcAsProc. 

=== Translation
In the translation we will use certain lower-case letters for names to illustrate their function such as $h$ being a channel name whose purpose is being a function, array or tuple handle and $v$ being a name signifying a value; that being the name received from a process that has already finished evaluating. In the translation the notation $circle.small.filled$ marks important reductions in #epi that matches a transition in #butf @ButfToEpi.

==== Translation of Expressions
#let translatedExpressions = [
  $
  tl(x)_o &= send(o,x) 
  
  \  #v(2em)
  
  tl(n)_o &= send(o,n) 
    
  \  #v(2em)
  
  tl(lambda x . e)_o &= nu h . (send(o,h) | repl receive(h,#[$x,r$]) . tl(e)_r) 
      
  \  #v(2em)
  
  tl(e_1 e_2)_o &= nu o_1 . nu o_2 . (tl(e_1)_o_1 | tl(e_2)_o_2 | receive(o_1,h) . receive(o_2, v). circle.small.filled send(h, #[$v, o$]))
      
  \  #v(2em)
  
  tl(e_1 [e_2])_o &= nu o_1 . nu o_2 . (tl(e_1)_o_1 | tl(e_2)_o_2 | receive(o_1, h) . receive(o_2, i) . circle.small.filled [i >= 0] receive(h dot i, #$i, v$) . send(o, v), null)
      
  \  #v(2em)
  
  tl(ifte(e_1, e_2, e_3))_o &= nu o_1 . (tl(e_1)_o_1 | receive(o_1, n) . circle.small.filled [n eq.not 0] tl(e_2)_o, tl(e_3)_o)

  \ #v(2em)
  tl(e_1 bin e_2)_o &= nu o_1 . nu o_2 . (tl(e_1)_o_1 | tl(e_2)_o_2 | receive(o_1, v_1).receive(o_2, v_2).send(o, v_1 bin v_2) )
  $
]
#figure(translatedExpressions, caption: [Translation of basic #butf expressions])<fig:tlOfExp>

The translation of variables and numbers is the same as in @funcAsProc with the channel $o$ being the link. 
In the translation of abstraction, the new name $h$ is introduced, which is a handle to the process. As we cannot transmit functions, this works as a pointer to the function. A replicated process is receiving on $h$, waiting for the parameter ($x$) and a return channel ($r$) which is used in the translation of the expression $tl(e)_r$. 

In application, we have three processes in parallel, the translations of expressions $tl(e_1)_o_1$ and $tl(e_2)_o_2$ and a process waiting for an output from the two processes. Upon receiving $h$ and $v$ the process will output the value and return channel on $h$ (the channel the value after evaluation will be output on). Recall that abstraction waits for an input on $h$ and that connects abstraction and application.

Indexing is translated similarly to application. First, we evaluate the two sub-expressions and receive the array handle (the name $h$) from $tl(e_1)_o_1$, and the index (the name $i$) from $tl(e_2)o_2$. Then we match the index and if its larger or equal to 0, we receive the value on the composite name $h dot i$ and outputs it, else we proceed as the inactive process #null.

For the translation of branching we make use of the match constructor in #tepi. We first evaluate the translation of sub-expression $tl(e_1)_o_1$, which will then output the result on the channel $o_1$. Upon receiving the name $n$ (which specify a number as seen in @sec:epiSyntax) we match it with 0 and proceed as either $tl(e_2)_o$ or $tl(e_3)_o$. As branching can only proceed as either one of the two we can use the same output channel ($o$) for both of them. 

In addition we have introduced the translation of binary operation which is missing in @ButfToEpi. In the translation of binary operation we first evaluate the two sub-expressions and receive the values on their respective output channel. We then send the value on $o$ with the corresponding #tepi binary operation.

==== Translation of Arrays and Tuples <sec:tlOfArr>
To define the translation of arrays we need a process $Pcell$ as introduced in @ButfToEpi. 

#eqn(
$
Pcell(h,i,v) = repl receive(h dot all,r) . send(r,#$i,v$) | repl send(h dot i, #$i,v$)
$
)<def:cell>

The $Pcell$ process is defined with a handle ($h$), an index ($i$) and a value ($v$). The reason for the handle is that $Pcell$ is defined using the same approach as translation of functions in the $pi$-calculus - the handle is pointer to the cell. $Pcell$ has two composed names: the first name ($h dot all$) is waiting for a request for all the values in the array. The second composed name ($h dot i$) is waiting for a request for a specific element in the array.

#let translatedArAndTup = [
  $
  tl([e_1, dots, e_n])_o &= nu o_1. dots . nu o_n . nu h.(product_(i=1)^(n) tl(e_i)_o_i | receive(o_1,v_1). dots . receive(o_n,v_n). 
 \ &#h(7.2em) (product_(i=1)^(n) Pcell(h, i-1, v_i) | send(h dot len, n) | send(o, h) )) 
 
  \  #v(5em)
  
  tl((e_1, dots, e_n))_o &= nu o_1 . dots . nu o_n . (product_(i=1)^(n) tl(e_i)_o_i | receive(o_1,v_1). dots . receive(o_n,v_n) . nu h . (repl send(h dot tup,#$v_1, dots v_n$) | send(o,h) )) 
  $
]
#figure(translatedArAndTup, caption:[Translation of arrays and tuples], )

Tuples and arrays are translated similarly. For array we translate each sub-expression and receive the evaluated values on each of their output channel. When we have received the values we can then create the array structure using the $Pcell$ process for each of the values we have received. The sub-process $send(h dot len, n)$ outputs the length of the array which will be used in the translation of the array operation $size$.

For the translation of tuples, we first we translate each sub-expression and receive the evaluated values over each of their output channel as in arrays. The output channel $h dot tup$ is a restriction for communication such that a tuple can only be used in place expecting a tuple. 
// We might want to move the restriction on h out with the other restrictions.

==== Translation of Array Operations
#let translatedArrOp = [
  $
  tl(size e_1)_o &= nu o_1 . (tl(e_1)_o_1 | receive(o_1,h) . receive(h dot len, n) . circle.small.filled send(o, n)) 
  
  \ #v(3em)
  
  tl(iota e_1)_o &= nu o_1 . nu r . nu h . (tl(e_1)_o_1 | receive(o_1,n) . Prepeat(n,r,d) | 
  \ &#h(6.2em) repl receive(r, #$i,v$) . Pcell(h,i,v) | circle.small.filled receive(d,"") . (send(h . len, n) | send(o,h)))  
  
  \ #v(3em)
  
  tl(map e_1)_o &= nu o_1 . nu h_1 . (tl(e_1)_o_1 | receive(o_1,x) . receive(x dot tup, #$f,h$) . receive(h dot len, n) . 
  \ &#h(5.2em) nu v_1 . broad(h dot all,v_1) . nu r .nu d.(Prepeat(n,r,d) | 
  \ &#h(5.2em) repl receive(v_1,#$i,v$) . nu r_1 . send(f, #$v,r_1$) . receive(r_1,v_2) . receive(r,#$"_","_"$) . Pcell(h_1,i,v_2) | 
  \ &#h(5.2em) nu o_2 . send(f,#$0,o_2$) . circle.small.filled receive(d,"") . send(o, h_1) | repl send(h_1 dot len,n) ) ) 
  $
]
#figure(translatedArrOp, caption:[Translation of array operations], )<fig:OgTlArrOp>

One important thing to note of the translation of array operations is our presentation have some important reductions in the translation of #size and #iota, which cannot be seen in @ButfToEpi. 

The translation of #size is quite simple. First we translate the expression $tl(e_1)$, which is an array. On its output channel we receive its handle which we can use to get the size of the array. Remember that the translation of arrays outputs the length over the channel $h dot len$. Here we receive the length of the array and will output on the return channel $o$.

For the translation of #map and #iota we introduce an auxiliary process called $Prepeat$ as seen in @ButfToEpi.

#eqn(
$
Prepeat(s,r,d) = nu c . (repl receive(c,n) . ([n >= 0] ( send(r,#$n-1,n-1$) | send(c,n-1) ), send(d,"")) | send(c,s) )
$
)
/*
$
Prepeat(s,r,d) = nu c . (repl receive(c,n) . ([n <= s] ( send(r,#$n+1,n+1$) | send(c,n+1) ), send(d,"")) | send(c,0) )
$
*/

$Prepeat$ is, as the name suggest, a process that will repeatedly communicate with itself a number of times. This is similar to a restricted replication were instead of an unbounded number iteration the process is limited to a set number of iterations. Before a countdown can begin, an output of the initial value that will counted down from (that being $s$), is sent on $c$. This will trigger the next process that will do the actual repeating - this is seen by the replicated input channel $c$ that upon receiving a number $n$ does a match with 0 and will proceed with either:
1. Match succeeds: Output $n-1$ on the return channel $r$ in parallel with outputting the same on its own channel $c$.
2. Match fails: Output an empty message on channel $d$ to signal we are finished.

$iota$ uses repeat with the number ($n$) we receive from evaluating the translated process $tl(e_1)$. In parallel with $Prepeat$ we receive the index and the value (this being the same number) and then construct the array cell. When $Prepeat$ has finished we can send the array handle ($h$) on the output channel ($o$).

For the translation of #map we first need the evaluation of the translation of $tl(e_1)$ as that will return the arguments ($x$) on $o_1$. On the $x dot tup$ channel we will receive the function we will apply ($f$) and the array handle ($h$). With the array handle we get the length of the array which will be used later. We then do a broadcast to all array element of a certain name $v_1$, which will have all the values from the array. We use the $Prepeat$ process with the array length we received earlier. In parallel we receive the index and value on $v_1$ followed by sending the value and return channel over the function channel ($f$). On this return channel we will receive the new value. We can then update the cell array, when have received on the $Prepeat$ return channel ($r$). The second last part is a check to ensure we are working with a function by sending a $0$ over the function channel. We cannot proceed before $Prepeat$ has finished which we will know when we receive on channel $d$. Finally we can send the new array handle.

=== Examples of Translations <sec:tl_Examples>
// Spoky scary stuff here 
We will now give three examples of a translation from #butf to #epi. The first is an example of indexing, the second of abstraction and the third of the map function. Different parts of the translations have been marked to help with readability.
#set math.lr(size: 1em)

#let arr = "arr"
#let inp = "in"
#let Out = "out"
#let sub = "sub"

==== Example of Indexing <ex:tlIndexing>
This first example is the translation of the expression $[2,3][1]$, indexing of an array consisting of two numbers. When translating we will have the following form for indexing $tl([2,3][1])_o$ expanding to @ex_arrInd.

// #let _arrIndEx = $ nu o_0.(nu o_1.(nu o_6.(nu o_7.(nu h_12. (overshell(send(o_6,2),"2")|overshell(send(o_7,3),"3")| overshell(receive(o_6,v_8).receive(o_7,v_9),"receiver")\ |overshell(repl(receive(h_12 dot all,r_10).send(r_10,0\,v_8)) | repl(send(h_12 dot 0,0\,v_8).null),"cell_0")|overshell(repl(receive(h_12 dot all,r_11).send(r_11,1\,v_9).null) | repl(send(h_12 dot 1,1\,v_9).null),"cell_1")| \ overshell(repl(send(h_12 dot len,2).null),"len")|overshell(send(o_0,h_12).null,"handle"))))  |overshell(send(o_1,1).null,"1")|overshell(receive(o_0,h_2).receive(o_1,i_3).[i_3 gt.eq 0] (receive(h_2 dot i_3,i_4\,v_5).send(o,v_5).null) (null),"access"))) $

#let ex_arrInd = $
tl([2,3][1])_o = &nu o_arr.(nu o_1.(nu o_2.(nu o_3.(nu h_1.(overshell(send(o_2,2),tl(2)_o_2)|overshell(send(o_3,3), tl(3)_o_3)|overshell(receive(o_2,v_1).receive(o_3,v_2),"receiver") \
&| overshell(repl(receive(h_1 dot all,r_0).send(r_0,0\,v_1)) | repl(send(h_1 dot 0,0\,v_1)),"cell_0") \ &| overshell(repl(receive(h_1 dot all,r_1).send(r_1,1\,v_2)) | repl(send(h_1 dot 1,1\,v_2)),"cell_1")|\ &overshell(repl(send(h_1 dot len,2)),"len")|overshell(send(o_arr,h_1),"handle")))) |overshell(send(o_1,1),"index") \ &|overshell(receive(o_arr,h_0).receive(o_1,i).[i gt.eq 0] (receive(h_0 dot i,i\,v).send(o,v))\, null,"access")))
$
#figure(ex_arrInd, caption:[Translation of the expression: [2,3][1]], )<ex_arrInd>

If we take a look at the translation of indexing from @fig:tlOfExp we first need to translate the two sub-expressions: The first being the array ($tl(e_1)$), the second being the number we want to index ($tl(e_2)$). 

For the first sub-expression (the translation of the array) we first need to translate each element in the array. This can be seen in the first two marks (2 and 3) where we output the number on their respective output channel. This matches the translation of numbers seen in @fig:tlOfExp. The next step is receiving the values (marked with receiver), and then construct the array with the $Pcell$ process. The whole array consists of two cells (each marked as cell_0 and cell_1) constructed as seen in $Pcell$ process, the composite name with length of the array, and the handle of the array. 

The second sub-expression is quite simple. It is just the output of the indexing number on the channel $o_1$ which has been marked with $1$ above.

For the final part (marked as access), we receive the array handle on channel $o_0$ and the indexing number on channel $o_1$. This is followed by a match on the indexing number we received. If the match succeeds (which we know it will in this case) we can use the handle and index the get the value at that index, and output it on channel $o$. If the match fails we go to the $null$ process.

==== Example of Abstraction <ex:tlAbs>
The second example is the translation of the expression $lambda x. x+1$, an abstraction that takes a value x and adds 1 to it. When translating we will have the following form for abstraction $tl(lambda x.x+1)_o$ expanding to @ex_absBin
#let ex_absBin = [ 
$
tl(lambda x.x+1)_o  =
& undershell(nu h_0.(send(o,h_0) | repl(receive(h_0,x\,r_0).tl(x+1)_r )),"lambda h_0") \

\ \

tl(x+1)_r = & undershell(nu o_0.(nu o_1.(overshell(send(o_0,x),"x") | overshell(send(o_1,1),"1") | overshell(receive(o_0,v_0).receive(o_1,v_1).,"receiver")overshell(send(r_0,v_0 + v_1),"binop"))),x+1) 

$
]
#figure(ex_absBin, caption:[Translation of $lambda x. x+1$])<ex_absBin>
If we take a look at the translation of a simple abstraction in @ex_absBin we first need to create a function handle to receive the $x$ and the return location $r_0$  and send it to the output channel $o$. Then we have to translate the sub-expression $tl(e)_r_0$ which is a binary operation between a variable $x$ and the number $1$.
The first part of the translation of the body $tl(e)_r_0$ is translating the variable $x$ and number $1$ followed by receiving the values (marked with receiver), and then sending the result of the binary operation (marked binop) in $r_0$.

==== Example of Map <ex:tlMap>


For our last example we have we have the expression $map (lambda x. size x, [[1, 2], [3, 4]])$, a mapping of the #size operation to an array of arrays. The translation of #map is quite long and therefore we have split it into smaller sub-translations.

First we have the translation of the two inner arrays.
$
tl([1,2])_o_B = &nu o_1. nu o_2. nu h_A.
    ( overshell(send(o_1,1) | send(o_2,3), tl(1)_0_1 "and" tl(2)_o_2 )              
    | overshell(o_1(v_1). o_2(v_2), "receiver"). \
        &( undershell(Pcell(h_A,0,v_1) | Pcell(h_A,1,v_2) | send(h_A dot len,2) | send(o_A, h_A), "array:" [1,2] ) )

\ \

tl([3,4])_o_B = &nu o_3. nu o_4. nu h_B.
    ( overshell(send(o_3,3) | send(o_4,4), tl(3)_0_3 "and" tl(4)_o_4 )   
    | overshell(o_3(v_3). o_4(v_4), "receiver"). \
        &( undershell(Pcell(h_B,0,v_3) | Pcell(h_B,1,v_4) | send(h_B dot len,2) | send(o_B, h_B), "array:" [3,4] ) ) )
$
The value located is each translated using the translation of numbers. When we have received the translated value (marked as receiver) we can then create the array using the $Pcell$ process:

$
Pcell(h_B,0,v_3) = !receive(h_B dot all, r). send(r, 0 \, v_3) | ! send(h dot 0, 0 \, v_3)
$ 

Next we have the translation of the outer array. When we receive the array handles from the inner arrays we can construct the outer array using the $Pcell$ process with the handles as values on the index.
$
tl([[1,2],[3,4]])_o_arr = &nu o_A. nu o_B. nu h.
    ( tl([1,2])_o_A | tl([3,4])_o_B
    | overshell(receive(o_A, h_A). receive(o_B, h_B), "Receive inner array handles"). \
        &( undershell(Pcell(h,0,h_A) | Pcell(h,1,h_B) | send(h dot len, 2) | send(o_arr,h), "array:" [[1,2],[3,4]] )) )

$

We also have the translation of the abstraction using the size operation. Following the translation rules in @fig:tlOfExp and @fig:OgTlArrOp we get the following:

$
/*tl(size x)_r =
  &nu o_x . (send(o_x,x) | receive(o_x,h). receive(h dot len,n). circle.filled.small send(r,n)) 

\ \
*/
tl(lambda x. size x)_o_F =
  &overshell(nu h_F .
    ( send(o_F,h_F)
    | !receive(h_F,x \, r). undershell(nu o_x . (send(o_x,x) | receive(o_x,h). receive(h dot len,n). circle.filled.small send(r,n)), tl(size x)_r)  ), "Abstraction" )      // -- λ‑rule  

$


We can now create the tuple with the function, and the array we apply the function to. We insert the translation of the function and the array. When we receive the handles to both we can then output tuple handle on the $o_tup$ channel such that communication with the tuple can occur.

$
tl((lambda x. size x , [[1,2],[3,4]]))o_tup =
  &nu o_F . nu o_arr .
    ( overshell(tl(lambda x. size x)_o_F 
    | tl([[1,2],[3,4]])_o_arr, "Tuple elements" )\
    &| undershell(receive(o_F, f). receive(o_arr, h_inp), "Function and array handle" ).
        nu h_tup .
          ( undershell(!send(h_tup dot tup, f \, h_inp) | send(o_tup, h_tup), "Communication with the tuple") ) )

$

Finally we have the translation of the full expression. First we have the translation of our tuple as seen above. When we have received all the handles from the tuple, we can then get the values from the input array. Then we can start the $Prepeat$ process to apply the function to each element. When we receive the value from the function we can the create the cell in the resulting array using the $Pcell$ process. 
$
tl(map (λ x. size x , [[1,2],[3,4]]))_o = & nu o_tup . nu h_Out . 
    (
      undershell(tl((λ x. size x , [[1,2],[3,4]]))_o_tup, "Tuple")    \       //-- §3
    & | undershell(receive(o_tup, h_tup) .
        receive(h_tup dot tup, f \, h_inp ), "Unpack tuple" ).                            // -- f is the λ‑handle, hIn the input array
        undershell(receive(h_inp dot len, n), "Input array size" ).                                   // -- n = 2
        nu h_all . \
        & undershell(broad(h_inp dot all, h_all), "Get input array elements" ) . nu r . nu d.
          ( Prepeat( n , r , d )                      // -- index driver
          | \ & !h_all (i , v_sub).
              nu r_1 . undershell(send(f, v_sub \, r_1), "Function call" ).                  //-- call λ on each sub‑array
              undershell(r_1(s_z), "return value"). r(\_, \_). \ &undershell(Pcell( h_Out , i , s_z ), "Fill resulting array" ) //-- fill result cell
          | undershell(circle.small.filled d(), Prepeat "finished" ). send(o,h_Out)                            //-- important reduction
          | !send(h_Out dot len,n))
    )

$
When we receive on $d$ we know the $Prepeat$ process has finished, and so the resulting array after a #map has been created which we can then output.


/*$
tl(map (size [[1][2,3]]))_o = &nu o_1. nu h_1.
( tl((size, [[1],[2,3]]))o_1 \ //-- Section 2 
&| o_1(x). x dot tup(f , h). //-- f = size
h dot len(n).
nu v_1. broad(h dot all,v_1).
ν r. \ &(
Prepeat(n , r , d) //-- §0
| !v_1(i , v). ν r_1.
send(f,v \, r_1). r_1(v_2). r(\_, \_). \ &Pcell(h_1 , i , v_2)
| ν o_2. f⟨0 , o_2⟩ // -- “is f a function?” guard
| ∙ d(). o⟨h_1⟩ //-- important reduction
| !send(h_1 dot len,n) )
)

$*/

/*
#let ex_mapSomething = [
$ nu o_0.( \ undershell(nu o_2.(nu o_3.(nu h_3.(undershell(nu h_4.(send(o_2,h_4).null | !(receive(h_4,x\,r_3).undershell(overshell(send(r_3,x).null,"x"),"body"))),"lambda h_4")\ |undershell(nu o_4.(nu h_5.(overshell(send(o_4,1).null,"1")|overshell(receive(o_4,v_5).null,"receiver")|overshell(!(receive(h_5 dot all,r_4).send(r_4,0\,v_5).null) | !(send(h_5 dot 0,0\,v_5).null),"cell_0")|overshell(!(send(h_5 dot len,1).null),"len")|overshell(send(o_3,h_5).null,"handle"))),"array")\ |overshell(receive(o_2,v_3).receive(o_3,v_4).null,"receiver")|overshell(send(o_0,h_3).null,"handle")|overshell(!(send(h_3 dot tup,v_3\,v_4).null),"rep")))),"tuple") \ | overshell(receive(o_0,h_0).receive(h_0 dot tup,f_0\,h_1).receive(h_1 dot len,n_0).,"arguments")nu v_0.(overshell(receive(h_1 dot all,v_0).,"elements") \ nu r_0.(overshell(nu c_0.(receive(c_0,n_1).[n_1 > 0] (send(r_0,n_1 - 1\,n_1 - 1).null | send(c_0,n_1 - 1).null), (send(d_0,"").null) | send(c_0,n_0).null),"Repeater") | \ !(receive(v_0,i_0\,v_1).nu r_1.(overshell(send(f_0,v_1\,r_1).receive(r_1,v_2).receive(r_0,t_0\,t_1).,"apply func")(overshell(!(receive(h_2 dot all,r_2).send(r_2,i_0\,v_2).null) | !(send(h_2 dot "i_0",i_0\,v_2).null),"cell_"i_0"")))) | \ nu o_1.(overshell(send(f_0,0\,o_1).receive(d_0,"").,"bound_check")overshell(send(o,h_2).null,"new array")) | overshell(!(send(h_1 dot len,n_0).null),"arry length"))))) $
]
#figure([#set math.lr(size: 1em); #ex_mapSomething], caption:[Translation of $map (lambda x. x, [1])$])<ex_mapSomething>
*/


