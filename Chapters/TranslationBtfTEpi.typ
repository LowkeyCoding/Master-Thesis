#import "../Packages/global.typ": *

We will in this chapter introduce the translation of #btf to #tepi and show the typed versions of the examples given in @sec:tl_Examples. We then define the correctness of the translations and show a part of the proof.


== Translation of #btf to #tepi <ch:TransBtfTEpi>
As the semantics of #btf and #tepi is not different from the semantics of #butf and #epi, the translation of the expressions themselves has not changed much. For the cases where the translation has changed we will discuss the differences compared to the original introduced in @ch:transButfEpi. 

=== Translation
Just as the introduction of the original translation from #butf to #epi by #cn(<ButfToEpi>), @ButfToEpi, we use certain characters to illustrate their value. For translating the types and the type environment we take inspiration from #cn(<TheBibble>) and their translation of the typed $lambda$-calculus @TheBibble. 

When translating expressions we use the notation $tle(e,o) = (PEnv, P)$  to denote translating some well-typed expression $Env tack e : tau$ to $PEnv tack P$. In the case where $o$ is a fresh name in $P$ we add the restriction on $o$ such that $tle(e,o) = (PEnv,(nu o : ch(tl(tau))).P)$. To simplify the definition of the translation when sub-expression are present we simply insert the $P_n$ from the resulting tuple $(DEnv_n,CEnv_n,P_n)$ from the sub-expression and collect the environments $(DEnv_1 union dots union DEnv_n, CEnv_1 union dots union CEnv_n, P)$. We omit the tuple notation when no change is made to $DEnv$ and $CEnv$ in the translation. When referencing $CEnv_n$ in the translation, it corresponds to the $CEnv$ from $tle(e_n,o_n) = (PEnv,P)$.
 
==== Translation of Basic Expressions<h3:ts_expr>
The translation of basic expression is similar to the one as seen in @ch:transButfEpi. 
#{
show figure: set block(breakable: true)
figure(translation-grid(sttrans_e), caption: [Translation of basic #btf expressions], kind:image, )
}<fig:tlOfBtfExp>

Indexing is one the more interesting cases as that has been changed the most. First we have moved the important reduction to the output of the value as we have removed the match on $i$. In the original translation the match stops us from proceeding if the value is below 0 but not if above the number of elements in the array. As we will show in the proof of @th:correctness removing the match does not change the correctness of the behaviour for the translation.

==== Translation of Arrays and Tuples <h3:ts_arr_tup>
For the translation of arrays and tuples we need an updated version of the $Pcell$ process with its type annotation.
#eqn(
$
Pcell(h, i, v,t_v) = repl receive(h dot all, r : ch(Int\, t_v)) . send(r,i\,v) | repl send(h dot i, v)
$
)

One of the changes in the $Pcell$ process is in the output on $overline(h dot i)$. In @ButfToEpi, when output on $overline(h dot i)$ both the value and index was sent. As only the value and not the index was needed to be sent we have removed it. When we construct the $Pcell$ process we require the type of the value located at the index.


#figure(translation-grid(sttrans_l), caption: [Translation of #btf arrays and tuples])<fig:tlOfBtfArr>

The biggest addition to translation of array and tuples is the construction of the $CEnv$ to ensure the correct typing of composed names. Building $CEnv$ for tuples are quite simple we only add one pair $(h,tup)$ with a pre-channel type for it. Then for arrays we add a pair for $all,len$ and then a pair for each index in the array. 

==== Translation of Types and Environments<h3:ts_types>
#figure(translation-grid(sttrans_t), caption: [Translation of basic #btf types], kind:image)<fig:tlOfBtfTyp>

First major addition in the translation we have, is the addition of the translation of types. The translation of $Int$ is straightforward as there is a one to one correspondence for this type. The translation of the array type is interesting as it depends on the translation of arrays. The reason we have a pre-channel type for arrays is that communication with arrays in #tepi is on composite names and therefore we must type it as such. We have three composite names to communicate with the array on: $h dot all$, $h dot i$ and $h dot len$. The type of $all, i$ and $len$ corresponds to what can be seen as $many(t_1)$ in #shown(rtepi,"t-comp") or #shown(rtepi,"t-comp2"). The translation of the tuple type is very similar as communication with tuples is on the $h dot tup$ channel. 
Lastly, the translation of the abstraction type is similar to the intuition of applying a function. The first type is the argument and the second is the return channel with the resulting type of the function application. 

#figure(translation-grid-s(sttrans_te), caption: [Translation of type environment], kind:image)<fig:tlOfBtfTypEnv>




==== Translation of Array Operations
Similar to the $Pcell$ process we need to update the $Prepeat$ process with type annotations. In addition we need to send a value on $d$ and for the translations using $Prepeat$ we need a restriction on $d$ for it to be well-typed. 
#eqn(
$
Prepeat(s,r,d) = (nu c : Int) . (repl receive(c,n : Int) . ([n >= 0] ( send(r,n-1) | send(c,n-1) ), send(d, 0)) | send(c,s) )
$
)

The translation of array operations are then as seen in @fig:tlOfBtfArrOp. The translation of #map has been changed by removing the check to ensure $f$ is a function as that is required for it to be well-typed.
#show figure: set block(breakable: true)
#figure(translation-grid(sttrans_o), caption: [Translation of #btf array operations],)<fig:tlOfBtfArrOp>
#show figure: set block(breakable: false)

=== Examples of Translations
We will now show some examples of translations. We will take the same examples as shown in @sec:tl_Examples. 

#set math.lr(size: 1em)
==== Example of Indexing
For the first example we have the indexing of an array like on #pageRef(<ex:tlIndexing>). The expression is as follows: $[2,3][1]$, with the translation of the expression being:

#let arr = "arr"

$
tle([2,3][1],o) = &(nu o_arr:ch(tl([Int]))) . (nu o_i:ch(Int)). \
  &(
    (nu o_2:ch(Int)). (nu o_3:ch(Int)). (nu h: tl([Int])). \
      &( overshell(send(o_2,2) | send(o_3,3), tle(2,o_2) "and" tle(3,o_3))
      | overshell(o_2(v_2:Int). o_3(v_3:Int), "receiver"). \
          &( undershell(Pcell(h,0,v_2,Int) | Pcell(h,1,v_3,Int) | send(h dot len,2) | send(o_arr,h), "array: " [2,3]) ) 
      ) \
  &| overshell(send(o_i,1), "index")
  | undershell(overshell(receive(o_arr , h : tl([Int])). receive(o_i , i : Int), "receive array handle and index") . overshell(receive(h dot i, v : Int), "receive value at index") . circle.small.filled send(o,v), "access and output of value")
  )
$

First we create restrictions on the different channels used for communication. These include channels for the array handle and the values in the array. Then we translate the respective values in the array and receive them on their output channel (marked as receiver). We then construct the array using the $Pcell$ process (marked as: $"array": [2,3]$). The $Pcell$ process for the value at index 1 is a follow:
$
Pcell(h,1,v_2,Int) = receive(h dot all, r : ch(Int, Int)) . send(r, 1\,v_3) | ! send(h dot 1, v_3);
$
// START HERE
After the translation of the indexing number we receive the array handle and index. We can then communicate with the $Pcell$ process on $h dot 1$ to receive the value located at the index. Finally we can send the value on our output channel $o$.

==== Example of Abstraction
For the second example we have the simple abstraction shown on #pageRef(<ex:tlAbs>). The expression is as follows $lambda (x: Int) . x + 1$ and is translated as shown below. 
#{

$
tle(lambda x: Int. x + 1,o) = &(nu h : tl(Int -> Int)) .  (send(o,h)
  |  !undershell(h(x : tl(Int), r : ch tl(Int)),"argument and return channel").tle(x + 1,r)
       
$
$ 
 tle(x + 1,r) = undershell((nu o_1 :ch(tl(Int)) ). (nu o_2 : ch(tl(Int))) . 
       ( overshell(send(o_1,x)
       | send(o_2,1), tle(x,o_1) "and" tle(1,o_2))
       | overshell(receive(o_1, v_1 : Int). receive(o_2, v_2 : Int),"receive values"). overshell(send(r, v_1 + v_2), "send result") ), tle(x + 1,r)) 
$
}
First we create a restriction on $h$, the function handle with the type $tl(Int -> Int)$, which is translated to $ch(Int,ch(Int))$. Then we send the handle on $o$ in parallel with constructing the function. The construction of the body consists of receiving the argument and return channel $x,r$ then translating the expressions $x$ and $1$, respectively, and receive them on the output channels $o_1$ and $o_2$. Finally we send the result of $v_1 + v_2$ over $r$.

==== Example of Map

#let tuple = "tuple"
#let out = "out"
#let sub = "sub"
#let inp = "in"
#let arr = "arr"
#let idx = "idx"

In the last example we have the translation of an expression with #map as seen on #pageRef(<ex:tlMap>). The expression is the following: $map (lambda (x : [Int] ) . size x, [[1,2], [3, 4]])$ . This translation is quite long and therefore we have split it into sub-translations.

First we have the translation of the two inner arrays.

$
tle([1,2], o_A) = &(nu o_1 : ch(Int)). (nu o_2 : ch(Int)) . (nu h_A: tl([Int]) ) . \
    &
    ( overshell(send(o_1, 1) | send(o_2, 2), tle(1,o_1) "and" tle(2,o_2)) | overshell(receive(o_1, v_1: Int). receive(o_2, v_2:Int), "receiver"). \
        &( undershell(Pcell(h_A,0,v_1,Int) | Pcell(h_A,1,v_2,Int)
        | send(h_A dot len, 2) | send(o_A, h_A), "array:" [1,2]) ) )

\ \

tle([3,4],o_B) = &(nu o_3 : ch(Int)) . (nu o_4 : ch(Int)) . (nu h_B : tl([Int])) .\ & (overshell( send(o_3,3) | send(o_4,4), tle(3,o_3) "and" tle(4,o_4)) | overshell(receive(o_3, v_3 : Int). receive(o_4, v_4 : Int), "receiver"). \
&(undershell(Pcell(h_B, 0, v_3, Int) | Pcell(h_B, 1, v_4, Int) | send(h_B dot len,2) | send(o_B,h_B), "array:" [3,4]) )
)
$
This part of the translation is quite simple. First the values of the array are translated and then the array is created using the $Pcell$ process just like in the indexing example. Next we have the translation of the outer array. We create the array using the handles we received from the translation of the two inner arrays as the value on the index. 
$
tle([[1,2],[3,4]],o_arr) =
  &(nu o_A : ch(tl([Int]))). (nu o_B : ch(tl([Int]))). (nu h : tl([[Int]])) . \
    &( tle([1,2],o_A) | tle([3,4],o_B) \
    &| overshell(receive(o_A, h_A: tl([Int])) . receive(o_B, h_B : tl([Int])), "receive handles to inner arrays"). \
        &( undershell( Pcell(h,0,h_A,tl([Int])) | Pcell(h,1,h_B,tl([Int]))
        | send(h dot len, 2) | send(o_arr,h), "array:" [[1,2],[3,4]] ) ) )

$

Next we have the translation of the abstraction. We start by outputting the handle such that processes can communicate with the abstraction process. In parallel with this, we have a replicated input on the handle which waits for the argument and the return channel were we output the result after applying the abstraction. This is followed by the translation of our sub-expression which is a direct translation of $size e_1$ with $e_1$ being $x$. 
$
tle(lambda (x : [Int]) . size x,o_F)  = &(nu h_F : tl([Int] -> Int)) . 
    (send(o_F,h_F)  | undershell(! receive(h_F, x : tl([Int]) \, r : ch(Int)),"Argument & return channel"). \
     &undershell( (nu o_x : ch(tl([Int]))) .
      ( overshell(send(o_x,x),tle(x,o_x)) | overshell(receive(o_x, h_arr : tl([Int])) . 
       h_arr dot len (n:Int),"Get size of array"))  .circle.filled.small send(r,n),tle(size x,r) )
$

In the translation of the tuple we first have the translation of the two sub-expressions which we have already shown. From their respective output channel we receive the function handle and array handle. We can then output the tuple handle such that other processes can communicate with it. 
$
tle((lambda x.size x , [[1,2],[3,4]]), o_tup) =
&(nu o_F: ch(tl([Int]->Int))) . (nu o_arr : ch(tl([[Int]])) ) .\
    &overshell( tle(λ x. size x, o_F)   
    | tle([[1,2],[3,4]], o_arr), "Tuple elements" )\
    &| undershell(receive(o_F, f) . receive(o_arr, h_inp), "Function and array handle" ).
    (nu h_tup : tl(([Int] -> Int , [[Int]])) ). \
          &( undershell(! send(h_tup dot tup, f \, h_inp) | send(o_tup, h_tup), "Tuple communication") )

$

Lastly we have the translation of the mapping. First, from the translation of the tuple we get the handle which we can then use to unpack the tuple. From the input array in the tuple we get the length of the array which will be used later in the $Prepeat$ process (marked as Setup guard). Additionally we also get the elements from the array, that being the two sub-arrays. When we receive the array element we can then apply the function. With the value we receive after a function application we can create a cell using the $Pcell$ process for the resulting array. When we receive on $d$ (marked guard) we know the $Prepeat$ process has finished and can then output the new array handle.

$
tle(map (lambda x.size x , [[1,2],[3,4]]), o) = &(nu o_tup : ch(tl(([Int]->Int,[[Int]]))).  (nu h_out : tl([Int]))  . \ & (
      undershell(tle((lambda x.size x , [[1,2],[3,4]]),o_tup) //  -- §3
    | receive(o_tup, h_tup : tl(([Int]->Int,[[Int]]))).,"Tuple") \
        & undershell(receive(h_tup dot tup, f : tl([Int] -> Int) \,
                   h_inp : tl([[Int]]) ).,"Unpack tuple")\

        &undershell(receive(h_inp dot len, n : Int), "Input array size").     //-- n = 2
        (nu h_all : ch(Int , tl([Int]))). \
        &undershell(broad(h_inp dot all, h_all) .,"Get input array elements") 
        (nu r_idx : ch(Int) ).   (nu d : ch(Int)). \
        &(  undershell(Prepeat(n , r_idx , d),"Setup guard")   //-- typed Repeat

        | undershell(!receive(h_all, i : Int \, v_sub : tl([Int]))., "Receive input array element") \
            &(nu r_sub : ch(Int)).
            undershell(send(f, v_sub \, r_sub) .        //-- call the λ
            receive(r_sub, s_z:Int).,"apply function") \
            &undershell(receive(r_idx, \_ : Int).  Pcell(h_out , i , s_z , Int),"Unguard new array element") //-- fill output cell

        | undershell(circle.small.filled receive(d, \_ : Int).,"Guard") \ & send(o, h_out)        //-- important reduction
        | !send(h_out dot len,n) )
    )

$

/*
$
tle([1],o_A) = &(nu o_5 : ch(Int)) . (nu h_A : tl([Int])). ( overshell(send(o_5,1), tle(1,o_5)) | \ &o_5(v_1 : Int). ( undershell( Pcell(h_A, 0, v_1, Int) | send(h_A dot len,1) | send(o_A,h_A), "array:" [1]) ) ) 
\ \

tle([2,3],o_B) = & (nu o_6 : ch(Int)) . (nu o_7 : ch(Int)) . (nu h_B : tl([Int])) .( overshell( send(o_6,2), tle(2,o_6)) | overshell( send(o_7,3), tle(3,o_7)) | \ &o_6(v_2 : Int). o_7(v_3 : Int). \
&(undershell(Pcell(h_B, 0, v_2, Int) | Pcell(h_B, 1, v_3, Int) | send(h_B dot len,2) | send(o_B,h_B), "array:" [2,3]) )
)
$
This part of the translation is quite simple. First the values of the array are translated and then the array is created using the $Pcell$ process just like in the indexing example. Next we have the translation of the outer array. We create the array using the handles we received from the translation of the two inner arrays as the value on the index. 

$
tle([[1],[2,3]],o_3) = &(nu o_A : ch(tl([Int]))) . (nu o_B : ch(tl([Int]))). (nu h_out : tl([[Int]]) ). \
    & ( tle([1],o_A) | tle([2,3],o_B) | o_A (h_A : tl([Int])). o_B (h_B : tl([Int])). \
    &( undershell(Pcell(h, 0, h_A, tl([Int])) | Pcell(h, 1, h_B, tl([Int]))
      | send(h dot len,2)
      | send(o_3,h_out), "array:" [[1],[2,3]]) )
    )
$

We then have the translation of #size. 

$  tle(size, o_2) = &(nu o_4 : ch(tl([tau]))) . (tle(e_1,o_4) |  receive(o_4,h_e_1 : tl([tau])) .  receive(h_e_1 dot len, n_len : Int) . circle.small.filled send(o_2, n_len))$

Lastly we have the translation of #map.

$
  tle(map (size, [[1],[2,3]]),o) =& (nu o_1 : ch(t₁) ) .                  //-- channel for the tuple result above
  (nu h_out : @{ch(Int\,Int), ch(Int), ch(Int)}) . \ //  -- handle of the resulting array [1,2]
  &( nu o_2 : ch(⟦[Int]→Int⟧)     // -- for ‘size’
    nu o_3 : ch(⟦[[Int]]⟧)      //  -- for the outer array
    ( tle(size,o_2)
    | ⟦[[1],[2,3]]⟧o_3          // -- built by two nested applications of the array rule
    \
    &| o_2(f). o_3(h_inp). 
    
    ν h_tuple : t₁. ( !send(h_tuple dot tup, f \, h_inp) | o_1⟨h_tuple⟩ )
    )      //-- Section 1 
  | \ &o_1(h_tuple : t₁).
      h_tuple dot tup (f : ⟦[Int]→Int⟧ , h_inp : ⟦[[Int]]⟧). \
      &h_inp dot len (2 : Int).         // -- here n = 2
      ν h_all : ch(Int\,⟦[Int]⟧). 
      h_inp dot all :⟨h_all⟩ . 
      ν r  : ch(Int) .
      \ &ν d  : ch(Int) . 
      ( Prepeat(n,r,d)             // -- Equation (4), Chapter 7
      | !h_all (i : Int, v_sub : ⟦[Int]⟧).
          ν r_1 : ch(Int).
          \ & f⟨v_sub , r_1⟩ .          // -- apply size
           r_1(s_z : Int).
           r (\_ : Int) . 
          Pcell(h_out , i , s_z , Int)   // -- Equation (3), Chapter 7
      \ &| ∙ d(\_ : Int).  o⟨h_out⟩          // -- emit the handle of the array of sizes
      | !h_out dot len⟨n⟩
      )
  )
 $

 */