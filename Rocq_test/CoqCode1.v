(* Requrie 引入三个库 *)
Require Import Arith. (* Rocq标准库，用于自然数 *)
Require Import ZArith. (* Rocq标准库，用于基本整数 *)
Require Import Bool. (* Rocq标准库，用于布尔型 *)

(* Open Scope 打开辖域 *)
Open Scope Z_scope. (* 打开整数辖域 *)

(* Locate 显示给定符号在各辖域中的解释 *)
Locate "*". (* *号在各辖域中的解释 *)

(* Print Scope 打印辖域信息 *)
Print Scope Z_scope. (* 打印整数辖域信息 *)

(* Check 命令：检查并显示项的类型 *)
(* 自然数 nat *)
Check 33%nat. (* %nat为定界关键字，指定33为自然数 *)
Check 0%nat.
Check O. (* 自然数 0 *)
Check S. (* 自然数上的后继函数 *)
Check 0. (* 因为最后打开的是整数辖域，所以默认0为整数*)

Open Scope nat_scope. (* 打开自然数辖域 *)
Check 33.
Check 0.

(* 整数 Z *)
Check 33%Z.
Check (-12)%Z.

Open Scope Z_scope.
Check (-12).
Check (33%nat).

(* 布尔值 Bool *)
Check true.
Check false.

(* 标识符的类型 *)
Check plus. (* plus为预定义的自然数加运算函数 *)
Check Zplus. (* Zplus为预定义的整数加运算函数 *)
Check negb.  (* 布尔非运算函数 *)
Check orb.   (* 布尔或运算函数 *)

(* 没定义过的标识符zero会显示错误 *)
(* Check zero. *) 

(* 函数应用的类型 *)
Check negb.
Check (negb true).
Check (negb (negb true)).

(* 函数应用左结合 *)
Check ifb. (* if b then s1 else s2 函数，接受布尔值b,s1,s2作为参数，返回布尔值 *)

(* Rocq的显示删掉了多余括号 *)
Check (((ifb (negb false))true)false).
Eval compute in (((ifb (negb false))true)false). 

(* 应用优先级出错 *)
(* Check (negb negb true). *)

(* 自然数的类型 *)
Open Scope nat_scope.
Check (S(S(S O))). (* 辖域内支持十进制数表示 *)
Check(mult(mult 5(minus 5 4)) 7). (* 辖域内支持中缀表示 *)

(* 十进制数和中缀算符只是语法美化，内部表示为S和O *)


(* 整数的类型 *)
Open Scope Z_scope.
(* Print Scope Z_scope. *)
Check Zmult.
Check Z.opp. (* 取负数：整数一元减 *)
Check (Z.opp (Zmult 3 (Zminus(-5)(-8)))).
Check ((-4)*(7-7)).

(* 多元函数只作用在一个参数上形成新的函数 *)
Open Scope nat_scope.
Check (plus 3).
Check (Zmult (-5)). (*虽然是nat_scope，但因Zmult需要整数参数，自动转换*)

Check (Zmult 3 45).
(* 类型错误，mult需要nat类型参数，-45是整数 *)
(* Check (mult 3 (-45)%Z). *) 

(* 函数抽象 *)
Check (fun n:nat=>(n+n+n)%nat).

Check Z_of_nat. (* nat类型转换为Z类型 *)
Check (fun n:nat => fun p:nat => fun z:Z => (Z_of_nat(n+p)+z)%Z).
Check (fun n p:nat=> fun z:Z=>(Z_of_nat(n+p)+z)%Z).
Check (fun (n p:nat)(z:Z)=>(Z_of_nat(n+p)+z)%Z).
(* 上述三个函数作用一样 *)

(* 类型推断 *)
Check (fun n (z:Z) f => (n+(Z_of_nat(f z)))%Z). (* 未指定f的类型，但能推断出其类型为Z->nat *)

(* 不允许出现 x x 这样的项，因为此时x必须同时具有A->B和 A的类型，Rocq不允许*)
(* Check (fun x=> x x). *) 

(* 匿名变量 *)
Check (fun n _:nat => n).

(* 局部绑定 ((n-p)^2 * ((n-p)^2 +n)) *)
Check(fun n p:nat =>
        (let diff := n-p in
         let square := diff * diff in
             square * (square + n))%nat).


(* 全局声明 *)
Parameter max_int : Z.
Check max_int.


Open Scope Z_scope.
(* 全局定义 *)
Definition min_int:=1-max_int.
Check min_int.
Print min_int.
(* 以下三种函数定义方法都可以 *)
Definition cute:=fun z:Z=>z*z*z.
Definition cute1 (z:Z):Z:=z*z*z.
Definition cute2 z := z*z*z. (* 参数和返回值类型由辖域中*的解释进行推断 *)
Print cute.
Print cute1.
Print cute2.

(* 定义泛函数以及在其他函数中应用 *)
Definition Z_thrice (f:Z->Z)(z:Z):=f(f(f z)).
Definition plus9:= Z_thrice(Z_thrice(fun z:Z=>z+1)).
Check Z_thrice.
Check plus9.
Eval compute in (plus9 0). (* 计算整数 0+9*)

(* Section 以及局部声明 *)

Section binomial_def. (* Section binomail_def 开始，简称B区 *)
  Variables a b:Z.  (* B区局部声明 *)
  Definition binomial z:Z := a*z+b. (* B区局部定义 *)
  Print binomial. (* B区内打印binomial定义 *)
  Section trinomial_def. (* Section trinomail_def 开始，简称T区 *)
    Variables c:Z. (* T区局部声明 *)
    Definition trinomial z:Z :=(binomial z)*z +c. (* T区局部定义 *)
    Print trinomial. (* T区内打印trinomial定义 *)
  End trinomial_def. (* T区结束 *)
  Print trinomial. (* T区外打印trinomial定义，原T区局部变量c成为参数 *)
End binomial_def. (* B区结束 *)
Print binomial. (* B区外打印binomial定义，原B区局部变量a,b都成为参数 *)
Print trinomial. (* B区外打印trinomial定义，原B,T区的所有局部变量都成为参数 *)

(* 使用Section中定义的变量 *)
Definition p1:Z->Z := binomial 5 (-3).
Definition p2:Z->Z := trinomial 1 0 (-1).
Definition p3:= trinomial 1 (-2) 1.
Check p3.

(* 只有在全局定义中被使用的局部变量才被抽象成新的参数 *)
Section mab.
  Variables m a b:Z.
  Definition f:= m*a*m.
  Definition g:= m*(a+b).
End mab.
Print f. (* m,a变为参数 *)
Print g. (* m, a, b变为参数 *)

(* 局部定义 *)
Section h_def.
  Variables a b:Z.
  Let s:Z := a+b.
  Let d:Z := a-b.
  Definition h:Z := s*s + d*d.
  Print h.
End h_def.
Print h. (* Section中的局部定义的变量变成了函数中的局部绑定 Let...in *)

(* 计算 *)
Definition Zsqr (z:Z):Z := z*z.
Definition my_fun (f:Z->Z)(z:Z):Z := f (f z).

(* 对项 (my_fun Zsqr)中的my_fun 和Zsqr标识符进行delta归约(即展开定义)
   []内的标识符可选，如果不写，则默认展开所有标识符
   cbv表示使用“传值调用”（cbv，优先计算参数）策略
 *)
Eval cbv delta [my_fun Zsqr] in (my_fun Zsqr).

Eval cbv delta [my_fun] in (my_fun Zsqr). (* 只展开my_fun *)

(* 对项(my_fun Zsqr)做标识符展开(delta归约)和函数应用(beta归约) *)
Eval cbv beta delta [my_fun Zsqr] in (my_fun Zsqr).

Print h. (* h是前面section中定义的函数 (a+b)^2+(a-b)^2 *)
(* 下面一行对项(h 56 79)进行标识符展开(delta归约)和函数应用(beta归约) *)
Eval cbv beta delta [h] in (h 56 78).
(* 下面一行对项 (h 56 79)做标识符展开(delta)、函数应用(beta)、局部绑定替换(zeta) *)
Eval cbv beta zeta delta [h] in (h 56 78).

(* 下面一行对项 (h 56 79) 进行所有4种规则的归约，并使用传值调用cbv *)
Eval compute in (h 56 78).
(* 下面一行对项 (my_fun Zsqr 3) 进行所有4种规则的归约，并使用传值调用cbv *)
Eval compute in (my_fun Zsqr 3).  (* (3^2)^2 *)  

(* 类型的类型 Set *)
Check Z. (* 整数类型Z的类型为Set *)
Check ((Z->Z)->nat->nat). (* 原子类型和->构造出的复合类型的类型也是Set *)

(* 类型空间 *)
Check Set.
Check Type. (* 所有层次的Type(i)都显示为Type *)

(* 定义规范说明 *)
Definition Z_bin : Set := Z->Z->Z. (* 给已有的类型起一个新的名字 *)

(* 下面一行的函数类型和之后定义的Zdist2类型实际都为Z->Z->Z，
   但Zdist2也可以写为Z_bin类型 *)
Check (fun z0 z1:Z => let d:=z0-z1 in d*d).
Definition Zdist2:Z_bin := fun z0 z1:Z=> let d:=z0-z1 in d*d.
Check Zdist2.

(* 强制转换操作符验证可转换类型 *)
Check (nat->nat). (* nat->nat属于specification，类型为Set *)
Check (nat->nat:Type). (* 强制转换类型为Type *)

(* 声明规范说明 *)
Section domain.
  Variable (D:Set)(op:D->D->D)(sym: D->D)(e:D). (* 声明了规范说明D 及其他变量*)
  Let diff: D->D->D :=
    fun (x y:D)=> op x (sym y).
    (*... *)
  Check diff. (* diff 可以用于多态扩展 *)
End domain.

(* 给出规范说明，找到类型为该规范说明的项 *)
Section realization.
  Variables (A B: Set). (* 声明两个类型A,B *)
  Let spec:Set :=(((A->B)->B)->B)->A->B. (* 定义规范说明 spec *)
  Let realization:spec      (* 找出了类型为spec的项（程序） *)
        := fun (f:((A->B)->B)->B) a => f (fun g => g a).
  Let realization2          (* 定义了一个与上一行同类型的项，没有类型声明 *)
        := fun (f:((A->B)->B)->B) a => f (fun g => g a).    
  Check realization. (* 检查项realization的类型是否与spec一致 *)
  Check realization2. (* 检查项realization2的类型是否与spec一致 *)
End realization.