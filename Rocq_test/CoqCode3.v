(* A->B类型的扩展 *)
Require Import Arith.
Require Import ZArith.


(* 谓词示例 le *)
Check le.
Print le.

(* 逻辑联结词的类型 *)
Check not.
Check not True.
Check ~True.

Check or.
Check (or True True).
Check True \/ True.

Check and.
Check (and True False).
Check (True /\ False).

(* 依赖积的例子，定理le_n *)
(* le_n是Rocq库中提供的一个定理:对自然数来说，n<=n *)
Check le_n.

(* 关于依赖积证明的一些典型策略 *)

(* exact 和assumption:目标可转换即可 *)
Print lt. (* < *)
(* nat_scope辖域内，"lt n p"可以写成 "n < p" *)

Theorem conv_example: forall n:nat,7*5<n -> 6*6 <=n.
Proof.
    intros n H. (* H: 7*5 < n *)
    (* exact H. *) (* 代替下面的assumption也可以成功。*)
    assumption. (* 根据lt定义，目标可转换为H *)
(*
lt =
fun n m : nat => S n <= m
     : nat -> nat -> Prop
*)

Qed.

(* intro策略：将forall x:A...中的x加入前提 *)
Lemma L35_36: forall n:nat,7*5<n -> 6*6 <=n.
Proof.
    intro n.
    intro H. (* H: 7*5 < n *)
(* H: lt 35 n

lt =
fun n m : nat => S n <= m
     : nat -> nat -> Prop

(lt 35 n) = (S 35 <= n) 

 *)
    assumption. (* 变换规则隐藏了乘法所需要的算术计算 *)
Qed.

(* 用forall...表示最小命题逻辑中的命题，从而形成最小多态命题逻辑，无需在上下文中声明命题 *)
Theorem imp_trans: forall P Q R:Prop,(P->Q)->(Q->R)->P->R.
Proof.
    intros P Q R H H0 p.
    apply H0.
    apply H.
    assumption.
Qed.
Print imp_trans.

(* intro策略：如果目标不是一个积，但可以被归约为一个积，那么intro就可以引发所需要的归约。 *)
(* 定义neutral_left *)
Definition neutral_left (A:Set)(op:A->A->A)(e:A):Prop:= 
    forall x:A, op e x = x.

(* 目标看起来不是一个积，但可以转换为积 *)
Theorem one_neutral_left: neutral_left Z Zmult 1%Z.
Proof.
    (* neutral_left Z Zmult 1%Z 本身不是依赖积形式，
     * 但是根据它的定义，可以转换成依赖积形式。
     * 因此可以用intro z.
     *)
    intro z.
    auto with zarith.
Qed.
Print one_neutral_left.

(* apply 策略 *)
(* 简单情况：对约束变元实例化 *)
Theorem le_i_SSi:forall i:nat,i<=S(S i).
Proof.
    intro i.
    (* 查看定理le_S的类型，这不是证明中必需的 *)
    Check le_S.
    (* 定理le_S处于环境中，可以直接应用，实例化le_S *)
    apply le_S.
    apply le_S.
     (* 查看定理le_n的类型，这不是证明中必需的 *)
    Check le_n.
    (* 应用le_n，实例化le_n *)
    apply le_n.
Qed.

(* apply的另外一个简单例子：最小谓词逻辑 *)
(* 该定理表示：蕴涵上的全称量词是可分配的 *)
Theorem all_imp_dist:
    forall(A:Type)(P Q:A->Prop),
      (forall x:A, P x -> Q x)->
      (forall y:A,P y)->(forall z:A, Q z).
Proof.
    intros A P Q H H0 z.
    apply H. (* 实例化H *)
    apply H0. (* 实例化H0 *)
Qed.

(* 帮助apply: 使用"apply t with v1:=t1 ... vk:=tk" *)

Theorem le_mult_mult:
    forall a b c d:nat,a<=c->b<=d->a*b<=c*d.
Proof.
    intros a b c d H H0.
    Check Nat.le_trans.

    (* 因为无法实例化m的值，因此不能直接应用Nat.le_trans. *)
    (* apply Nat.le_trans.*)

    (* 帮助apply找到m(令m=c*b) *)
    apply Nat.le_trans with (m:=c*b).
    Check Nat.mul_le_mono_r.
    apply Nat.mul_le_mono_r.
    assumption.
    Check Nat.mul_le_mono_l.
    apply Nat.mul_le_mono_l;assumption.
Qed.
Print le_mult_mult.

(* 使用eapply策略：
 * 类似apply策略，但即使一些依赖变量没有被实例化，该策略也不会失败。*)
Theorem le_mult_mult2:
    forall a b c d:nat,a<=c->b<=d->a*b<=c*d.
Proof.
    intros a b c d H H0.
    (* eapply有无法示例化的变量时，用?id代替，可以之后再实例化。 *)
    eapply Nat.le_trans.
    Check Nat.mul_le_mono_l.
    eapply Nat.mul_le_mono_l.
    (* 实例化原未知变量为 a * ?m *)
    (* 产生了新目标 b<=?m，出现了新的存在变量?m。
     * 可以通过声明一个新的目标来示例化这个新的变量。
     * 用策略 eexact H0实现。
     *)
     eexact H0. (* 实例化?m为d *)
     apply Nat.mul_le_mono_r;assumption.
Qed.

(* apply和可转换性 *)
Theorem le_0_mult:forall n p:nat, 0*n<=0*p.
Proof.
    intros n p.
    Check le_n.
    apply le_n.
    (* 乘积被转换为0以保证能应用定理le_n *)
Qed.

(* 可转换性严格遵循递归定义中的模式，n*0形式的项不可以归约 *)
Theorem le_0_mult_R:forall n p:nat, n*0<=p*0.
Proof.
    intros n p.
    (* apply le_n. *) (* 不会成功，因为n*0无法被归约为0 *)
    Abort.

(* 寻找用于apply的定理 Search p *)

(* 下面这条指令让Rocq列出所有nat上证明n<=p的定理
 * 这些定理必须在当前环境或上下文中可用。
 *)
Search le. 

(* SearchPattern 按模式搜索。"_"为通配符*)
SearchPattern (_+_<=_)%Z.

(* 下面这个模式中?x也是通配符，但是两处?x表示相同的表达式 *)
SearchPattern (?x * _ <= ?x * _)%Z.

(* unfold策略应用：展开定义 *)
(* 能使用unfold的标识符必须是透明的，不透明的标识符无法展开。 *)
Theorem lt_S: forall n p:nat,n<p -> n<S p.
Proof.
    intros n p H.
    Print lt. (* 查看lt的定义，证明中非必须 *)
(* n < S p 相当于 lt n (S p)，即 S n <= S p*)
    unfold lt. (* 展开lt定义，为了能应用le_S *)
    Check le_S.
    apply le_S.
    trivial.
Qed.
Print lt_S.

(* Rocq中的相等性 *)
Check eq. (* 查看eq的类型 *)
(* eq a b也可以写成a=b 
 * 下面两条命令无法通过，因为等式两边类型不同
 *)
(*
Check not (eq true 1).
*)
(*
Check not (true=1).
*)

(* 使用等式引入规则证明 *)
Theorem ThirtySix: 9*4 = 6*6.
Proof.
    Check refl_equal. (* 等式引入规则，表示等式是自反的。此行非证明必须*)
    apply refl_equal. (* 乘法自动计算了 *)
Qed.

(* 三个等式消去规则，只有P的类型有所不同 *)
Check eq_ind.
Check eq_rec.
Check eq_rect.

(* 处理逻辑联结词 *)

(* 否定 *)
(* 否定第一例：反证法和elim的使用 *)
Section ex_false_quodlibet.
  Hypothesis ff:False. (* 上下文中包含False（可以推出任意命题） *)
  (* 证法1：用否定消去规则 *)
  Lemma ex1:200=284. (* 该矛盾式可以被证明（因为上下文中包含False） *)
  Proof.
    Check False_ind.
    apply False_ind. (* 该规则表示False推出一切 *)
    exact ff.  (*用exact使用上下文中的False假设 *)
    (* 下面两条策略中的任意一条也都可以替换exact ff*)
    (* apply ff. *)
    (* assumption. *)
  Qed.

  (* 证法2：直接用elim ff. *)
  Lemma ex2:200=284.
  Proof.
    (* 如果t具有类型False，elim t将会立即解决当前目标 *)
    elim ff. (* 推荐使用第二种方法证明 *)
  Qed.
End ex_false_quodlibet.

(* 否定第二例：elim H，H为P->False形式 *)
Theorem absurd:forall P Q:Prop,P->~P->Q.
Proof.
    intros P Q p H.
    (* 下面一行通过elim H策略消去否定(H:~P)，
     * 因为该假设与另一假设p矛盾。
     * 该证明使用了转换规则，因为类型~P的假设H也具有类型P->False,因此"H p"具有类型False 
     *)
    Print not. (*通过not(~)的定义可以看出 not P(即~P)也就是P->False (此句非证明必须)*)
    elim H. (* 消去False后，解决当前目标并将P作为当前目标（因为H：P->False） *)
    assumption.
Qed.

(* 否定第三例：不用elim策略 *)
Theorem double_neg_i:forall P:Prop,P->~~P.
Proof.
    (* ~~P看成 ~P->False，此处用了delta归约 *)
    intros P p H.
    (* H:~P看成H:P->False，用了delta归约
     * 可以用apply H.
     *)
    apply H.
    assumption.
    (* 上面的2行用下面这行策略代替也可以 *)
    (* elim H;assumption. *)
Qed.

(* 否定第四例：unfold not *)
Theorem contrap:forall A B:Prop,(A->B)->~B->~A.
Proof.
    intros A B.
    unfold not.
    Check imp_trans. (* 查看蕴涵传递规则，非证明必须 *)
    apply imp_trans. (* 应用蕴涵传递规则 *)
Qed.

(* 合取和析取 *)
(* 合取引入split *)
(* 第一种证法：应用conj规则（合取引入规则） *)
Theorem conj1:forall P Q R:Prop,P->Q->R->P/\Q/\R.
Proof.
    intros P Q R p q r.
    Check conj. (* 检查conj规则类型 *)
    apply conj.
    assumption.
    apply conj.
    assumption.
    assumption.
Qed.

(* 第二种证法：用split *)
Theorem conj2:forall P Q R:Prop,P->Q->R->P/\Q/\R.
Proof.
    split. (*相当于intros;apply conj.*)
    assumption.
    split;assumption.
Qed.

(* 第三种证法： *)
Theorem conj3:forall P Q R:Prop,P->Q->R->P/\Q/\R.
Proof.
    repeat split;assumption.
Qed.

(* 析取引入：left和right *)
(* 左引入规则和left策略： *)
(* 第一种证法：应用左引入规则 *)
Theorem distjL1:forall P Q:Prop,P->P\/Q.
Proof.
    intros P Q p.
    Check or_introl. (* 检查左引入规则，非证明必须 *)
    apply or_introl.
    assumption.
Qed.
(* 第二种证法：应用left策略 *)
Theorem distjL2:forall P Q:Prop,P->P\/Q.
Proof.
    left.
 (* 相当于 *)
 (* intros; apply or_introl. *)
    assumption.
Qed.

(* 右引入规则和right策略 *)
(* 第一种证法：应用右引入规则 *)
Theorem distjR1:forall P Q:Prop,Q->P\/Q.
Proof.
    intros P Q q.
    Check or_intror.
    apply or_intror.
    assumption.
Qed.
(* 第二种证法：应用right策略 *)
Theorem distjR2:forall P Q:Prop,Q->P\/Q.
Proof.
    right.
 (* 相当于 *)
 (* intros; apply or_intror. *)
    assumption.
Qed.

(* 综合使用left和right策略 *)
Theorem distj1:forall P Q R S:Prop,R->P\/Q\/R\/S.
Proof.
    right.
    right.
    left.
    assumption.
Qed.

(* 合取和析取的消去：elim *)
(* 合取的消去 *)

(* 合取消去证法1：用合取消去规则 *)
Theorem and_commutes1:forall A B:Prop,A/\B->B/\A.
Proof.
    intros A B H.
    Check and_ind. (* 检查合取消去规则 *)
    apply (and_ind) with (A:=A)(B:=B). (* 应用合取消去规则 *)
    intros a b.
    split;assumption. (* 合取引入策略证明第一目标 *)
    assumption. (* 证明第二目标 *)
Qed.

(* 合取消去证法2：用elim策略 *)
Theorem and_commutes2:forall A B:Prop,A/\B->B/\A.
Proof.
    intros A B H.
    elim H. (* 消去H后，合取A/\B变为两个前提A和B加入到原结论的前件中 *)
    split;assumption. (* 合取的引入 *)
Qed.
Print and_commutes2.

(* 析取的消去 *)
(* 析取消去证法1：用析取消去规则 *)
Theorem or_commutes1:forall A B:Prop,A\/B->B\/A.
Proof.
    intros A B H.
    Check or_ind.
    apply or_ind with (A:=A)(B:=B).
    intro a.
    right. (* 析取右引入 *)
    assumption. 
    intro b;left;assumption. (* 析取左引入 *)
    assumption.
Qed.
(* 析取消去证法2：用elim策略 *)
Theorem or_commutes2:forall A B:Prop,A\/B->B\/A.
Proof.
    intros A B H.
    elim H. (* 消去H：A\/B后，变为“A->结论”和“B->结论”两个目标 *)
    intro a;right;assumption.
    intro b;left;assumption.
Qed.

(* 存在量词： *)
Section exist1.
(* 存在量词借助常量ex定义 *)
Check ex.
Variables (A:Set)(x:A)(P:A->Prop).
(* ex P 即 exists x:A, P x (A为ex的隐参数，在ex P中可以不写出来)
 * 写成抽象形式即 fun x:A=> P x
 * 优先写成前两种形式。
 *)
Check (ex P).
End exist1.

(* 存在量词的消去和引入规则 *)
(* 证法1：用存在量词消去和引入规则 *)
Theorem ex_imp_ex1:forall(A:Type)(P Q:A->Prop),
  (ex P)->(forall x:A,P x ->Q x)->(ex Q).
Proof.
    intros A P Q H H0.
    Check ex_ind. (* 检查存在量词消去策略 *)
(*
ex_ind
     : forall (A : Type) (P : A -> Prop) (P0 : Prop),
       (forall x : A, P x -> P0) ->
       (exists y, P y) -> P0
*)
    apply ex_ind with (A:=A)(P:=P). (* 应用量词消去策略 *)
    intros a Ha.
    Check ex_intro. (* 检查存在量词引入策略 *)
    apply ex_intro with (x:=a). (* 应用量词引入策略 *)
    apply H0.
    assumption.
    exact H. (* 或 assumption. *)
Qed.

(* 存在量词消去策略和引入策略 *)
(* 证法2：用存在量词消去elim和引入exists策略 *)
Theorem ex_imp_ex2:forall(A:Type)(P Q:A->Prop),
  (ex P)->(forall x:A,P x ->Q x)->(ex Q).
Proof.
    intros A P Q H H0.
    elim H. (* H中的存在量词消去 *)
(* 这个策略实际上提供了一个满足该量词公式的变量（某个存在的量） *)
(* 
 * 类比辖域收缩扩张等值式：  
 * (forall x.(A(x)->B)) <=> ((exist x. A(x))->B)
 * 待证明的目标为B,
 * 上下文中有公式H：exist x.A(x)，
 * 则如果能证明((exist x. A(x))->B)，就能证明B。
 * elim H策略实际上解决了当前目标B并生成了目标（ forall x.(A(x)->B) ）
 * 也就是目标（(exist x.A(x)) -> B）
 *)
    intros a Ha. (* 消去存在量词后得到 a:A 和Ha:P a *)
    exists a. (* 存在量词引入 *)
(* exists a使用上下文中的一个假设a（某个存在的量）
 * 来证明一个存在量词公式。 
 *)
    apply H0.
    exact Ha. (* 或 assumption.*)
Qed.


