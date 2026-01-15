Require Import Arith.   (* 导入自然数算术库 *)
Require Import ZArith.  (* 导入整数算术库 *)

(*
   Homework 7 - 命题逻辑的基本引理
   以下引理展示了命题逻辑中的基本推理规则
*)

(*
   imp_perm: 蕴含前提的交换
   原始形式: (P->Q->R) -> (Q->P->R)
   含义: 如果P和Q能推出R，那么Q和P也能推出R
   即前提的顺序可以交换
*)
Lemma imp_perm: forall P Q R, (P -> Q -> R) -> (Q -> P -> R).
Proof.
    (* 引入前提 *)
    intros P Q R H q p.  (* H: P->Q->R, q: Q, p: P *)
    (* 使用H: 要得到R，需要P和Q *)
    apply H.            (* 当前目标变为: P, Q *)
    assumption.         (* 证明P: 使用假设p *)
    assumption.         (* 证明Q: 使用假设q *)
Qed.
Print imp_perm.

(*
   delta_impR: 蕴含结论的重复
   原始形式: (P->Q) -> (P->P->Q)
   含义: 如果P能推出Q，那么P能推出(P->Q)
   即前提可以重复使用
*)
Lemma delta_impR: forall P Q, (P -> Q) -> (P -> P -> Q).
Proof.
    (* 引入前提 *)
    intros P Q H p1 p2.  (* H: P->Q, p1: P, p2: P *)
    (* 使用H: 要得到Q，需要P *)
    apply H.            (* 当前目标: P *)
    assumption.         (* 使用p1或p2都可以 *)
Qed.
Print delta_impR.

(*
   diamond: 钻石推理模式
   原始形式: (P->Q)->(P->R)->(Q->R->T)->P->T
   含义: 如果有三条推理链都能从P出发，可以汇合到T
*)
Lemma diamond: forall P Q R T, (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
Proof.
    (* 引入所有前提 *)
    intros P Q R T H1 H2 H3 p.  (* H1: P->Q, H2: P->R, H3: Q->R->T, p: P *)
    (* 使用H3: 要得到T，需要Q和R *)
    apply H3.
    (* 证明第一个子目标Q *)
    apply H1.          (* 使用H1: P->Q *)
    assumption.        (* 提供P *)
    (* 证明第二个子目标R *)
    apply H2.          (* 使用H2: P->R *)
    assumption.        (* 提供P *)
Qed.
Print diamond.

(*
   weak_peirce: 弱皮尔士定律
   原始形式: ((((P->Q)->P)->P)->Q)->Q
   这是经典逻辑中皮尔士定律的一个弱化版本
*)
Lemma weak_peirce: forall P Q, ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
    intros P Q H.  (* H: (((P->Q)->P)->P) -> Q *)
    (* 要证明Q，使用H: 需要证明 ((P->Q)->P)->P *)
    apply H.
    (* 引入假设: (P->Q)->P *)
    intros H0.  (* H0: (P->Q)->P *)
    (* 要证明P，使用H0: 需要证明P->Q *)
    apply H0.
    (* 引入假设: P *)
    intro p.  (* p: P *)
    (* 要证明Q，使用H: 需要证明 ((P->Q)->P)->P *)
    apply H.
    (* 引入假设: (P->Q)->P *)
    intros H1.  (* H1: (P->Q)->P *)
    (* 要证明P，使用H1: 需要证明P->Q *)
    (* 但我们有p: P，可以直接用 *)
    assumption.
Qed.
Print weak_peirce.


(*
   Homework 8 - 谓词逻辑的推理
   涉及全称量词和谓词的推理规则
*)

(*
   all_perm: 全称量词中变量的交换
   含义: 如果对于所有x,y都有P(x,y)，那么对于所有x,y也有P(y,x)
   注意: 这里P是对称关系的前提下的结论
*)
Theorem all_perm: 
    forall (A: Type)(P: A -> A -> Prop),
    (forall x y: A, P x y) ->
    forall x y: A, P y x.
Proof.
    intros A P H x y.  (* A: 类型, P: 二元关系, H: ∀x y, P x y, x,y: 具体元素 *)
    (* 要证明P y x *)
    (* 使用H: 可以实例化为任意x,y *)
    apply H.  (* 自动匹配: 将H中的x实例化为y, y实例化为x *)
Qed.
(* 证明项显示 *)
Print all_perm.

(*
   resolution: 消解原理
   含义: 如果Q和R能推出S，且P能推出Q，那么P和R能推出S
   这是逻辑推理中的三段论
*)
Theorem resolution:
    forall (A: Type)(P Q R S: A -> Prop),
    (forall a: A, Q a -> R a -> S a) ->
    (forall b: A, P b -> Q b) ->
    (forall c: A, P c -> R c -> S c).
Proof.
    (* 引入所有前提和变量 *)
    intros A P Q R S H1 H2 c Hp Hr.
    (* H1: ∀a, Q a → R a → S a *)
    (* H2: ∀b, P b → Q b *)
    (* c: 特定元素, Hp: P c, Hr: R c *)
    (* 要证明: S c *)
    
    (* 使用H1: 要得到S c，需要Q c和R c *)
    apply H1.  (* 将a实例化为c *)
    (* 证明第一个子目标: Q c *)
    apply H2.  (* 使用H2: 要得到Q c，需要P c *)
    assumption.  (* 使用Hp: P c *)
    (* 证明第二个子目标: R c *)
    assumption.  (* 使用Hr: R c *)
Qed.
(* 证明项显示 *)
Print resolution.


(*
   Homework 9 - 否定相关的引理
   涉及否定和矛盾的推理
*)

(*
   nf: False的否定
   逻辑含义: 假命题的否定为真
   直觉: False永远不会成立
*)
Lemma nf: ~False.
Proof.
    (* ~False 展开为 False -> False *)
    intros H.  (* 假设H: False *)
    assumption.  (* 从False可以推出任何东西，包括目标False *)
Qed.
Print nf.

(*
   nnnp: 三重否定等价于一重否定
   逻辑含义: ~~~P 蕴含 ~P
   直觉主义逻辑中，三重否定等价于单重否定
*)
Lemma nnnp: forall P:Prop, ~~~P -> ~P.
Proof.
    intros P H1 H2.  (* H1: ~~~P, H2: P *)
    (* ~P 展开为 P -> False *)
    (* 当前目标: False *)
    
    (* 使用H1: ~~~P 即 ~(~(~P)) *)
    apply H1.  (* 应用~~~P，需要证明~~P *)
    (* ~~P 展开为 ~P -> False *)
    intros H3.  (* 假设~P *)
    (* 当前目标: False *)
    
    (* 使用H3: ~P *)
    apply H3.  (* 应用~P，需要证明P *)
    assumption.  (* 使用H2: P *)
Qed.
Print nnnp.

(*
   nnnpp: 从矛盾推出任意命题
   逻辑含义: 如果有~~~P和P，可以推出任意Q
   这是爆炸原理(Ex Falso Quodlibet)的应用
*)
Lemma nnnpp: forall P Q:Prop, ~~~P -> P -> Q.
Proof.
    intros P Q H1 H2.  (* H1: ~~~P, H2: P *)
    (* 当前目标: Q *)
    
    (* 使用消去策略处理三重否定 *)
    elim H1.  (* 处理~~~P *)
    (* 需要证明~~P *)
    intros np.  (* 假设~P *)
    (* 当前目标: False *)
    
    elim np.  (* 处理~P *)
    (* 需要证明P *)
    assumption.  (* 使用H2: P *)
    (* 从False可以推出Q *)
Qed.
Print nnnpp.

(*
   pqnq: 逆否命题
   逻辑含义: 如果P蕴含Q，且Q为假，则P为假
   这是逆否推理的变形
*)
Lemma pqnq: forall P Q:Prop, (P->Q) -> ~Q -> ~P.
Proof.
    intros P Q H1 H2.  (* H1: P->Q, H2: ~Q *)
    (* ~P 展开为 P -> False *)
    intros p.  (* 假设P *)
    (* 当前目标: False *)
    
    (* 使用H2: ~Q 即 Q -> False *)
    apply H2.  (* 需要证明Q *)
    (* 使用H1: P->Q *)
    apply H1.  (* 需要证明P *)
    assumption.  (* 使用p: P *)
Qed.
Print pqnq.

(*
   pqrpq: 从矛盾推出任意结论
   逻辑含义: 如果P同时蕴含Q和~Q，那么从P可以推出任何R
   这是爆炸原理的另一种形式
*)
Lemma pqrpq: forall P Q R:Prop, (P->Q) -> (P->~Q) -> P->R.
Proof.
    intros P Q R H1 H2 p.  (* H1: P->Q, H2: P->~Q, p: P *)
    (* 当前目标: R *)
    
    (* 首先从P推出Q *)
    assert (Hq: Q).  (* 声明中间引理: Q *)
    apply H1.  (* 使用H1: P->Q *)
    assumption.  (* 使用p: P *)
    
    (* 然后从P推出~Q *)
    assert (Hnq: ~Q).  (* 声明中间引理: ~Q *)
    apply H2.  (* 使用H2: P->~Q *)
    assumption.  (* 使用p: P *)
    
    (* 现在有Hq: Q 和 Hnq: ~Q，矛盾 *)
    (* 从矛盾可以推出任何R *)
    elim Hnq.  (* 应用~Q *)
    assumption.  (* 提供Q，得到矛盾 *)
Qed.
Print pqrpq.

(* 实践作业10：合取析取引理 *)

(* 这个引理表明对于任意类型A和四个元素a,b,c,d，c=c总是成立（自反性）
   证明通过重复使用析取的右引入和左引入来定位到c=c这个平凡情况 *)
Lemma and4:forall (A:Set)(a b c d:A), a=c \/ b=c \/ c=c \/ d=c.
Proof.
  right.        (* 选择第一个析取的右分支：b=c \/ c=c \/ d=c *)
  right.        (* 选择第二个析取的右分支：c=c \/ d=c *)
  left.         (* 选择第三个析取的左分支：c=c *)
  apply refl_equal.  (* 应用自反性公理，证明c=c *)
Qed.

(* 证明合取操作的结合律：A/\(B/\C)蕴含(A/\B)/\C *)
Lemma and_asso:forall A B C:Prop, A/\(B/\C)->(A/\B)/\C.
Proof.
  intros A B C H.     (* 引入命题A,B,C和假设H *)
  elim H.             (* 分解合取假设H为A和B/\C *)
  intros HA HBC.      (* 命名：HA是A的证明，HBC是B/\C的证明 *)
  elim HBC.           (* 继续分解HBC为B和C *)
  intros HB HC.       (* 命名：HB是B的证明，HC是C的证明 *)
  split.              (* 将目标(A/\B)/\C分解为两个子目标：A/\B 和 C *)
  split.              (* 将子目标A/\B进一步分解为A和B *)
  exact HA.           (* 第一个子目标A，直接用HA证明 *)
  exact HB.           (* 第二个子目标B，直接用HB证明 *)
  exact HC.           (* 第三个子目标C，直接用HC证明 *)
Qed.

(* 这个引理描述了一个逻辑推理：如果A蕴含B，C蕴含D，且A和C都成立，那么B和D都成立 *)
Lemma and_abcd : forall A B C D : Prop, 
  (A -> B) /\ (C -> D) /\ A /\ C -> B /\ D.
Proof.
  intros A B C D H.   (* 引入命题和假设H *)
  elim H.             (* 分解H为(A->B)和剩余部分 *)
  intros H1 H2.       (* H1: A->B, H2: (C->D)/\A/\C *)
  elim H2.            (* 分解H2为(C->D)和A/\C *)
  intros H2' H3.      (* H2': C->D, H3: A/\C *)
  elim H3.            (* 分解H3为A和C *)
  intros HA HC.       (* HA: A, HC: C *)
  split.              (* 将目标B/\D分解为B和D两个子目标 *)
  apply H1.           (* 使用H1: A->B，要证B需要先证A *)
  exact HA.           (* 用HA证明A，从而得到B *)
  apply H2'.          (* 使用H2': C->D，要证D需要先证C *)
  exact HC.           (* 用HC证明C，从而得到D *)
Qed.

(* 矛盾律：A和非A不能同时成立 *)
Lemma nana : forall A : Prop, ~(A /\ ~A).
Proof.
  intros A H.         (* 引入命题A和假设H（假设A/\~A成立） *)
  elim H.             (* 分解H为A和~A *)
  intros HA Hna.      (* HA: A, Hna: ~A *)
  apply Hna.          (* 应用Hna（即~A），需要证明A来引出矛盾 *)
  exact HA.           (* 用HA证明A，完成矛盾推导 *)
Qed.

(* 证明析取操作的结合律：A\/(B\/C)蕴含(A\/B)\/C *)
Lemma or_asso : forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
  intros A B C H.     (* 引入命题和假设H *)
  elim H.             (* 对H进行情况分析（分解析取） *)
  intro HA.           (* 第一种情况：HA是A的证明 *)
  left.               (* 选择目标(A\/B)\/C的左分支：A\/B *)
  left.               (* 进一步选择A\/B的左分支：A *)
  exact HA.           (* 直接用HA证明A *)
  intro HBC.          (* 第二种情况：HBC是B\/C的证明 *)
  elim HBC.           (* 对HBC进行情况分析 *)
  intro HB.           (* 子情况1：HB是B的证明 *)
  left.               (* 选择目标(A\/B)\/C的左分支：A\/B *)
  right.              (* 选择A\/B的右分支：B *)
  exact HB.           (* 用HB证明B *)
  intro HC.           (* 子情况2：HC是C的证明 *)
  right.              (* 选择目标(A\/B)\/C的右分支：C *)
  exact HC.           (* 用HC证明C *)
Qed.

(* 这个引理描述了一个推理：如果A或B成立，但A不成立，那么B必须成立 *)
Lemma abna : forall A B : Prop, (A \/ B) /\ ~A -> B.
Proof.
  intros A B H.       (* 引入命题和假设H *)
  elim H.             (* 分解H为A\/B和~A *)
  intros Hor Hna.     (* Hor: A\/B, Hna: ~A *)
  elim Hor.           (* 对Hor进行情况分析 *)
  intro HA.           (* 第一种情况：HA是A的证明 *)
  elim Hna.           (* 应用Hna（~A），需要证明A来引出矛盾 *)
  exact HA.           (* 用HA证明A，从而矛盾（此时目标B可由矛盾推导） *)
  intro HB.           (* 第二种情况：HB是B的证明 *)
  exact HB.           (* 直接用HB证明B *)
Qed.

(* 双重否定排中律：非非(A或非A)总是成立（在构造性逻辑中成立） *)
Lemma nnana : forall A : Prop, ~~(A \/ ~A).
Proof.
  intros A.           (* 引入命题A *)
  intro H.            (* 引入假设H：假设~(A\/~A)成立 *)
  apply H.            (* 应用H，需要证明A\/~A来引出矛盾 *)
  right.              (* 选择证明A\/~A的右分支：~A *)
  intro H2.           (* 引入假设H2：假设A成立 *)
  apply H.            (* 再次应用H（即~(A\/~A)），需要证明A\/~A *)
  left.               (* 这次选择左分支：A *)
  exact H2.           (* 用H2证明A *)
Qed.

(* 实践作业11：存在量词Section *)

Section Existentials.
Variable A : Set.          (* 声明一个集合A *)
Variable P Q : A -> Prop.  (* 声明两个关于A的谓词P和Q *)

(* 证明：如果存在x满足P(x)或Q(x)，那么存在x满足P(x) 或 存在x满足Q(x) *)
Lemma ex1 : (exists x : A, P x \/ Q x) -> (ex P) \/ (ex Q).
Proof.
  intro H.             (* 引入假设H *)
  elim H.              (* 分解存在量词H，得到具体的x和证明 *)
  intros x Hx.         (* x: A, Hx: P x \/ Q x *)
  elim Hx.             (* 对Hx进行情况分析 *)
  intro Hp.            (* 情况1: Hp是P x的证明 *)
  left.                (* 选择左分支：存在x满足P(x) *)
  exists x.            (* 提供见证x *)
  exact Hp.            (* 用Hp证明P x *)
  intro Hq.            (* 情况2: Hq是Q x的证明 *)
  right.               (* 选择右分支：存在x满足Q(x) *)
  exists x.            (* 提供见证x *)
  exact Hq.            (* 用Hq证明Q x *)
Qed.

(* 证明反向蕴含：如果存在x满足P(x) 或 存在x满足Q(x)，那么存在x满足P(x)或Q(x) *)
Lemma ex2 : (ex P) \/ (ex Q) -> exists x : A, P x \/ Q x.
Proof.
  intro H.             (* 引入假设H *)
  elim H.              (* 对H进行情况分析 *)
  intro Hp.            (* 情况1: Hp是存在x满足P(x)的证明 *)
  elim Hp.             (* 分解存在量词Hp *)
  intros x Hp'.        (* 得到具体的x和Hp': P x *)
  exists x.            (* 提供见证x *)
  left.                (* 选择左分支：P x *)
  exact Hp'.           (* 用Hp'证明P x *)
  intro Hq.            (* 情况2: Hq是存在x满足Q(x)的证明 *)
  elim Hq.             (* 分解存在量词Hq *)
  intros x Hq'.        (* 得到具体的x和Hq': Q x *)
  exists x.            (* 提供见证x *)
  right.               (* 选择右分支：Q x *)
  exact Hq'.           (* 用Hq'证明Q x *)
Qed.

(* 证明：如果所有x都满足P(x)，那么不存在y满足非P(y) *)
Lemma ex3 : (forall x : A, P x) -> ~(exists y : A, ~ P y).
Proof.
  intros Hall Hex.     (* 引入全称假设Hall和存在假设Hex *)
  elim Hex.            (* 分解存在量词Hex *)
  intros y Hny.        (* 得到具体的y和Hny: ~P y *)
  apply Hny.           (* 应用Hny（需要证明P y来引出矛盾） *)
  apply Hall.          (* 应用全称假设Hall，它对于任意x（包括y）都给出P x *)
Qed.

(* 这个引理假设存在一个"万能"元素x满足所有谓词，但这会导致矛盾（因为存在假谓词） *)
Lemma ex4 : (exists x : A, (forall R : A -> Prop, R x)) -> 2 = 3.
Proof.
  intro H.             (* 引入假设H *)
  elim H.              (* 分解存在量词H *)
  intros x Hx.         (* 得到x和Hx: 对于所有谓词R，都有R x *)
  assert (Hfalse : False).  (* 声明一个中间目标False *)
  specialize (Hx (fun _ => False)).  (* 对Hx实例化R为常假谓词fun _ => False *)
  exact Hx.            (* 现在Hx断言了False，完成Hfalse的证明 *)
  elim Hfalse.         (* 从False可推出任何目标，包括2=3 *)
Qed.

End Existentials.