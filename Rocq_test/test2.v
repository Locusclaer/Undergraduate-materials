(*
 * 基本命题逻辑证明示例
 * 展示各种命题逻辑定理的证明
 * 使用策略：intros, apply, assumption
 *)

Require Import ZArith.
Require Import Arith.
Require Import Bool.

Section Test2. (* 定义测试区域Test2，声明命题变量P, Q, R, T *)
  Variables P Q R T: Prop. (* 声明P, Q, R, T为命题 *)
  
  (* 定理1：同一律 *)
  Lemma id_P: P->P. 
  Proof.
    intros p. (* 引入前提P作为假设p，当前目标从P->P变为P *)
    assumption. (* 当前目标P在假设p中，直接完成证明 *)
  Qed.
  Print id_P. (* 打印证明项，查看生成的lambda项 *)



  (* 定理2：函数自身的恒等映射 *)
  Lemma id_PP: (P->P)->(P->P).
  Proof.
    intros H p. (* 引入两个前提 H: P->P, p: P，当前目标从(P->P)->(P->P)变为P *)
    apply H. (* 应用假设H，需要P来得到P *)
    assumption. (* 当前目标P在假设p中 *)
  Qed.
  Print id_PP.



  (* 定理3：蕴涵传递性 *)
  Lemma imp_trans: (P->Q)->(Q->R)->P->R.
  Proof.
    intros H1 H2 p. (* 引入三个前提 H1: P->Q, H2: Q->R, p: P，当前目标变为：R *)
    apply H2. (* 应用H2，需要Q来得到R，新目标：Q *)
    apply H1. (* 应用H1，需要P来得到Q，新目标：P *)
    assumption. (* 当前目标P在假设p中 *)
  Qed.
  Print imp_trans.





  (* 定理4：前提交换 *)
  Lemma imp_perm: (P->Q->R)->(Q->P->R).
  Proof.
    intros H q p. (* 引入三个前提 H: P->Q->R, q: Q, p: P，当前目标变为：R *)
    apply H. (* 应用H，需要P和Q来得到R，生成两个子目标 *)
    assumption. (* 第一个子目标：P，在假设p中 *)
    assumption. (* 第二个子目标：Q，在假设q中 *)
  Qed.
  Print imp_perm.



  (* 定理5：忽略多余前提 *)
  Lemma ignore_Q: (P->R)->P->Q->R.
  Proof.
    intros H p q. (* 引入三个前提 H: P->R, p: P, q: Q，当前目标变为：R *)
    apply H. (* 应用H，需要P来得到R，新目标：P *)  
    assumption. (* 当前目标P在假设p中 *)
  Qed.
  Print ignore_Q.



  (* 定理6：合并重复前提 *)
  Lemma delta_imp: (P->P->Q)->P->Q.
  Proof.
    intros H p. (* 引入两个前提 H: P->P->Q, p: P，当前目标变为：Q *)
    apply H. (* 应用H，需要两个P来得到Q，生成两个子目标 *)
    assumption. (* 第一个子目标：P，在假设p中 *)
    assumption. (* 第二个子目标：P，在假设p中 *)
  Qed.
  Print delta_imp.




  (* 定理7：扩展前提 *)
  Lemma delta_impR: (P->Q)->(P->P->Q).
  Proof.
    intros H p1 p2. (* 引入三个前提 H: P->Q, p1: P, p2: P，当前目标变为：Q *)
    apply H. (* 应用H，需要P来得到Q，新目标：P *)
    assumption. (* 当前目标P在假设p1中（也可以使用p2） *)
  Qed.
  Print delta_impR.



  (* 定理8：菱形模式推理 *)
  Lemma diamond: (P->Q)->(P->R)->(Q->R->T)->P->T.
  Proof.
    intros H1 H2 H3 p. (* 引入四个前提 H1: P->Q, H2: P->R, H3: Q->R->T, p: P，当前目标变为：T *)
    apply H3. (* 应用H3，需要Q和R来得到T，生成两个子目标 *)
    apply H1. (* 第一个子目标：Q，应用H1和p可得 *)
    assumption. 
    apply H2. (* 第二个子目标：R，应用H2和p可得 *)
    assumption.
  Qed.
  Print diamond.

  (* 定理9：弱皮尔士定律 *)
  Lemma weak_peirce: ((((P->Q)->P)->P)->Q)->Q.
  Proof.
    intros H. (* 引入前提 H: (((P->Q)->P)->P)->Q，当前目标变为：Q *)
    apply H. (* 应用H，需要((P->Q)->P)->P来得到Q，新目标：((P->Q)->P)->P *)
    intros H1. (* 引入前提 H1: (P->Q)->P，当前目标变为：P *)
    apply H1. (* 应用H1，需要P->Q来得到P，新目标：P->Q *)
    intros p. (* 引入前提 p: P，当前目标变为：Q *)
    apply H. (* 应用H，需要((P->Q)->P)->P来得到Q，新目标：((P->Q)->P)->P *)
    intros H2. (* 引入前提 H2: (P->Q)->P，当前目标变为：P *)
    assumption. (* assumption策略：当前目标P在假设p中 *)
  Qed.
  Print weak_peirce. (* 打印证明项，观察复杂的lambda项结构 *)


  (* 方法1：直接证明（不使用cut和assert） *)
    Theorem theorem_method1: (P->Q)->(Q->R)->((P->R)->T->Q)->((P->R)->T)->Q.
    Proof.
    intros H1 H2 H3 H4.
    apply H3.
    
    (* 子目标1: 证明P->R *)
    intros p.
    apply H2.
    apply H1.
    assumption.
    
    (* 子目标2: 证明T *)
    apply H4.
    intros p.
    apply H2.
    apply H1.
    assumption.
    Qed.
    Print theorem_method1.

    (* 方法2：使用cut策略 *)
    Theorem theorem_method2: (P->Q)->(Q->R)->((P->R)->T->Q)->((P->R)->T)->Q.
    Proof.
    intros H1 H2 H3 H4.
    cut (P -> R).
    
    (* 第一个子目标: 假设P->R成立，证明Q *)
    intros H5.
    apply H3.
    assumption.
    apply H4.
    assumption.
    
    (* 第二个子目标: 证明P->R *)
    intros p.
    apply H2.
    apply H1.
    assumption.
    Qed.
    Print theorem_method2.

    (* 方法3：使用assert策略 *)
    Theorem theorem_method3: (P->Q)->(Q->R)->((P->R)->T->Q)->((P->R)->T)->Q.
    Proof.
    intros H1 H2 H3 H4.
    assert (H5: P -> R).
    
    (* 证明中间命题P->R *)
    intros p.
    apply H2.
    apply H1.
    assumption.
    
    (* 使用中间命题证明原目标 *)
    apply H3.
    assumption.
    apply H4.
    assumption.
    Qed.
    Print theorem_method3.

  
(* 结束Test2区域 *)
End Test2.