(* 命题和假设的声明。 *)
Section dom1.
  (* 局部声明P为一个命题 *)
  Variable P:Prop.

  (* 局部声明一个假设,h为假设名，P为假设命题 *)
  Hypothesis h:P. 

  (*与上面一行同义，在声明假设时推荐使用上面的Hypothesis形式*)
  Variable h1:P. 

  (* 同时声明多个假设 *) 
  Hypotheses h2 h3 h4: P. 

  (* 与上面一行同义，在声明假设时推荐使用上面的Hypotheses形式 *)
  Variables h5 h6 h7:P. 
End dom1.

(* 命题和公理的声明 *)
Parameter P:Prop. (* 全局声明P为一个命题 *)
Axiom x:P. (* 全局声明x为一个命题，即公理。 *)
Parameter x1:P. (* 与上面一行同义，在声明公理时推荐使用上面的Axiom形式 *)

(* 第一个命题的证明： *)
Section Minimal_propositional_logic. (* 建立Section，产生上下文 *)
  Variable P Q R: Prop. (* 声明P Q R 为命题 *)
  Theorem imp_trans: (P->Q)->(Q->R)->P->R. (* 陈述要证明的定理 *)
   (* Lemma imp_trans2:(P->Q)->(Q->R)->P->R.*)
   (*陈述待证明的定理也可以像上一行一样写成引理。*)

  Proof. (* 证明开始，为了易读 *)
    intros H H' p. (* 把命题蕴涵式的所有前件分别附加为前提 H H' p*)
    apply H'. (* 应用前提H'，将H'的前件作为新目标。H'的结论要和当前待证明结论相同。 *)
    apply H.
    
    (* apply p. *) (* 这条策略可以代替下面一条策略 *)
    assumption. (* 直接使用假设：识别出结论恰好为某一假设，应用该假设，不生成新目标。*)
  Qed. (* 建立和保存证明项 *)
  Print imp_trans. (*打印证明项*)

  (* 下面是相同定理的一步到位自动证明 *)
  Theorem imp_trans2: (P->Q)->(Q->R)->P->R.
  Proof.
    auto. (* 自动应用策略进行证明，只有部分简单定理可用。 *)
  Qed.
  Print imp_trans2. 
End Minimal_propositional_logic.

(* exact *)
Theorem theorem_P:P. (* 全局环境，证明P这个命题 *)
Proof.
  exact x. (* 因为环境中有x这个公理，因此x就是P的证明项，应用exact策略直接得到证明*)
Qed.
Print theorem_P.

(* exact的参数为证明项的情况： *)
Section dom2.
Variable P Q:Prop.
Theorem delta: (P->P->Q)->P->Q.
Proof.
    exact (fun(H:P->P->Q)(p:P)=>H p p). (* 直接用证明项作为exact的参数 *)
Qed.
Print delta.

(* Proof命令的一种变体，不需要使用Qed来终止证明。*)
Theorem delta2: (P->P->Q)->P->Q.
Proof (fun(H:P->P->Q)(p:P)=>H p p).
Print delta2.
End dom2.

(* assumption *)
Parameter T:Prop. (* 全局声明T为一个命题 *)
Axiom xt:T. (* 全局声明xt为公理T的证明项 *)
Section example_of_assumption.
  Variable P Q R:Prop.
  Hypothesis H: P->Q->R.
  Lemma L1: P->Q->R.
  Proof.
    assumption. (* 上下文中能找到结论，直接使用assumption *)
  Qed.

  Lemma L2:T.
  Proof.
    (* assumption. *)  (*assumption失败，因为上下文没有相应假设*)
    exact xt. (* exact xt成功，因为环境中声明了xt是命题T的证明项（公理）*)
    Qed.
End example_of_assumption.

(* apply *)
Section dom3.
  Variable P Q R T:Prop.
  Theorem apply_example: (Q->R->T)->(P->Q)->P->R->T.
  Proof.
    intros H H0 p. (* 待证命题的前件变为附加前提：H:(Q->R->T)，H0(P->Q), p:P *)
    (* 待证目标为R->T，它是H的秩为2的首类型，应用策略apply H后生成新目标Q。 *)
    apply H. 
    exact (H0 p). (* 新目标可以由 H0 p得到 *)
  Qed.
  Print apply_example.

  (* apply后生成2个子目标的例子 *)
  Theorem imp_dist:(P->Q->R)->(P->Q)->(P->R).
  Proof.
    intros H H' p. (* 待证命题的前件变为附加前提：H:(P->Q->R)，H'(P->Q), p:P *)
   (* 待证目标为R，它是H的秩为3的首类型，应用策略apply H后生成2个新子目标 *)
    apply H. 
    assumption. (* 第一个子目标P在上下文中出现了。*)
    apply H'. (* 第二个子目标Q先apply H' 得到新子目标P *)
    assumption. (* 新子目标P在上下文中出现 *)
  Qed.
  Print imp_dist. (* 观察apply的多重应用 *)

  (* 下面例子观察intros的应用。*)
  Theorem K:P->Q->P.
  Proof.
    intros p q.
    assumption.
  Qed.
  
  (* 上例中的intros和下例中的intro策略序列比较。*)
  Theorem K2:P->Q->P.
  Proof.
    intro p.
    intro q.
    assumption.
  Qed.

(* 下面例子演示交互证明过程，
 * 以及在交互证明中,show i的作用
 *)
  Theorem imp_show_i:(P->Q->R)->(P->Q)->(P->R).
  Proof.
    intros H H' p. (* 待证命题的前件变为附加前提：H:(P->Q->R)，H'(P->Q), p:P *)
    apply H. (* 待证目标为R，它是H的秩为3的首类型，应用策略apply H后生成2个新子目标 *)
    Show 1. (* 输出显示第1个目标。 *)
    Show 2. (* 输出显示第2个目标。 *)
    2:apply H'. (* 第二个子目标Q先apply H' 得到新子目标P，占据原第二子目标Q的位置 *)
    Show 2. (* 再确认一下第二子目标的前提和结论 *)
    2:assumption. (* 新子目标P在上下文中出现，对第二子目标可以用assumption *)
    assumption. (* 第一个子目标P在上下文中也出现了，也可以用assumption。*)
  Qed.
  Print imp_show_i. 

  (*(* Undo, Undo n, Restart, Abort *)
  Theorem imp_Undo:(P->Q->R)->(P->Q)->(P->R).
  Proof.
    intro H. (* 待证命题的前件变为附加前提：H:(P->Q->R) *)
    intro H'. (* 待证命题的前件变为附加前提：H'(P->Q) *)
    intro p. (* 待证命题的前件变为附加前提：p:P *)
    apply H. (* 待证目标为R，应用策略apply H后生成2个新子目标 *)
    Undo. (* 取消上一步操作 apply H *)
    Undo 2. (* 取消之前两步操作 intro p, intro H' *)
    Restart. (* 退回证明开始阶段 *)
    intros H H0 p.
    apply H.
    assumption. (* 第一个子目标P在上下文中出现了。*)
    Abort. (* 放弃证明了 *)
   (* Print imp_Undo. *) (* 打印不出imp_Undo，因为没有证明结束。但是Rocq可以继续向下运行。 *)*)

End dom3.

(* 展示不用证明策略，只用section机制构造证明的过程 *)
Section dom4. (* 这个section为了定义P Q为命题 *)
  Variable P Q: Prop.
  (* 待证明的定理为：(((P->Q)->Q)->Q)->P->Q *)
  Section proof_of_triple_impl. (* 这个Section为了构造证明 *)
    Hypothesis H: ((P->Q)->Q)->Q. (* 假设定理的第一个前提成立 *)
    Hypothesis p:P. (* 假设定理的第二个前提成立 *)

    (* 定理的待证明结论为：Q *)
    (* 为了证明Q，可以用前提H应用((P->Q)->Q)，
     * 因此先证明一个引理。
     *)
    Lemma Rem: (P->Q)->Q.
    Proof (fun H0:P->Q=> H0 p). (* 直接写lambda项作为该引理的证明 *)
   
    Theorem triple_impl: Q. (* 待证定理的结论 *)
    Proof (H Rem). (* 直接写证明项作为定理的证明 *)
  End proof_of_triple_impl.
  (* 在proof_of_triple_impl这个Section外打印该定理，会得到完整的证明项 *)
  Print triple_impl.
  (* 在proof_of_triple_impl这个Section外，
   * 引理Rem的陈述也发生了改变，新的陈述强调了证明过程中
   * 用到了H0和p。
   *)
  Print Rem.
End dom4.

(* 证明策略的结合 *)
Section tactical.
Variable P Q R T: Prop.

(* 简单复合策略 *)
Theorem then_example: P->Q->(P->Q->R)->R.
Proof.
  intros p q H.
  apply H;assumption.
  (* apply H应用于当前子目标，产生两个子目标，
  assumption应用到所有两个子目标。
  下面的策略可以代替上一条策略实现相同功能。
  ****************************************
  apply H.
  assumption.
  assumption.
  *)
  Qed.
  Print then_example.

(*另外一个简单策略组合的例子：*)
Theorem triple_impl_one_shot:(((P->Q)->Q)->Q)->P->Q.
Proof.
   intros H p;apply H;intros H0;apply H0;assumption.
  (* 上面用一个组合策略完成了证明，和下面这个证明实现同样功能：
  intros H p.
  apply H.
  intros H0.
  apply H0.
  assumption.
  *)
Qed.
Print triple_impl_one_shot.

(* 一般化复合证明策略 *)
Theorem compose_example:(P->Q->R)->(P->Q)->(P->R).
Proof.
  intros H H' p.
  (* apply H后得到P, Q两个子目标，
     第一个子目标直接assumption，
     第二个子目标需要apply H'后再assumption *)
  apply H;[assumption | apply H';assumption].
Qed.
Print compose_example.

(* || 泛证明策略（orelse） *)
Theorem orelse_example: (P->Q)->R->((P->Q)->R->(T->Q)->T)->T.
Proof.
  intros H r H0.
  (* apply H0产生3个子目标(P->Q),R,(T->Q)
     前2个可以用assumption，但第3个不行，但可以用intro H1.
   *)
  apply H0;(assumption||intro H1).
  apply H.
  Abort.

(* idtac证明策略 *)
Lemma L3: (P->Q)->(P->R)->(P->Q->R->T)->P->T.
Proof.
  intros H H0 H1 p.
  (* apply H1产生3个子目标 P，Q，R
   * 第一个先不动，后两个可以apply H和apply H0，
   * 最后得到3个可以用assumption的目标
   *)
  apply H1;[idtac | apply H | apply H0];assumption.
Qed.
Print L3.

(* fail 策略 *)
Theorem then_fail_example:(P->Q)->(P->Q).
Proof.
  intro X;apply X;fail. 
  (* 因为apply X不生成子目标，因此不会运行fail*)
Qed.

Theorem then_fail_example2:((P->P)->(Q->Q)->R)->R.
Proof.
  (* 下面一条复合策略会失败 *)
  (* intro X;apply X;fail. *)
  intro X;apply X.
  exact (fun p:P=>p). (* 直接找出两个子目标的证明项 *)
  exact (fun q:Q=>q).
Qed.
Print then_fail_example2.

(* try 泛证明策略 *)
Theorem try_example:(P->Q->R->T)->(P->Q)->(P->R->T).
Proof.
  intros H H' p r.
  (* apply H产生3个子目标，不能都用assumption，
     所以下面的策略会失败 *)
  (* apply H;assumption. *)
  apply H;try assumption. (*成功，能用assumption的就用，不能用的不做处理*)
  apply H';assumption.
Qed.
Print try_example.

End tactical.

(* 其他证明策略 *)

Section dom5. (* 为了定义P Q等为Prop *)
  Variable P Q R T:Prop.
  (* cut *)
  Section cut_dom.
    Hypotheses  (H: P->Q)
                (H0: Q->R)
                (H1:(P->R)->T->Q)
                (H2:(P->R)->T).
    Theorem cut_example: Q.
    Proof.
      (* 为了证明Q，用cut命令先证明(P->R)->Q，且 (P->R)*)
      cut (P->R).
      intros H3.
      apply H1.
      assumption.
      apply H2.
      assumption.
      (* 下面一条策略组合可以代替上面4条策略。*)
      (* apply H1;[assumption | apply H2;assumption]. *)

      intro p;apply H0;apply H;assumption.
    Qed.
  (* 打印cut_example的证明时，我们会发现生成的是Let-in结构 *)
   Print cut_example.   
 
  (* assert *)
  Theorem assert_example:Q.
  Proof.
    (* 先证明P->R,并将其作为引理H' *)
    assert (H':P->R).
    intro p;apply H0; apply H;assumption. (* 证明 P->R *)
    apply H1;[assumption | apply H2;assumption]. (* 证明Q(用到了引理H') *)
  Qed.
  Print assert_example.
  End cut_dom.

  (* auto *)
  Theorem triple_impl2:(((P->Q)->Q)->Q)->P->Q.
  Proof.
    auto.
  Qed.
  Print triple_impl2.

  (* trivial *)
  Theorem trivial_impl:(P->Q)->(Q->R)->P->R.
  Proof.
    intros.
    apply H0.
    apply H.
    trivial.
  Qed.

End dom5.

