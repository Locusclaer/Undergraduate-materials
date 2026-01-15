(* 实践作业15：练习用destruct策略(分情形讨论)和其他策略配合进行证明 *)

Inductive bool : Type :=
  | true
  | false.
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(* ################################################################# *)
(** * Proof by Case Analysis *)

(** **** Exercise: 2 stars, standard (andb_true_elim2)

    Prove the following claim, marking cases (and subcases) with
    bullets when you use [destruct].

    Hint 1: Thus far, we've only ever used [simpl] to simplify the goal.
    It is also possible to use it to simplify hypotheses:
    use [simpl in H], where [H] is a hypothesis, to simplify it.
    You may find this useful in this exercise.

    Hint 2: You will eventually need to destruct both booleans, as in
    the theorems above. It is better to simplify the hypothesis
    before attempting to destruct the second boolean.

    Hint 3: If you reach a contradiction in the hypotheses, focus on
    how to [rewrite] using that contradiction. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct b eqn:Eb.
  - simpl in H.
    rewrite -> H.
    reflexivity.
  - simpl in H.
    discriminate H.
Qed.
(** [] *)

 

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

(** **** Exercise: 1 star, standard (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros n.
  destruct n as [| n'] eqn:En.
  - reflexivity.
  - reflexivity.
Qed.
(** [] *)


Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
(* FILL IN HERE *) Admitted.

(** **** Exercise: 3 stars, standard, optional (andb_eq_orb)

    Prove the following theorem.  (Hint: This can be a bit tricky,
    depending on how you approach it.  You will probably need both
    [destruct] and [rewrite], but destructing everything in sight is
    not the best way.) *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)
