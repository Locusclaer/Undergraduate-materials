(* 实践作业13：数值类型的定义和证明：factorial, ltb *)
(* ================================================================= *)
(** ** Numbers *)

(** **** Exercise: 1 star, standard (factorial)

    Recall the standard mathematical factorial function:

       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)

    Translate this into Rocq.

    Hint: Make sure you put a [:=] between the header we've provided
    and your definition.  If you see an error like "The reference
    factorial was not found in the current environment," it means
    you've forgotten the [:=]. *)

Fixpoint factorial (n:nat) : nat :=
  match n with
  | 0 => 1
  | S n' => (mult n (factorial n'))
  end.

Example test_factorial1:          (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2:          (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.
(** [] *)


(** When we say that Rocq comes with almost nothing built-in, we really
    mean it: even testing equality is a user-defined operation!
    Here is a function [eqb] that tests natural numbers for
    [eq]uality, yielding a [b]oolean.  Note the use of nested
    [match]es -- we could also have used a simultaneous match, as
    in [minus]. *)

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

(** Similarly, the [leb] function tests whether its first argument is
    less than or equal to its second argument, yielding a boolean. *)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

(** We'll be using these (especially [eqb]) a lot, so let's give
    them infix notations. *)

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

(** We now have two symbols that both look like equality: [=]
    and [=?].  We'll have much more to say about their differences and
    similarities later. For now, the main thing to notice is that
    [x = y] is a logical _claim_ -- a "proposition" -- that we can try to
    prove, while [x =? y] is a boolean _expression_ whose value (either
    [true] or [false]) we can compute. *)

(** **** Exercise: 1 star, standard (ltb)

    Fill in the definition of an [ltb] function that tests natural
    numbers for [l]ess-[t]han, yielding a [b]oolean.

    Hint: Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined
    function.  It can be done with just one previously defined
    function, but you can use two if you want. *)

Definition ltb (n m : nat) : bool :=
  if (n <=? m) then (if (n =? m) then false else true)
  else false.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1:             (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2:             (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3:             (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.
(** [] *)
