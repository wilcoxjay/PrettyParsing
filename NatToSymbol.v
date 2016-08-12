Require Import List Ascii Omega.
Import ListNotations.

From PrettyParsing Require Import LexicalConsiderations.
From StructTact Require Import StructTactics BoolUtil.

Fixpoint inc_digits (base : nat) (l : list nat) : list nat :=
  match l with
  | [] => [1]
  | d :: l => if base =? (S d) then 0 :: inc_digits base l
             else S d :: l
  end.

Fixpoint digits' (base : nat) (acc : list nat) (n : nat) : list nat :=
  match n with
  | 0 => acc
  | S n => digits' base (inc_digits base acc) n
  end.

Definition digits (base : nat) (n : nat) : list nat := List.rev (digits' base [0] n).

Eval compute in digits 10 1234.

Definition decimal_digit_to_ascii (d : nat) : ascii :=
  ascii_of_nat (48 + d).

Definition ascii_to_decimal_digit (a : ascii) : nat :=
  nat_of_ascii a - 48.

Lemma decimal_digit_to_from_ascii :
  forall d,
    0 <= d < 10 ->
    ascii_to_decimal_digit (decimal_digit_to_ascii d) = d.
Proof.
  do 10 try destruct d; intros; try omega; auto.
Qed.

Definition nat_to_symbol (n : nat) : symbol.t :=
  List.map decimal_digit_to_ascii (digits 10 n).

Lemma wf_map :
  forall A (l : list A) (f : A -> _),
    List.Forall (fun a => ~ chars.reserved (f a)) l ->
    l <> [] ->
    symbol.wf (List.map f l).
Proof.
  induction 1; intros.
  - intuition.
  - destruct H0.
    + simpl. auto.
    + rewrite map_cons.
      cbn [symbol.wf].
      rewrite map_cons.
      rewrite <- map_cons.
      split.
      * auto.
      * apply IHForall.
        discriminate.
Qed.

Lemma decimal_digit_to_ascii_not_reserved :
  forall d,
    0 <= d < 10 ->
    ~ chars.reserved (decimal_digit_to_ascii d).
Proof.
  unfold decimal_digit_to_ascii.
  do 10 try destruct d; intros; try omega; compute; intuition discriminate.
Qed.

Lemma inc_digits_in_bounds :
  forall base acc d,
    (forall d, In d acc -> 0 <= d < base) ->
    2 <= base ->
    In d (inc_digits base acc) ->
    0 <= d < base.
Proof.
  induction acc; simpl; intros.
  - intuition.
  - break_if; simpl in *; break_or_hyp.
    + intuition.
    + auto.
    + do_bool. specialize (H a (or_introl eq_refl)). omega.
    + auto.
Qed.

Lemma digits'_in_bounds :
  forall n base acc,
    2 <= base ->
    (forall d, In d acc -> 0 <= d < base) ->
    forall d, In d (digits' base acc n) -> 0 <= d < base.
Proof.
  induction n; simpl; intros.
  - auto.
  - apply IHn in H1; auto.
    intros. apply inc_digits_in_bounds in H2; auto.
Qed.

Lemma digits_in_bounds :
  forall n base d,
    2 <= base ->
    In d (digits base n) ->
    0 <= d < base.
Proof.
  unfold digits.
  intros.
  apply in_rev in H0.
  apply digits'_in_bounds in H0; auto.
  simpl. intuition.
Qed.

Lemma inc_digits_nonempty :
  forall base acc, inc_digits base acc <> [].
Proof.
  destruct acc; simpl.
  - discriminate.
  - break_if; discriminate.
Qed.

Lemma digits'_nonempty :
  forall base n acc,
    acc <> [] ->
    digits' base acc n <> [].
Proof.
  induction n; simpl; auto using inc_digits_nonempty.
Qed.

Lemma digits_nonempty :
  forall base n, digits base n <> [].
Proof.
  unfold digits.
  intros.
  intro.
  destruct (digits' base [0] n) eqn:?.
  - eapply digits'_nonempty; eauto.
    discriminate.
  - simpl in H. apply app_eq_nil in H. intuition discriminate.
Qed.

Lemma nat_to_symbol_wf :
  forall n,
    symbol.wf (nat_to_symbol n).
Proof.
  unfold nat_to_symbol.
  intros.
  apply wf_map.
  apply Forall_forall.
  intros d H.
  apply decimal_digit_to_ascii_not_reserved.
  - apply digits_in_bounds in H; auto. omega.
  - apply digits_nonempty.
Qed.

Fixpoint from_digits (base : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | d :: l => base * from_digits base l + d
  end.

Definition nat_from_symbol (s : symbol.t) :=
  from_digits 10 (List.rev (List.map ascii_to_decimal_digit s)).

Lemma from_digits_inc_digits :
  forall base l,
    from_digits base (inc_digits base l) = S (from_digits base l).
Proof.
  induction l; simpl.
  - omega.
  - break_if; simpl.
    + rewrite IHl. do_bool. subst. simpl.
      rewrite <- mult_n_Sm. omega.
    + omega.
Qed.

Lemma from_digits_digits':
  forall base n acc, from_digits base (digits' base acc n) = n + from_digits base acc.
Proof.
  induction n; simpl; intros.
  - auto.
  - rewrite IHn. rewrite from_digits_inc_digits. omega.
Qed.

Lemma from_digits_digits:
  forall base n, from_digits base (rev (digits base n)) = n.
Proof.
  intros.
  unfold digits.
  rewrite rev_involutive.
  rewrite from_digits_digits'.
  simpl. omega.
Qed.

Lemma nat_to_from_symbol : forall n, nat_from_symbol (nat_to_symbol n) = n.
Proof.
  unfold nat_to_symbol, nat_from_symbol.
  intros.
  rewrite map_map.
  erewrite map_ext_in.
  - now rewrite map_id, from_digits_digits.
  - intros. rewrite decimal_digit_to_from_ascii; auto.
    eapply digits_in_bounds; eauto.
    omega.
Qed.

Lemma nat_to_symbol_in_bounds :
  forall n c, In c (nat_to_symbol n) -> 48 <= nat_of_ascii c < 58.
Proof.
  unfold nat_to_symbol.
  intros.
  apply in_map_iff in H.
  break_exists. break_and.
  apply digits_in_bounds in H0; try omega.
  unfold decimal_digit_to_ascii in *.
  subst c.
  rewrite nat_ascii_embedding; omega.
Qed.
