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

Definition pos_to_symbol (p : positive) : symbol.t :=
  nat_to_symbol (Pos.to_nat p).

Definition pos_from_symbol (s : symbol.t) : positive :=
  Pos.of_nat (nat_from_symbol s).

Lemma pos_to_from_symbol : forall p, pos_from_symbol (pos_to_symbol p) = p.
Proof.
  intros.
  unfold pos_to_symbol, pos_from_symbol.
  now rewrite nat_to_from_symbol, Pos2Nat.id.
Qed.

Definition Z_to_symbol (z : Z) : symbol.t :=
  match z with
  | Z0 => symbol.of_string_unsafe "0"
  | Zpos p => pos_to_symbol p
  | Zneg p => "-"%char :: pos_to_symbol p
  end.

Definition Z_from_symbol (s : symbol.t) : Z :=
  match s with
  | [] => 0%Z (* bogus! *)
  | c :: s' =>
    if ascii_dec c "0" then 0%Z
    else if ascii_dec c "-" then Zneg (pos_from_symbol s')
    else Zpos (pos_from_symbol s)
  end.

Lemma inc_digits_non_empty :
  forall l,
    inc_digits 10 l <> [].
Proof.
  destruct l; simpl.
  - congruence.
  - repeat break_match; congruence.
Qed.

Lemma digits'_10_non_empty :
  forall n acc, acc <> [] -> digits' 10 acc n <> [].
Proof.
  induction n; simpl; intros.
  - auto.
  - apply IHn. apply inc_digits_nonempty.
Qed.

Lemma digits_10_non_empty :
  forall n, digits 10 n <> [].
Proof.
  intros.
  unfold digits.
  destruct (digits' 10 [0] n) eqn:?.
  - intro. eapply digits'_10_non_empty; eauto. congruence.
  - simpl. intro H. apply app_eq_nil in H. intuition congruence.
Qed.

Lemma nat_to_symbol_non_empty :
  forall n, nat_to_symbol n <> [].
Proof.
  intros.
  unfold nat_to_symbol.
  intro H.
  apply map_eq_nil in H.
  eapply digits_10_non_empty; eauto.
Qed.

Lemma pos_to_symbol_non_empty :
  forall p, pos_to_symbol p <> [].
Proof.
  intros.
  unfold pos_to_symbol.
  apply nat_to_symbol_non_empty.
Qed.


  Lemma inc_digits_does_not_end_with_0 :
    forall l d p,
      (forall d p, l = p ++ [d] -> d = 0 -> False) ->
      inc_digits 10 l = p ++ [d] -> d = 0 -> False.
  Proof.
    induction l; simpl; intros.
    - destruct p; simpl in *; try congruence.
      destruct p; simpl in *; congruence.
    - set (b := match a with
                | 0 => false
                | 1 => false
                | 2 => false
                | 3 => false
                | 4 => false
                | 5 => false
                | 6 => false
                | 7 => false
                | 8 => false
                | 9 => true
                | S (S (S (S (S (S (S (S (S (S _))))))))) => false
                end) in *.
      destruct b eqn:? in *.
      + repeat (destruct a; try discriminate).
        destruct p; simpl in *; invc H0.
        * apply inc_digits_nonempty in H4. intuition.
        * apply IHl in H4; auto.
          intros.
          eapply H with (d := d) (p := 9 :: _).
          subst. simpl. eauto. auto.
      + destruct p; simpl in *; invc H0.
        * discriminate.
        * eapply H with (p0 := _ :: _). simpl. eauto. auto.
  Qed.

Lemma digits'_10_does_not_end_with_0 :
  forall n acc d p,
    (forall d p, acc = p ++ [d] -> d = 0 -> False) ->
    digits' 10 acc n = p ++ [d] ->
    d = 0 ->
    False.
Proof.
  induction n; simpl; intros.
  - eauto.
  - eapply IHn; [| apply H0|]; auto.
    eauto using inc_digits_does_not_end_with_0.
Qed.

Lemma digits_10_does_not_start_with_0 :
  forall n d l,
    n <> 0 ->
    digits 10 n = d :: l ->
    d = 0 ->
    False.
Proof.
  unfold digits.
  intros.
  apply f_equal with (f := @rev _) in H0.
  rewrite rev_involutive in *.
  simpl in *.
  destruct n.
  - congruence.
  - simpl in H0.
    eapply digits'_10_does_not_end_with_0 in H0; auto.
    intros.
    repeat (destruct p; simpl in *; try congruence).
Qed.

Lemma nat_to_symbol_does_not_start_with_0 :
  forall n c s,
    n <> 0 ->
    nat_to_symbol n = c :: s ->
    c = "0"%char ->
    False.
Proof.
  unfold nat_to_symbol.
  intros.
  destruct (digits 10 n) eqn:? in *; simpl in *; invc H0.
  eapply digits_10_does_not_start_with_0 in Heql; auto.

  pose proof (digits_in_bounds n 10 n0 ltac:(omega)).
  rewrite Heql in *. simpl in *.
  specialize (H0 (or_introl eq_refl)).
  do 10 try destruct n0; simpl in H3; try discriminate.
  - auto.
  - omega.
Qed.

Lemma pos_to_symbol_does_not_start_with_0 :
  forall p c s,
    pos_to_symbol p = c :: s ->
    c = "0"%char ->
    False.
Proof.
  unfold pos_to_symbol.
  intros.
  eapply nat_to_symbol_does_not_start_with_0; try exact H; auto.
  pose proof (Pos2Nat.is_pos p). omega.
Qed.

Lemma nat_to_symbol_does_not_start_with_minus :
  forall n c s,
    nat_to_symbol n = c :: s ->
    c = "-"%char ->
    False.
Proof.
  unfold nat_to_symbol.
  intros.
  destruct (digits 10 n) eqn:? in *; simpl in *; invc H.
  pose proof (digits_in_bounds n 10 n0 ltac:(omega)).
  rewrite Heql in *. simpl in *.
  specialize (H (or_introl eq_refl)).
  do 10 try destruct n0; simpl in H2; try discriminate.
  omega.
Qed.

Lemma pos_to_symbol_does_not_start_with_minus :
  forall p c s,
    pos_to_symbol p = c :: s ->
    c = "-"%char ->
    False.
Proof.
  unfold pos_to_symbol.
  intros.
  eapply nat_to_symbol_does_not_start_with_minus; try exact H; auto.
Qed.


Lemma Z_to_from_symbol : forall z, Z_from_symbol (Z_to_symbol z) = z.
Proof.
  intros.
  unfold Z_from_symbol, Z_to_symbol.
  destruct z; simpl; auto.
  - break_match.
    + now apply pos_to_symbol_non_empty in Heqt.
    + break_if.
      * exfalso. eapply pos_to_symbol_does_not_start_with_0; eauto.
      * break_if.
        -- exfalso. eapply pos_to_symbol_does_not_start_with_minus; eauto.
        -- now rewrite <- Heqt, pos_to_from_symbol.
  - now rewrite pos_to_from_symbol.
Qed.

Lemma pos_to_symbol_wf :
  forall p, symbol.wf (pos_to_symbol p).
Proof.
  unfold pos_to_symbol.
  auto using nat_to_symbol_wf.
Qed.

Lemma Z_to_symbol_wf :
  forall z,
    symbol.wf (Z_to_symbol z).
Proof.
  destruct z; simpl.
  - compute. intuition congruence.
  - auto using pos_to_symbol_wf.
  - break_match.
    + compute. intuition congruence.
    + split.
      * compute. intuition congruence.
      * rewrite <- Heqt. auto using pos_to_symbol_wf.
Qed.




