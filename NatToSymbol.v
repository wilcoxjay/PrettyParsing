Require Import List Ascii String Omega.
Import ListNotations.

Require Import Psatz.

From PrettyParsing Require Import LexicalConsiderations.
From StructTact Require Import StructTactics BoolUtil.

Fixpoint inc_digits (base : nat) (l : list nat) : list nat :=
  match l with
  | [] => [1]
  | d :: l => if base =? (S d) then 0 :: inc_digits base l
             else S d :: l
  end.

Fixpoint double_digits' (base : nat) (l : list nat) (carry : nat) : list nat :=
  match l with
  | [] =>
          match carry with
          | 0 => []
          | _ => [carry]
          end
  | d :: l =>
          let d' := 2 * d + carry in
          if base <=? d'
              then d' - base :: double_digits' base l 1
              else d' :: double_digits' base l 0
  end.

Definition double_digits (base : nat) (l : list nat) : list nat :=
    double_digits' base l 0.

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

Lemma double_digits'_in_bounds :
  forall base acc carry d,
    (forall d, In d acc -> 0 <= d < base) ->
    2 <= base ->
    0 <= carry < 2 ->
    In d (double_digits' base acc carry) ->
    0 <= d < base.
Proof.
  induction acc; simpl; intros.
  - break_match; simpl in *; intuition.
  - break_match; simpl in *; break_or_hyp.
    + do_bool. specialize (H a (or_introl eq_refl)). lia.
    + eapply IHacc with (carry := 1); eauto.
    + do_bool. specialize (H a (or_introl eq_refl)). lia.
    + eapply IHacc with (carry := 0); eauto.
Qed.

Lemma double_digits_in_bounds :
  forall base acc d,
    (forall d, In d acc -> 0 <= d < base) ->
    2 <= base ->
    In d (double_digits base acc) ->
    0 <= d < base.
Proof.
  intros. unfold double_digits in *. eauto using double_digits'_in_bounds.
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

Lemma double_digits_nonempty :
  forall base l, l <> [] -> double_digits base l <> [].
Proof.
  destruct l; intros; try (exfalso; congruence).
  cbn. break_if; simpl; discriminate.
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

Lemma from_digits_double_digits' :
  forall base l carry,
    from_digits base (double_digits' base l carry) = carry + 2 * (from_digits base l).
Proof.
  induction l; simpl; intros.
  - destruct carry; simpl; omega.
  - break_if; simpl in *.
    + rewrite IHl.
      repeat rewrite Nat.mul_add_distr_l.  rewrite Nat.mul_1_r.
      eapply leb_true_le in Heqb.
      omega.
    + rewrite IHl.
      repeat rewrite Nat.mul_add_distr_l.
      eapply leb_false_lt in Heqb.
      omega.
Qed.

Lemma from_digits_double_digits :
  forall base l,
    from_digits base (double_digits base l) = 2 * (from_digits base l).
Proof.
  intros. unfold double_digits. rewrite from_digits_double_digits'. omega.
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



Fixpoint pos_digits (base : nat) (p : positive) : list nat :=
    match p with
    | xH => [1]
    | xO p => double_digits base (pos_digits base p)
    | xI p => inc_digits base (double_digits base (pos_digits base p))
    end.

Lemma pos_digits_in_bounds :
  forall p base d,
    2 <= base ->
    In d (pos_digits base p) ->
    0 <= d < base.
Proof.
  induction p; simpl; intros.
  - eapply inc_digits_in_bounds; cycle 1; eauto.
    intros. eapply double_digits_in_bounds; eauto.
  - eapply double_digits_in_bounds; eauto.
  - break_or_hyp; try contradiction. lia.
Qed.

Lemma pos_digits_non_empty :
  forall base p, pos_digits base p <> [].
Proof.
  induction p; simpl.
  - eapply inc_digits_nonempty.
  - eapply double_digits_nonempty. auto.
  - discriminate.
Qed.

Definition pos_to_symbol (p : positive) : symbol.t :=
  List.map decimal_digit_to_ascii (List.rev (pos_digits 10 p)).

Lemma rev_eq_nil : forall A (l : list A), rev l = [] -> l = [].
Proof.
  intros.
  rewrite <- rev_involutive with (l := l).
  rewrite H. reflexivity.
Qed.

Lemma pos_to_symbol_wf :
  forall p,
    symbol.wf (pos_to_symbol p).
Proof.
  unfold pos_to_symbol.
  intros.
  apply wf_map.
  - apply Forall_forall. intros d H.
    apply decimal_digit_to_ascii_not_reserved.
    eapply in_rev in H.
    eapply pos_digits_in_bounds; eauto. omega.
  - assert (pos_digits 10 p <> []) by apply pos_digits_non_empty.
    contradict H. eauto using rev_eq_nil.
Qed.

Lemma pos_to_symbol_non_empty :
  forall p, pos_to_symbol p <> [].
Proof.
  intros.
  unfold pos_to_symbol.
  intro H.
  apply map_eq_nil in H.
  apply rev_eq_nil in H.
  eapply pos_digits_non_empty. eauto.
Qed.

Lemma pos_to_symbol_in_bounds :
  forall p c, In c (pos_to_symbol p) -> 48 <= nat_of_ascii c < 58.
Proof.
  unfold pos_to_symbol.
  intros.
  apply in_map_iff in H.
  break_exists. break_and.
  apply in_rev in H0.
  apply pos_digits_in_bounds in H0; try omega.
  unfold decimal_digit_to_ascii in *.
  subst c.
  rewrite nat_ascii_embedding; omega.
Qed.

(* return `None` when the input is zero *)
Fixpoint pos_from_digits (base : positive) (l : list nat) : option positive :=
    match l with
    | [] => None
    | 0 :: l =>
            match pos_from_digits base l with
            | None => None
            | Some x => Some (base * x)%positive
            end
    | S d :: l =>
            match pos_from_digits base l with
            | None => Some (Pos.of_succ_nat d)
            | Some x => Some (Pos.of_succ_nat d + base * x)%positive
            end
    end.

Lemma pos_from_digits_nat : forall base1 l,
    let base := S base1 in
    2 <= base ->
    pos_from_digits (Pos.of_succ_nat base1) l =
    match from_digits base l with
    | 0 => None
    | S n => Some (Pos.of_succ_nat n)
    end.
Proof.
  induction l; intros; cbn.
  - reflexivity.
  - rewrite IHl by eauto. unfold base.
    destruct a, (from_digits _ l); simpl in *.
    + rewrite Nat.mul_0_r. reflexivity.
    + f_equal. lia.
    + rewrite Nat.mul_0_r. simpl. reflexivity.
    + f_equal. lia.
Qed.

Lemma pos_from_digits_inc_digits : forall base1 l p,
    let base := S base1 in
    2 <= base ->
    pos_from_digits (Pos.of_succ_nat base1) l = Some p ->
    pos_from_digits (Pos.of_succ_nat base1) (inc_digits base l) = Some (Pos.succ p).
Proof.
  intros.
  rewrite pos_from_digits_nat in *; eauto. rewrite from_digits_inc_digits.
  unfold base. break_match_hyp; simpl.
  - discriminate.
  - invc H0. reflexivity.
Qed.

Lemma pos_from_digits_double_digits : forall base1 l p,
    let base := S base1 in
    2 <= base ->
    pos_from_digits (Pos.of_succ_nat base1) l = Some p ->
    pos_from_digits (Pos.of_succ_nat base1) (double_digits base l) = Some (2 * p)%positive.
Proof.
  intros.
  rewrite pos_from_digits_nat in *; eauto. rewrite from_digits_double_digits.
  unfold base. break_match_hyp; simpl.
  - discriminate.
  - invc H0. f_equal. lia.
Qed.

Lemma pos_from_digits_digits : forall base1 p,
    let base := S base1 in
    2 <= base ->
    pos_from_digits (Pos.of_succ_nat base1) (pos_digits base p) = Some p.
Proof.
  induction p; intros.
  - cbn.
    erewrite pos_from_digits_inc_digits with (p := (p~0)%positive); eauto.
    erewrite pos_from_digits_double_digits with (p := p); eauto.
  - cbn.
    erewrite pos_from_digits_double_digits with (p := p); eauto.
  - cbn.
    reflexivity.
Qed.

(* returns `None` if the input is zero *)
Definition pos_from_symbol' (s : symbol.t) : option positive :=
  pos_from_digits 10 (List.rev (List.map ascii_to_decimal_digit s)).

(* returns 1 if the input is zero *)
Definition pos_from_symbol (s : symbol.t) : positive :=
  match pos_from_symbol' s with
  | None => 1%positive
  | Some p => p
  end.

Lemma pos_to_from_symbol' : forall p, pos_from_symbol' (pos_to_symbol p) = Some p.
Proof.
  unfold pos_to_symbol, pos_from_symbol'.
  intros.
  rewrite map_map.
  erewrite map_ext_in.
  - change 10%positive with (Pos.of_succ_nat 9).
    rewrite map_id, rev_involutive, pos_from_digits_digits; eauto. lia.
  - intros. rewrite decimal_digit_to_from_ascii; auto.
    eapply pos_digits_in_bounds.
    + lia.
    + eapply in_rev. eauto.
Qed.

Lemma pos_to_from_symbol : forall p, pos_from_symbol (pos_to_symbol p) = p.
Proof.
  intros.
  unfold pos_from_symbol.
  rewrite pos_to_from_symbol'.
  reflexivity.
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
          if ascii_dec c "-" then
            match pos_from_symbol' s' with
            | None => 0%Z
            | Some p => Zneg p
            end
          else
            match pos_from_symbol' s with
            | None => 0%Z
            | Some p => Zpos p
            end
  end.

Lemma Z_to_from_symbol : forall z, Z_from_symbol (Z_to_symbol z) = z.
Proof.
  intros. unfold Z_from_symbol, Z_to_symbol.
  destruct z; simpl.
  - reflexivity.
  - break_match.
      { exfalso. eapply pos_to_symbol_non_empty. eauto. }
    break_if.
      { exfalso.
        cut (48 <= nat_of_ascii "-" < 58).
          { unfold nat_of_ascii. simpl. intro. lia. }
        eapply pos_to_symbol_in_bounds. subst a. erewrite Heqt. simpl. auto. }
    rewrite <- Heqt. rewrite pos_to_from_symbol'. reflexivity.
  - rewrite pos_to_from_symbol'. reflexivity.
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
