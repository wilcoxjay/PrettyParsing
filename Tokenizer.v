Require Import List String Ascii.
Import ListNotations.

From PrettyParsing Require Import LexicalConsiderations StringUtils ListUtils.
From StructTact Require Import StructTactics.

Local Open Scope char.

Fixpoint tokenize' (s : list ascii) (sym : symbol.t) (toks : list token.t) :
  option (list token.t) :=
  let symtok := if symbol.is_empty sym then [] else [token.symbol (symbol.rev sym)] in
  match s with
  | [] => Some (List.rev (symtok ++ toks))
  | a :: s =>
    let '(symtok, sym', atok) :=
        if ascii_dec a "(" then (symtok, symbol.empty, [token.lparen])
        else if ascii_dec a ")" then (symtok, symbol.empty, [token.rparen])
        else if ascii_dec a "010" then (symtok, symbol.empty, [])
        else if ascii_dec a " " then (symtok, symbol.empty, [])
        else ([], symbol.extend a sym,  [])
    in
    tokenize' s sym' (atok ++ symtok ++ toks)
  end.

Definition tokenize (s : string) := tokenize' (string_to_list s) symbol.empty [].

Definition separating (s : list ascii) : Prop :=
  match s with
  | [] => True
  | a :: s => chars.reserved a
  end.

Arguments separating _ : simpl never.

Lemma separating_nil : separating [].
Proof. exact I. Qed.

Lemma separating_cons :
  forall a s,
    chars.reserved a ->
    separating (a :: s).
Proof. auto. Qed.

Hint Resolve separating_nil separating_cons.

Lemma tokenize'_separating:
  forall a s toks sym,
    separating s ->
    tokenize' s (symbol.extend a sym) toks =
    tokenize' s symbol.empty (token.symbol (rev sym ++ [a]) :: toks).
Proof.
  unfold separating.
  intros.
  destruct s.
  - auto.
  - simpl. repeat break_match; repeat find_inversion; auto.
    unfold chars.reserved in *.
    simpl in *.
    intuition; congruence.
Qed.


Lemma tokenize'_symbol :
  forall a s toks sym,
    symbol.wf a ->
    separating s ->
    tokenize' (a ++ s) sym toks = tokenize' s symbol.empty (token.symbol (rev sym ++ a) :: toks).
Proof.
  induction a; intros.
  - simpl in *. intuition.
  - simpl in *.
    repeat break_match; repeat find_inversion; intuition; try solve [exfalso; auto];
    cbn [List.app] in *.
    + rewrite tokenize'_separating; auto.
    + rewrite IHa by auto.
      simpl. now rewrite app_ass.
Qed.

Lemma intersperse_cons_cons :
  forall A (a x y : A) l,
    intersperse a (x :: y :: l) = x :: a :: intersperse a (y :: l).
Proof. auto. Qed.

Lemma tokenize'_space :
  forall s toks,
    tokenize' (" " :: s) symbol.empty toks =
    tokenize' s symbol.empty toks.
Proof. reflexivity. Qed.

Hint Rewrite rev_app_distr app_ass : list.

Lemma tokenize'_intercalate_space :
  forall l ts,
    List.Forall2 (fun s1 t1 =>
       forall s2 toks,
         separating s2 ->
         tokenize' (s1 ++ s2)%list symbol.empty toks =
         tokenize' s2 symbol.empty (List.rev t1 ++ toks)) l ts ->
    forall s toks,
      separating s ->
      tokenize' (intercalate [" "] l ++ s) symbol.empty toks =
      tokenize' s symbol.empty (List.rev (concat ts) ++ toks).
Proof.
  unfold intercalate.
  induction 1; intros.
  - auto.
  - destruct H0.
    + simpl. rewrite !app_ass, rev_app_distr. simpl.
      rewrite H; auto.
    + rewrite intersperse_cons_cons.
      cbn [concat]. rewrite !app_ass.
      rewrite H by (simpl; auto).
      cbn [List.app].
      rewrite tokenize'_space.
      rewrite IHForall2 by auto.
      simpl.
      now autorewrite with list.
Qed.

Hint Rewrite concat_app concat_map  : list.

Lemma rev_concat :
  forall A (l : list (list A)),
    List.rev (concat l) = concat (List.rev (List.map (@List.rev _) l)).
Proof with autorewrite with list; auto.
  induction l; simpl...
  rewrite IHl; simpl...
Qed.

Hint Rewrite rev_concat flat_map_concat_map : list.

Lemma tokenize'_repeat_space :
  forall n s toks,
    tokenize' (repeat " " n ++ s) symbol.empty toks = tokenize' s symbol.empty toks.
Proof. induction n; simpl; intuition. Qed.
