Require Import List String Ascii.
Import ListNotations.

From PrettyParsing Require Import StringUtils.
From StructTact Require Import StructTactics.

Local Open Scope char.

Module chars.
  Notation lparen := "("%char.
  Notation rparen := ")"%char.
  Notation space  := " "%char.
  Notation newline  := "010"%char.

  Definition reserved (a : ascii) : Prop  :=
    In a [lparen; rparen; newline; space].

  Definition reserved_dec (a : ascii) : {reserved a} + {~ reserved a}.
    unfold reserved.
    apply in_dec.
    apply ascii_dec.
  Defined.

  Lemma lparen_reserved : reserved lparen.
  Proof. red. intuition. Qed.

  Lemma rparen_reserved : reserved rparen.
  Proof. red. intuition. Qed.

  Lemma space_reserved : reserved space.
  Proof. red. intuition. Qed.

  Lemma newline_reserved : reserved newline.
  Proof. red. intuition. Qed.

  Hint Resolve lparen_reserved rparen_reserved space_reserved newline_reserved.
End chars.

Module symbol.
  Definition t := list ascii.

  Definition nil := string_to_list "nil".

  Definition empty := string_to_list "".

  Definition extend (c : ascii) (s : t) : t := c :: s.

  Definition print : t -> string := list_to_string.

  Definition rev : t -> t := @List.rev _.

  Definition of_string_unsafe : string -> t := string_to_list.

  Definition is_empty (s : t) : bool :=
    match s with
    | [] => true
    | _ => false
    end.

  Fixpoint wf (s : t) : Prop :=
    match s with
    | [] => False
    | [a] => ~ chars.reserved a
    | a :: s => ~ chars.reserved a /\ wf s
    end.

  Ltac solve_wf :=
    compute; intuition discriminate.

  Hint Extern 3 (wf _)=> solve_wf.

  Lemma wf_app : forall s1 s2, wf s1 -> wf s2 -> wf (s1 ++ s2).
  Proof.
    induction s1; simpl; intuition.
    - destruct s1.
      + destruct s2; simpl; auto.
      + destruct H as [Ha Hs1].
        specialize (IHs1 _ Hs1 H0).
        simpl in IHs1.
        simpl. auto.
  Qed.

  Definition escape (a : ascii) : list ascii :=
    if ascii_dec a "\" then ["\"; "\"]
    else if ascii_dec a "(" then ["\"; "l"]
    else if ascii_dec a ")" then ["\"; "r"]
    else if ascii_dec a " " then ["\"; "s"]
    else if ascii_dec a "010" then ["\"; "n"]
    else [a].

  Lemma escape_wf : forall a, wf (escape a).
  Proof.
    unfold escape.
    intros.
    repeat break_if; auto.
    simpl.
    unfold chars.reserved.
    compute. intuition.
  Qed.

  Fixpoint of_string_safe (s : string) : t :=
    match s with
    | EmptyString => ["\"; "0"]
    | String a s =>
      escape a ++ of_string_safe s
    end.

  Lemma of_string_safe_wf : forall s, wf (of_string_safe s).
  Proof.
    induction s.
    - auto.
    - simpl. auto using wf_app, escape_wf.
  Qed.

  Definition eq_dec (x y : t) : {x = y} + {x <> y} := list_eq_dec ascii_dec x y.
End symbol.

Module token.
  Inductive t : Type :=
  | symbol : symbol.t -> t
  | lparen
  | rparen
  .

  Local Coercion singleton_string := (fun a => String a EmptyString).

  Definition print (x : t) : string :=
    match x with
    | symbol s => symbol.print s
    | lparen => chars.lparen
    | rparen => chars.rparen
    end.
End token.
