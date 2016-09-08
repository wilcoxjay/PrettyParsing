Require Import List String Ascii.
Import ListNotations.

From PrettyParsing Require Import StringUtils OptionUtils.
Import OptionNotations.
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

  Definition unescape (l : list ascii) : option ascii :=
    let la_eq_dec := list_eq_dec ascii_dec in
    if      la_eq_dec l ["\"; "\"] then Some "\"
    else if la_eq_dec l ["\"; "l"] then Some "("
    else if la_eq_dec l ["\"; "r"] then Some ")"
    else if la_eq_dec l ["\"; "s"] then Some " "
    else if la_eq_dec l ["\"; "n"] then Some "010"
    else match l with
         | [a] => Some a
         | _ => None
         end.

  Lemma unescape_escape_id : forall a, unescape (escape a) = Some a.
  Proof.
    intros.
    unfold unescape, escape.
    repeat break_if; congruence.
  Qed.

  Fixpoint of_string_safe' (s : string) : t :=
    match s with
    | EmptyString => []
    | String a s =>
      escape a ++ of_string_safe' s
    end.

  Lemma of_string_safe'_wf : forall s, s = EmptyString \/ wf (of_string_safe' s).
  Proof.
    induction s; intuition idtac.
    - right. subst. simpl. rewrite app_nil_r. auto using escape_wf.
    - right. simpl. auto using wf_app, escape_wf.
  Qed.

  Fixpoint to_string' (l : t) : option string :=
    match l with
    | [] => Some EmptyString
    | a :: l => if ascii_dec a "\"
               then match l with
                    | [] => None
                    | b :: l => String <$> unescape [a; b] <*> to_string' l
                    end
               else String a <$> to_string' l
    end.

  Lemma to_string'_app_escape :
    forall a s, to_string' (escape a ++ s) = String a <$> to_string' s.
  Proof.
    unfold escape.
    intros.
    repeat break_if; simpl; unfold_option; repeat break_match; auto; try congruence.
  Qed.

  Lemma to_string'_of_string_safe'_id : forall s, to_string' (of_string_safe' s) = Some s.
  Proof.
    induction s; simpl; auto.
    now rewrite to_string'_app_escape, IHs.
  Qed.

  Definition of_string_safe (s : string) : t:=
    match s with
    | EmptyString => ["\"; "0"]
    | _ => of_string_safe' s
    end.

  Lemma of_string_safe_wf : forall s, wf (of_string_safe s).
  Proof.
    unfold of_string_safe.
    intros.
    break_match.
    - auto.
    - pose proof of_string_safe'_wf s.
      break_or_hyp.
      + discriminate.
      + auto.
  Qed.

  Definition to_string (l : t) : option string :=
    if list_eq_dec ascii_dec l ["\"; "0"] then Some EmptyString
    else to_string' l.

  Lemma to_string_of_string_safe_id : forall s, to_string (of_string_safe s) = Some s.
  Proof.
    unfold to_string, of_string_safe.
    intros.
    repeat break_match; try congruence.
    - simpl in *.
      unfold escape in *.
      repeat break_if; simpl in *; try congruence.
    - now rewrite to_string'_of_string_safe'_id.
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
