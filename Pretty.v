(* An implementation of (a call-by-value version of the slow version of) Wadler's
   pretty printer, ported from sections 1 and 2 of the paper [1].

   This version is slow for two reasons. First, Wadler's printer makes essential use
   of call-by-need which is difficult to simulate in Coq. Second, we stick to the 
   structurally recursive but potentially quadratic-time implementation from 
   section 2, instead of the linear time but not structurally recursive algorithm 
   given later in the paper.

   [1] http://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf
*)

Require Import List String Ascii Arith.
Import ListNotations.

From PrettyParsing Require Import StringUtils LexicalConsiderations Tokenizer.

From StructTact Require Import StructTactics.

Local Open Scope char.

Module internal.
  Inductive t :=
  | nil
  | text : list ascii -> t -> t
  | line : nat -> t -> t
  | union : t -> t -> t
  .

  Fixpoint app (x y : t) : t :=
    match x with
    | nil => y
    | text s x => text s (app x y)
    | line n x => line n (app x y)
    | union x1 x2 => union (app x1 y) (app x2 y)
    end.

  Fixpoint nest (i : nat) (x : t) : t :=
    match x with
    | nil => nil
    | text s x => text s (nest i x)
    | line n x => line (n + i) (nest i x)
    | union x1 x2 => union (nest i x1) (nest i x2)
    end.

  Fixpoint flatten (x : t) : t :=
    match x with
    | nil => nil
    | text s x => text s (flatten x)
    | line _ x => text [" "] (flatten x)
    | union x1 x2 => flatten x1
    end.

  Fixpoint group (x : t) : t :=
    match x with
    | nil => nil
    | text s x => text s (group x)
    | line n x => union (text [" "] (flatten x)) (line n x)
    | union x1 x2 => union (group x1) x2
    end.


  Fixpoint fits (w k : nat) (x : t) : bool :=
    if w <? k then false
    else match x with
         | nil => true
         | text s x => fits w (k + List.length s) x
         | line _ _ => true
         | union _ _ => false (* bogus! *)
         end.

  Definition better (w k : nat) (x1 x2 : t) : t :=
    if fits w k x1 then x1 else x2.

  Fixpoint best (w k : nat) (x : t) : t :=
    match x with
    | nil => nil
    | text s x => text s (best w (k + List.length s) x)
    | line n x => line n (best w n x)
    | union x1 x2 => better w k (best w k x1) (best w k x2)
    end.

  Fixpoint layout (x : t) : list ascii :=
    match x with
    | nil => []
    | text s x => s ++ layout x
    | line n x => ["010"] ++ repeat " " n ++ layout x
    | union x _ => layout x (* bogus *)
    end.

  Definition pretty (w : nat) (x : t) : list ascii :=
    layout (best w 0 x).
End internal.

Module Doc.
  Definition t := internal.t.

  Definition nil : t := internal.nil.
  Definition text s : t := internal.text s nil.
  Definition line : t := internal.line 0 nil.
  Definition app : t -> t -> t := internal.app.
  Definition nest : nat -> t -> t := internal.nest.
  Definition group : t -> t := internal.group.
  Definition pretty : nat -> t -> string := (fun n d => list_to_string (internal.pretty n d)).

  Local Notation "x ++ y" := (app x y) : pretty_scope.

  Local Open Scope pretty_scope.

  Definition hsep (x y : t) := x ++ text [" "] ++ y.
  Definition vsep (x y : t) := x ++ line ++ y.

    Definition folddoc f :=
    fix folddoc (l : list t) : t :=
      match l with
      | [] => nil
      | [x] => x
      | x :: l => f x (folddoc l)
      end.

  Definition spread := folddoc hsep.
  Definition stack := folddoc vsep.

  Definition bracket l x r := group (text l ++ nest 1 x ++ text r).

  Definition hvsep (x y : t) := x ++ group line ++ y.

  Module Notations.
    Notation "x ++ y" := (app x y) : pretty_scope.
    Notation "x <+> y" := (hsep x y) (right associativity, at level 60) : pretty_scope.
    Notation "x </> y" := (vsep x y) (right associativity, at level 60) : pretty_scope.
    Notation "x <+/> y" := (vsep x y) (right associativity, at level 60) : pretty_scope.
  End Notations.
End Doc.

Module doc_to_token_list_internal.
  Fixpoint f (d : internal.t) : list token.t :=
    match d with
    | internal.nil => []
    | internal.text l d =>
      (if list_eq_dec ascii_dec l ["("] then [token.lparen]
       else if list_eq_dec ascii_dec l [")"] then [token.rparen]
       else if list_eq_dec ascii_dec l [" "] then []
       else [token.symbol l]) ++ f d
    | internal.line i d => f d
    | internal.union d1 d2 => f d1
    end.

  Lemma nil : f internal.nil = [].
  Proof. reflexivity. Qed.

  Lemma text_lparen : forall d, f (internal.text ["("] d) = token.lparen :: f d.
  Proof. reflexivity. Qed.

  Lemma text_rparen : forall d, f (internal.text [")"] d) = token.rparen :: f d.
  Proof. reflexivity. Qed.

  Lemma text_space : forall d, f (internal.text [" "] d) = f d.
  Proof. reflexivity. Qed.

  Lemma text_symbol : forall d s, symbol.wf s -> f (internal.text s d) = token.symbol s :: f d.
  Proof. intros. simpl. repeat break_if; auto; subst; compute in H; intuition. Qed.

  Lemma line : forall d n, f (internal.line n d) = f d.
  Proof. reflexivity. Qed.

  Lemma app :
    forall d1 d2,
      f (internal.app d1 d2) = f d1 ++ f d2.
  Proof.
    induction d1; simpl; intros; auto.
    repeat break_match; autorewrite with list; auto using f_equal.
  Qed.

  Lemma nest :
    forall n d,
      f (internal.nest n d) = f d.
  Proof.
    induction d; simpl; auto.
    repeat break_match; auto using f_equal.
  Qed.

  Lemma flatten:
    forall d, f (internal.flatten d) = f d.
  Proof.
    induction d; simpl; auto.
    repeat break_match; auto using f_equal.
  Qed.

  Lemma group:
    forall d, f (internal.group d) = f d.
  Proof.
    induction d; simpl; auto using flatten.
    repeat break_match; auto using f_equal.
  Qed.
End doc_to_token_list_internal.

Module wf_internal.
  Section local_hints.

  Fixpoint empty (d : internal.t) : Prop :=
    match d with
    | internal.nil => True
    | internal.union d1 d2 => empty d1 /\ empty d2
    | _ => False
    end.

  Fixpoint starts_with_reserved_or_newline (d : internal.t) : Prop :=
    match d with
    | internal.text [c] d => chars.reserved c
    | internal.line _ _ => True
    | internal.union d1 d2 => starts_with_reserved_or_newline d1 /\
                             starts_with_reserved_or_newline d2
    | _ => False
    end.

  Fixpoint ends_with_reserved_or_newline (d : internal.t) : Prop :=
    match d with
    | internal.text [c] d => ends_with_reserved_or_newline d \/ (empty d /\ chars.reserved c)
    | internal.text _ d => ends_with_reserved_or_newline d
    | internal.line _ d => ends_with_reserved_or_newline d \/ empty d
    | internal.union d1 d2 => ends_with_reserved_or_newline d1 /\
                             ends_with_reserved_or_newline d2
    | _ => False
    end.

  Definition separating_left (d : internal.t) : Prop :=
    empty d \/ starts_with_reserved_or_newline d.

  Definition separating_right (d : internal.t) : Prop :=
    empty d \/ ends_with_reserved_or_newline d.

  Lemma separating_left_nil : separating_left internal.nil.
  Proof. compute; auto. Qed.

  Lemma starts_with_reserved_or_newline_app_intro_l :
    forall d1 d2,
      starts_with_reserved_or_newline d1 ->
      starts_with_reserved_or_newline (internal.app d1 d2).
  Proof. induction d1; simpl; intuition. Qed.


  Inductive t : internal.t -> Prop :=
  | nil : t internal.nil
  | text_lparen : forall d, t d -> t (internal.text ["("] d)
  | text_rparen : forall d, t d -> t (internal.text [")"] d)
  | text_space : forall d, t d -> t (internal.text [" "] d)
  | text_symbol : forall s d, symbol.wf s -> t d -> separating_left d -> t (internal.text s d)
  | line : forall n d, t d -> t (internal.line n d)
  | union : forall d1 d2, doc_to_token_list_internal.f d1 = doc_to_token_list_internal.f d2 ->
                     t d1 -> t d2 -> t (internal.union d1 d2)
  .
  Hint Constructors t.

  Definition app_compat (d1 d2 : internal.t) : Prop :=
    separating_right d1 \/ separating_left d2.

  Lemma app_compat_text_char_l_inv :
    forall c d1 d2,
      app_compat (internal.text [c] d1) d2 ->
      app_compat d1 d2.
  Proof.
    unfold app_compat, separating_right.
    simpl. intuition.
  Qed.

  Lemma app_compat_line_l_inv :
    forall n d1 d2,
      app_compat (internal.line n d1) d2 ->
      app_compat d1 d2.
  Proof.
    unfold app_compat, separating_right.
    simpl. intuition.
  Qed.

  Lemma app_compat_symbol_l_inv:
    forall s d1 d2,
      symbol.wf s ->
      app_compat (internal.text s d1) d2 -> app_compat d1 d2.
  Proof.
    unfold app_compat.
    intuition.
    unfold separating_right in *. simpl in *.
    repeat (intuition; break_match).
  Qed.

  Lemma app_compat_union_l_inv1 :
    forall d1 d2 d3,
      app_compat (internal.union d1 d2) d3 ->
      app_compat d1 d3.
  Proof.
    unfold app_compat.
    intuition.
    unfold separating_right in *. simpl in *.
    repeat (intuition; break_match).
  Qed.

  Lemma app_compat_union_l_inv2 :
    forall d1 d2 d3,
      app_compat (internal.union d1 d2) d3 ->
      app_compat d2 d3.
  Proof.
    unfold app_compat.
    intuition.
    unfold separating_right in *. simpl in *.
    repeat (intuition; break_match).
  Qed.

  Lemma empty_ends_with_reserved_or_newline_contra :
    forall d,
      empty d ->
      ends_with_reserved_or_newline d ->
      False.
  Proof. induction d; simpl; intuition. Qed.

  Lemma empty_app: forall d1 d2, empty d1 -> empty d2 -> empty (internal.app d1 d2).
  Proof. induction d1; simpl in *; intuition. Qed.

  Lemma starts_with_reserved_or_newline_app_empty_l:
    forall d1 d2,
      empty d1 ->
      starts_with_reserved_or_newline d2 ->
      starts_with_reserved_or_newline (internal.app d1 d2).
  Proof. induction d1; simpl in *; intuition. Qed.

  Hint Resolve empty_app starts_with_reserved_or_newline_app_empty_l.

  Lemma separating_left_empty_l :
    forall d1 d2,
      empty d1 ->
      separating_left d2 ->
      separating_left (internal.app d1 d2).
  Proof. unfold separating_left. intuition. Qed.

  Lemma starts_with_reserved_or_newline_app:
    forall d1 d2,
      starts_with_reserved_or_newline d1 ->
      starts_with_reserved_or_newline (internal.app d1 d2).
  Proof. induction d1; simpl; intuition. Qed.

  Lemma ends_with_reserved_or_newline_app:
    forall d1 d2,
      ends_with_reserved_or_newline d2 ->
      ends_with_reserved_or_newline (internal.app d1 d2).
  Proof. induction d1; simpl; repeat break_match; intuition. Qed.

  Lemma app : forall d1 d2, t d1 -> t d2 -> app_compat d1 d2 -> t (internal.app d1 d2).
  Proof.
    induction 1; simpl; intros;
      eauto using app_compat_text_char_l_inv, app_compat_line_l_inv.
    - concludes.
      constructor; eauto using app_compat_symbol_l_inv.
      assert (ends_with_reserved_or_newline d \/ separating_left d2).
      { unfold app_compat, separating_right in H3. simpl in *.
        repeat (intuition; try break_match). subst.
        simpl in *. congruence.
      }
      clear H3.
      unfold separating_left in H1.
      intuition.
      + exfalso. eauto using empty_ends_with_reserved_or_newline_contra.
      + auto using separating_left_empty_l.
      + red. right. auto using starts_with_reserved_or_newline_app.
      + red. right. auto using starts_with_reserved_or_newline_app.
    - econstructor; eauto using app_compat_union_l_inv1, app_compat_union_l_inv2.
      rewrite !doc_to_token_list_internal.app.
      auto using f_equal2.
  Qed.

  Lemma app_compat_intro_l : forall d1 d2, separating_right d1 -> app_compat d1 d2.
  Proof. firstorder. Qed.

  Lemma app_compat_intro_r : forall d1 d2, separating_left d2 -> app_compat d1 d2.
  Proof. firstorder. Qed.

  Lemma separating_left_starts_intro :
    forall d, starts_with_reserved_or_newline d -> separating_left d.
  Proof. firstorder. Qed.

  Lemma separating_right_ends_intro :
    forall d, ends_with_reserved_or_newline d -> separating_right d.
  Proof. firstorder. Qed.

  Lemma starts_with_reserved_or_newline_text_char_intro :
    forall c, chars.reserved c -> starts_with_reserved_or_newline (Doc.text [c]).
  Proof. firstorder. Qed.

  Lemma ends_with_reserved_or_newline_text_char_intro :
    forall c, chars.reserved c -> ends_with_reserved_or_newline (Doc.text [c]).
  Proof. firstorder. Qed.

  Lemma starts_with_reserved_or_newline_line_intro :
    forall n d, starts_with_reserved_or_newline (internal.line n d).
  Proof. firstorder. Qed.

  Lemma ends_with_reserved_or_newline_line_empty_intro :
    forall n, ends_with_reserved_or_newline (internal.line n internal.nil).
  Proof. firstorder. Qed.

  Lemma empty_nest: forall n d, empty d -> empty (internal.nest n d).
  Proof. induction d; simpl in *; intuition. Qed.

  Lemma starts_with_reserved_or_newline_nest:
    forall n d, starts_with_reserved_or_newline d ->
           starts_with_reserved_or_newline (internal.nest n d).
  Proof. induction d; simpl in *; intuition. Qed.

  Hint Resolve empty_nest starts_with_reserved_or_newline_nest.

  Lemma separating_left_nest:
    forall n d, separating_left d -> separating_left (internal.nest n d).
  Proof. unfold separating_left. intuition. Qed.

  Lemma nest : forall n d, t d -> t (internal.nest n d).
  Proof.
    induction 1; simpl; constructor; auto using separating_left_nest.
    now rewrite !doc_to_token_list_internal.nest.
  Qed.

  Lemma empty_flatten: forall d, empty d -> empty (internal.flatten d).
  Proof. induction d; simpl in *; intuition. Qed.
  Hint Resolve empty_flatten.

  Lemma starts_with_reserved_or_newline_flatten:
    forall d, starts_with_reserved_or_newline d ->
         starts_with_reserved_or_newline (internal.flatten d).
  Proof. induction d; simpl in *; intuition. Qed.
  Hint Resolve starts_with_reserved_or_newline_flatten.

  Lemma ends_with_reserved_or_newline_flatten:
    forall d, ends_with_reserved_or_newline d ->
         ends_with_reserved_or_newline (internal.flatten d).
  Proof. induction d; simpl in *; repeat break_match; intuition. Qed.
  Hint Resolve ends_with_reserved_or_newline_flatten.

  Lemma separating_left_flatten:
    forall d, separating_left d -> separating_left (internal.flatten d).
  Proof. unfold separating_left. intuition. Qed.

  Lemma empty_group: forall d, empty d -> empty (internal.group d).
  Proof. induction d; simpl in *; intuition. Qed.
  Hint Resolve empty_group.

  Lemma starts_with_reserved_or_newline_group:
    forall d, starts_with_reserved_or_newline d ->
         starts_with_reserved_or_newline (internal.group d).
  Proof. induction d; simpl in *; intuition. Qed.
  Hint Resolve starts_with_reserved_or_newline_group.

  Lemma ends_with_reserved_or_newline_group:
    forall d, ends_with_reserved_or_newline d ->
         ends_with_reserved_or_newline (internal.group d).
  Proof. induction d; simpl in *; repeat break_match; intuition. Qed.
  Hint Resolve ends_with_reserved_or_newline_group.

  Lemma separating_left_group:
    forall d, separating_left d -> separating_left (internal.group d).
  Proof. unfold separating_left. intuition. Qed.

  Lemma flatten : forall d, t d -> t (internal.flatten d).
  Proof. induction 1; simpl; auto using separating_left_flatten. Qed.

  Lemma group : forall d, t d -> t (internal.group d).
  Proof.
    induction 1; simpl; auto.
    - auto using separating_left_group.
    - econstructor; auto using flatten.
      simpl. auto using doc_to_token_list_internal.flatten.
    - econstructor; auto.
      now rewrite doc_to_token_list_internal.group.
  Qed.

  Lemma separating_left_best:
    forall w k d,
      separating_left d ->
      separating_left (internal.best w k d).
  Proof.
    unfold separating_left.
    intuition.
    - left. induction d; simpl in *; intuition.
      unfold internal.better. break_if; auto.
    - right. induction d; simpl in *; intuition.
      unfold internal.better. break_if; auto.
  Qed.

  Lemma best : forall w k d, t d -> t (internal.best w k d).
  Proof.
    intros. revert k.
    induction H; simpl; intros; auto using separating_left_best.
    unfold internal.better. break_if; auto.
  Qed.

  Lemma separating_right_group:
    forall d, separating_right d -> separating_right (internal.group d).
  Proof. unfold separating_right. intuition. Qed.

  Lemma doc_to_token_list_best :
    forall w k d,
      t d ->
      doc_to_token_list_internal.f (internal.best w k d) = doc_to_token_list_internal.f d.
  Proof.
    intros. revert k.
    induction H; simpl; intros; auto using f_equal.
    unfold internal.better. break_if; auto.
    now rewrite IHt2.
  Qed.
  End local_hints.
End wf_internal.


Module wf.
  Definition t : Doc.t -> Prop := wf_internal.t.
  Definition nil : t Doc.nil := wf_internal.nil.
  Lemma text_lparen : t (Doc.text ["("]). repeat constructor. Qed.
  Lemma text_rparen : t (Doc.text [")"]). repeat constructor. Qed.
  Lemma text_space : t (Doc.text [" "]). repeat constructor. Qed.
  Lemma text_symbol s : symbol.wf s -> t (Doc.text s).
    intro. repeat constructor. auto.
  Qed.
  Lemma line : t Doc.line. repeat constructor. Qed.
  Lemma app d1 d2 : t d1 -> t d2 -> wf_internal.app_compat d1 d2 -> t (Doc.app d1 d2).
    exact (wf_internal.app d1 d2).
  Qed.
  Definition nest n d : t d -> t (Doc.nest n d) := wf_internal.nest n d.
  Definition group d : t d -> t (Doc.group d) := wf_internal.group d.

  Definition starts_with_reserved_or_newline_line_intro :
    wf_internal.starts_with_reserved_or_newline Doc.line :=
    wf_internal.starts_with_reserved_or_newline_line_intro _ _.

  Definition ends_with_reserved_or_newline_line_intro :
    wf_internal.ends_with_reserved_or_newline Doc.line :=
    wf_internal.ends_with_reserved_or_newline_line_empty_intro _.

  Hint Resolve nil text_lparen text_rparen text_space text_symbol line app nest group
       wf_internal.app_compat_intro_l
       wf_internal.app_compat_intro_r
       wf_internal.separating_left_starts_intro
       wf_internal.separating_right_ends_intro
       wf_internal.starts_with_reserved_or_newline_text_char_intro
       wf_internal.ends_with_reserved_or_newline_text_char_intro
       wf_internal.starts_with_reserved_or_newline_app
       wf_internal.ends_with_reserved_or_newline_app
       starts_with_reserved_or_newline_line_intro
       ends_with_reserved_or_newline_line_intro
       wf_internal.starts_with_reserved_or_newline_group
       wf_internal.ends_with_reserved_or_newline_group
       wf_internal.starts_with_reserved_or_newline_app_intro_l
    : doc_wf.

  Lemma hsep d1 d2 : t d1 -> t d2 -> t (Doc.hsep d1 d2).
  Proof. unfold Doc.hsep. auto 10 with doc_wf. Qed.

  Lemma vsep d1 d2 : t d1 -> t d2 -> t (Doc.vsep d1 d2).
  Proof. unfold Doc.vsep. auto 10 with doc_wf. Qed.

  Lemma folddoc :
    forall (f : Doc.t -> Doc.t -> Doc.t),
      (forall d1 d2, t d1 -> t d2 -> t (f d1 d2)) ->
      forall l, List.Forall t l -> t (Doc.folddoc f l).
  Proof.
    induction l; simpl; intros.
    - auto with doc_wf.
    - invc H0. destruct l; auto with doc_wf.
  Qed.

  Hint Resolve hsep vsep folddoc : doc_wf.

  Lemma spread l : List.Forall t l -> t (Doc.spread l).
  Proof. unfold Doc.spread. auto with doc_wf. Qed.

  Lemma stack l : List.Forall t l -> t (Doc.stack l).
  Proof. unfold Doc.stack. auto with doc_wf. Qed.

  Lemma bracket d : t d -> t (Doc.bracket ["("] d [")"]).
  Proof. intros. unfold Doc.bracket. auto 10 with doc_wf. Qed.

  Lemma hvsep d1 d2 : t d1 -> t d2 -> t (Doc.hvsep d1 d2).
  Proof. unfold Doc.hvsep. auto 10 with doc_wf. Qed.

  Hint Resolve spread stack bracket hvsep : doc_wf.
End wf.




Module doc_to_token_list.
  Definition f := doc_to_token_list_internal.f.
  Definition nil : f Doc.nil = [] := doc_to_token_list_internal.nil.
  Definition text_lparen : f (Doc.text ["("]) = [token.lparen] :=
    doc_to_token_list_internal.text_lparen _.
  Definition text_rparen : f (Doc.text [")"]) = [token.rparen] :=
    doc_to_token_list_internal.text_rparen _.
  Definition text_space : f (Doc.text [" "]) = [] :=
    doc_to_token_list_internal.text_space _.
  Definition text_symbol s : symbol.wf s -> f (Doc.text s) = [token.symbol s] :=
    doc_to_token_list_internal.text_symbol _ s.
  Definition line : f Doc.line = [] :=
    doc_to_token_list_internal.line _ _.
  Definition app : forall d1 d2 : Doc.t, f (Doc.app d1 d2) = f d1 ++ f d2 :=
    doc_to_token_list_internal.app.
  Definition nest : forall n (d : Doc.t), f (Doc.nest n d) = f d :=
    doc_to_token_list_internal.nest.
  Definition group : forall d : Doc.t, f (Doc.group d) = f d :=
    doc_to_token_list_internal.group.

  Lemma hsep : forall d1 d2 : Doc.t, f (Doc.hsep d1 d2) = f d1 ++ f d2.
  Proof. intros. unfold Doc.hsep. now rewrite !app, text_space. Qed.

  Lemma vsep : forall d1 d2 : Doc.t, f (Doc.vsep d1 d2) = f d1 ++ f d2.
  Proof. intros. unfold Doc.vsep. now rewrite !app, line. Qed.

  Lemma folddoc : forall (g : Doc.t -> Doc.t -> Doc.t),
      (forall d1 d2, f (g d1 d2) = f d1 ++ f d2) ->
      forall l, f (Doc.folddoc g l) = List.flat_map f l.
  Proof.
    induction l.
    - auto.
    - simpl. destruct l.
      + simpl in *. auto with *.
      + now rewrite H, IHl.
  Qed.

  Lemma spread : forall l, f (Doc.spread l) = List.flat_map f l.
  Proof. apply folddoc. auto using hsep. Qed.

  Lemma stack : forall l, f (Doc.stack l) = List.flat_map f l.
  Proof. apply folddoc. auto using vsep. Qed.

  Lemma bracket : forall d, f (Doc.bracket ["("] d [")"]) = [token.lparen] ++ f d ++ [token.rparen].
  Proof. unfold Doc.bracket. intros. now rewrite group, !app, text_lparen, nest, text_rparen. Qed.

  Lemma hvsep : forall d1 d2, f (Doc.hvsep d1 d2) = f d1 ++ f d2.
  Proof. unfold Doc.hvsep. intros. now rewrite !app, group, line. Qed.

  Hint Rewrite nil text_lparen text_rparen text_space line app nest group hsep vsep
       spread stack bracket hvsep
    : doc_to_token_list.
End doc_to_token_list.




Lemma layout_empty : forall d, wf_internal.empty d -> internal.layout d = [].
Proof. induction d; simpl; intuition. Qed.

Lemma separating_layout_starts_with: forall d s,
    wf_internal.starts_with_reserved_or_newline d ->
    separating (internal.layout d ++ s).
Proof. induction d; simpl; repeat (intuition; try break_match). Qed.

Lemma layout_separating_left :
  forall d s,
    separating s ->
    wf_internal.separating_left d ->
    separating (internal.layout d ++ s).
Proof.
  unfold wf_internal.separating_left.
  intuition.
  - now rewrite layout_empty.
  - auto using separating_layout_starts_with.
Qed.

Lemma tokenize'_layout :
  forall d, wf.t d -> forall toks s,
      separating s ->
    tokenize' (internal.layout d ++ s) symbol.empty toks =
    tokenize' s symbol.empty (List.rev (doc_to_token_list.f d) ++ toks).
Proof.
  induction 1; simpl; intros.
  - auto.
  - rewrite IHt by auto. now autorewrite with list.
  - rewrite IHt by auto. now autorewrite with list.
  - rewrite IHt by auto. now autorewrite with list.
  - autorewrite with list.
    rewrite tokenize'_symbol; auto using layout_separating_left.
    rewrite IHt by auto.
    repeat break_if; auto.
    all: subst; compute in H; intuition.
  - autorewrite with list.
    rewrite tokenize'_repeat_space.
    now rewrite IHt by auto.
  - now rewrite IHt1 by auto.
Qed.

Lemma tokenize'_internal_pretty :
  forall w d toks s,
    wf.t d ->
    separating s ->
    tokenize' (internal.pretty w d ++ s) symbol.empty toks =
    tokenize' s symbol.empty (List.rev (doc_to_token_list.f d) ++ toks).
Proof.
  unfold internal.pretty.
  intros.
  rewrite tokenize'_layout by (unfold wf.t; auto using wf_internal.best).
  now rewrite wf_internal.doc_to_token_list_best.
Qed.

Lemma tokenize_pretty :
  forall w d,
    wf.t d ->
    tokenize (Doc.pretty w d) = Some (doc_to_token_list.f d).
Proof.
  unfold tokenize, Doc.pretty.
  intros.
  rewrite list_to_string_to_list.
  rewrite <- app_nil_r with (l := internal.pretty w d).
  rewrite tokenize'_internal_pretty; auto.
  simpl.
  now autorewrite with list.
Qed.
