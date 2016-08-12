(* A very simple but not-that-pretty way of printing a tree. *)
Require Import List String Ascii Arith Omega.
Import ListNotations.

From PrettyParsing Require Import StringUtils ListUtils Tree Pretty
     LexicalConsiderations Tokenizer Parser OptionUtils.
From StructTact Require Import StructTactics Util.
Import OptionNotations.

Local Open Scope bool.
Local Open Scope char.

Fixpoint print_tree' (t : tree symbol.t) : list ascii :=
  match t with
  | atom s => s
  | node l => ["("] ++ intercalate [" "] (List.map print_tree' l) ++ [")"]
  end.

Definition print_tree t := list_to_string (print_tree' t).

(* This function is purely for specification purposes.
   It anticipates the result of tokenizing the printed tree. *)
Fixpoint tree_to_token_list (t : tree symbol.t) : list token.t :=
  match t with
  | atom s => [token.symbol s]
  | node l => [token.lparen] ++ List.flat_map tree_to_token_list l ++ [token.rparen]
  end.

Lemma print_tree'_tokenize'_tree_to_token_list :
  forall t s toks,
    Tree.Forall symbol.wf t ->
    separating s ->
    tokenize' (print_tree' t ++ s) symbol.empty toks =
    tokenize' s symbol.empty (List.rev (tree_to_token_list t) ++ toks).
Proof.
  induction t using tree_rect
  with (P_list := fun l =>
      List.Forall (Tree.Forall symbol.wf) l ->
      List.Forall2 (fun s1 t1 => forall s2 toks, separating s2 ->
             tokenize' (s1 ++ s2) symbol.empty toks = tokenize' s2 symbol.empty (rev t1 ++ toks))
         (List.map print_tree' l) (List.map tree_to_token_list l));
  intros; simpl.
  - auto.
  - invc H. auto.
  - invc H. now rewrite tokenize'_symbol.
  - invc H. rewrite !app_ass.
    rewrite tokenize'_intercalate_space with (ts := List.map tree_to_token_list l)
      by (simpl; auto).
    autorewrite with list; auto.
Qed.

Lemma print_tree_tokenize_tree_to_token_list :
  forall t,
    Forall symbol.wf t ->
    tokenize (print_tree t) = Some (tree_to_token_list t).
Proof.
  intros.
  unfold tokenize, print_tree.
  rewrite list_to_string_to_list.
  rewrite <- app_nil_r with (l := print_tree' t).
  rewrite print_tree'_tokenize'_tree_to_token_list; auto.
  simpl.
  now autorewrite with list.
Qed.

Lemma parse_toks'_tree_to_token_list :
  forall t toks acc,
    Tree.Forall symbol.wf t ->
    parse_toks' (tree_to_token_list t ++ toks) acc =
    match acc with
    | [] => Some (t, toks)
    | ts :: acc => parse_toks' toks ((t :: ts) :: acc)
    end.
Proof.
  induction t using tree_rect
  with (P_list := fun l =>
    forall toks ts acc,
      List.Forall (Tree.Forall symbol.wf) l ->
      parse_toks' (List.flat_map tree_to_token_list l ++ toks) (ts :: acc) =
      parse_toks' toks ((List.rev l ++ ts) :: acc)); intros.
  - auto.
  - simpl. rewrite !app_ass.
    invc H. rewrite IHt; auto.
  - auto.
  - simpl. invc H.
    rewrite !app_ass. rewrite IHt by auto.
    simpl. autorewrite with list. auto.
Qed.

Lemma parse_toks_tree_to_token_list :
  forall t,
    Tree.Forall symbol.wf t ->
    parse_toks (tree_to_token_list t) = Some t.
Proof.
  unfold parse_toks.
  intros.
  rewrite <- app_nil_r with (l := tree_to_token_list t).
  now rewrite parse_toks'_tree_to_token_list.
Qed.

Lemma parse_print_tree :
  forall t,
    Tree.Forall symbol.wf t ->
    parse (print_tree t) = Some t.
Proof.
  unfold parse.
  intros.
  rewrite print_tree_tokenize_tree_to_token_list; auto.
  simpl.
  now rewrite parse_toks_tree_to_token_list.
Qed.
