Require Import List String Ascii Arith Omega.
Import ListNotations.

From PrettyParsing Require Import StringUtils ListUtils Tree Pretty
     LexicalConsiderations Tokenizer Parser OptionUtils PrintTree.
From StructTact Require Import StructTactics Util.
Import OptionNotations.

Local Open Scope bool.
Local Open Scope char.


Fixpoint tree_to_doc (t : tree symbol.t) : Doc.t :=
  match t with
  | atom s => Doc.text s
  | node l => Doc.bracket ["("] (Doc.group (Doc.stack (List.map tree_to_doc l))) [")"]
  end.

Definition pretty_tree w t := Doc.pretty w (tree_to_doc t).

Lemma doc_to_token_list_tree_to_doc :
  forall t,
    Tree.Forall symbol.wf t ->
    doc_to_token_list.f (tree_to_doc t) = tree_to_token_list t.
Proof.
  induction t using tree_rect
  with (P_list := fun l => List.Forall (Tree.Forall symbol.wf) l ->
                        List.flat_map doc_to_token_list.f (List.map tree_to_doc l) =
                        List.flat_map tree_to_token_list l);
  simpl; intros.
  - auto.
  - invc H. auto using f_equal2.
  - invc H. repeat break_if; subst; compute in *; intuition.
  - invc H. autorewrite with doc_to_token_list. auto using f_equal2.
Qed.

Lemma tree_to_doc_wf : forall t, Tree.Forall symbol.wf t -> wf.t (tree_to_doc t).
Proof.
  induction t using tree_rect
  with (P_list := fun l => List.Forall (Forall symbol.wf) l ->
                        List.Forall wf.t (List.map tree_to_doc l));
  simpl; intros.
  - auto.
  - invc H. auto.
  - invc H. auto with doc_wf.
  - invc H. auto with doc_wf.
Qed.

Lemma tokenize_pretty_tree :
  forall w t, Tree.Forall symbol.wf t -> tokenize (pretty_tree w t) = Some (tree_to_token_list t).
Proof.
  unfold pretty_tree.
  intros.
  rewrite tokenize_pretty by auto using tree_to_doc_wf.
  now rewrite doc_to_token_list_tree_to_doc.
Qed.

Lemma parse_pretty_tree :
  forall w t,
    Tree.Forall symbol.wf t ->
    parse (pretty_tree w t) = Some t.
Proof.
  unfold parse.
  intros.
  rewrite tokenize_pretty_tree by auto.
  simpl.
  now rewrite parse_toks_tree_to_token_list.
Qed.
