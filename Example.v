Require Export List String Ascii Arith Omega.

From PrettyParsing Require Import PrettyParsing.
From StructTact Require Import StructTactics.

Import ListNotations OptionNotations.

Local Open Scope char.

Module extended_example.
  Module expr.
    (* The untyped lambda calculus using de Bruijn indices. *)
    Inductive t : Type :=
    | Var : nat -> t
    | Lam : t -> t
    | App : t -> t -> t
    .

    Module examples.
      Definition id : t := Lam (Var 0).

      Definition omega : t := App (Lam (App (Var 0) (Var 0)))
                                  (Lam (App (Var 0) (Var 0))).
    End examples.
  End expr.

  Module keyword.
    Definition t (s : string) : Prop := s = "lambda"%string.

    Definition dec (s : string) : {t s} + {~ t s} := string_dec _ _.
  End keyword.

  Module var.
    Definition t := string.

    Definition dec (x y : t) := string_dec x y.

    Import error.notations.

    Definition of_string (s : string) : error.t var.t :=
      if keyword.dec s
      then error.error ("Cannot use keyword " ++ s ++ " as a variable name.")
      else error.ret s.

    Definition fresh (context : list string) : string :=
      if List.length context <=? 26
      then let s := String (ascii_of_nat (97 + List.length context)) EmptyString
           in if in_dec string_dec s context then ""
              else s
      else "".
  End var.

  Module ast.
    Inductive t : Type :=
    | Var : var.t -> t
    | Lam : var.t -> t -> t
    | App : t -> t -> t
    .

    Module wf.
      Fixpoint t (a : ast.t) : Prop :=
        match a with
        | Var s => ~ keyword.t s
        | Lam s a => ~ keyword.t s /\ t a
        | App a1 a2 => t a1 /\ t a2
        end.
    End wf.

    Import error.notations.

    Fixpoint to_expr' (context : list var.t) (a : ast.t) : error.t expr.t :=
      match a with
      | ast.Var s =>
        v <- var.of_string s ;;
          expr.Var <$> error.expect ("Unbound variable " ++ v) (index_of var.dec v context)
      | ast.Lam s a =>
        v <- var.of_string s ;;
          expr.Lam <$> to_expr' (v :: context) a
      | ast.App a1 a2 => expr.App <$> to_expr' context a1 <*> to_expr' context a2
      end.

    Definition to_expr := to_expr' [].

    Fixpoint of_expr' (context : list var.t) (e : expr.t) : ast.t :=
      match e with
      | expr.Var n => match nth_error context n with
                     | None => ast.Var ""%string (* bogus *)
                     | Some v => ast.Var v
                     end
      | expr.Lam e => let v := var.fresh context in
                     ast.Lam v (of_expr' (v :: context) e)
      | expr.App e1 e2 => ast.App (of_expr' context e1) (of_expr' context e2)
      end.

    Definition of_expr := of_expr' [].

    Eval compute in of_expr expr.examples.id.
    Eval compute in to_expr (of_expr expr.examples.id).

    Eval compute in of_expr expr.examples.omega.
    Eval compute in to_expr (of_expr expr.examples.omega).
  End ast.

  Fixpoint expr_to_symbol_tree (e : expr.t) : tree symbol.t :=
    match e with
    | expr.Var n => atom (nat_to_symbol n)
    | expr.Lam e => node [atom (symbol.of_string_unsafe "lambda"); expr_to_symbol_tree e]
    | expr.App e1 e2 => node [ expr_to_symbol_tree e1; expr_to_symbol_tree e2]
    end.

  Fixpoint expr_from_symbol_tree (t : tree symbol.t) : option expr.t :=
    match t with
    | atom s => Some (expr.Var (nat_from_symbol s))
    | node [arg1; arg2] =>
      if symbol.eq_dec (match arg1 with
                        | atom tag => tag
                        | _ => symbol.of_string_unsafe "bogus!"
                        end)
                       (symbol.of_string_unsafe "lambda")
      then expr.Lam <$> expr_from_symbol_tree arg2
      else expr.App <$> expr_from_symbol_tree arg1
                    <*> expr_from_symbol_tree arg2
    | _ => None
    end.

  Lemma expr_to_symbol_no_confusion:
    forall e, expr_to_symbol_tree e = atom ["l"; "a"; "m"; "b"; "d"; "a"] -> False.
  Proof.
    intros.
    destruct e; try discriminate.
    simpl in *.
    find_inversion.
    pose proof nat_to_symbol_in_bounds n "l".
    rewrite H1 in H.
    concludes. compute in H. omega.
  Qed.

  Lemma expr_to_from_symbol_tree :
    forall e, expr_from_symbol_tree (expr_to_symbol_tree e) = Some e.
  Proof.
    induction e; simpl.
    - now rewrite nat_to_from_symbol.
    - now rewrite IHe.
    - rewrite IHe1, IHe2.
      repeat break_match; try discriminate; auto.
      subst. exfalso. eauto using expr_to_symbol_no_confusion.
  Qed.

  Lemma expr_to_symbol_tree_wf :
    forall e, Tree.Forall symbol.wf (expr_to_symbol_tree e).
  Proof. induction e; simpl; auto using nat_to_symbol_wf. Qed.

  Definition round_trip (e : expr.t) : option expr.t :=
    parse (print_tree (expr_to_symbol_tree e)) >>= expr_from_symbol_tree.

  Lemma round_trip_id : forall e, round_trip e = Some e.
  Proof.
    unfold round_trip.
    intros.
    rewrite parse_print_tree by auto using expr_to_symbol_tree_wf.
    simpl.
    now rewrite expr_to_from_symbol_tree.
  Qed.

  Eval compute in print_tree (expr_to_symbol_tree expr.examples.id).

  Eval compute in eq_refl : Some expr.examples.id = round_trip expr.examples.id.

  Eval compute in print_tree (expr_to_symbol_tree expr.examples.omega).

  Eval compute in eq_refl : Some expr.examples.omega = round_trip expr.examples.omega.


  Definition round_trip' w (e : expr.t) : option expr.t :=
    parse (pretty_tree w (expr_to_symbol_tree e)) >>= expr_from_symbol_tree.

  Lemma round_trip'_id : forall w e, round_trip' w e = Some e.
  Proof.
    unfold round_trip'.
    intros.
    rewrite parse_pretty_tree by auto using expr_to_symbol_tree_wf.
    simpl.
    now rewrite expr_to_from_symbol_tree.
  Qed.

  Eval compute in String "010" (pretty_tree 10 (expr_to_symbol_tree expr.examples.id)).

  Eval compute in eq_refl : Some expr.examples.id = round_trip expr.examples.id.

  Eval compute in String "010" (pretty_tree 20 (expr_to_symbol_tree expr.examples.omega)).

  Eval compute in eq_refl : Some expr.examples.omega = round_trip expr.examples.omega.

End extended_example.
