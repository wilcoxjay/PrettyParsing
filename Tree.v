Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section tree.
  (* The tree is parametrized on the type of data stored at the leaves. *)
  Variable A : Type.

  (* Each node of the tree contains a list of subtrees.
     Coq does not generate a useful induction scheme for such types,
     so we just tell it not to generate anything, and we'll write our own. *)
  Local Unset Elimination Schemes.

  Inductive tree : Type :=
  | atom : A -> tree
  | node : list tree -> tree
  .

  (* Here is an actually useful recursion principle for tree,
     which requires an additional motive P_list. *)
  Section tree_rect.
    Variable P : tree -> Type.
    Variable P_list : list tree -> Type.
    Hypothesis P_nil : P_list [].
    Hypothesis P_cons : forall t l, P t -> P_list l -> P_list (t :: l).
    Hypothesis P_atom : forall a, P (atom a).
    Hypothesis P_node : forall l, P_list l -> P (node l).

    Fixpoint tree_rect (t : tree) : P t :=
      let fix go_list (l : list tree) : P_list l :=
          match l with
          | [] => P_nil
          | t :: l => P_cons (tree_rect t) (go_list l)
          end
      in
      match t with
      | atom a => P_atom a
      | node l => P_node (go_list l)
      end.
  End tree_rect.

  (* Setting P_list := List.Forall P is a reasonable default. *)
  Section tree_ind.
    Variable P : tree -> Prop.

    Hypothesis P_atom : forall a, P (atom a).
    Hypothesis P_node : forall l, List.Forall P l -> P (node l).

    Definition tree_ind (t : tree) : P t :=
      tree_rect P (List.Forall P)
                (List.Forall_nil _)
                (fun t l Pt Pl => List.Forall_cons _ Pt Pl) P_atom P_node t.
  End tree_ind.

  Variable A_eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.

  Fixpoint tree_eq_dec (t1 t2 : tree) : {t1 = t2} + {t1 <> t2}.
    unshelve refine (
    let fix go_list (l1 l2 : list tree) : {l1 = l2} + {l1 <> l2}  :=
        match l1 with
        | [] =>
          match l2 with
          | [] => left eq_refl
          | _ => right _
          end
        | t1 :: l1 =>
          match l2 with
          | [] => right _
          | t2 :: l2 =>
            match tree_eq_dec t1 t2 with
            | left _ =>
              match go_list l1 l2 with
              | left _ => left _
              | right _ => right _
              end
            | right _ => right _
            end
          end
        end
    in
    match t1 with
    | atom a1 =>
      match t2 with
      | atom a2 =>
        match A_eq_dec a1 a2 with
        | left _ => left _
        | right _ => right _
        end
      | _ => right _
      end
    | node l1 =>
      match t2 with
      | atom a2 => right _
      | node l2 =>
        match go_list l1 l2 with
        | left _ => left _
        | right _ => right _
        end
      end
    end); congruence.
  Defined.

  Definition get_atom (t : tree) : option A :=
    match t with
    | atom a => Some a
    | _ => None
    end.
End tree.

Section Forall.
  Variable A : Type.
  Variable P : A -> Prop.

  Inductive Forall : tree A -> Prop :=
  | Forall_atom : forall a, P a -> Forall (atom a)
  | Forall_node : forall l, List.Forall Forall l -> Forall (node l)
  .
End Forall.
Hint Resolve Forall_atom Forall_node.