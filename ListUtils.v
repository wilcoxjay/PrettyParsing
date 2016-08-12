Require Import List.
Import ListNotations.

Fixpoint intersperse {A} (a : A) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: l1 => x ::
    match l1 with
    | [] => []
    | y :: l2 => a :: intersperse a l1
    end
  end.

Definition intercalate {A} (x : list A) (ys : list (list A)) : list A :=
  concat (intersperse x ys).

Fixpoint index_of {A} (A_eq_dec : forall x y : A, {x = y} + {x <> y})
         (a : A) (l : list A) : option nat :=
  match l with
  | [] => None
  | x :: l => if A_eq_dec a x then Some 0
             else match index_of A_eq_dec a l with
                  | None => None
                  | Some n => Some (S n)
                  end
  end.
