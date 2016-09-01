Require Import List.
Import ListNotations.

Definition option_bind {A B} (m : option A) (f : A -> option B) : option B :=
  match m with
  | Some a => f a
  | None => None
  end.

Definition option_seq {A B} (f : option (A -> B)) (x : option A) : option B :=
  option_bind f (fun f => option_bind x (fun x => Some (f x))).

Fixpoint sequence {A} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | a :: l => match a with
             | Some a => match sequence l with
                        | Some l => Some (a :: l)
                        | None => None
                        end
             | None => None
             end
  end.

Ltac unfold_option := 
  unfold sequence, option_seq, option_bind, option_map in *.

Module OptionNotations.
  Notation "f <$> o" := (@option_map _ _ f o) (at level 42, left associativity) : option.
  Notation "f <*> x" := (@option_seq _ _ f x) (at level 42, left associativity) : option.
  Notation "m >>= f" := (@option_bind _ _ m f) (at level 42, left associativity) : option.
  Open Scope option.
End OptionNotations.
