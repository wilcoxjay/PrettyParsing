Require Import String.

Module error.
  Inductive t (A : Type) : Type :=
  | Ok : A -> t A
  | Err : string -> t A
  .
  Arguments Ok {_} _.
  Arguments Err {_} _.

  Definition ret {A} (x : A) : t A := Ok x.

  Definition bind {A B} (x : t A) (f : A -> t B) : t B :=
    match x with
    | Ok a => f a
    | Err s => Err s
    end.

  Definition map {A B} (f : A -> B) (x : t A) : t B :=
    bind x (fun a => ret (f a)).

  Definition seq {A B} (f : t (A -> B)) (x : t A) : t B :=
    bind f (fun f => bind x (fun a => ret (f a))).

  Definition error {A} (msg : string) : t A := Err msg.

  Definition unwrap {A} (x : option A) : t A :=
    match x with
    | Some x => ret x
    | None => error "unwrap None!"
    end.

  Definition expect {A} (msg : string) (x : option A) : t A :=
    match x with
    | Some a => ret a
    | None => error msg
    end.

  Module notations.
    Delimit Scope error with error.
    Open Scope error.
    Notation "m >>= f" := (@bind _ _ m f) (at level 42, left associativity) : error.
    Notation "x <- m ;; f" := (m >>= (fun x => f)) (at level 43, right associativity) : error.
    Notation "f <$> x" := (@map _ _ f x) (at level 42, left associativity) : error.
    Notation "f <*> x" := (@seq _ _ f x) (at level 42, left associativity) : error.
  End notations.
End error.
