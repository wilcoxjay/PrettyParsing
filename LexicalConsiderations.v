Require Import List String Ascii.
Import ListNotations.

From PrettyParsing Require Import StringUtils.

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

  Definition of_string : string -> t := string_to_list.

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
