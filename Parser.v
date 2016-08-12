Require Import List.
Import ListNotations.

From PrettyParsing Require Import Tree LexicalConsiderations Tokenizer OptionUtils.
Import OptionNotations.

Fixpoint parse_toks' (toks : list token.t) (acc : list (list (tree symbol.t))) :
    option (tree symbol.t * list token.t) :=
  match toks with
  | [] => None
  | tok :: toks =>
    match tok with
    | token.symbol s =>
      match acc with
      | [] => Some (atom s, toks)
      | ts :: acc => parse_toks' toks ((atom s :: ts) :: acc)
      end
    | token.lparen => parse_toks' toks ([] :: acc)
    | token.rparen =>
      match acc with
      | [] => None
      | ts1 :: acc =>
        let t := node (List.rev ts1) in
        match acc with
        | [] => Some (t, toks)
        | ts2 :: acc => parse_toks' toks ((t :: ts2) :: acc)
        end
      end
    end
  end.

Definition parse_toks (toks : list token.t) : option (tree symbol.t) :=
  match parse_toks' toks [] with
  | Some (t, _) => Some t
  | None => None
  end.

Definition parse s := tokenize s >>= parse_toks.
