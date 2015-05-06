Module Effect.
  Record t := New {
    command : Type;
    answer : command -> Type }.
End Effect.

Module C.
  Inductive t (E : Effect.t) (A : Type) : Type :=
  | Ret : A -> t E A
  | Call : forall c, (Effect.answer E c -> t E A) -> t E A.
  Arguments Ret {E A} _.
  Arguments Call {E A} _ _.
End C.

(*Module Run.
  Inductive t {E A} (x : C.t E A) 
End Run.*)

Module State.
  Module Command.
    Inductive t (S : Type) : Type :=
    | Read : t S
    | Write : S -> t S.

    Definition answer {S : Type} (c : t S) : Type :=
      match c with
      | Read => S
      | Write _ => unit
      end.

    Definition run_anwser {S : Type} (c : t S) (s : S) : answer c :=
      match c with
      | Read => s
      | Write x => tt
      end.

    Definition run_state {S : Type} (c : t S) (s : S) : S :=
      match c with
      | Read => s
      | Write x => x
      end.
  End Command.

  Definition E (S : Type) : Effect.t :=
    Effect.New (Command.t S) Command.answer.

  Module Invariant.
    Inductive t {S A : Type} (s : S) : C.t (E S) A -> Prop :=
    | Ret : forall v, t s (C.Ret v)
    | Call : forall c h,
      t (Command.run_state c s) (h (Command.run_anwser c s)) ->
      t s (C.Call (E := E S) c h).
  End Invariant.
End State.
