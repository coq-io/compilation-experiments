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

Module Run.
  Inductive t {E A} : C.t E A -> Type :=
  | Ret : forall v, t (C.Ret v)
  | Call : forall c a h, t (h a) -> t (C.Call c h).
  Arguments Ret {E A} _.
  Arguments Call {E A} _ _ _ _.
End Run.

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
    Inductive t {S A} (s : S) : forall {x : C.t (E S) A}, Run.t x -> Prop :=
    | Ret : forall v, t s (Run.Ret v)
    | Call : forall c h run_h_a,
      t (Command.run_state c s) run_h_a ->
      t s (Run.Call (E := E S) c (Command.run_anwser c s) h run_h_a).
  End Invariant.
End State.
