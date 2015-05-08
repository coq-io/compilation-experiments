Require Import Coq.Lists.List.
Require Import ErrorHandlers.All.
Require Import Io.All.

Import ListNotations.
Import C.Notations.

Module Trace.
  Inductive t (E : Effect.t) : Type :=
  | Ret : t E
  | Call : forall c, Effect.answer E c -> t E
  | Let : t E -> t E -> t E
  | Choose : t E + t E -> t E
  | Join : t E -> t E -> t E.
  Arguments Ret {E}.
  Arguments Call {E} _ _.
  Arguments Let {E} _ _.
  Arguments Choose {E} _.
  Arguments Join {E} _ _.

  Module Valid.
    Inductive t {E} : forall {A}, C.t E A -> Trace.t E -> A -> Prop :=
    | Ret : forall A v, t (C.Ret A v) Trace.Ret v
    | Call : forall c a, t (C.Call c) (Trace.Call c a) a
    | Let : forall A B x trace_x v_x f trace_y v_y,
      t x trace_x v_x -> t (f v_x) trace_y v_y ->
      t (C.Let A B x f) (Trace.Let trace_x trace_y) v_y
    | ChooseLeft : forall A x1 trace_x1 v_x1 x2,
      t x1 trace_x1 v_x1 ->
      t (C.Choose A x1 x2) (Trace.Choose (inl trace_x1)) v_x1
    | ChooseRight : forall A x1 x2 trace_x2 v_x2,
      t x2 trace_x2 v_x2 ->
      t (C.Choose A x1 x2) (Trace.Choose (inr trace_x2)) v_x2
    | Join : forall A B x trace_x v_x y trace_y v_y,
      t x trace_x v_x -> t y trace_y v_y ->
      t (C.Join A B x y) (Trace.Join trace_x trace_y) (v_x, v_y).
  End Valid.
End Trace.

Module Model.
  Definition t (E : Effect.t) (S : Type) : Type :=
    forall (c : Effect.command E), S -> option (Effect.answer E c * S).

  Module Invariant.
    Inductive t {E S} (m : t E S) (s s_ _s : S) : Trace.t E -> S -> Prop :=
    | Ret : t m s Trace.Ret s.
    | Call : forall c a s',
      m c s = Some (a, s') ->
      t m s (Trace.Call c a) s'
    | Let : forall trace_x s'_x s_y trace_y s'_y,
      t m s trace_x s'_x -> t m s_y trace_y s'_y ->
      t m s (Trace.Let trace_x trace_y) s'_y
    | ChooseLeft : forall trace s',
      t m s trace s' ->
      t m s (Trace.Choose (inl trace)) s'
    | ChooseRight : forall trace s',
      t m s trace s' ->
      t m s (Trace.Choose (inr trace)) s'
    | Join : forall trace_x.
  End Invariant.
End Model.

Module State.
  Module Command.
    Inductive t (S : Type) : Type :=
    | Read : t S
    | Write : S -> t S.
    Arguments Read {S}.
    Arguments Write {S} _.

    Definition answer {S : Type} (c : t S) : Type :=
      match c with
      | Read => S
      | Write _ => unit
      end.
  End Command.

  Definition E (S : Type) : Effect.t :=
    Effect.New (Command.t S) Command.answer.

  Definition model (S : Type) : Model.t (E S) S :=
    fun c s =>
      match c with
      | Command.Read => Some (s, s)
      | Command.Write s => Some (tt, s)
      end.
End State.

(*Module Incr.
  Module Command.
    Inductive t : Set :=
    | Incr : t
    | Read : t.

    Definition answer (c : t) : Type :=
      match c with
      | Incr => unit
      | Read => nat
      end.

    Definition run_anwser (c : t) (s : nat) : answer c :=
      match c with
      | Incr => tt
      | Read => s
      end.

    Definition run_state (c : t) (s : nat) : nat :=
      match c with
      | Incr => S s
      | Read => s
      end.

    Definition run (c : t) : C.t (State.E nat) (answer c) :=
      match c with
      | Incr =>
        C.Call (E := State.E nat) State.Command.Read (fun s =>
        C.Call (E := State.E nat) (State.Command.Write (S s)) (fun _ =>
        C.Ret tt))
      | Read =>
        C.Call (E := State.E nat) State.Command.Read (fun s =>
        C.Ret s)
      end.
  End Command.

  Definition E : Effect.t :=
    Effect.New Command.t Command.answer.

  Module Invariant.
    Inductive t (s : nat) : Trace.t E -> Prop :=
    | Ret : t s []
    | Call : forall c trace,
      t (Command.run_state c s) trace ->
      t s (Event.New (E := E) c (Command.run_anwser c s) :: trace).
  End Invariant.

  Fixpoint eval {A} (x : C.t E A) (s : nat) : A :=
    match x with
    | C.Ret v => v
    | C.Call c h =>
      let a := Command.run_anwser c s in
      let s' := Command.run_state c s in
      eval (h a) s'
    end.

  Fixpoint run {A} (x : C.t E A) : C.t (State.E nat) A :=
    match x with
    | C.Ret v => C.Ret v
    | C.Call c h => C.Call (Command)
    end.
End Incr.*)
