Require Import Coq.Lists.List.
Require Import Io.All.

Import ListNotations.
Import C.Notations.

Module Event.
  Record t (E : Effect.t) : Type := New {
    c : Effect.command E;
    a : Effect.answer E c }.
  Arguments New {E} _ _.
  Arguments c {E} _.
  Arguments a {E} _.
End Event.

Module Trace.
  Definition t (E : Effect.t) : Type :=
    list (Event.t E).

  Module Valid.
    Inductive t {E} : forall {A}, C.t E A -> Trace.t E -> A -> Prop :=
    | Ret : forall A v, t (C.Ret A v) [] v
    | Call : forall c a,
      t (C.Call c) [Event.New c a] a
    | Let : forall A B x trace_x v_x f trace_y v_y,
      t x trace_x v_x -> t (f v_x) trace_y v_y ->
      t (C.Let A B x f) (trace_x ++ trace_y) v_y.
  End Valid.
End Trace.

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
    Inductive t {S} (s : S) : Trace.t (E S) -> Prop :=
    | Ret : t s []
    | Call : forall c trace,
      t (Command.run_state c s) trace ->
      t s (Event.New (E := E S) c (Command.run_anwser c s) :: trace).
  End Invariant.

  Fixpoint eval {S A} (x : C.t (E S) A) (s : S) : A :=
    match x with
    | C.Ret v => v
    | C.Call c h =>
      let a := Command.run_anwser c s in
      let s' := Command.run_state c s in
      eval (h a) s'
    end.

  Fixpoint eval_ok {S A} {x : C.t (E S) A} {s : S} {trace : Trace.t (E S)}
    {v : A} (H_inv : Invariant.t s trace) (H_trace : Trace.Valid.t x trace v)
    : eval x s = v.
    destruct x; simpl.
    - now inversion_clear H_trace.
    - generalize H_inv; clear H_inv.
      refine (
        match H_trace in Trace.Valid.t x trace v return
          match x with
          | C.Call c t =>
            Invariant.t s trace ->
            eval (t (Command.run_anwser c s)) (Command.run_state c s) = v
          | _ => True
          end : Prop with
        | Trace.Valid.Call _ _ _ _ _ _ => _
        | _ => I
        end).
      intro H_inv.
      apply eval_ok with (trace := trace0).
      + now inversion H_inv.
      + assert (H_a : a = Command.run_anwser c0 s) by now inversion_clear H_inv.
        now rewrite <- H_a.
  Qed.
End State.

Module Incr.
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
End Incr.
