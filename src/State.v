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
    Inductive t {S} (s : S) : Trace.t (E S) -> S -> Prop :=
    | Ret : t s Trace.Ret s
    | Call : forall (c : Effect.command (E S)),
      t s (Trace.Call c (Command.run_anwser c s)) (Command.run_state c s)
    | Let : forall trace_x s_x trace_y s_y,
      t s trace_x s_x -> t s_x trace_y s_y ->
      t s (Trace.Let trace_x trace_y) s_y.
  End Invariant.

  Fixpoint eval {S A} (s : S) (x : C.t (E S) A) : option (A * S) :=
    match x with
    | C.Ret _ v => Some (v, s)
    | C.Call c => Some (Command.run_anwser c s, Command.run_state c s)
    | C.Let _ _ x f =>
      Option.bind (eval s x) (fun r =>
      let (v_x, s_x) := r in
      eval s_x (f v_x))
    | C.Choose _ _ _ | C.Join _ _ _ _ => None
    end.

  Require Import Coq.Logic.JMeq.

  Fixpoint eval_ok {S A} {s : S} {x : C.t (E S) A} {s' trace v}
    (H_trace : Trace.Valid.t x trace v) (H_inv : Invariant.t s trace s')
    : eq (eval s x) (Some (v, s')).
    destruct trace.
    - inversion_clear H_inv.
      exact (
        match H_trace in Trace.Valid.t x trace v return
          match trace with
          | Trace.Ret => eq (eval s' x) (Some (v, s'))
          | _ => True
          end : Prop with
        | Trace.Valid.Ret _ _ => eq_refl
        | _ => I
        end).
    - destruct x; [inversion H_trace | | inversion H_trace | inversion H_trace | inversion H_trace].
      simpl.
      assert (Command.run_state command s = s').
      inversion_clear H_inv.
      now inversion_clear H_trace.
      assert (JMeq (Command.run_anwser command s) v).
      generalize H_trace.
      refine (
        match H_trace in Trace.Valid.t x trace v return
          match x with
          | C.Call command =>
            match trace with
            | Trace.Call c a =>
              Trace.Valid.t (C.Call command) (Trace.Call c a) v ->
              JMeq (Command.run_anwser command s) v
            | _ => False
            end
          | _ => True
          end : Prop with
        | Trace.Valid.Call _ _ => _
        | _ => I
        end).
      assert (command = c).
      refine (
        match H_trace in Trace.Valid.t x trace _ return
          match x with
          | C.Call command =>
            match trace with
            | Trace.Call c _ => command = c
            | _ => False
            end
          | _ => True
          end : Prop with
        | Trace.Valid.Call _ _ => eq_refl
        | _ => I
        end).
      refine (
        match H_trace in Trace.Valid.t _ trace _ return
          match trace with
          | Trace.Call c a => JMeq (Command.run_anwser c s) v
          | _ => True
          end : Prop with
        | Trace.Valid.Call _ _ => _
        | _ => I
        end).
      refine (
        match H_inv in Invariant.t _ trace _ return
          match trace with
          | Trace.Call c a => JMeq (Command.run_anwser command s) v
          | _ => True
          end : Prop with
        | Invariant.Call _ => _
        | _ => I
        end).
              
              match trace with
              | Trace.Call c a =>
                JMeq (eval s (C.Call command)) (Some (a, Command.run_state c s))
              | _ => False
              end
            | _ => True
            end : Prop with
        | Trace.Valid.Call _ _ => _
        | _ => I
        end).
      inversion_clear H_trace.
      assert (H_c : command = c) by now inversion_clear H_trace.
      assert (JMeq (eval s (C.Call command)) (Some (v, Command.run_state c s))).
      assert (JMeq () v).
      refine (
        match H_trace in Trace.Valid.t x trace v return
          match x with
          | C.Call command =>
            match trace with
            | Trace.Call c a =>
              JMeq (eval s (C.Call command)) (Some (a, Command.run_state c s))
            | _ => False
            end
          | _ => True
          end : Prop with
        | Trace.Valid.Call _ _ => _
        | _ => I
        end).
      simpl.
      assert (JMeq a v).
      refine (
        match H_trace in Trace.Valid.t x trace v return
          match trace with
          | Trace.Call c a => JMeq a v
          | _ => True
          end : Prop with
        | Trace.Valid.Call _ _ => JMeq_refl
        | _ => I
        end).
      refine (
        match H_trace in Trace.Valid.t x trace v return
          match x with
          | C.Call command =>
            match trace with
            | Trace.Call c a =>
              Some (Command.run_anwser command s, Command.run_state command s) =
              Some (v, Command.run_state c s)
            | _ => False
            end
          | _ => True
          end : Prop with
        | Trace.Valid.Call _ _ => _
        | _ => I
        end).
      inversion H_trace.
    inversion H_trace.
    destruct x; simpl.
    - refine (
        match H_trace in Trace.Valid.t x trace v return
          match x with
          | C.Ret _ x => Invariant.t s trace s' -> Some (x, s) = Some (v, s')
          | _ => True
          end : Prop with
        | Trace.Valid.Ret _ _ => _
        | _ => I
        end).
    ; inversion_clear H_trace; intro H_inv.
    - inversion_clear H_inv.
    (*destruct x; simpl.
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
        now rewrite <- H_a.*)
  Qed.
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
