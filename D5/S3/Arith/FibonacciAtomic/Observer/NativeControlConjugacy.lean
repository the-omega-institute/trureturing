/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeControlConjugacy
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/NativeControlConjugacy
   mirror-E: none(waiver:unbounded-execution-transport)
   anchors: []
   utility: none
   digest: Complete control equivalences preserve native actions, same-source traces and exact finite prefixes. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeControlConjugacy

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open NativeSerialMachine

/-- Change control coordinates only, retaining instruction type, literal and output. -/
def mapOp {C D O : Type} (f : C → D) : Op C O → Op D O
  | .localStep c => .localStep (f c)
  | .read a k => .read a (fun y => f (k y))
  | .applyRho c => .applyRho (f c)
  | .stop o => .stop o

def reindex {C D O : Type} (e : C ≃ D) (δ : C → Op C O) (w : D) : Op D O :=
  mapOp e (δ (e.symm w))

def mapConfig {C D : Type} (e : C → D) (x : Config C) : Config D :=
  (e x.1, x.2)

/-- Iteration counts chronological actions; none remains none after a halt. -/
def advance {C O : Type} (δ : C → Op C O) (x : Option (Config C)) :
    Option (Config C) := x.bind (nativeStep δ)

/-- A fixed event-indexed model with five explicit charged coordinates. -/
structure CostModel where
  address : Address → Nat
  response : Reply → Nat
  updateAcknowledgement : Nat

def eventCost (m : CostModel) : Event → Fin 5 → Nat
  | .localStep => ![0, 0, 0, 0, 0]
  | .update _ => ![1, 0, 1, 0, m.updateAcknowledgement]
  | .read _ p y => ![1, 1, 0, m.address p, m.response y]

/-- Primitive, Read, Update, address and response costs of the actual trace. -/
def cost (m : CostModel) (t : Trace) (i : Fin 5) : Nat :=
  ((t.map (fun a => eventCost m a i))).sum

/-- Exactly n more actions to a fixed first halt, with no skipped instruction. -/
def Remaining {C O : Type} (δ : C → Op C O) (c : C) (j : Nat)
    (u : Source) (n : Nat) (o : O) : Prop :=
  ∃ t, Run δ c j u t o ∧ t.length = n

private theorem run_map {C D O : Type} (f : C → D) (δ : C → Op C O)
    (ε : D → Op D O) (rows : ∀ c, ε (f c) = mapOp f (δ c))
    {c : C} {j : Nat} {u : Source} {t : Trace} {o : O}
    (run : Run δ c j u t o) : Run ε (f c) j u t o := by
  induction run with
  | stop h => exact .stop (by rw [rows, h]; rfl)
  | localStep h _ ih => exact .localStep (by rw [rows, h]; rfl) ih
  | update h _ ih => exact .update (by rw [rows, h]; rfl) ih
  | read h hy _ ih => exact .read (by rw [rows, h]; rfl) hy ih

private theorem step_map {C D O : Type} (f : C → D) (δ : C → Op C O)
    (ε : D → Op D O) (rows : ∀ c, ε (f c) = mapOp f (δ c)) (x : Config C) :
    nativeStep ε (mapConfig f x) = (nativeStep δ x).map (mapConfig f) := by
  obtain ⟨c,j,u,t⟩ := x
  simp only [mapConfig, nativeStep, rows]
  cases δ c <;> rfl

/-- The complete same-source certificate, including empty reachability fibers.
The prefix equivalence counts each actual action and preserves the full log. -/
structure Certificate {C D O : Type} (e : C ≃ D) (δ : C → Op C O) : Prop where
  rows : ∀ c, reindex e δ (e c) = mapOp e (δ c)
  steps : ∀ x, nativeStep (reindex e δ) (mapConfig e x) =
    (nativeStep δ x).map (mapConfig e)
  runs : ∀ c j u t o, Run (reindex e δ) (e c) j u t o ↔ Run δ c j u t o
  prefixes : ∀ (x y : Config C) (n : Nat),
    (advance (reindex e δ))^[n] (some (mapConfig e x)) = some (mapConfig e y) ↔
      (advance δ)^[n] (some x) = some y
  halt : ∀ c o, reindex e δ (e c) = .stop o ↔ δ c = .stop o
  remaining : ∀ c j u n o,
    Remaining (reindex e δ) (e c) j u n o ↔ Remaining δ c j u n o
  deterministic : ∀ c j u t s o b, Run δ c j u t o → Run δ c j u s b → t = s ∧ o = b
  bills : ∀ c j u t s o b m,
    Run δ c j u t o → Run (reindex e δ) (e c) j u s b →
      t = s ∧ o = b ∧ ∀ i : Fin 5, cost m t i = cost m s i

/-- Reindexing the complete control preserves the actual native interpreter,
without changing the source, adding actions, or replacing a raw response. -/
theorem native_control_conjugacy {C D O : Type} (e : C ≃ D) (δ : C → Op C O) :
    (∀ c, reindex e δ (e c) = mapOp e (δ c)) ∧
    (∀ x, nativeStep (reindex e δ) (mapConfig e x) =
      (nativeStep δ x).map (mapConfig e)) ∧
    (∀ c j u t o, Run (reindex e δ) (e c) j u t o ↔ Run δ c j u t o) ∧
    (∀ (x y : Config C) (n : Nat),
      (advance (reindex e δ))^[n] (some (mapConfig e x)) = some (mapConfig e y) ↔
        (advance δ)^[n] (some x) = some y) ∧
    (∀ c o, reindex e δ (e c) = .stop o ↔ δ c = .stop o) ∧
    (∀ c j u n o, Remaining (reindex e δ) (e c) j u n o ↔ Remaining δ c j u n o) ∧
    (∀ c j u t s o b, Run δ c j u t o → Run δ c j u s b → t = s ∧ o = b) ∧
    (∀ c j u t s o b m, Run δ c j u t o → Run (reindex e δ) (e c) j u s b →
      t = s ∧ o = b ∧ ∀ i : Fin 5, cost m t i = cost m s i) := by
  have rows : ∀ c, reindex e δ (e c) = mapOp e (δ c) := by
    intro c; simp [reindex]
  have inverse : ∀ w, δ (e.symm w) = mapOp e.symm (reindex e δ w) := by
    intro w
    simp only [reindex]
    cases δ (e.symm w) <;> simp [mapOp, Function.comp_def]
  have runs : ∀ c j u t o, Run (reindex e δ) (e c) j u t o ↔ Run δ c j u t o := by
    intro c j u t o
    constructor
    · intro r
      simpa using run_map e.symm (reindex e δ) δ inverse r
    · exact run_map e δ (reindex e δ) rows
  have step := step_map e δ (reindex e δ) rows
  have injective : Function.Injective (mapConfig e) := by
    rintro ⟨c,j,u,t⟩ ⟨d,k,v,s⟩ h
    have hc := e.injective (congrArg Prod.fst h)
    have ht := congrArg Prod.snd h
    change c = d at hc
    subst d
    exact Prod.ext rfl ht
  have iter : ∀ n x,
      (advance (reindex e δ))^[n] (x.map (mapConfig e)) =
        ((advance δ)^[n] x).map (mapConfig e) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        cases h : (advance δ)^[n] x with
        | none => rfl
        | some y => exact step y
  refine ⟨rows, step, runs, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y n
    rw [show some (mapConfig e x) = (some x).map (mapConfig e) from rfl, iter]
    change ((advance δ)^[n] (some x)).map (mapConfig e) =
      (some y).map (mapConfig e) ↔ _
    exact (Option.map_injective injective).eq_iff
  · intro c o
    rw [rows]
    cases δ c <;> simp [mapOp]
  · intro c j u n o
    simp only [Remaining, runs]
  · intro c j u t s o b p q
    exact NativeSerialDepth.run_unique p q
  · intro c j u t s o b m p q
    obtain ⟨same,out⟩ := NativeSerialDepth.run_unique p ((runs c j u s b).mp q)
    exact ⟨same,out,fun i => congrArg (fun trace => cost m trace i) same⟩

/-- Typed packaging of the complete conjugacy, used by installed-table realizations. -/
def certificate {C D O : Type} (e : C ≃ D) (δ : C → Op C O) : Certificate e δ := by
  obtain ⟨rows,steps,runs,prefixes,halt,remaining,deterministic,bills⟩ :=
    native_control_conjugacy e δ
  exact ⟨rows,steps,runs,prefixes,halt,remaining,deterministic,bills⟩

#print axioms native_control_conjugacy

end D5.S3.Arith.FibonacciAtomic.Observer.NativeControlConjugacy
