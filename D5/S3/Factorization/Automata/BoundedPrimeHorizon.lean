/- GID: D5/S3/Factorization/Automata/BoundedPrimeHorizon
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/BoundedPrimeHorizon
   mirror-E: none(waiver:exact-all-word-observation-kernel)
   anchors: []
   utility: none
   digest: Bounded multiplication/division words have an exact realizable two-boundary observation quotient. -/

import D5.S0.Automata.TypedPartialDFAOOverBase
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Factorization.Automata.BoundedPrimeHorizon

open D5.S0.Automata.TypedPartialDFAOOverBase

/-- A live exponent is in the closed interval `[0,a]`; undefined steps reject. -/
def step (a : Nat) (e : Fin (a + 1)) (up : Bool) : Option (Fin (a + 1)) :=
  if up then
    if h : e.val < a then some ⟨e.val + 1, by omega⟩ else none
  else
    if h : 0 < e.val then some ⟨e.val - 1, by have := e.isLt; omega⟩ else none

/-- Execute a guarded multiplication/division word from a live exponent. -/
def run (a : Nat) (e : Fin (a + 1)) (w : List Bool) : Option (Fin (a + 1)) :=
  runTransition (step a) e w

/-- Record whether every command in the word respects the two guards. -/
def accepts (a : Nat) (e : Fin (a + 1)) (w : List Bool) : Bool :=
  (run a e w).isSome

/-- Distances to both guards, truncated at the remaining query horizon. -/
def close (a H : Nat) (e f : Fin (a + 1)) : Prop :=
  min e.val H = min f.val H ∧ min (a - e.val) H = min (a - f.val) H

/-- Complete finite-horizon characterization for the actual guarded word runner.
The induction treats failure at each intermediate step, not only net displacement. -/
theorem finite_horizon_kernel (a H : Nat) (e f : Fin (a + 1)) :
    (∀ w : List Bool, w.length ≤ H → accepts a e w = accepts a f w) ↔ close a H e f := by
  have accepts_up (x : Fin (a + 1)) (n : Nat) :
      accepts a x (List.replicate n true) = decide (x.val + n ≤ a) := by
    induction n generalizing x with
    | zero =>
        have hx : x.val ≤ a := by have := x.isLt; omega
        simp [accepts, run, runTransition, hx]
    | succ n ih =>
        unfold accepts at ih ⊢
        simp only [List.replicate_succ, run, runTransition]
        by_cases hx : x.val < a
        · have hy : x.val + 1 < a + 1 := by omega
          simpa [run, step, hx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using ih (⟨x.val + 1, hy⟩ : Fin (a + 1))
        · have hn : ¬ x.val + (n + 1) ≤ a := by omega
          simp [step, hx, hn]
  have accepts_down (x : Fin (a + 1)) (n : Nat) :
      accepts a x (List.replicate n false) = decide (n ≤ x.val) := by
    induction n generalizing x with
    | zero => simp [accepts, run, runTransition]
    | succ n ih =>
        unfold accepts at ih ⊢
        simp only [List.replicate_succ, run, runTransition]
        by_cases hx : 0 < x.val
        · have hy : x.val - 1 < a + 1 := by have := x.isLt; omega
          have hn : (n ≤ x.val - 1) ↔ n + 1 ≤ x.val := by omega
          simpa [run, step, hx, hn] using ih (⟨x.val - 1, hy⟩ : Fin (a + 1))
        · have hn : ¬ n + 1 ≤ x.val := by omega
          simp [step, hx, hn]
  constructor
  · intro hall
    have low (x y : Fin (a + 1))
        (hxy : ∀ w : List Bool, w.length ≤ H → accepts a x w = accepts a y w) :
        min x.val H ≤ y.val := by
      have hl := hxy (List.replicate (min x.val H) false)
        (by simp [min_le_right])
      have hx : accepts a x (List.replicate (min x.val H) false) = true := by
        rw [accepts_down]
        simpa only [decide_eq_true_eq] using (min_le_left x.val H)
      have hy := hl.symm.trans hx
      rw [accepts_down] at hy
      exact of_decide_eq_true hy
    have high (x y : Fin (a + 1))
        (hxy : ∀ w : List Bool, w.length ≤ H → accepts a x w = accepts a y w) :
        min (a - x.val) H ≤ a - y.val := by
      have hl := hxy (List.replicate (min (a - x.val) H) true)
        (by simp [min_le_right])
      have hx : accepts a x (List.replicate (min (a - x.val) H) true) = true := by
        rw [accepts_up]
        simp only [decide_eq_true_eq]
        have := x.isLt
        have := min_le_left (a - x.val) H
        omega
      have hy := hl.symm.trans hx
      rw [accepts_up] at hy
      have hb : y.val + min (a - x.val) H ≤ a := of_decide_eq_true hy
      omega
    have hrev : ∀ w : List Bool, w.length ≤ H → accepts a f w = accepts a e w :=
      fun w hw => (hall w hw).symm
    exact ⟨le_antisymm
        (le_min (low e f hall) (min_le_right _ _))
        (le_min (low f e hrev) (min_le_right _ _)),
      le_antisymm
        (le_min (high e f hall) (min_le_right _ _))
        (le_min (high f e hrev) (min_le_right _ _))⟩
  · intro hc
    induction H generalizing e f with
    | zero =>
        intro w hw
        have hnil : w = [] := List.length_eq_zero_iff.mp (by omega)
        subst w
        rfl
    | succ H ih =>
        intro w hw
        have heBound := e.isLt
        have hfBound := f.isLt
        obtain ⟨hlo, hhi⟩ := hc
        cases w with
        | nil => rfl
        | cons b w =>
            have hw' : w.length ≤ H := by simpa using Nat.le_of_succ_le_succ hw
            cases b with
            | false =>
                by_cases he : 0 < e.val
                · have hf : 0 < f.val := by omega
                  let e' : Fin (a + 1) := ⟨e.val - 1, by omega⟩
                  let f' : Fin (a + 1) := ⟨f.val - 1, by omega⟩
                  have hc' : close a H e' f' := by
                    dsimp [close, e', f']
                    constructor <;> omega
                  have hs := ih e' f' hc' w hw'
                  simpa [accepts, run, runTransition, step, he, hf, e', f'] using hs
                · have hf : ¬ 0 < f.val := by omega
                  simp [accepts, run, runTransition, step, he, hf]
            | true =>
                by_cases he : e.val < a
                · have hf : f.val < a := by omega
                  let e' : Fin (a + 1) := ⟨e.val + 1, by omega⟩
                  let f' : Fin (a + 1) := ⟨f.val + 1, by omega⟩
                  have hc' : close a H e' f' := by
                    dsimp [close, e', f']
                    constructor <;> omega
                  have hs := ih e' f' hc' w hw'
                  simpa [accepts, run, runTransition, step, he, hf, e', f'] using hs
                · have hf : ¬ f.val < a := by omega
                  simp [accepts, run, runTransition, step, he, hf]

/-- A canonical code of the actual profile image: collapse only the central
interval, if it is wider than one point. This is not a same-horizon state update. -/
def codeValue (a H e : Nat) : Nat :=
  if a ≤ 2 * H then e else if e ≤ H then e else max H (e - (a - 2 * H))

def code (a H : Nat) (e : Fin (a + 1)) : Fin (min a (2 * H) + 1) :=
  ⟨codeValue a H e.val, by
    have he := e.isLt
    dsimp [codeValue]
    split_ifs <;> omega⟩

def observed (a : Nat) (q : Option (Fin (a + 1))) (w : List Bool) : Bool :=
  match q with
  | none => false
  | some e => accepts a e w

/-- Exact realized observation quotient including the absorbing reject state.
Its full carrier has min(a,2H)+2 elements. Both kernel equality and surjectivity
are proved, so this is an exact count and not merely an encoding upper bound. -/
theorem profile_classification (a H : Nat) :
    Function.Surjective (fun q : Option (Fin (a + 1)) => q.map (code a H)) ∧
    (∀ q r : Option (Fin (a + 1)),
      (∀ w : List Bool, w.length ≤ H → observed a q w = observed a r w) ↔
        q.map (code a H) = r.map (code a H)) ∧
    Fintype.card (Option (Fin (min a (2 * H) + 1))) = min a (2 * H) + 2 := by
  have hkernel (e f : Fin (a + 1)) : code a H e = code a H f ↔ close a H e f := by
    have he := e.isLt
    have hf := f.isLt
    rw [Fin.ext_iff]
    change codeValue a H e.val = codeValue a H f.val ↔ _
    dsimp [codeValue, close]
    split_ifs <;> omega
  have hsurj : Function.Surjective (code a H) := by
    intro q
    have hq := q.isLt
    have hqa : q.val ≤ a := by have := min_le_left a (2 * H); omega
    have hqH : q.val ≤ 2 * H := by have := min_le_right a (2 * H); omega
    by_cases ha : a ≤ 2 * H
    · refine ⟨⟨q.val, by omega⟩, ?_⟩
      apply Fin.ext
      change codeValue a H q.val = q.val
      simp [codeValue, ha]
    · by_cases hq0 : q.val ≤ H
      · refine ⟨⟨q.val, by omega⟩, ?_⟩
        apply Fin.ext
        change codeValue a H q.val = q.val
        simp [codeValue, ha, hq0]
      · refine ⟨⟨a - (2 * H - q.val), by omega⟩, ?_⟩
        apply Fin.ext
        change codeValue a H (a - (2 * H - q.val)) = q.val
        dsimp [codeValue]
        split_ifs <;> omega
  refine ⟨?_, ?_, by simp [Nat.add_assoc]⟩
  · intro q
    cases q with
    | none => exact ⟨none, rfl⟩
    | some q =>
        obtain ⟨e, he⟩ := hsurj q
        exact ⟨some e, by simp [he]⟩
  · intro q r
    cases q with
    | none =>
        cases r with
        | none => simp [observed]
        | some f =>
            constructor
            · intro h
              have hf := h [] (by simp)
              simp [observed, accepts, run, runTransition] at hf
            · simp
    | some e =>
        cases r with
        | none =>
            constructor
            · intro h
              have he := h [] (by simp)
              simp [observed, accepts, run, runTransition] at he
            · simp
        | some f =>
            simpa only [observed, Option.map_some, Option.some.injEq] using
              (finite_horizon_kernel a H e f).trans (hkernel e f).symm

#print axioms finite_horizon_kernel
#print axioms profile_classification

end D5.S3.Factorization.Automata.BoundedPrimeHorizon
