/- GID: D5/S3/Factorization/Automata/BoundedPrimeHorizon
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/BoundedPrimeHorizon
   mirror-E: none(waiver:exact-all-word-observation-kernel)
   anchors: []
   utility: none
   digest: Actual bounded multiplication/division words have the exact two-boundary
     observation kernel, a realizable finite quotient, and sharp separation lengths. -/

import D5.S3.Factorization.Automata.BoundedPrimeWalk
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace D5.S3.Factorization.Automata.BoundedPrimeHorizon

open BoundedPrimeWalk
open D5.S0.Automata.TypedPartialDFAOOverBase

/-- Distances to both guards, truncated at the remaining query horizon. -/
def close (a H : Nat) (e f : Fin (a + 1)) : Prop :=
  min e.val H = min f.val H ∧ min (a - e.val) H = min (a - f.val) H

/-- Complete finite-horizon characterization for the actual guarded word runner.
The induction treats failure at each intermediate step, not only net displacement. -/
theorem finite_horizon_kernel (a H : Nat) (e f : Fin (a + 1)) :
    (∀ w : List Bool, w.length ≤ H → accepts a e w = accepts a f w) ↔ close a H e f := by
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
        have hnil : w = [] := List.length_eq_zero.mp (by omega)
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

/-- An exact query-length threshold for any two ordered live exponents.
The witnessing word is a pure sequence of multiplications or exact divisions;
no shorter mixed word can distinguish this pair. -/
theorem shortest_separation (a H : Nat) (e f : Fin (a + 1)) (hef : e.val < f.val) :
    (∃ w : List Bool, w.length ≤ H ∧ accepts a e w ≠ accepts a f w) ↔
      min (e.val + 1) (a - f.val + 1) ≤ H := by
  have he := e.isLt
  have hf := f.isLt
  constructor
  · rintro ⟨w, hw, hd⟩
    by_contra hn
    have hc : close a H e f := by
      dsimp [close]
      constructor <;> omega
    exact hd ((finite_horizon_kernel a H e f).mpr hc w hw)
  · intro h
    by_cases hlo : e.val + 1 ≤ H
    · refine ⟨List.replicate (e.val + 1) false, by simpa, ?_⟩
      rw [accepts_down, accepts_down]
      have he0 : ¬ e.val + 1 ≤ e.val := by omega
      have hf0 : e.val + 1 ≤ f.val := by omega
      simp [he0, hf0]
    · have hhi : a - f.val + 1 ≤ H := by omega
      refine ⟨List.replicate (a - f.val + 1) true, by simpa, ?_⟩
      rw [accepts_up, accepts_up]
      have he0 : e.val + (a - f.val + 1) ≤ a := by omega
      have hf0 : ¬ f.val + (a - f.val + 1) ≤ a := by omega
      simp [he0, hf0]

/-- The least horizon that separates all live states is ceiling(a/2).
Necessity constructs the distinct central states H and H+1 when a>2H. -/
theorem full_separation_threshold (a H : Nat) :
    (∀ e f : Fin (a + 1),
      (∀ w : List Bool, w.length ≤ H → accepts a e w = accepts a f w) → e = f) ↔
      a ≤ 2 * H := by
  constructor
  · intro hall
    by_contra hn
    let e : Fin (a + 1) := ⟨H, by omega⟩
    let f : Fin (a + 1) := ⟨H + 1, by omega⟩
    have hc : close a H e f := by
      dsimp [close, e, f]
      constructor <;> omega
    have heq := hall e f ((finite_horizon_kernel a H e f).mpr hc)
    have := congrArg Fin.val heq
    dsimp [e, f] at this
    omega
  · intro ha e f h
    obtain ⟨hlo, hhi⟩ := (finite_horizon_kernel a H e f).mp h
    have he := e.isLt
    have hf := f.isLt
    apply Fin.ext
    omega

#print axioms finite_horizon_kernel
#print axioms profile_classification
#print axioms shortest_separation
#print axioms full_separation_threshold

end D5.S3.Factorization.Automata.BoundedPrimeHorizon
