/- GID: D5/S3/Observer/Hankel/ExecutableHoKalman
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/ExecutableHoKalman
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Total rational pivot search computes a finite realization or rejects insufficient margin. -/

import D5.S3.Observer.Hankel.FiniteHoKalmanBlocks
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.ExecutableHoKalman

open D5.S3.Observer.Hankel.FiniteHoKalmanBlocks

/-- List-valued finite Cartesian power. It avoids noncomputable `Finset.toList`. -/
def tuples {α : Type*} (xs : List α) : (n : Nat) → List (Fin n → α)
  | 0 => [fun i => Fin.elim0 i]
  | n + 1 => xs.flatMap fun x => (tuples xs n).map (Fin.cons x)

/-- Every tuple over the supplied finite alphabet is enumerated. -/
theorem mem_tuples {α : Type*} (xs : List α) (n : Nat) (f : Fin n → α)
    (hf : ∀ i, f i ∈ xs) : f ∈ tuples xs n := by
  induction n generalizing f with
  | zero =>
    have he : f = (fun i : Fin 0 => Fin.elim0 i) := by
      funext i
      exact Fin.elim0 i
    simp [tuples, he]
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨f 0, hf 0, ?_⟩
    apply List.mem_map.mpr
    refine ⟨Fin.tail f, ih (Fin.tail f) (fun i => hf i.succ), ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Exhaustive MIMO pivot list, in a fixed list order. Repetitions are rejected by the determinant. -/
def allPivots (h p m r : Nat) : List (Pivot h p m r) :=
  (tuples ((List.finRange h).product (List.finRange p)) r).product
    (tuples ((List.finRange h).product (List.finRange m)) r)

theorem mem_allPivots {h p m r : Nat} (q : Pivot h p m r) :
    q ∈ allPivots h p m r := by
  apply List.mem_product.mpr
  constructor
  · apply mem_tuples
    intro i
    simp
  · apply mem_tuples
    intro i
    simp

/-- A computable rational upper bound for every row-sum operator norm. -/
def absSum {a b : Nat} (M : Matrix (Fin a) (Fin b) ℚ) : ℚ :=
  ∑ i, ∑ j, |M i j|

/-- Accept only a nonsingular minor and a nonnegative entrywise-noise budget with
strict conservative inverse margin. Neither inverse nor success proof is an input. -/
def acceptable {h p m r : Nat} (s : Samples ℚ h p m) (ε : ℚ)
    (q : Pivot h p m r) : Bool :=
  decide ((baseBlock s q).det ≠ 0 ∧ 0 ≤ ε ∧
    absSum (adjInverse (baseBlock s q)) * (r : ℚ) * ε < 1)

/-- First acceptable pivot. Both rejection and success terminate on a finite list. -/
def scan {h p m r : Nat} (s : Samples ℚ h p m) (ε : ℚ) :
    List (Pivot h p m r) → Option (Pivot h p m r)
  | [] => none
  | q :: qs => if acceptable s ε q then some q else scan s ε qs

theorem scan_sound {h p m r : Nat} (s : Samples ℚ h p m) (ε : ℚ)
    (qs : List (Pivot h p m r)) (q : Pivot h p m r)
    (hq : scan s ε qs = some q) : acceptable s ε q = true := by
  induction qs generalizing q with
  | nil => simp [scan] at hq
  | cons a qs ih =>
    by_cases ha : acceptable s ε a = true
    · have he : a = q := by simpa [scan, ha] using hq
      simpa [← he] using ha
    · exact ih q (by simpa [scan, ha] using hq)

theorem scan_none_iff {h p m r : Nat} (s : Samples ℚ h p m) (ε : ℚ)
    (qs : List (Pivot h p m r)) :
    scan s ε qs = none ↔ ∀ q ∈ qs, acceptable s ε q ≠ true := by
  induction qs with
  | nil => simp [scan]
  | cons a qs ih =>
    by_cases ha : acceptable s ε a = true <;> simp [scan, ha, ih]

/-- Exhaustive data-only selection, with target order supplied as a natural number. -/
def choosePivot {h p m : Nat} (r : Nat) (s : Samples ℚ h p m) (ε : ℚ) :
    Option (Pivot h p m r) := scan s ε (allPivots h p m r)

/-- Rejection means that every candidate fails the explicit finite acceptance test. -/
theorem choosePivot_none_iff {h p m r : Nat} (s : Samples ℚ h p m) (ε : ℚ) :
    choosePivot r s ε = none ↔ ∀ q : Pivot h p m r, acceptable s ε q ≠ true := by
  rw [choosePivot, scan_none_iff]
  exact ⟨fun hh q => hh q (mem_allPivots q), fun hh q _ => hh q⟩

/-- A good pivot is sufficient for algorithmic success; success is not an oracle hypothesis. -/
theorem choosePivot_success {h p m r : Nat} (s : Samples ℚ h p m) (ε : ℚ)
    (hex : ∃ q : Pivot h p m r, acceptable s ε q = true) :
    ∃ q, choosePivot r s ε = some q := by
  cases he : choosePivot r s ε with
  | none =>
    obtain ⟨q, hq⟩ := hex
    exact False.elim ((choosePivot_none_iff s ε).mp he q hq)
  | some q => exact ⟨q, by simp [he]⟩

/-- Successful selection exposes the determinant and numerical-margin certificates. -/
theorem choosePivot_certificate {h p m r : Nat} (s : Samples ℚ h p m) (ε : ℚ)
    (q : Pivot h p m r) (hq : choosePivot r s ε = some q) :
    (baseBlock s q).det ≠ 0 ∧ 0 ≤ ε ∧
      absSum (adjInverse (baseBlock s q)) * (r : ℚ) * ε < 1 := by
  have hh := scan_sound s ε (allPivots h p m r) q hq
  simpa only [acceptable, decide_eq_true_eq] using hh

/-- Plain executable result, with no correctness or error conclusion assumed as a field. -/
structure Result (h p m r : Nat) where
  pivot : Pivot h p m r
  A : Matrix (Fin r) (Fin r) ℚ
  B : Matrix (Fin r) (Fin m) ℚ
  C : Matrix (Fin p) (Fin r) ℚ

/-- Compute the selected model, or return `none` when no certified pivot exists. -/
def run {h p m : Nat} (r : Nat) (s : Samples ℚ h p m) (ε : ℚ) :
    Option (Result h p m r) :=
  (choosePivot r s ε).map fun q => ⟨q, fittedA s q, fittedB s q, fittedC s q⟩

/-- The result fields really are computed from the selected finite samples. -/
theorem run_fields {h p m r : Nat} (s : Samples ℚ h p m) (ε : ℚ)
    (out : Result h p m r) (ho : run r s ε = some out) :
    choosePivot r s ε = some out.pivot ∧
    out.A = fittedA s out.pivot ∧ out.B = fittedB s out.pivot ∧
    out.C = fittedC s out.pivot := by
  cases hq : choosePivot r s ε with
  | none => simp [run, hq] at ho
  | some q =>
    have he : (⟨q, fittedA s q, fittedB s q, fittedC s q⟩ : Result h p m r) = out := by
      simpa [run, hq] using ho
    subst out
    exact ⟨by simp [hq], rfl, rfl, rfl⟩

/-- The actual executable output has the exact behavior of every order-r reference
realization matching noiseless input data. -/
theorem run_exact_recovery {h p m r : Nat}
    (s : Samples ℚ h p m) (ε : ℚ) (out : Result h p m r)
    (ho : run r s ε = some out)
    (A : Matrix (Fin r) (Fin r) ℚ) (B : Matrix (Fin r) (Fin m) ℚ)
    (C : Matrix (Fin p) (Fin r) ℚ)
    (hs : ∀ k : Fin (2 * h), s k = C * A ^ k.val * B) (n : Nat) :
    out.C * out.A ^ n * out.B = C * A ^ n * B := by
  obtain ⟨hq, hA, hB, hC⟩ := run_fields s ε out ho
  rw [hA, hB, hC]
  exact finite_samples_exact_recovery s out.pivot A B C hs
    (choosePivot_certificate s ε out.pivot hq).1 n

private def scalarExample : Samples ℚ 1 1 1 :=
  fun k _ _ => if k.val = 0 then 1001 / 1000 else 501 / 1000

-- Kernel-reduction examples. They are source checks, not a recorded compiler run.
example : (run 1 scalarExample (1 / 1000)).map
    (fun out => (out.A 0 0, out.B 0 0, out.C 0 0)) =
      some ((501 / 1001 : ℚ), (1 : ℚ), (1001 / 1000 : ℚ)) := by decide

example : (run 1 scalarExample (-1)).isNone = true := by decide

example : (run 1 (fun _ _ _ => (0 : ℚ) : Samples ℚ 1 1 1) 0).isNone = true := by decide

#print axioms choosePivot_success
#print axioms run_exact_recovery

end D5.S3.Observer.Hankel.ExecutableHoKalman
