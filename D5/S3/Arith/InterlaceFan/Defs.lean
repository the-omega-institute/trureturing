/- GID: D5/S3/Arith/InterlaceFan/Defs
   generality: G
   mirror-B: D5/B/S3/Arith/InterlaceFan/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic, mathlib/module/Mathlib.NumberTheory.Divisors, mathlib/module/Mathlib.Data.Finset.Max]
   utility: none
   digest: Interlace functionals, their closed fan faces, rational points and the rational-face classification. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Max

open Finset

namespace D5.S3.Arith.InterlaceFan.Defs

/-- The interlace functional I_j of eq. (12). -/
noncomputable def I (n j : ℕ) (x : Fin (n / 2) → ℝ) : ℝ :=
  ∑ k : Fin (n / 2), -Real.cos (2 * Real.pi * j * ((k : ℕ) + 1) / n) * x k

/-- Cert indices j = 0, …, ⌊n/2⌋. -/
def certIdx (n : ℕ) : Finset ℕ := range (n / 2 + 1)

/-- Interlace number (Interlace Formula): max_j I_j. -/
noncomputable def interlaceNumber (n : ℕ) (x : Fin (n / 2) → ℝ) : ℝ :=
  (certIdx n).sup' (by simp [certIdx]) (fun j => I n j x)

/-- Closed face of the FOIC whose cert set contains S (Proposition 5.5, eq. (15)). -/
def face (n : ℕ) (S : Finset ℕ) : Set (Fin (n / 2) → ℝ) :=
  {x | ∀ s ∈ S, ∀ j ∈ certIdx n, I n j x ≤ I n s x}

def IsRationalPt {m : ℕ} (x : Fin m → ℝ) : Prop := ∀ k, ∃ q : ℚ, x k = q

def HasRatPt (n : ℕ) (S : Finset ℕ) : Prop :=
  ∃ x ∈ face n S, x ≠ 0 ∧ IsRationalPt x

/-- Cert indices whose root of unity e^{2πij/n} has multiplicative order d. -/
def orderClass (n d : ℕ) : Finset ℕ :=
  (certIdx n).filter (fun j => n / Nat.gcd n j = d)

def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ S ⊆ certIdx n, S.Nonempty →
      (HasRatPt n S ↔ ∃ d ∈ n.divisors, Disjoint S (orderClass n d))) ∧
    (∀ S ⊆ certIdx n, S.Nonempty →
      ((HasRatPt n S ∧ ∀ T ⊆ certIdx n, S ⊂ T → ¬ HasRatPt n T) ↔
        ∃ d ∈ n.divisors, S = certIdx n \ orderClass n d)) ∧
    (∀ d ∈ n.divisors, ∀ x ∈ face n (certIdx n \ orderClass n d),
      x ≠ 0 → IsRationalPt x →
      (∀ j ∈ orderClass n d, I n j x < interlaceNumber n x) ∧
        ∃ q : ℚ, interlaceNumber n x = q)

end D5.S3.Arith.InterlaceFan.Defs
