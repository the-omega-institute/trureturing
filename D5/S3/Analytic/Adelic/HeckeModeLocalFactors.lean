/- GID: D5/S3/Analytic/Adelic/HeckeModeLocalFactors
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/HeckeModeLocalFactors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Split primes alone carry the mode dependence of the golden Hecke local factors. -/

import D5.S3.PrimeForms.Splitting.GoldenLocalBranchClassification
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/- Library-search audit trail (2026-08-30):
   * Current-tree exact-name and body-shape searches found no frozen whole-statement
     owner for the split, inert, and ramified regulator-mode local factors.
   * Searches for a list product of norm-phase Euler factors and for a golden-character
     selection among two norm-p places, one norm-p-squared place, and one norm-p place
     found no existing D5 primitive with either body introduced below.
   * `GoldenLocalBranchClassification.goldenLocalBranchOperator` is the canonical
     three-branch classifier and is used in the public support clause.
   * Pinned Mathlib hits `Complex.two_cos`, `Complex.exp_add`,
     `Complex.cpow_nat_mul`, `legendreSym.eq_zero_iff`, and
     `legendreSym.eq_one_or_neg_one` are applied directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Adelic.HeckeModeLocalFactors

open Complex
open D5.S3.PrimeForms.Splitting.GoldenLocalBranchClassification

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The Euler factor constructed from the norm and regulator phase of every
prime ideal above one rational prime. -/
noncomputable def localHeckeEulerFactor
    (places : List (ℕ × ℝ)) (mode : ℤ) (s : ℂ) : ℂ :=
  (places.map fun place =>
    (1 - Complex.exp ((((mode : ℝ) * place.2 : ℝ) : ℂ) * Complex.I) *
      (place.1 : ℂ) ^ (-s))⁻¹).prod

/-- The prime-ideal norm-phase data selected by the canonical quadratic
character: a conjugate pair when split, one norm-square place when inert,
and one zero-phase place when ramified. -/
def goldenLocalPrimePlaces (p : ℕ) (theta : ℝ) : List (ℕ × ℝ) :=
  if legendreSym 5 p = 1 then
    [(p, theta), (p, -theta)]
  else if legendreSym 5 p = -1 then
    [(p ^ 2, 0)]
  else
    [(p, 0)]

private theorem split_place_factor_formula
    (mode : ℤ) (s : ℂ) (p : ℕ) (theta : ℝ) :
    localHeckeEulerFactor [(p, theta), (p, -theta)] mode s =
      (1 - 2 * (Real.cos ((mode : ℝ) * theta) : ℂ) * (p : ℂ) ^ (-s) +
        (p : ℂ) ^ (-(2 * s)))⁻¹ := by
  simp only [localHeckeEulerFactor, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_inv]
  congr 1
  let x : ℝ := (mode : ℝ) * theta
  let q : ℂ := (p : ℂ) ^ (-s)
  have hpositivePhase :
      Complex.exp (((((mode : ℝ) * theta : ℝ) : ℂ)) * Complex.I) =
        Complex.exp ((x : ℂ) * Complex.I) := by
    rfl
  have hnegativePhase :
      Complex.exp (((((mode : ℝ) * -theta : ℝ) : ℂ)) * Complex.I) =
        Complex.exp (-(x : ℂ) * Complex.I) := by
    congr 1
    simp only [x]
    push_cast
    ring
  have hphaseSum :
      Complex.exp ((x : ℂ) * Complex.I) +
          Complex.exp (-(x : ℂ) * Complex.I) =
        2 * (Real.cos x : ℂ) := by
    rw [Complex.ofReal_cos, Complex.two_cos]
  have hphaseProduct :
      Complex.exp ((x : ℂ) * Complex.I) *
          Complex.exp (-(x : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    have hzero : (x : ℂ) * Complex.I + -(x : ℂ) * Complex.I = 0 := by ring
    rw [hzero, Complex.exp_zero]
  have hpower : q * q = (p : ℂ) ^ (-(2 * s)) := by
    calc
      q * q = q ^ 2 := by ring
      _ = (p : ℂ) ^ ((2 : ℕ) * (-s)) :=
        (Complex.cpow_nat_mul (p : ℂ) 2 (-s)).symm
      _ = (p : ℂ) ^ (-(2 * s)) := by
        congr 1
        push_cast
        ring
  rw [hpositivePhase, hnegativePhase]
  change (1 - Complex.exp ((x : ℂ) * Complex.I) * q) *
      (1 - Complex.exp (-(x : ℂ) * Complex.I) * q) = _
  calc
    _ = 1 -
          (Complex.exp ((x : ℂ) * Complex.I) +
            Complex.exp (-(x : ℂ) * Complex.I)) * q +
          (Complex.exp ((x : ℂ) * Complex.I) *
            Complex.exp (-(x : ℂ) * Complex.I)) * (q * q) := by ring
    _ = 1 - 2 * (Real.cos ((mode : ℝ) * theta) : ℂ) * q +
          (p : ℂ) ^ (-(2 * s)) := by
      rw [hphaseSum, hphaseProduct, hpower]
      simp only [one_mul, x]

private theorem inert_place_factor_formula
    (mode : ℤ) (s : ℂ) (p : ℕ) :
    localHeckeEulerFactor [(p ^ 2, 0)] mode s =
      (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ := by
  simp only [localHeckeEulerFactor, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, Complex.ofReal_zero, mul_zero, mul_one]
  rw [zero_mul, Complex.exp_zero, one_mul]
  congr 2
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul p 2 (-s)]
  congr 1
  push_cast
  ring

private theorem zero_phase_factor_mode_independent
    (mode₁ mode₂ : ℤ) (s : ℂ) (norm : ℕ) :
    localHeckeEulerFactor [(norm, 0)] mode₁ s =
      localHeckeEulerFactor [(norm, 0)] mode₂ s := by
  simp [localHeckeEulerFactor]

/-- The regulator-mode local factors have the split cosine denominator, the
inert norm-square denominator independent of mode, and the ramified norm-five
denominator. Therefore the canonical local branch operator can detect mode
dependence only on its split branch. -/
theorem hecke_mode_local_factors
    (mode₁ mode₂ : ℤ) (s : ℂ) (p : ℕ) (theta : ℝ) (hp : p.Prime) :
    (legendreSym 5 p = 1 →
      localHeckeEulerFactor (goldenLocalPrimePlaces p theta) mode₁ s =
        (1 - 2 * (Real.cos ((mode₁ : ℝ) * theta) : ℂ) * (p : ℂ) ^ (-s) +
          (p : ℂ) ^ (-(2 * s)))⁻¹) ∧
      (legendreSym 5 p = -1 →
        localHeckeEulerFactor (goldenLocalPrimePlaces p theta) mode₁ s =
          (1 - (p : ℂ) ^ (-(2 * s)))⁻¹) ∧
      (legendreSym 5 p = -1 →
        localHeckeEulerFactor (goldenLocalPrimePlaces p theta) mode₁ s =
          localHeckeEulerFactor (goldenLocalPrimePlaces p theta) mode₂ s) ∧
      (localHeckeEulerFactor (goldenLocalPrimePlaces 5 theta) mode₁ s =
        (1 - (5 : ℂ) ^ (-s))⁻¹) ∧
      (Matrix.det (goldenLocalBranchOperator p) ≠ 1 →
        localHeckeEulerFactor (goldenLocalPrimePlaces p theta) mode₁ s =
          localHeckeEulerFactor (goldenLocalPrimePlaces p theta) mode₂ s) := by
  have splitClause : legendreSym 5 p = 1 →
      localHeckeEulerFactor (goldenLocalPrimePlaces p theta) mode₁ s =
        (1 - 2 * (Real.cos ((mode₁ : ℝ) * theta) : ℂ) * (p : ℂ) ^ (-s) +
          (p : ℂ) ^ (-(2 * s)))⁻¹ := by
    intro hsplit
    rw [goldenLocalPrimePlaces, if_pos hsplit]
    exact split_place_factor_formula mode₁ s p theta
  have inertClause : legendreSym 5 p = -1 →
      localHeckeEulerFactor (goldenLocalPrimePlaces p theta) mode₁ s =
        (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ := by
    intro hinert
    have hnotSplit : legendreSym 5 p ≠ 1 := by
      intro hsplit
      rw [hsplit] at hinert
      norm_num at hinert
    rw [goldenLocalPrimePlaces, if_neg hnotSplit, if_pos hinert]
    exact inert_place_factor_formula mode₁ s p
  have inertIndependent : legendreSym 5 p = -1 →
      localHeckeEulerFactor (goldenLocalPrimePlaces p theta) mode₁ s =
        localHeckeEulerFactor (goldenLocalPrimePlaces p theta) mode₂ s := by
    intro hinert
    have hnotSplit : legendreSym 5 p ≠ 1 := by
      intro hsplit
      rw [hsplit] at hinert
      norm_num at hinert
    rw [goldenLocalPrimePlaces, if_neg hnotSplit, if_pos hinert]
    exact zero_phase_factor_mode_independent mode₁ mode₂ s (p ^ 2)
  have ramifiedClause :
      localHeckeEulerFactor (goldenLocalPrimePlaces 5 theta) mode₁ s =
        (1 - (5 : ℂ) ^ (-s))⁻¹ := by
    have hzero : legendreSym 5 5 = 0 := by norm_num
    simp [goldenLocalPrimePlaces, hzero, localHeckeEulerFactor]
  have nonsplitIndependent : Matrix.det (goldenLocalBranchOperator p) ≠ 1 →
      localHeckeEulerFactor (goldenLocalPrimePlaces p theta) mode₁ s =
        localHeckeEulerFactor (goldenLocalPrimePlaces p theta) mode₂ s := by
    intro hdet
    have hnotSplit : legendreSym 5 p ≠ 1 := by
      intro hsplit
      apply hdet
      exact (golden_local_branch_classification p).2.1 hp hsplit |>.1
    by_cases hzero : legendreSym 5 p = 0
    · rw [goldenLocalPrimePlaces, if_neg hnotSplit]
      have hnotInert : legendreSym 5 p ≠ -1 := by
        intro hinert
        rw [hinert] at hzero
        norm_num at hzero
      rw [if_neg hnotInert]
      exact zero_phase_factor_mode_independent mode₁ mode₂ s p
    · have hnonzeroMod : (p : ZMod 5) ≠ 0 := fun hmod =>
        hzero ((legendreSym.eq_zero_iff (p := 5) (a := (p : ℤ))).2 hmod)
      have hinert : legendreSym 5 p = -1 :=
        (legendreSym.eq_one_or_neg_one (p := 5) (a := (p : ℤ)) hnonzeroMod).resolve_left
          hnotSplit
      rw [goldenLocalPrimePlaces, if_neg hnotSplit, if_pos hinert]
      exact zero_phase_factor_mode_independent mode₁ mode₂ s (p ^ 2)
  exact ⟨splitClause, inertClause, inertIndependent, ramifiedClause,
    nonsplitIndependent⟩

#print axioms hecke_mode_local_factors

end D5.S3.Analytic.Adelic.HeckeModeLocalFactors
