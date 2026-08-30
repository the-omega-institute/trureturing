/- GID: D5/S3/PrimeForms/Splitting/GoldenLocalBranchClassification
   generality: I
   mirror-B: D5/B/S3/PrimeForms/Splitting/GoldenLocalBranchClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden local branch operator ramifies only at five. -/

import D5.S3.PrimeForms.GoldenPrimeClassification
import D5.S3.QuantumBounds.ReferenceFrame.ChannelFidelityBridge
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/- Library-search audit trail (2026-08-30):
   * The frozen `GoldenPrimeClassification` family supplies the canonical golden-integer
     carrier and the exact ramified-square identity at five.
   * `ChannelFidelityBridge.bitFlip` supplies the existing complex two-by-two swap matrix.
   * Current-tree searches for `legendreSym 5`, golden-character names, branch operators,
     even/odd projectors, and the half-sum/half-difference body shapes found no existing
     all-prime complex branch operator. `LocalReciprocityMatrix` is restricted to odd primes.
   * Pinned Mathlib exact hits `legendreSym.eq_zero_iff`, `Matrix.det_fin_two`, and
     `Matrix.isUnit_iff_isUnit_det` are applied below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.Splitting.GoldenLocalBranchClassification

open D5.S0.Carrier
open D5.S3.QuantumBounds.ReferenceFrame.ChannelFidelityBridge

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The projector onto the branch fixed by Galois conjugation. -/
noncomputable def evenBranchProjection : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • (1 + bitFlip)

/-- The projector onto the branch negated by Galois conjugation. -/
noncomputable def oddBranchProjection : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • (1 - bitFlip)

/-- The local golden observer acts trivially on the even branch and by the
quadratic character modulo five on the odd branch. -/
noncomputable def goldenLocalBranchOperator (p : Nat) : Matrix (Fin 2) (Fin 2) ℂ :=
  evenBranchProjection + (legendreSym 5 p : ℂ) • oddBranchProjection

/-- The local operator has quadratic-character determinant. Its three character values
respectively preserve both branches, exchange them, and collapse the odd branch. Among
primes it is noninvertible exactly at five, which is the square of `-1 + 2 * phi` in the
canonical golden-integer carrier. -/
theorem golden_local_branch_classification (p : Nat) :
    (p.Prime → Matrix.det (goldenLocalBranchOperator p) = (legendreSym 5 p : ℂ)) ∧
      (p.Prime → legendreSym 5 p = 1 →
        Matrix.det (goldenLocalBranchOperator p) = 1 ∧ goldenLocalBranchOperator p = 1) ∧
      (p.Prime → legendreSym 5 p = -1 →
        Matrix.det (goldenLocalBranchOperator p) = -1 ∧
          goldenLocalBranchOperator p = bitFlip) ∧
      (p.Prime → legendreSym 5 p = 0 →
        Matrix.det (goldenLocalBranchOperator p) = 0 ∧
          goldenLocalBranchOperator p = evenBranchProjection ∧
          Matrix.mulVec (goldenLocalBranchOperator p) ![(1 : ℂ), (-1 : ℂ)] = 0 ∧
          Matrix.mulVec (goldenLocalBranchOperator p) ![(1 : ℂ), 1] = ![(1 : ℂ), 1]) ∧
      (p.Prime → (¬ IsUnit (goldenLocalBranchOperator p) ↔ p = 5)) ∧
      (5 : GoldenInt) = (-1 + 2 * phi) ^ 2 := by
  have determinantIdentity :
      Matrix.det (goldenLocalBranchOperator p) = (legendreSym 5 p : ℂ) := by
    simp [goldenLocalBranchOperator, evenBranchProjection, oddBranchProjection,
      bitFlip, Matrix.det_fin_two]
    ring
  have splitAction :
      legendreSym 5 p = 1 →
        Matrix.det (goldenLocalBranchOperator p) = 1 ∧
          goldenLocalBranchOperator p = 1 := by
    intro hsplit
    constructor
    · rw [determinantIdentity, hsplit]
      norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [goldenLocalBranchOperator, evenBranchProjection, oddBranchProjection,
          bitFlip, hsplit] <;> norm_num
  have inertAction :
      legendreSym 5 p = -1 →
        Matrix.det (goldenLocalBranchOperator p) = -1 ∧
          goldenLocalBranchOperator p = bitFlip := by
    intro hinert
    constructor
    · rw [determinantIdentity, hinert]
      norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [goldenLocalBranchOperator, evenBranchProjection, oddBranchProjection,
          bitFlip, hinert] <;> norm_num
  have ramifiedAction :
      legendreSym 5 p = 0 →
        Matrix.det (goldenLocalBranchOperator p) = 0 ∧
          goldenLocalBranchOperator p = evenBranchProjection ∧
          Matrix.mulVec (goldenLocalBranchOperator p) ![(1 : ℂ), (-1 : ℂ)] = 0 ∧
          Matrix.mulVec (goldenLocalBranchOperator p) ![(1 : ℂ), 1] = ![(1 : ℂ), 1] := by
    intro hramified
    have hop : goldenLocalBranchOperator p = evenBranchProjection := by
      simp [goldenLocalBranchOperator, hramified]
    refine ⟨?_, hop, ?_, ?_⟩
    · rw [determinantIdentity, hramified]
      norm_num
    · rw [hop]
      ext i
      fin_cases i <;>
        norm_num [evenBranchProjection, bitFlip, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two]
    · rw [hop]
      ext i
      fin_cases i <;>
        norm_num [evenBranchProjection, bitFlip, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two]
  have zeroCharacterIff (hp : p.Prime) : legendreSym 5 p = 0 ↔ p = 5 := by
    rw [legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · intro hdiv
      have hnat : 5 ∣ p := by exact_mod_cast hdiv
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp hnat).symm
    · intro h
      subst p
      norm_num
  have castZeroCharacterIff (hp : p.Prime) : (legendreSym 5 p : ℂ) = 0 ↔ p = 5 := by
    constructor
    · intro hzero
      apply (zeroCharacterIff hp).mp
      exact_mod_cast hzero
    · intro hfive
      exact_mod_cast (zeroCharacterIff hp).mpr hfive
  have uniqueNoninvertible :
      p.Prime → (¬ IsUnit (goldenLocalBranchOperator p) ↔ p = 5) := by
    intro hp
    rw [Matrix.isUnit_iff_isUnit_det, determinantIdentity, isUnit_iff_ne_zero]
    simp only [not_not]
    exact castZeroCharacterIff hp
  have ramifiedSquare : (5 : GoldenInt) = (-1 + 2 * phi) ^ 2 := by
    rw [D5.S3.PrimeForms.GoldenPrimeClassification.golden_five_eq_ramified_square]
    congr 1
  exact ⟨fun _ => determinantIdentity, fun _ => splitAction, fun _ => inertAction,
    fun _ => ramifiedAction,
    uniqueNoninvertible, ramifiedSquare⟩

#print axioms golden_local_branch_classification

end D5.S3.PrimeForms.Splitting.GoldenLocalBranchClassification
