import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBRawIterateJacobi

/-! Graded mode sums for the three raw HHBB channels. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBModeResidue

open ActualLeechHyperbolic (leechData)
open LatticeHalfFockGradedTrace (actualGrade)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeFixedPairField (nu)
open Orbifold.NativeMixedPairField (mu)
open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff)
open NativeMixedComplexSewing (aJointTerm)
open NativeMixedUpperProductCusp (bJointTerm bProductCoeff b_inner_coeff_off_grid)
open NativeMixedUpperDLip (dProductCoeff)

open private pair_off_energy from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing

local notation "ℒ" => leechData

/-- The doubled mode selectors in the raw HHBB identity, in inner then outer order. -/
abbrev bModes (W q r : ℤ) (j : ℕ) : ℤ × ℤ :=
  (2 * (W + q + r - j + 1) - 1, 2 * ((j : ℤ) - q - r) - 1)

abbrev dModes (W q : ℤ) (j : ℕ) : ℤ × ℤ :=
  (-2 * (q + j) - 1, 2 * (W + q + j + 1) - 1)

abbrev aModes (W r : ℤ) (j : ℕ) : ℤ × ℤ :=
  (-2 * (r + j + 1), 2 * (W + r + j + 1))

private theorem finsum_eq_sum_modePairs {f : ℕ → ℂ} (g : ℕ → ℕ → ℂ) (k : ℤ)
    (hOn : ∀ m j : ℕ, (m : ℤ) + j = k → f j = g m j)
    (hOff : ∀ j : ℕ, k < (j : ℤ) → f j = 0) :
    (∑ᶠ j, f j) = ∑ ij ∈ modePairs k, g ij.1 ij.2 := by
  classical
  have hsupport : Function.support f ⊆ ↑((modePairs k).image Prod.snd) := by
    intro j hj
    have hjk : (j : ℤ) ≤ k := le_of_not_gt (fun h => hj (hOff j h))
    exact Finset.mem_image.mpr
      ⟨((k - j).toNat, j), mem_modePairs.mpr (by omega), rfl⟩
  rw [finsum_eq_sum_of_support_subset f hsupport, Finset.sum_image]
  · exact Finset.sum_congr rfl fun ij h => hOn ij.1 ij.2 (mem_modePairs.mp h)
  · intro i hi j hj h
    have hi' := mem_modePairs.mp hi
    have hj' := mem_modePairs.mp hj
    exact Prod.ext (by omega) h

/-- On the total grade of the four states, each raw selector sum is the
corresponding sum over nonnegative intermediate energies and binomial indices.
The weights are arbitrary because the conversion holds for each summand. -/
theorem hhbb_graded_mode_sums (M K L N : ℕ)
    (u v : TwistedEven) (w bState : TwistedOdd)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L)
    (hM : (M : ℤ) % 2 = 0) (hK : (K : ℤ) % 2 = 0)
    (hL : (L : ℤ) % 2 = 1) (hN : (N : ℤ) % 2 = 1)
    (q r : ℤ) (weightB weightD weightA : ℕ → ℂ) :
    let W := ((N : ℤ) - M - K - L - 6) / 2
    let a : ℕ := (5 + K + L) / 2
    let b : ℕ := (6 + M + K) / 2
    let c : ℕ := (M + L + 7) / 2
    ((∑ᶠ j, weightB j * bJointTerm false false v w u bState 1 1 (bModes W q r j)) =
      ∑ ij ∈ modePairs (W + a + q + r + 1),
        weightB ij.2 * bProductCoeff false false M K L N v w u bState ij.1) ∧
    ((∑ᶠ j, weightD j * bJointTerm false false u w v bState 1 1 (dModes W q j)) =
      ∑ ij ∈ modePairs ((c : ℤ) - q - 1),
        weightD ij.2 * dProductCoeff false false M K L N u w v bState ij.1) ∧
    ((∑ᶠ j, weightA j * aJointTerm u v w bState 1 1 (aModes W r j)) =
      ∑ ij ∈ modePairs ((b : ℤ) - r - 1),
        weightA ij.2 * fixedAIterateCoeff false M K L N (fixedAExponent M K ij.1)
          u v w.val bState.val) := by
  intro W a b c
  have hTotal : 2 * W = (N : ℤ) - M - K - L - 6 := by dsimp only [W]; omega
  have ha : 2 * (a : ℤ) = 5 + (K : ℤ) + L := by dsimp only [a]; omega
  have hb : 2 * (b : ℤ) = 6 + (M : ℤ) + K := by dsimp only [b]; omega
  have hc : 2 * (c : ℤ) = (M : ℤ) + L + 7 := by dsimp only [c]; omega
  have hKL : Odd ((K : ℤ) + L) := Int.odd_iff.mpr (by omega)
  have hML : Odd ((M : ℤ) + L) := Int.odd_iff.mpr (by omega)
  refine ⟨finsum_eq_sum_modePairs
    (f := fun j => weightB j * bJointTerm false false v w u bState 1 1 (bModes W q r j))
    (fun m j => weightB j * bProductCoeff false false M K L N v w u bState m)
    (W + a + q + r + 1) ?_ ?_, finsum_eq_sum_modePairs
    (f := fun j => weightD j * bJointTerm false false u w v bState 1 1 (dModes W q j))
    (fun m j => weightD j * dProductCoeff false false M K L N u w v bState m)
    ((c : ℤ) - q - 1) ?_ ?_, finsum_eq_sum_modePairs
    (f := fun j => weightA j * aJointTerm u v w bState 1 1 (aModes W r j))
    (fun m j => weightA j * fixedAIterateCoeff false M K L N (fixedAExponent M K m)
      u v w.val bState.val) ((b : ℤ) - r - 1) ?_ ?_⟩
  · intro m j hmj
    have hpair : bModes W q r j =
        (2 * (m : ℤ) - (6 + (K : ℤ) + L), (N : ℤ) - M - 2 * (m : ℤ)) := by
      apply Prod.ext <;> dsimp only [bModes] <;> omega
    rw [hpair]
    simp only [bJointTerm, bProductCoeff, one_zpow, mul_one]
  · intro j hj
    have hz := b_inner_coeff_off_grid false K L v w hv hw hKL (bModes W q r j).1
      (fun m hm => by dsimp only [bModes] at hm; omega)
    unfold bJointTerm
    rw [hz]
    simp
  · intro m j hmj
    have hpair : dModes W q j =
        (2 * (m : ℤ) - (6 + (M : ℤ) + L), (N : ℤ) - K - 2 * (m : ℤ)) := by
      apply Prod.ext <;> dsimp only [dModes] <;> omega
    rw [hpair]
    simp only [bJointTerm, dProductCoeff, bProductCoeff, one_zpow, mul_one]
  · intro j hj
    have hz := b_inner_coeff_off_grid false M L u w hu hw hML (dModes W q j).1
      (fun m hm => by dsimp only [dModes] at hm; omega)
    unfold bJointTerm
    rw [hz]
    simp
  · intro m j hmj
    have hpair : aModes W r j = (fixedAExponent M K m,
        (N : ℤ) - L - (fixedAExponent M K m + ((M : ℤ) + K + 6))) := by
      apply Prod.ext <;> dsimp only [aModes, fixedAExponent] <;> omega
    rw [hpair]
    simp only [aJointTerm, fixedAIterateCoeff, one_zpow, mul_one]
  · intro j hj
    have hz := pair_off_energy M K u v hu hv (aModes W r j).1
      (fun m hm => by dsimp only [aModes, fixedAExponent] at hm; omega)
    unfold aJointTerm
    rw [hz]
    simp

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBModeResidue
