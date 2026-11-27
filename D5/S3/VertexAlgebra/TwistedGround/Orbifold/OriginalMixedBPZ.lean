/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed BPZ for the original odd coefficients by finite stress transposition. -/
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalMixedBPZ

open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticePositiveEnergy LatticeInvolution
open HalfFock.LatticeHalfFockParityField ActualChargedAdjoint CorrectedInversion
open MixedIntertwiner OriginalFourMChargeCoset
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open SourceBPZ.SourcePairingLaws (sourcePairing_grade)
open private stress from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation
open private T kernel from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private fixedProjection from D5.S3.VertexAlgebra.TwistedGround.MixedOpposite
open private mixedMode fixedSourceInclusion fixed_source_expansion from
  D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
open private phase_even_shift from
  D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCommonCube
open private rightTerm rightTerm_finite translation_power_pairing from
  D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew
open private sourceGradePairingEquiv from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMContraction
open private normalized_single from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMCoefficients

variable (D : LatticeData) (hu : IsUnit D.G.det)
  (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
local notation "M" => paritySpace D hu (-1)
local notation "V" => FixedCarrier D

/-- The original fixed stress state's mode two on the negative twisted sector. -/
def twistedL1 : Module.End ℂ M :=
  (fixedParitySlice D hu (-1) (stress D))[[2]]

theorem twistedL1_val (u : M) :
    (twistedL1 D hu u).val = T D hu u.val := by
  change (correctedField D hu
      (LatticeActualConformalState.omega D (HalfFockSpectralFiberSource.actualInverse D))).coeff
        (-6) u.val = _
  rw [LatticeHalfFockCorrectedConformal.correctedField_omega D hu _
    (HalfFockSpectralFiberSource.actualInverse_left D hu)]
  simp only [tensorStressField, HVertexOperator.coeff_of_coeff, stressCoeff,
    show (-6 : ℤ) % 2 = 0 by decide, ite_eq_left,
    show (-(-6 : ℤ)-4)/2 = 1 by decide, T, tensorL]

private theorem twistedL1_pow_val (j : ℕ) (u : M) :
    ((twistedL1 D hu ^ j) u).val = (T D hu ^ j) u.val := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply, twistedL1_val, ih]

private theorem lowering_tail (h24 : D.rank = 24) (K : ℕ)
    (v : ActualTensor D hu) (hvK : actualTensorL0 D hu v = (K : ℂ) • v)
    (ell : ℕ) (hell : K - 1 ≤ ell) : (T D hu ^ ell) v = 0 := by
  have energy := lowering_integer_energy D hu h24 (K : ℤ) v
    (by simpa only [Int.cast_natCast] using hvK) ell
  exact integer_energy_zero D hu h24 ((K : ℤ) - ell) _ energy (by omega)

private theorem right_pairing_sum (h24 : D.rank = 24) (K : ℕ) (s : ℤ)
    (a : V) (w v : M) (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val) :
    actualForm D hu v.val (originalRightCoefficient D hu s w a).val =
      ∑ ell ∈ Finset.range (K - 1),
        ((-1 : ℂ) ^ (s + (ell : ℤ) + 1) * (ell.factorial : ℂ)⁻¹) *
          actualForm D hu ((T D hu ^ ell) v.val)
            ((correctedField D hu a.val).coeff (-2 * (s + (ell : ℤ)) - 2) w.val) := by
  classical
  let pair : M →ₗ[ℂ] ℂ :=
    (actualForm D hu v.val).comp (paritySpace D hu (-1)).subtype
  let term (ell : ℕ) : ℂ :=
    ((-1 : ℂ) ^ (s + (ell : ℤ) + 1) * (ell.factorial : ℂ)⁻¹) *
      actualForm D hu ((T D hu ^ ell) v.val)
        ((correctedField D hu a.val).coeff (-2 * (s + (ell : ℤ)) - 2) w.val)
  have mode_val (m : ℤ) :
      (mixedMode D hu m a w).val =
        (correctedField D hu a.val).coeff (-2 * m - 2) w.val := by
    change (correctedField D hu a.val).coeff (2 * (-m - 1)) w.val = _
    rw [show 2 * (-m - 1) = -2 * m - 2 by ring]
  have transpose (ell : ℕ) : pair (rightTerm D hu s w a ell) = term ell := by
    change actualForm D hu v.val (rightTerm D hu s w a ell).val = _
    simp only [rightTerm, Submodule.coe_smul, map_smul, smul_eq_mul,
      translation_power_pairing, mode_val, term]
  have support : Function.support term ⊆ (Finset.range (K - 1) : Set ℕ) := by
    intro ell hell
    apply Finset.mem_range.mpr
    by_contra outside
    have zero := lowering_tail D hu h24 K v.val hvK ell (Nat.le_of_not_gt outside)
    exact hell (by simp [term, zero])
  change pair (∑ᶠ ell : ℕ, rightTerm D hu s w a ell) = ∑ ell ∈ Finset.range (K - 1), term ell
  rw [map_finsum pair (rightTerm_finite D hu s w a)]
  calc
    (∑ᶠ ell : ℕ, pair (rightTerm D hu s w a ell)) = ∑ᶠ ell : ℕ, term ell := by
      simp only [transpose]
    _ = _ := finsum_eq_sum_of_support_subset term support

private theorem originalI_pairing_grade (h24 : D.rank = 24) (H K : ℕ) (n : ℤ)
    (u v : M) (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val)
    (d : ℤ) (a : fixedGrade D d) :
    sourcePairing D (originalI D hu hD n u v).val a.val =
      normalizedCoefficient D hu n u v d a := by
  classical
  let e : ℤ := (H : ℤ) + K - n - 1
  let x := (sourceGradePairingEquiv D hu hD e).symm (normalizedCoefficient D hu n u v e)
  rw [originalI_homogeneous D hu hD h24 H K n u v huH hvK]
  change sourcePairing D x.val a.val = _
  by_cases hd : d = e
  · subst d
    exact sourceGradePairingEquiv_evaluation D hu hD e _ a
  · rw [sourcePairing_grade D e d (Ne.symm hd) x.val a.val x.property.1 a.property.1,
      normalized_single D hu h24 H K n u v huH hvK]
    change 0 = (DirectSum.lof ℂ ℤ (fun d => Module.Dual ℂ (fixedGrade D d))
      e (normalizedCoefficient D hu n u v e)) d a
    simp [DirectSum.lof_eq_of, DirectSum.of_apply, hd, Ne.symm hd]

private theorem originalI_pairing_kernel (h24 : D.rank = 24) (H K : ℕ) (n : ℤ)
    (u v : M) (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val) (a : V) :
    sourcePairing D (originalI D hu hD n u v).val a.val =
      kernel D hu H K n u.val v.val a.val := by
  classical
  let left : V →ₗ[ℂ] ℂ :=
    (sourcePairing D (originalI D hu hD n u v).val).comp (fixedSpace D).subtype
  let right : V →ₗ[ℂ] ℂ :=
    (kernel D hu H K n u.val v.val).comp (fixedSpace D).subtype
  change left a = right a
  rw [← fixed_source_expansion D hu a]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  let b := fixedProjection D hu d a
  change sourcePairing D (originalI D hu hD n u v).val b.val =
    kernel D hu H K n u.val v.val b.val
  rw [originalI_pairing_grade D hu hD h24 H K n u v huH hvK d b,
    normalizedCoefficient_pairing D hu h24 H K n u v huH hvK d b]
  simp only [kernel, K_R, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]

/- proof_shape: content
   admission_basis: escape-witness
   escape_witness: the actual source inverse and transposed right sum are
   compared term by term using the opposite doubled index and even phase shift. -/
/-- The original mixed coefficient and right field have the same finite BPZ sum.
The two ranges are determined by the actual lowering tails of the inputs. -/
theorem original_mixed_bpz_finite (h24 : D.rank = 24) (H K : ℕ) (n : ℤ)
    (u v : M) (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val) (a : V) :
    sourcePairing D (originalI D hu hD n u v).val a.val =
      (-1 : ℂ) ^ (H : ℤ) * ∑ j ∈ Finset.range (H - 1),
        (j.factorial : ℂ)⁻¹ * actualForm D hu v.val
          (originalRightCoefficient D hu (2 * (H : ℤ) - n - (j : ℤ) - 2)
            ((twistedL1 D hu ^ j) u) a).val := by
  classical
  rw [originalI_pairing_kernel D hu hD h24 H K n u v huH hvK a]
  simp only [kernel, K_R, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  let t : ℤ := 2 * (H : ℤ) - n - (j : ℤ) - 2
  rw [right_pairing_sum D hu h24 K t a ((twistedL1 D hu ^ j) u) v hvK,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell _
  let s : ℤ := n + 1 - (ell : ℤ) - 2 * (H : ℤ) + (j : ℤ)
  have mode_index : -2 * (t + (ell : ℤ)) - 2 = 2 * s := by
    dsimp [s, t]
    ring
  have phase : (-1 : ℂ) ^ (H : ℤ) * (-1 : ℂ) ^ (t + (ell : ℤ) + 1) =
      (-1 : ℂ) ^ ((H : ℤ) + s) := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      show (H : ℤ) + (t + (ell : ℤ) + 1) =
        ((H : ℤ) + s) + 2 * (t + (ell : ℤ) + 1) by dsimp [s, t]; ring,
      phase_even_shift]
  change ((-1 : ℂ) ^ ((H : ℤ) + s) / ((ell.factorial : ℂ) * (j.factorial : ℂ))) *
      actualForm D hu ((T D hu ^ ell) v.val)
        ((correctedField D hu a.val).coeff (2 * s) ((T D hu ^ j) u.val)) =
    (-1 : ℂ) ^ (H : ℤ) * ((j.factorial : ℂ)⁻¹ *
      (((-1 : ℂ) ^ (t + (ell : ℤ) + 1) * (ell.factorial : ℂ)⁻¹) *
        actualForm D hu ((T D hu ^ ell) v.val)
          ((correctedField D hu a.val).coeff (-2 * (t + (ell : ℤ)) - 2)
            ((twistedL1 D hu ^ j) u).val)))
  rw [mode_index, twistedL1_pow_val]
  simp only [div_eq_mul_inv, mul_inv_rev]
  rw [← phase]
  ring

/-- Mixed BPZ on the original weight-homogeneous negative twisted inputs and
the full fixed carrier. The outer algebraic sum has support in `range (H - 1)`. -/
theorem original_mixed_bpz (h24 : D.rank = 24) (H K : ℕ) (n : ℤ)
    (u v : M) (huH : actualTensorL0 D hu u.val = (H : ℂ) • u.val)
    (hvK : actualTensorL0 D hu v.val = (K : ℂ) • v.val) (a : V) :
    sourcePairing D (originalI D hu hD n u v).val a.val =
      (-1 : ℂ) ^ (H : ℤ) * ∑ᶠ j : ℕ,
        (j.factorial : ℂ)⁻¹ * actualForm D hu v.val
          (originalRightCoefficient D hu (2 * (H : ℤ) - n - (j : ℤ) - 2)
            ((twistedL1 D hu ^ j) u) a).val := by
  classical
  let term (j : ℕ) : ℂ := (j.factorial : ℂ)⁻¹ * actualForm D hu v.val
    (originalRightCoefficient D hu (2 * (H : ℤ) - n - (j : ℤ) - 2)
      ((twistedL1 D hu ^ j) u) a).val
  have support : Function.support term ⊆ (Finset.range (H - 1) : Set ℕ) := by
    intro j hj
    apply Finset.mem_range.mpr
    by_contra outside
    have zero : (twistedL1 D hu ^ j) u = 0 := by
      apply Subtype.ext
      rw [twistedL1_pow_val]
      exact lowering_tail D hu h24 H u.val huH j (Nat.le_of_not_gt outside)
    exact hj (by simp [term, zero])
  change _ = (-1 : ℂ) ^ (H : ℤ) * ∑ᶠ j : ℕ, term j
  rw [finsum_eq_sum_of_support_subset term support]
  exact original_mixed_bpz_finite D hu hD h24 H K n u v huH hvK a

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalMixedBPZ
