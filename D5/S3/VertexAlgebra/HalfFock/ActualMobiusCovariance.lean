/- GID: D5/S3/VertexAlgebra/HalfFock/ActualMobiusCovariance
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/HalfFock/ActualMobiusCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Work in progress on the original all-source physical L1 Ward law. -/

import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.LatticeHalfFockChargedLZero
import D5.S3.VertexAlgebra.LatticeHalfFockCurrentWard
import D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier

/- Classical twisted lattice construction; original conventions and notices
are inherited from the imported owners. No replacement field is introduced.
The intended endpoint is the all-source original corrected-field L1 law,
not the charged calculation below. The endpoint remains unfinished. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open scoped BigOperators TensorProduct
noncomputable section

private theorem charged_flat_zero_jet (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (i : Fin D.rank) (j e : ℤ) :
    flatCoefficient D hu (chargedField D hu a) [(i, 0)] (j, ()) (e - 4) =
      if j < 0 then tensorCurrent D (ActualGround D hu) i j *
        chargedCoefficient D hu a (e + 2*j - 1)
      else chargedCoefficient D hu a (e + 2*j - 1) *
        tensorCurrent D (ActualGround D hu) i j := by
  have coeff (d : ℤ) : (chargedField D hu a).coeff d =
      chargedCoefficient D hu a d := by
    rw [chargedField, HVertexOperator.coeff_of_coeff]
  simp only [flatCoefficient, jetCurrent, jetScalar, Finset.range_zero,
    Finset.prod_empty, Nat.factorial_zero, Nat.cast_one, div_one,
    one_smul, Nat.cast_zero, mul_zero, add_zero, coeff]
  rw [show e - 4 + 2*j + 3 = e + 2*j - 1 by omega]

/-- Local quadratic expansion before pointwise finite summation. The j=0
normal-order boundary contributes both original charge pairings. -/
private theorem charged_pair_l1 (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (i l : Fin D.rank) (j e : ℤ) :
    tensorPair D (ActualGround D hu) i l j (-j) * chargedCoefficient D hu a e -
      chargedCoefficient D hu a e * tensorPair D (ActualGround D hu) i l j (-j) =
      (bilinear D (unitCharge D l) a : ℂ) •
        flatCoefficient D hu (chargedField D hu a) [(i, 0)] (j, ()) (e - 4) +
      (bilinear D (unitCharge D i) a : ℂ) •
        flatCoefficient D hu (chargedField D hu a) [(l, 0)] (-j, ()) (e - 4) +
      (if j = 0 then (bilinear D (unitCharge D i) a : ℂ) *
        (bilinear D (unitCharge D l) a : ℂ) else 0) •
        chargedCoefficient D hu a (e - 2) := by
  rw [tensorPair_eq, charged_flat_zero_jet, charged_flat_zero_jet]
  have ward (c : Fin D.rank) (k d : ℤ) := charged_tensor_current_ward D hu c a k d
  by_cases hj : j < 0
  · simp only [if_pos hj, if_neg (by omega : ¬ -j < 0),
      if_neg (by omega : j ≠ 0), zero_smul, add_zero]
    calc
      _ = tensorCurrent D (ActualGround D hu) i j *
          (tensorCurrent D (ActualGround D hu) l (-j) * chargedCoefficient D hu a e -
            chargedCoefficient D hu a e * tensorCurrent D (ActualGround D hu) l (-j)) +
          (tensorCurrent D (ActualGround D hu) i j * chargedCoefficient D hu a e -
            chargedCoefficient D hu a e * tensorCurrent D (ActualGround D hu) i j) *
              tensorCurrent D (ActualGround D hu) l (-j) := by noncomm_ring
      _ = _ := by
        rw [ward, ward]
        simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        rw [show e - (2 * -j + 1) = e + 2*j - 1 by omega,
          show e - (2*j + 1) = e + 2*(-j) - 1 by omega]
  · by_cases hz : j = 0
    · subst j
      simp only [lt_self_iff_false, if_false, neg_zero, if_true, mul_zero, add_zero]
      have cross := ward l 0 (e - 1)
      simp only [mul_zero, zero_add] at cross
      calc
        _ = tensorCurrent D (ActualGround D hu) l 0 *
            (tensorCurrent D (ActualGround D hu) i 0 * chargedCoefficient D hu a e -
              chargedCoefficient D hu a e * tensorCurrent D (ActualGround D hu) i 0) +
            (tensorCurrent D (ActualGround D hu) l 0 * chargedCoefficient D hu a e -
              chargedCoefficient D hu a e * tensorCurrent D (ActualGround D hu) l 0) *
                tensorCurrent D (ActualGround D hu) i 0 := by noncomm_ring
        _ = _ := by
          rw [ward, ward]
          simp only [mul_zero, zero_add, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
          rw [show e - 1 - 1 = e - 2 by omega] at cross
          rw [sub_eq_iff_eq_add.mp cross, smul_add, smul_smul]
          abel
    · simp only [if_neg hj, if_pos (by omega : -j < 0), if_neg hz, zero_smul, add_zero]
      calc
        _ = tensorCurrent D (ActualGround D hu) l (-j) *
            (tensorCurrent D (ActualGround D hu) i j * chargedCoefficient D hu a e -
              chargedCoefficient D hu a e * tensorCurrent D (ActualGround D hu) i j) +
            (tensorCurrent D (ActualGround D hu) l (-j) * chargedCoefficient D hu a e -
              chargedCoefficient D hu a e * tensorCurrent D (ActualGround D hu) l (-j)) *
                tensorCurrent D (ActualGround D hu) i j := by noncomm_ring
        _ = _ := by
          rw [ward, ward]
          simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
          rw [show e - (2 * -j + 1) = e + 2*j - 1 by omega,
            show e - (2*j + 1) = e + 2*(-j) - 1 by omega]
          abel


/-- The quadratic-to-singleton transport is pointwise in the original actual
module. Finite support is used only after application at x and C_e x. -/
private theorem charged_normal_sum_l1 (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (i l : Fin D.rank) (e : ℤ) (x : ActualTensor D hu) :
    tensorNormalSum D (ActualGround D hu) i l 1 (chargedCoefficient D hu a e x) -
      chargedCoefficient D hu a e (tensorNormalSum D (ActualGround D hu) i l 1 x) =
      (bilinear D (unitCharge D l) a : ℂ) •
        (wordField D hu (chargedField D hu a) [(i, 0)]).coeff (e - 4) x +
      (bilinear D (unitCharge D i) a : ℂ) •
        (wordField D hu (chargedField D hu a) [(l, 0)]).coeff (e - 4) x +
      ((bilinear D (unitCharge D i) a : ℂ) *
        (bilinear D (unitCharge D l) a : ℂ)) • chargedCoefficient D hu a (e - 2) x := by
  classical
  let qi : ℂ := (bilinear D (unitCharge D i) a : ℂ)
  let ql : ℂ := (bilinear D (unitCharge D l) a : ℂ)
  let fi : ℤ → ActualTensor D hu := fun j =>
    flatTerm D hu (chargedField D hu a) [(i, 0)] (e - 4) x (j, ())
  let fl : ℤ → ActualTensor D hu := fun j =>
    flatTerm D hu (chargedField D hu a) [(l, 0)] (e - 4) x (j, ())
  let boundary : ℤ → ActualTensor D hu := fun j =>
    (if j = 0 then qi * ql else 0) • chargedCoefficient D hu a (e - 2) x
  have hfi : Function.HasFiniteSupport fi :=
    LatticeHalfFockChargedSeedPhysical.singleton_finite D hu a i (e - 4) x
  have hfl : Function.HasFiniteSupport fl :=
    LatticeHalfFockChargedSeedPhysical.singleton_finite D hu a l (e - 4) x
  have hflneg : Function.HasFiniteSupport (fun j : ℤ => fl (-j)) :=
    hfl.fun_comp_of_injective neg_injective
  have hboundary : Function.HasFiniteSupport boundary := by
    apply (Set.finite_singleton (0 : ℤ)).subset
    intro j hj
    by_contra h
    apply hj
    simp only [Set.mem_singleton_iff] at h
    simp [boundary, h]
  have pairfinite (v : ActualTensor D hu) : Function.HasFiniteSupport
      (fun j : ℤ => tensorPair D (ActualGround D hu) i l j (-j) v) := by
    have shift (j : ℤ) : (1 : ℤ) - j - 1 = -j := by omega
    simpa only [shift] using tensorPair_finite D (ActualGround D hu) i l 1 v
  have pair (j : ℤ) :
      tensorPair D (ActualGround D hu) i l j (-j) (chargedCoefficient D hu a e x) -
        chargedCoefficient D hu a e (tensorPair D (ActualGround D hu) i l j (-j) x) =
        ql • fi j + qi • fl (-j) + boundary j := by
    exact congrArg (fun U : Module.End ℂ (ActualTensor D hu) => U x)
      (charged_pair_l1 D hu a i l j e)
  change (∑ᶠ j : ℤ, tensorPair D (ActualGround D hu) i l j (1-j-1)
      (chargedCoefficient D hu a e x)) -
    chargedCoefficient D hu a e
      (∑ᶠ j : ℤ, tensorPair D (ActualGround D hu) i l j (1-j-1) x) = _
  have shift (j : ℤ) : (1 : ℤ) - j - 1 = -j := by omega
  simp only [shift]
  rw [map_finsum _ (pairfinite x),
    ← finsum_sub_distrib (pairfinite (chargedCoefficient D hu a e x))
      ((pairfinite x).fun_comp (map_zero (chargedCoefficient D hu a e))),
    finsum_congr pair,
    finsum_add_distrib ((hfi.fun_comp (smul_zero ql)).add
      (hflneg.fun_comp (smul_zero qi))) hboundary,
    finsum_add_distrib (hfi.fun_comp (smul_zero ql))
      (hflneg.fun_comp (smul_zero qi)),
    ← smul_finsum' ql hfi, ← smul_finsum' qi hflneg]
  have reindex : (∑ᶠ j : ℤ, fl (-j)) = ∑ᶠ j : ℤ, fl j :=
    finsum_eq_of_bijective (fun j : ℤ => -j) neg_bijective (fun _ => rfl)
  rw [reindex]
  have sumBoundary : (∑ᶠ j : ℤ, boundary j) =
      (qi * ql) • chargedCoefficient D hu a (e - 2) x := by
    rw [finsum_eq_single _ 0 (fun j hj => by simp [boundary, hj])]
    simp [boundary]
  rw [sumBoundary]
  change ql • (∑ᶠ j : ℤ, fi j) + qi • (∑ᶠ j : ℤ, fl j) + _ = _
  have left := singletonLinear_coefficient D hu (chargedField D hu a) (i, 0) (e - 4) x
  have right := singletonLinear_coefficient D hu (chargedField D hu a) (l, 0) (e - 4) x
  rw [← left, ← right]
  rfl


/-- Charged base on every original actual target input. This is a dependency,
not a replacement for the all-source corrected-field endpoint. -/
theorem charged_l1_coefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (e : ℤ) :
    tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 *
        chargedCoefficient D hu a e - chargedCoefficient D hu a e *
        tensorL D (ActualGround D hu) (HalfFockSpectralFiberSource.actualInverse D) 1 =
      (((e : ℂ) - 2) / 2 + (bilinear D a a : ℂ)) •
        chargedCoefficient D hu a (e - 2) := by
  classical
  let H := HalfFockSpectralFiberSource.actualInverse D
  have hHG := HalfFockSpectralFiberSource.actualInverse_left D hu
  have hGH := HalfFockSpectralFiberSource.actualInverse_right D hu
  have inv := LatticeSugawaraConformal.inverse_charge_contractions D H hHG hGH a
  apply LinearMap.ext
  intro x
  let chi : Fin D.rank → ℂ := fun i => (bilinear D (unitCharge D i) a : ℂ)
  let W : Fin D.rank → ActualTensor D hu := fun i =>
    (wordField D hu (chargedField D hu a) [(i, 0)]).coeff (e - 4) x
  let C : ActualTensor D hu := chargedCoefficient D hu a (e - 2) x
  let Q : ℂ := (bilinear D a a : ℂ)
  have rows : (∑ i : Fin D.rank, ∑ l : Fin D.rank,
      H i l • (chi l • W i)) = ∑ i : Fin D.rank, (a i : ℂ) • W i := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = (∑ l : Fin D.rank, H i l * chi l) • W i := by
        simp only [Finset.sum_smul, smul_smul]
      _ = _ := by rw [inv.1 i]
  have cols : (∑ i : Fin D.rank, ∑ l : Fin D.rank,
      H i l • (chi i • W l)) = ∑ l : Fin D.rank, (a l : ℂ) • W l := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    calc
      _ = (∑ i : Fin D.rank, H i l * chi i) • W l := by
        simp only [Finset.sum_smul, smul_smul]
      _ = _ := by rw [inv.2 l]
  have quadratic : (∑ i : Fin D.rank, ∑ l : Fin D.rank,
      H i l * chi i * chi l) = Q := by
    have h := LatticeSugawaraConformal.chargeQuadratic_eq D H hHG hGH a
    change (2 : ℂ)⁻¹ * (∑ i : Fin D.rank, ∑ l : Fin D.rank,
      H i l * chi i * chi l) = Q / 2 at h
    linear_combination (2 : ℂ) * h
  have quad : (∑ i : Fin D.rank, ∑ l : Fin D.rank,
      H i l • ((chi i * chi l) • C)) = Q • C := by
    calc
      _ = (∑ i : Fin D.rank, ∑ l : Fin D.rank, H i l * chi i * chi l) • C := by
        simp only [Finset.sum_smul, smul_smul, mul_assoc]
      _ = _ := by rw [quadratic]
  have seed : (∑ i : Fin D.rank, (a i : ℂ) • W i) - (Q / 2) • C =
      (((e : ℂ) - 2) / 2) • C := by
    have h := LatticeHalfFockChargedSeedPhysical.charged_seed_physical_coefficient
      D hu a (e - 4) x
    rw [show e - 4 + 2 = e - 2 by omega] at h
    simpa only [W, C, Q, chargeNorm, Int.cast_sub, Int.cast_ofNat] using h
  have l1 : tensorL D (ActualGround D hu) H 1 = tensorRawL D (ActualGround D hu) H 1 := by
    simp [tensorL, tensorRawL, L]
  have expansion : tensorL D (ActualGround D hu) H 1 (chargedCoefficient D hu a e x) -
      chargedCoefficient D hu a e (tensorL D (ActualGround D hu) H 1 x) =
      (2 : ℂ)⁻¹ • ∑ i : Fin D.rank, ∑ l : Fin D.rank,
        H i l • (chi l • W i + chi i • W l + (chi i * chi l) • C) := by
    rw [l1, tensor_rawL_finsum, tensor_rawL_finsum]
    simp_rw [map_smul, map_sum]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [← smul_sub]
    congr 1
    exact charged_normal_sum_l1 D hu a i l e x
  change tensorL D (ActualGround D hu) H 1 (chargedCoefficient D hu a e x) -
      chargedCoefficient D hu a e (tensorL D (ActualGround D hu) H 1 x) =
      (((e : ℂ) - 2) / 2 + Q) • C
  rw [expansion]
  simp_rw [smul_add, Finset.sum_add_distrib]
  rw [rows, cols, quad, sub_eq_iff_eq_add.mp seed]
  module

#print axioms charged_pair_l1
#print axioms charged_normal_sum_l1
#print axioms charged_l1_coefficient

end
end D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance
