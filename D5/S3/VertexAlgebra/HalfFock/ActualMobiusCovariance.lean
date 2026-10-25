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

end
end D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance
