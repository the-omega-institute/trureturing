/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldModeRealForm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldModeRealForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conjugation of every normalized coefficient of the original Leech orbifold field. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldNativeBPZRadical
import D5.S3.VertexAlgebra.TwistedGround.ActualLeechFixedTwistedModeRealForm
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalMixedBPZ

/-! Coefficient conjugation on the original Leech orbifold field. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators ComplexConjugate VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldModeRealForm

open ActualLeechHyperbolic (leechData leech_spec)
open ActualLeechOrbifoldMatter (Orbifold leechUnit leechPosDef)
open ActualLeechOrbifoldBRST.NativeBPZ (fixed_sourcePairing_nondegenerate)
open HalfFock.LatticeHalfFockParityField (fixedParitySlice paritySpace)
open Lattice.ActualCoefficientRealForm
  (fixedKappa fixedKappa_add fixedKappa_smul fixedKappa_involutive
    fixedKappa_leechStress fixedY_kappa)
open LatticeHalfFockGradedTrace (actualAmbientBasis actualTensorL0 oddWeight)
open LatticeInvolution (FixedCarrier)
open SourceBPZ.OriginalMatterHermitian (sourcePairing_kappa)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open TwistedGround.ActualChargedAdjoint (actualForm)
open TwistedGround.ActualLeechFixedTwistedModeRealForm (fixedParitySlice_kappa)
open TwistedGround.ActualLeechTwistedTensorRealForm
  (negativeConjugation actualForm_negativeConjugation)
open TwistedGround.MixedIntertwiner (originalRightCoefficient translation)
open TwistedGround.OriginalFourMChargeCoset (originalI)
open TwistedGround.Orbifold
open TwistedGround.Orbifold.OriginalMixedBPZ (twistedL1 original_mixed_bpz)

open private mixedMode actualInputBasis actual_input_basis_expansion actual_input_basis_energy
  from D5.S3.VertexAlgebra.TwistedGround.MixedJacobiFinite
open private rightTerm rightTerm_finite
  from D5.S3.VertexAlgebra.TwistedGround.OriginalRightSkew
open private stress stress_twisted_mode
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation
open private fixedY_ncoeff
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldField

local notation "F" => FixedCarrier leechData
local notation "M" => paritySpace leechData leechUnit (-1)
local notation "I" => originalI leechData leechUnit leechPosDef

private def fixedConjugation : F →ₗ⋆[ℂ] F where
  toFun := fixedKappa leechData
  map_add' := fixedKappa_add leechData
  map_smul' := fixedKappa_smul leechData

private theorem neg_one_zpow_conj (n : ℤ) :
    conj ((-1 : ℂ) ^ n) = (-1 : ℂ) ^ n := by
  simp only [map_zpow₀, map_neg, map_one]

private theorem factorial_inv_conj (j : ℕ) :
    conj ((j.factorial : ℂ)⁻¹) = (j.factorial : ℂ)⁻¹ := by
  simp only [map_inv₀, map_natCast]

private theorem twisted_stress_mode_kappa (n : ℤ) (u : M) :
    negativeConjugation (((fixedParitySlice leechData leechUnit (-1)
      (stress leechData))[[n]]) u) =
      ((fixedParitySlice leechData leechUnit (-1) (stress leechData))[[n]])
        (negativeConjugation u) := by
  have hstress : fixedKappa leechData (stress leechData) = stress leechData :=
    fixedKappa_leechStress
  simpa only [hstress] using fixedParitySlice_kappa (stress leechData) n u

private theorem translation_kappa (u : M) :
    negativeConjugation (translation leechData leechUnit u) =
      translation leechData leechUnit (negativeConjugation u) := by
  simpa only [stress_twisted_mode] using twisted_stress_mode_kappa 0 u

private theorem twistedL1_kappa (u : M) :
    negativeConjugation (twistedL1 leechData leechUnit u) =
      twistedL1 leechData leechUnit (negativeConjugation u) :=
  twisted_stress_mode_kappa 2 u

private theorem pow_kappa (A : Module.End ℂ M)
    (hA : ∀ u, negativeConjugation (A u) = A (negativeConjugation u)) (j : ℕ) (u : M) :
    negativeConjugation ((A ^ j) u) = (A ^ j) (negativeConjugation u) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [pow_succ', Module.End.mul_apply, hA, ih]

/-- The original skew coefficient commutes with conjugation of both inputs. -/
theorem originalRightCoefficient_kappa (n : ℤ) (u : M) (a : F) :
    negativeConjugation (originalRightCoefficient leechData leechUnit n u a) =
      originalRightCoefficient leechData leechUnit n
        (negativeConjugation u) (fixedKappa leechData a) := by
  change negativeConjugation (∑ᶠ ell, rightTerm leechData leechUnit n u a ell) =
    ∑ᶠ ell, rightTerm leechData leechUnit n (negativeConjugation u) (fixedKappa leechData a) ell
  rw [map_finsum negativeConjugation (rightTerm_finite leechData leechUnit n u a)]
  apply finsum_congr
  intro ell
  have hmode :
      negativeConjugation (mixedMode leechData leechUnit (n + (ell : ℤ)) a u) =
        mixedMode leechData leechUnit (n + (ell : ℤ)) (fixedKappa leechData a)
          (negativeConjugation u) :=
    fixedParitySlice_kappa a (n + (ell : ℤ)) u
  simp only [rightTerm, map_smulₛₗ, map_mul, neg_one_zpow_conj, factorial_inv_conj,
    pow_kappa (translation leechData leechUnit) translation_kappa, hmode]

private theorem twisted_stress_mode_one_val (u : M) :
    (((fixedParitySlice leechData leechUnit (-1) (stress leechData))[[1]]) u).val =
      actualTensorL0 leechData leechUnit u.val := by
  let x : Orbifold := (0, u)
  have hfield := OriginalOrbifoldField.Y_fixed_ncoeff_apply leechData leechUnit leechPosDef
    1 (stress leechData) x
  have hmode := ActualLeechOrbifoldMatter.mode_apply 0 x
  exact (congrArg (fun y : Orbifold => y.2.val) hfield).symm.trans (congrArg Prod.snd hmode)

private theorem twisted_energy_kappa (H : ℕ) (u : M)
    (hu : actualTensorL0 leechData leechUnit u.val = (H : ℂ) • u.val) :
    actualTensorL0 leechData leechUnit (negativeConjugation u).val =
      (H : ℂ) • (negativeConjugation u).val := by
  have hu' : ((fixedParitySlice leechData leechUnit (-1) (stress leechData))[[1]]) u =
      (H : ℂ) • u := by
    apply Subtype.ext
    exact (twisted_stress_mode_one_val u).trans hu
  have h := (twisted_stress_mode_kappa 1 u).symm
  rw [hu', map_smulₛₗ, map_natCast] at h
  exact (twisted_stress_mode_one_val (negativeConjugation u)).symm.trans
    (congrArg Subtype.val h)

private theorem conj_finsum (f : ℕ → ℂ) :
    conj (∑ᶠ j, f j) = ∑ᶠ j, conj (f j) :=
  (starRingEnd ℂ).toAddMonoidHom.map_finsum_of_injective
    (starRingAut (R := ℂ)).injective f

private theorem originalI_kappa_homogeneous (H K : ℕ) (n : ℤ) (u v : M)
    (hu : actualTensorL0 leechData leechUnit u.val = (H : ℂ) • u.val)
    (hv : actualTensorL0 leechData leechUnit v.val = (K : ℂ) • v.val) :
    fixedConjugation (I n u v) = I n (negativeConjugation u) (negativeConjugation v) := by
  change fixedKappa leechData (I n u v) = _
  apply sub_eq_zero.mp
  apply fixed_sourcePairing_nondegenerate.1
  intro a
  obtain ⟨b, rfl⟩ := (fixedKappa_involutive leechData).surjective a
  change sourcePairing leechData
    (fixedKappa leechData (I n u v) - I n (negativeConjugation u) (negativeConjugation v)).val
    (fixedKappa leechData b).val = 0
  have hpair :
      sourcePairing leechData (fixedKappa leechData (I n u v)).val (fixedKappa leechData b).val =
        conj (sourcePairing leechData (I n u v).val b.val) :=
    sourcePairing_kappa (I n u v).val b.val
  rw [Submodule.coe_sub, map_sub, LinearMap.sub_apply, sub_eq_zero, hpair,
    original_mixed_bpz leechData leechUnit leechPosDef leech_spec.1 H K n u v hu hv b,
    original_mixed_bpz leechData leechUnit leechPosDef leech_spec.1 H K n
      (negativeConjugation u) (negativeConjugation v)
      (twisted_energy_kappa H u hu) (twisted_energy_kappa K v hv) (fixedKappa leechData b),
    map_mul, neg_one_zpow_conj, conj_finsum]
  apply congrArg (fun z : ℂ => (-1 : ℂ) ^ (H : ℤ) * z)
  apply finsum_congr
  intro j
  let s : ℤ := 2 * (H : ℤ) - n - (j : ℤ) - 2
  rw [map_mul, factorial_inv_conj, ← actualForm_negativeConjugation v
    (originalRightCoefficient leechData leechUnit s ((twistedL1 leechData leechUnit ^ j) u) b),
    originalRightCoefficient_kappa, pow_kappa (twistedL1 leechData leechUnit) twistedL1_kappa]

set_option maxHeartbeats 800000 in
/-- Mixed BPZ and the finite actual energy expansions give conjugation of the
original coefficient with two arbitrary negative twisted inputs. -/
theorem originalI_kappa (n : ℤ) (u v : M) :
    fixedKappa leechData (I n u v) = I n (negativeConjugation u) (negativeConjugation v) := by
  classical
  let basis := actualAmbientBasis leechData leechUnit
  let us := ∑ i ∈ (basis.repr u.val).support.attach,
    (basis.repr u.val i.val) • actualInputBasis leechData leechUnit u i
  let vs := ∑ j ∈ (basis.repr v.val).support.attach,
    (basis.repr v.val j.val) • actualInputBasis leechData leechUnit v j
  have hu : us = u := actual_input_basis_expansion leechData leechUnit u
  have hv : vs = v := actual_input_basis_expansion leechData leechUnit v
  change fixedConjugation (I n u v) = _
  calc
    fixedConjugation (I n u v) = fixedConjugation (I n us vs) :=
      congrArg₂ (fun x y => fixedConjugation (I n x y)) hu.symm hv.symm
    _ = I n (negativeConjugation us) (negativeConjugation vs) := by
      dsimp only [us, vs]
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, RingHom.id_apply,
        LinearMap.smul_apply, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [originalI_kappa_homogeneous ((oddWeight leechData i.val.1 + 3) / 2)
        ((oddWeight leechData j.val.1 + 3) / 2) n
        (actualInputBasis leechData leechUnit u i) (actualInputBasis leechData leechUnit v j)
        (actual_input_basis_energy leechData leechUnit leech_spec.1 u i)
        (actual_input_basis_energy leechData leechUnit leech_spec.1 v j)]
    _ = I n (negativeConjugation u) (negativeConjugation v) :=
      congrArg₂ (fun x y => I n (negativeConjugation x) (negativeConjugation y)) hu hv

/-- The original orbifold conjugation on the fixed and negative twisted sectors. -/
def orbifoldConjugation : Orbifold →ₗ⋆[ℂ] Orbifold where
  toFun a := (fixedKappa leechData a.1, negativeConjugation a.2)
  map_add' a b := Prod.ext (fixedKappa_add leechData a.1 b.1)
    (negativeConjugation.map_add a.2 b.2)
  map_smul' z a := Prod.ext (fixedKappa_smul leechData z a.1)
    (negativeConjugation.map_smulₛₗ z a.2)

private theorem orbifoldConjugation_apply (a : Orbifold) :
    orbifoldConjugation a = (fixedKappa leechData a.1, negativeConjugation a.2) :=
  rfl

/-- Every normalized coefficient of the original Leech orbifold field is
covariant for the sectorwise conjugation, on all original inputs. -/
theorem Y_ncoeff_kappa (n : ℤ) (a b : Orbifold) :
    orbifoldConjugation (((OriginalOrbifoldField.Y leechData leechUnit leechPosDef a)[[n]]) b) =
      ((OriginalOrbifoldField.Y leechData leechUnit leechPosDef (orbifoldConjugation a))[[n]])
        (orbifoldConjugation b) := by
  rw [OriginalOrbifoldField.Y_ncoeff_apply leechData leechUnit leechPosDef n a b,
    OriginalOrbifoldField.Y_ncoeff_apply leechData leechUnit leechPosDef n
      (orbifoldConjugation a) (orbifoldConjugation b)]
  have hfixed := fixedY_kappa leechData a.1 b.1 n
  simp only [fixedY_ncoeff] at hfixed
  simp only [orbifoldConjugation_apply, fixedKappa_add, map_add, hfixed,
    originalI_kappa, fixedParitySlice_kappa, originalRightCoefficient_kappa]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldModeRealForm
