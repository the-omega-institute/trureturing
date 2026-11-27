import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBMonodromy
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairSkew

/-! The literal mixed coefficient at doubled exponent -5 surjects onto
the odd weight-one space with its second input fixed at the native ground vector. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWeightOne

open scoped BigOperators
open Complex
open ActualLeechHyperbolic (leechData)
open LatticePositiveEnergy (grade)
open LatticeHalfFockGradedTrace (actualGrade)
open ActualChargedAdjoint (actualForm)
open NativeOddTwistedIntertwiner (OddCarrier TwistedEven TwistedOdd Jplus J_grade oddTranslation
  leechGroundVector leechUnit paritySign)
open NativeOddUpperRightSkew (R)
open NativeMixedPairState (mixedPairState_pairing mixedPairState_grade
  mixedPairState_truncation oddGrade oddGradePairing)
open NativeMixedPairField (mu mu_coeff_of_grade)
open NativeMixedPairSkew (mu_skew_of_grade swapInput)
open SourceBPZ.OriginalSourcePairing (sourcePairing sourcePairing_symmetric)

open private groundBasis_energy leechGroundVector_nonzero from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private R_lowest exists_grade_detector mixedPairing_lowest upper_phase_neg_one
  upper_phase_neg_three upper_phase_neg_four from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private oddGradeDualEquiv from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairState
open private first_oscillator_ne_zero from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBMonodromy

local notation "ℒ" => leechData
local notation "H" => leechGroundVector

/-- The specified native ground state is nonzero and has doubled grade zero. -/
theorem ground_nonzero_grade_zero : H ≠ 0 ∧ (H).val ∈ actualGrade ℒ leechUnit 0 :=
  ⟨leechGroundVector_nonzero, groundBasis_energy⟩

/-- The first doubled grade of the actual odd twisted state space. -/
abbrev firstTwistedGrade : Submodule ℂ TwistedOdd :=
  (actualGrade ℒ leechUnit 1).comap
    (HalfFock.LatticeHalfFockParityField.paritySpace ℒ leechUnit (paritySign true)).subtype

/-- Both inputs may vary within their stated native grades. -/
theorem mu_true_negFive_grade (P : TwistedOdd) (h : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit 1)
    (hh : h.val ∈ actualGrade ℒ leechUnit 0) :
    ((mu true P).coeff (-5) h).val ∈ grade ℒ 1 := by
  rw [show (-5 : ℤ) = -2 * 1 - 3 by decide, mu_coeff_of_grade true 1 0 1 P h hP hh]
  exact mixedPairState_grade true 1 0 1 P h

/-- At the requested coefficient the BPZ inversion sum has only order zero
and its inversion phase is one. -/
theorem mu_true_negFive_pairing (P : TwistedOdd) (h : TwistedEven)
    (hP : P.val ∈ actualGrade ℒ leechUnit 1)
    (hh : h.val ∈ actualGrade ℒ leechUnit 0) (a : OddCarrier ℒ) :
    sourcePairing ℒ ((mu true P).coeff (-5) h).val a.val =
      actualForm ℒ leechUnit h.val (R ℒ leechUnit true 0 P a).val := by
  rw [show (-5 : ℤ) = -2 * 1 - 3 by decide, mu_coeff_of_grade true 1 0 1 P h hP hh,
    mixedPairState_pairing true 1 0 1 P h hP hh, mixedPairing_lowest true 1 1 (by decide)]
  change I ^ (-4 : ℤ) * actualForm ℒ leechUnit h.val (R ℒ leechUnit true 0 P a).val = _
  rw [upper_phase_neg_four, one_mul]

private theorem mu_false_negFive_pairing (P : firstTwistedGrade)
    (a : OddCarrier ℒ) (ha : a.val ∈ grade ℒ 1) :
    sourcePairing ℒ ((mu false H).coeff (-5) P.val).val a.val =
      actualForm ℒ leechUnit P.val.val (Jplus (-1) a H).val := by
  rw [show (-5 : ℤ) = -2 * 1 - 3 by decide,
    mu_coeff_of_grade false 0 1 1 H P.val groundBasis_energy P.property,
    mixedPairState_pairing false 0 1 1 H P.val groundBasis_energy P.property,
    mixedPairing_lowest false 0 1 (by decide)]
  change I ^ (-3 : ℤ) * actualForm ℒ leechUnit P.val.val
    (R ℒ leechUnit false (-1) H a).val = _
  rw [R_lowest ℒ leechUnit false (-1) 1 0 H a ha groundBasis_energy (by decide) (by decide)]
  change I ^ (-3 : ℤ) * actualForm ℒ leechUnit P.val.val
    ((I ^ (-1 : ℤ)) • Jplus (-1) a H).val = _
  rw [upper_phase_neg_three, upper_phase_neg_one, Submodule.coe_smul, map_smul,
    smul_eq_mul, ← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]

private theorem mu_true_negFive_skew (P : firstTwistedGrade) :
    (mu true P.val).coeff (-5) H = (-I) • (mu false H).coeff (-5) P.val := by
  have h := mu_skew_of_grade true true 1 0 (-5) P.val H P.property groundBasis_energy
  have hswap : swapInput P.val = P.val := Subtype.ext rfl
  rw [hswap] at h
  change (mu true P.val).coeff (-5) H =
    (-1 : ℂ) ^ (4 : ℕ) • ∑ᶠ j : ℕ,
      (I ^ ((-5 : ℤ) - 2 * (j : ℤ)) * (j.factorial : ℂ)⁻¹) •
        (oddTranslation ℒ ^ j) ((mu false H).coeff (-5 - 2 * (j : ℤ)) P.val) at h
  rw [finsum_eq_single _ 0] at h
  · have hphase : I ^ (-5 : ℤ) = -I := by
      rw [show (-5 : ℤ) = -4 + -1 by decide, zpow_add₀ I_ne_zero,
        upper_phase_neg_four, upper_phase_neg_one, one_mul]
    have hsign : (-1 : ℂ) ^ (4 : ℕ) = 1 := by norm_num
    simpa [hphase, hsign] using h
  · intro j hj
    have hcut : (0 : ℤ) + 1 + 3 - 2 * (1 + (j : ℤ)) ≤ 0 := by omega
    rw [show (-5 : ℤ) - 2 * (j : ℤ) = -2 * (1 + (j : ℤ)) - 3 by ring,
      mu_coeff_of_grade false 0 1 (1 + (j : ℤ)) H P.val groundBasis_energy P.property,
      mixedPairState_truncation false 0 1 (1 + (j : ℤ)) H P.val (by simpa using hcut),
      map_zero, smul_zero]

/-- The native pairing identifies the transpose of the actual ground
coefficient with the first oscillator creation map, with its skew phase. -/
theorem mu_ground_negFive_creation_pairing (P : firstTwistedGrade)
    (a : OddCarrier ℒ) (ha : a.val ∈ grade ℒ 1) :
    sourcePairing ℒ ((mu true P.val).coeff (-5) H).val a.val =
      (-I) * actualForm ℒ leechUnit P.val.val (Jplus (-1) a H).val := by
  rw [mu_true_negFive_skew, Submodule.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul,
    mu_false_negFive_pairing P a ha]

/-- The literal coefficient as a linear map into the actual odd weight-one grade. -/
def groundCoefficient : firstTwistedGrade →ₗ[ℂ] oddGrade 1 := by
  let extract : HVertexOperator ℤ ℂ TwistedEven (OddCarrier ℒ) →ₗ[ℂ] OddCarrier ℒ :=
    (LinearMap.applyₗ H).comp ((LinearMap.proj (-5)).comp HVertexOperator.coeff)
  let raw := extract.comp (mu true)
  let ambient := (LatticeInvolution.minusSpace ℒ).subtype.comp (raw.comp firstTwistedGrade.subtype)
  refine LinearMap.codRestrict (oddGrade 1) ambient ?_
  intro P
  change ((mu true P.val).coeff (-5) H).val ∈ oddGrade 1
  exact ⟨mu_true_negFive_grade P.val H P.property groundBasis_energy,
    ((mu true P.val).coeff (-5) H).property⟩

@[simp] theorem groundCoefficient_val (P : firstTwistedGrade) :
    (groundCoefficient P).val = ((mu true P.val).coeff (-5) H).val :=
  rfl

set_option maxHeartbeats 800000 in
/-- With the ground vector fixed, the literal coefficient map is surjective
onto every odd weight-one state. -/
theorem groundCoefficient_surjective : Function.Surjective groundCoefficient := by
  classical
  by_contra hn
  have hlt : LinearMap.range groundCoefficient < ⊤ :=
    lt_top_iff_ne_top.mpr (fun he => hn (LinearMap.range_eq_top.mp he))
  obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_lt_top
    (K := ℂ) (V := oddGrade 1) (LinearMap.range groundCoefficient) hlt
  let a := (oddGradeDualEquiv 1).symm f
  have ha : a ≠ 0 := by
    intro hz
    apply hf
    have he := congrArg (fun x : oddGrade 1 => (oddGradeDualEquiv 1) x) hz
    change (oddGradeDualEquiv 1) ((oddGradeDualEquiv 1).symm f) =
      (oddGradeDualEquiv 1) 0 at he
    exact ((oddGradeDualEquiv 1).apply_symm_apply f).symm.trans
      (he.trans ((oddGradeDualEquiv 1).toLinearMap.map_zero))
  let b : OddCarrier ℒ := ⟨a.val, a.property.2⟩
  have hb : b ≠ 0 := fun hz => ha (Subtype.ext (congrArg (fun x : OddCarrier ℒ => x.val) hz))
  have hbg : b.val ∈ grade ℒ 1 := a.property.1
  let w := Jplus (-1) b H
  have hw : w ≠ 0 := first_oscillator_ne_zero b hbg hb
  have hwg : w.val ∈ actualGrade ℒ leechUnit 1 :=
    J_grade ℒ leechUnit false (-1) 1 0 1 b H hbg groundBasis_energy (by decide)
  obtain ⟨P, hP, hpair⟩ := exists_grade_detector ℒ leechUnit true 1 w hwg hw
    (by norm_num [paritySign])
  let p : firstTwistedGrade := ⟨P, hP⟩
  have hzero : f (groundCoefficient p) = 0 :=
    hker (LinearMap.mem_range_self groundCoefficient p)
  have hdual : oddGradePairing 1 a (groundCoefficient p) = f (groundCoefficient p) := by
    change (oddGradeDualEquiv 1) a (groundCoefficient p) = _
    exact congrArg (fun g : Module.Dual ℂ (oddGrade 1) => g (groundCoefficient p))
      ((oddGradeDualEquiv 1).apply_symm_apply f)
  have hcoeff := mu_ground_negFive_creation_pairing p b hbg
  change sourcePairing ℒ ((mu true p.val).coeff (-5) H).val a.val =
    (-I) * actualForm ℒ leechUnit P.val w.val at hcoeff
  rw [hpair, mul_one, sourcePairing_symmetric, ← groundCoefficient_val] at hcoeff
  change oddGradePairing 1 a (groundCoefficient p) = -I at hcoeff
  rw [hdual, hzero] at hcoeff
  exact (neg_ne_zero.mpr I_ne_zero) hcoeff.symm

/-- Every odd weight-one lattice state is a single coefficient with the
second input fixed at the native ground state. -/
theorem exists_mu_true_negFive_ground_eq (a : OddCarrier ℒ) (ha : a.val ∈ grade ℒ 1) :
    ∃ P : TwistedOdd, P.val ∈ actualGrade ℒ leechUnit 1 ∧
      (mu true P).coeff (-5) H = a := by
  obtain ⟨P, hP⟩ := groundCoefficient_surjective ⟨a.val, ha, a.property⟩
  refine ⟨P.val, P.property, Subtype.ext ?_⟩
  rw [← groundCoefficient_val P]
  exact congrArg (fun x : oddGrade 1 => x.val) hP

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWeightOne
