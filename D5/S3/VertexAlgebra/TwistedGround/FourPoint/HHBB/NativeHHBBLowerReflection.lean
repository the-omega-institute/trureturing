import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedArbitrarySewing
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
import D5.S3.VertexAlgebra.TwistedGround.RealForm.ActualLeechFixedTwistedModeRealForm
import Batteries.Tactic.OpenPrivate

/-! Coefficient conjugation and the physical lower HHBB overlap for the native fields. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section

open scoped BigOperators ComplexConjugate VertexOperator
open Complex (I)

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBLowerReflection

open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open ActualLeechTwistedTensorRealForm
  (tensorConjugation tensorConjugation_actualParity actualForm_conjugation)
open ActualLeechFixedTwistedModeRealForm (correctedField_kappa)
open Lattice.ActualCoefficientRealForm (fixedKappa fixedKappa_smul fixedKappa_leechStress)
open LatticeGeneratingFieldLocality (Carrier)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace (actualGrade actualTensorL0 actualAmbientBasis oddWeight)
open HalfFock.LatticeHalfFockParityField (paritySpace fixedParitySlice)
open LatticeHalfFockParityT (actualParity)
open LatticeInvolution (FixedCarrier minusSpace eigenspace mem_eigenspace theta)
open SourceBPZ.OriginalMatterHermitian
  (kappaCarrier kappaCarrier_add kappaCarrier_smul kappaCarrier_theta
    kappaCarrier_involutive sourcePairing_kappa)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open Orbifold.NativeOddTwistedIntertwiner
  (Twisted TwistedEven TwistedOdd OddCarrier paritySign leechUnit field J)
open Orbifold.NativeOddUpperRightSkew
  (translation lowering R rightTerm rightTerm_finite rightField rightField_coeff
    rightField_even_zero rightField_convolution mixedPairing)
open Orbifold.NativeMixedPairState (mixedPairState mixedPairState_pairing existsUnique_mixedPairState)
open Orbifold.NativeFixedPairState (fixedPairState fixedPairing_apply fixedPairState_pairing)
open Orbifold.NativeMixedPairField (mu mu_coeff_of_grade mu_coeff_even_zero)
open Orbifold.NativeFixedPairField (nu nu_coeff_of_grade nu_coeff_odd_zero)
open NativeMixedUpperProductCusp (bJointTerm)
open NativeMixedComplexSewing (aJointTerm)
open NativeMixedArbitrarySewing (hhbbCorrelation hhbb_actual_complex_sewing_of_states)
open Orbifold.NativeFullMixedField (project)

open private stress from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTranslation
open private T from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private lowering_pow_val actualGrade_eigen from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private fixed_source_ext from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFixedPairState
open private projectedBasis_mem_grade from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFixedPairField
open private sqrt_square from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

local notation "ℒ" => leechData
local notation "U" => leechUnit

/-- The actual tensor real form restricted to either physical parity sector. -/
def twistedConjugation (s : Bool) : Twisted ℒ U s →ₗ⋆[ℂ] Twisted ℒ U s :=
  tensorConjugation.restrict fun x hx => by
    simp only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    rw [← tensorConjugation_actualParity, hx, map_smulₛₗ]
    cases s <;> simp [paritySign]

/-- The original lattice real form restricted to theta-odd sources. -/
def oddConjugation : OddCarrier ℒ →ₗ⋆[ℂ] OddCarrier ℒ where
  toFun a := ⟨kappaCarrier a.val, by
    change kappaCarrier a.val ∈ eigenspace ℒ (-1)
    have ha := (mem_eigenspace ℒ (-1) a.val).mp a.property
    rw [mem_eigenspace, ← kappaCarrier_theta, ha, kappaCarrier_smul]
    simp only [map_neg, map_one]⟩
  map_add' a b := Subtype.ext (kappaCarrier_add a.val b.val)
  map_smul' c a := Subtype.ext (kappaCarrier_smul c a.val)

private theorem oddConjugation_involutive : Function.Involutive oddConjugation :=
  fun a => Subtype.ext (kappaCarrier_involutive a.val)

private theorem stress_mode_conj (s : Bool) (n : ℤ) (u : Twisted ℒ U s) :
    twistedConjugation s (((fixedParitySlice ℒ U (paritySign s) (stress ℒ))[[n]]) u) =
      ((fixedParitySlice ℒ U (paritySign s) (stress ℒ))[[n]]) (twistedConjugation s u) := by
  apply Subtype.ext
  have hstress : kappaCarrier (stress ℒ).val = (stress ℒ).val :=
    congrArg Subtype.val fixedKappa_leechStress
  have h := correctedField_kappa (stress ℒ).val (2 * (-n - 1)) u.val
  rw [hstress] at h
  simpa only [twistedConjugation, LinearMap.coe_restrict_apply, fixedParitySlice,
    VertexOperator.ncoeff_of_coeff] using h

private theorem pow_conj {s : Bool} (A : Module.End ℂ (Twisted ℒ U s))
    (hA : ∀ u, twistedConjugation s (A u) = A (twistedConjugation s u))
    (j : ℕ) (u : Twisted ℒ U s) :
    twistedConjugation s ((A ^ j) u) = (A ^ j) (twistedConjugation s u) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [pow_succ', Module.End.mul_apply, hA, ih]

private theorem lowering_pow_conj (s : Bool) (j : ℕ) (x : Twisted ℒ U s) :
    tensorConjugation ((T ℒ U ^ j) x.val) =
      (T ℒ U ^ j) (twistedConjugation s x).val := by
  simpa only [lowering_pow_val, twistedConjugation, LinearMap.coe_restrict_apply] using
    congrArg Subtype.val (pow_conj (lowering ℒ U s) (stress_mode_conj s 2) j x)

private theorem J_conj (s : Bool) (n : ℤ) (a : OddCarrier ℒ) (u : Twisted ℒ U s) :
    twistedConjugation (!s) (J ℒ U s n a u) =
      J ℒ U s n (oddConjugation a) (twistedConjugation s u) := by
  apply Subtype.ext
  exact correctedField_kappa a.val (-2 * n - 3) u.val

private theorem phase_conj (e : ℤ) :
    conj (I ^ e) = (-1 : ℂ) ^ e * I ^ e := by
  rw [map_zpow₀, Complex.conj_I, ← neg_one_mul I, mul_zpow]

private theorem right_phase_conj (n : ℤ) :
    conj (I ^ (-(2 * n) - 3)) = -(I ^ (-(2 * n) - 3)) := by
  rw [phase_conj, neg_one_zpow_eq_ite, ite_eq_right (by rintro ⟨k, hk⟩; omega), neg_one_mul]

/-- Conjugation replaces the right-skew upper half-turn by the lower half-turn.
Every nonzero doubled exponent of the right field is odd. -/
theorem rightMode_conj (s : Bool) (n : ℤ) (u : Twisted ℒ U s) (a : OddCarrier ℒ) :
    twistedConjugation (!s) (R ℒ U s n u a) =
      (-1 : ℂ) • R ℒ U s n (twistedConjugation s u) (oddConjugation a) := by
  change twistedConjugation (!s) (∑ᶠ ell, rightTerm ℒ U s n u a ell) =
    (-1 : ℂ) • (∑ᶠ ell, rightTerm ℒ U s n (twistedConjugation s u) (oddConjugation a) ell)
  rw [map_finsum _ (rightTerm_finite ℒ U s n u a)]
  calc
    _ = ∑ᶠ ell, (-1 : ℂ) • rightTerm ℒ U s n (twistedConjugation s u) (oddConjugation a) ell := by
      apply finsum_congr
      intro ell
      simp only [rightTerm, map_smulₛₗ, map_mul, map_inv₀, map_natCast,
        pow_conj (translation ℒ U (!s)) (stress_mode_conj (!s) 0), J_conj, smul_smul]
      have hphase : conj (I ^ (-2 * (n + (ell : ℤ)) - 3)) =
          -(I ^ (-2 * (n + (ell : ℤ)) - 3)) := by
        simpa only [neg_mul] using right_phase_conj (n + (ell : ℤ))
      rw [hphase, neg_mul, neg_one_mul]
    _ = _ := (smul_finsum (-1 : ℂ)
      (rightTerm ℒ U s n (twistedConjugation s u) (oddConjugation a))).symm


theorem rightField_conj (s : Bool) (e : ℤ) (u : Twisted ℒ U s) (a : OddCarrier ℒ) :
    twistedConjugation (!s) ((rightField ℒ U s u).coeff e a) =
      (-1 : ℂ) • ((rightField ℒ U s (twistedConjugation s u)).coeff e (oddConjugation a)) := by
  by_cases he : Even e
  · simp only [rightField_even_zero _ _ _ _ he, map_zero, smul_zero]
  · have hm : e = -2 * ((-e - 3) / 2) - 3 := by
      obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp he
      omega
    rw [hm, rightField_coeff, rightField_coeff]
    exact rightMode_conj s _ u a

/-- Changing the half-turn from `I` to `-I` multiplies the original right field
by `(-1)^e` at every doubled mode. Translation advances the exponent by an even number. -/
theorem lowerRight_convolution (s : Bool) (e : ℤ) (u : Twisted ℒ U s) (a : OddCarrier ℒ) :
    (∑ᶠ ell : ℕ, ((-I) ^ (e - 2 * (ell : ℤ)) * (ell.factorial : ℂ)⁻¹) •
        (translation ℒ U (!s) ^ ell) ((field ℒ U s a).coeff (e - 2 * (ell : ℤ)) u)) =
      (-1 : ℂ) ^ e • ((rightField ℒ U s u).coeff e a) := by
  let upperTerm (ell : ℕ) : Twisted ℒ U (!s) :=
    (I ^ (e - 2 * (ell : ℤ)) * (ell.factorial : ℂ)⁻¹) •
      (translation ℒ U (!s) ^ ell) ((field ℒ U s a).coeff (e - 2 * (ell : ℤ)) u)
  rw [rightField_convolution]
  calc
    _ = ∑ᶠ ell, (-1 : ℂ) ^ e • upperTerm ell := by
      apply finsum_congr
      intro ell
      have he : Even (2 * (ell : ℤ)) := ⟨ell, by ring⟩
      have hsign : (-1 : ℂ) ^ (e - 2 * (ell : ℤ)) = (-1 : ℂ) ^ e := by
        rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0), he.neg_one_zpow, div_one]
      dsimp only [upperTerm]
      rw [← Complex.conj_I, ← map_zpow₀, phase_conj, hsign, smul_smul, mul_assoc]
    _ = _ := (smul_finsum ((-1 : ℂ) ^ e) upperTerm).symm

private theorem conj_mem_grade (s : Bool) (M : ℕ) (u : Twisted ℒ U s)
    (hu : u.val ∈ actualGrade ℒ U M) : (twistedConjugation s u).val ∈ actualGrade ℒ U M := by
  have hL (v : Twisted ℒ U s) :
      (((fixedParitySlice ℒ U (paritySign s) (stress ℒ))[[1]]) v).val =
        actualTensorL0 ℒ U v.val := by
    change (correctedField ℒ U
      (LatticeActualConformalState.omega ℒ (HalfFockSpectralFiberSource.actualInverse ℒ))).coeff
        (-4) v.val = _
    rw [LatticeHalfFockCorrectedConformal.correctedField_omega ℒ U _
      (HalfFockSpectralFiberSource.actualInverse_left ℒ U)]
    simp only [LatticeHalfFock.tensorStressField, HVertexOperator.coeff_of_coeff,
      LatticeHalfFock.stressCoeff, show (-4 : ℤ) % 2 = 0 by decide, ite_eq_left,
      show (-(-4 : ℤ) - 4) / 2 = 0 by decide, actualTensorL0, LatticeHalfFock.tensorL]
  have h := congrArg Subtype.val (stress_mode_conj s 1 u)
  change tensorConjugation (((fixedParitySlice ℒ U (paritySign s) (stress ℒ))[[1]]) u).val = _ at h
  rw [hL, hL, (actualGrade_eigen ℒ U M u.val).mp hu] at h
  apply (actualGrade_eigen ℒ U M _).mpr
  simpa only [map_smulₛₗ, map_add, map_div₀, map_natCast, map_ofNat,
    twistedConjugation, LinearMap.coe_restrict_apply] using h.symm

private theorem inversion_phase (M : ℕ) :
    (-1 : ℂ) ^ (-(3 + (M : ℤ))) = -((-1 : ℂ) ^ M) := by
  have h : Even (-(3 + (M : ℤ))) ↔ ¬ Even M := by
    rw [Int.even_iff, Nat.even_iff]
    omega
  rw [neg_one_zpow_eq_ite, neg_one_pow_eq_ite]
  by_cases hM : Even M
  · rw [ite_eq_right (fun he => h.mp he hM), ite_eq_left hM]
  · rw [ite_eq_left (h.mpr hM), ite_eq_right hM, neg_neg]

/-- The mixed BPZ phase is the product of the inversion and odd right-skew phases. -/
theorem mixedPairing_conj (s : Bool) (M : ℕ) (m : ℤ)
    (u : Twisted ℒ U s) (v : Twisted ℒ U (!s)) (a : OddCarrier ℒ) :
    conj (mixedPairing s M m u v a) =
      (-1 : ℂ) ^ M *
        mixedPairing s M m (twistedConjugation s u) (twistedConjugation (!s) v)
          (oddConjugation a) := by
  let A : Twisted ℒ U s →ₗ[ℂ] Twisted ℒ U s := lowering ℒ U s
  let term (x : Twisted ℒ U s) (y : Twisted ℒ U (!s)) (c : OddCarrier ℒ) (j : ℕ) :=
    (j.factorial : ℂ)⁻¹ * actualForm ℒ U y.val (R ℒ U s ((M : ℤ) - m - (j : ℤ))
      ((A ^ j) x) c).val
  have eval (x : Twisted ℒ U s) (y : Twisted ℒ U (!s)) (c : OddCarrier ℒ) :
      mixedPairing s M m x y c =
        I ^ (-(3 + (M : ℤ))) * ∑ j ∈ Finset.range (M / 2 + 1), term x y c j := by
    simp only [mixedPairing, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, smul_eq_mul, term, A]
  have hterm (j : ℕ) :
      conj (term u v a j) =
        -term (twistedConjugation s u) (twistedConjugation (!s) v) (oddConjugation a) j := by
    have hR := congrArg Subtype.val (rightMode_conj s ((M : ℤ) - m - (j : ℤ)) ((A ^ j) u) a)
    change tensorConjugation (R ℒ U s _ ((A ^ j) u) a).val = _ at hR
    rw [pow_conj A (stress_mode_conj s 2)] at hR
    dsimp only [term]
    rw [map_mul, map_inv₀, map_natCast, ← actualForm_conjugation, hR]
    change _ * actualForm ℒ U (twistedConjugation (!s) v).val _ = _
    simp only [Submodule.coe_smul, map_smul, smul_eq_mul, neg_one_mul, mul_neg]
  simp only [eval, map_mul, phase_conj, inversion_phase, map_sum, hterm, Finset.sum_neg_distrib,
    neg_mul, mul_neg, neg_neg, mul_assoc]

/-- The sign of a homogeneous mixed-pair state under the physical real form. -/
theorem mixedPairState_conj (s : Bool) (M K : ℕ) (m : ℤ)
    (u : Twisted ℒ U s) (v : Twisted ℒ U (!s))
    (hu : u.val ∈ actualGrade ℒ U M) (hv : v.val ∈ actualGrade ℒ U K) :
    oddConjugation (mixedPairState s M K m u v) =
      (-1 : ℂ) ^ M • mixedPairState s M K m (twistedConjugation s u) (twistedConjugation (!s) v) := by
  let X := mixedPairState s M K m u v
  let Y := mixedPairState s M K m (twistedConjugation s u) (twistedConjugation (!s) v)
  let c : ℂ := (-1 : ℂ) ^ M
  have hc : c * c = 1 := by
    rw [show c = (-1 : ℂ) ^ M from rfl, ← mul_pow]
    norm_num
  obtain ⟨z, hz, unique⟩ := existsUnique_mixedPairState s M K m
    (twistedConjugation s u) (twistedConjugation (!s) v)
    (conj_mem_grade s M u hu) (conj_mem_grade (!s) K v hv)
  have hy : Y = z := unique Y (mixedPairState_pairing s M K m _ _
    (conj_mem_grade s M u hu) (conj_mem_grade (!s) K v hv))
  have hx : c • oddConjugation X = z := by
    apply unique
    intro a
    obtain ⟨a, rfl⟩ := oddConjugation_involutive.surjective a
    rw [Submodule.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
    change c * sourcePairing ℒ (kappaCarrier X.val) (kappaCarrier a.val) = _
    rw [sourcePairing_kappa, show sourcePairing ℒ X.val a.val = mixedPairing s M m u v a
      from mixedPairState_pairing s M K m u v hu hv a, mixedPairing_conj, ← mul_assoc, hc, one_mul]
  change oddConjugation X = c • Y
  rw [hy, ← hx, smul_smul, hc, one_smul]

private theorem fixedPairing_conj (s : Bool) (M K : ℕ) (m : ℤ)
    (u v : Twisted ℒ U s) (a : FixedCarrier ℒ) :
    conj (Orbifold.NativeFixedPairState.fixedPairing s M K m u v a) =
      ((-1 : ℂ) ^ (-(3 + (M : ℤ)))) *
        Orbifold.NativeFixedPairState.fixedPairing s M K m (twistedConjugation s u)
          (twistedConjugation s v) (fixedKappa ℒ a) := by
  simp only [fixedPairing_apply, map_mul, map_sum, map_div₀, map_zpow₀ (starRingEnd ℂ) (-1),
    map_neg, map_one, map_natCast, ← actualForm_conjugation, lowering_pow_conj,
    correctedField_kappa, phase_conj, mul_assoc]
  rfl

/-- The fixed-pair sign comes from the inversion phase alone. -/
theorem fixedPairState_conj (s : Bool) (M K : ℕ) (m : ℤ)
    (u v : Twisted ℒ U s) (hu : u.val ∈ actualGrade ℒ U M) (hv : v.val ∈ actualGrade ℒ U K) :
    fixedKappa ℒ (fixedPairState s M K m u v) =
      (-1 : ℂ) ^ (-(3 + (M : ℤ))) •
        fixedPairState s M K m (twistedConjugation s u) (twistedConjugation s v) := by
  apply fixed_source_ext
  intro a
  obtain ⟨a, rfl⟩ := (Lattice.ActualCoefficientRealForm.fixedKappa_involutive ℒ).surjective a
  rw [Submodule.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  change sourcePairing ℒ (kappaCarrier (fixedPairState s M K m u v).val) (kappaCarrier a.val) = _
  rw [sourcePairing_kappa, fixedPairState_pairing s M K m u v hu hv, fixedPairing_conj,
    fixedPairState_pairing s M K m _ _ (conj_mem_grade s M u hu) (conj_mem_grade s K v hv)]


private def fixedConjugation : FixedCarrier ℒ →ₗ⋆[ℂ] FixedCarrier ℒ where
  toFun := fixedKappa ℒ
  map_add' := Lattice.ActualCoefficientRealForm.fixedKappa_add ℒ
  map_smul' := fixedKappa_smul ℒ

private theorem extend_even_first {V : Type*} [AddCommMonoid V] [Module ℂ V] {t : Bool}
    (F : TwistedEven →ₗ[ℂ] Twisted ℒ U t →ₗ[ℂ] V) (κ : V →ₗ⋆[ℂ] V) (c : ℂ)
    (h : ∀ (M K : ℕ) (u : TwistedEven) (v : Twisted ℒ U t),
      u.val ∈ actualGrade ℒ U M → v.val ∈ actualGrade ℒ U K → Even M →
        κ (F u v) = c • F (twistedConjugation false u) (twistedConjugation t v))
    (u : TwistedEven) (v : Twisted ℒ U t) :
    κ (F u v) = c • F (twistedConjugation false u) (twistedConjugation t v) := by
  classical
  let B := actualAmbientBasis ℒ U
  let us := ∑ i ∈ (B.repr u.val).support, (B.repr u.val i) • project false (B i)
  let vs := ∑ j ∈ (B.repr v.val).support, (B.repr v.val j) • project t (B j)
  suffices κ (F us vs) = c • F (twistedConjugation false us) (twistedConjugation t vs) by
    rwa [show us = u from sum_projectedBasis false u,
      show vs = v from sum_projectedBasis t v] at this
  dsimp only [us, vs]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    map_smulₛₗ, Finset.smul_sum, smul_comm c]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have hi := projectedBasis_mem_grade false i
  by_cases hM : Even (oddWeight ℒ i.1)
  · rw [h _ _ _ _ hi (projectedBasis_mem_grade t j) hM]
  · have hzero : project false (B i) = 0 :=
      NativeFourHHomogeneousExtension.homogeneousH_zero_of_odd_grade _ _ hi hM
    simp [hzero]

/-- The BPZ inversion sign cancels the right-skew sign for an even first input. -/
theorem mu_evenOdd_conj (e : ℤ) (u : TwistedEven) (v : TwistedOdd) :
    oddConjugation ((mu false u).coeff e v) =
      (mu false (twistedConjugation false u)).coeff e (twistedConjugation true v) := by
  by_cases he : Even e
  · simp only [mu_coeff_even_zero false e _ _ he, map_zero]
  · have hm : e = -2 * ((-e - 3) / 2) - 3 := by
      obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp he
      omega
    rw [hm]
    let m := (-e - 3) / 2
    let F : TwistedEven →ₗ[ℂ] TwistedOdd →ₗ[ℂ] OddCarrier ℒ :=
      ((LinearMap.proj (-2 * m - 3)).comp HVertexOperator.coeff).comp (mu false)
    change oddConjugation (F u v) = F (twistedConjugation false u) (twistedConjugation true v)
    have h := extend_even_first F oddConjugation 1 (fun M K x y hx hy hM => by
      change oddConjugation ((mu false x).coeff (-2 * m - 3) y) =
        (1 : ℂ) • (mu false (twistedConjugation false x)).coeff (-2 * m - 3)
          (twistedConjugation true y)
      rw [mu_coeff_of_grade false M K m x y hx hy,
        mu_coeff_of_grade false M K m _ _
          (conj_mem_grade false M x hx) (conj_mem_grade true K y hy),
        mixedPairState_conj false M K m x y hx hy, hM.neg_one_pow]
      rfl) u v
    simpa only [one_smul] using h

/-- The fixed even-even field acquires the inversion minus at every doubled mode. -/
theorem nu_evenEven_conj (e : ℤ) (u v : TwistedEven) :
    fixedKappa ℒ ((nu false u).coeff e v) =
      (-1 : ℂ) • ((nu false (twistedConjugation false u)).coeff e (twistedConjugation false v)) := by
  by_cases he : Odd e
  · change fixedConjugation ((nu false u).coeff e v) = _
    simp only [nu_coeff_odd_zero false e _ _ he, map_zero, smul_zero]
  · have hm : e = -2 * ((-e - 2) / 2) - 2 := by
      obtain ⟨k, hk⟩ := Int.not_odd_iff_even.mp he
      omega
    rw [hm]
    let m := (-e - 2) / 2
    let F : TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] FixedCarrier ℒ :=
      ((LinearMap.proj (-2 * m - 2)).comp HVertexOperator.coeff).comp (nu false)
    exact extend_even_first F fixedConjugation (-1) (fun M K x y hx hy hM => by
      change fixedKappa ℒ ((nu false x).coeff (-2 * m - 2) y) =
        (-1 : ℂ) • ((nu false (twistedConjugation false x)).coeff (-2 * m - 2)
          (twistedConjugation false y))
      rw [nu_coeff_of_grade false M K m x y hx hy,
        nu_coeff_of_grade false M K m _ _
          (conj_mem_grade false M x hx) (conj_mem_grade false K y hy),
        fixedPairState_conj false M K m x y hx hy, inversion_phase, hM.neg_one_pow]) u v

/-- Reflection of the literal B term at the conjugate coordinate roots. -/
theorem bJointTerm_conj (u v : TwistedEven) (w b : TwistedOdd) (xRoot zRoot : ℂ)
    (i : ℤ × ℤ) :
    conj (bJointTerm false false v w u b xRoot zRoot i) =
      -bJointTerm false false (twistedConjugation false v) (twistedConjugation true w)
        (twistedConjugation false u) (twistedConjugation true b) (conj xRoot) (conj zRoot) i := by
  have hR := congrArg Subtype.val (rightField_conj false i.2 u ((mu false v).coeff i.1 w))
  change tensorConjugation (((rightField ℒ U false u).coeff i.2 ((mu false v).coeff i.1 w)).val)
    = _ at hR
  rw [mu_evenOdd_conj] at hR
  simp only [bJointTerm, map_mul, map_zpow₀, ← actualForm_conjugation, hR,
    Submodule.coe_smul, map_smul, smul_eq_mul, neg_mul, one_mul]
  rfl

/-- Reflection of the literal fixed A term at the conjugate coordinate roots. -/
theorem aJointTerm_conj (u v : TwistedEven) (w b : TwistedOdd) (differenceRoot zRoot : ℂ)
    (i : ℤ × ℤ) :
    conj (aJointTerm u v w b differenceRoot zRoot i) =
      -aJointTerm (twistedConjugation false u) (twistedConjugation false v)
        (twistedConjugation true w) (twistedConjugation true b)
        (conj differenceRoot) (conj zRoot) i := by
  have hnu := congrArg Subtype.val (nu_evenEven_conj i.1 u v)
  change kappaCarrier ((nu false u).coeff i.1 v).val = _ at hnu
  simp only [aJointTerm, map_mul, map_zpow₀, ← actualForm_conjugation,
    correctedField_kappa, hnu, Submodule.coe_smul, map_smul, Pi.smul_apply,
    LinearMap.smul_apply, smul_eq_mul, neg_mul, one_mul]
  rfl

/-- The opposite right half-turn is represented by flipping only the outer B root. -/
theorem bJointTerm_neg_outer (u v : TwistedEven) (w b : TwistedOdd) (xRoot zRoot : ℂ)
    (i : ℤ × ℤ) :
    bJointTerm false false v w u b (-xRoot) zRoot i =
      -bJointTerm false false v w u b xRoot zRoot i := by
  by_cases he : Even i.2
  · simp [bJointTerm, rightField_even_zero ℒ U false i.2 he]
  · rw [bJointTerm, bJointTerm, (Int.not_even_iff_odd.mp he).neg_zpow, mul_neg, mul_neg]

private theorem sqrt_conj_of_arg_ne_pi {y : ℂ} (h : (conj y).arg ≠ Real.pi) :
    conj (Complex.sqrt y) = Complex.sqrt (conj y) := by
  have hpow := (Complex.cpow_conj (conj y) (1 / 2 : ℂ) h).symm
  simpa only [map_div₀, map_one, map_ofNat, map_inv₀, Complex.conj_conj, Complex.sqrt, one_div] using hpow

/-- Reflect an upper overlap to the physical lower overlap with the original
principal roots. The native A and B sums remain opposite with these roots.
Changing only the outer B root implements the lower right-skew half-turn. -/
theorem hhbb_lower_physical_overlap (u v : TwistedEven) (w b : TwistedOdd)
    {xRoot y : ℂ} (hx : xRoot ≠ 0) (hy : ‖y‖ < 1)
    (hre : (1 / 2 : ℝ) < y.re) (him : 0 < y.im) :
    let u' := twistedConjugation false u
    let v' := twistedConjugation false v
    let w' := twistedConjugation true w
    let b' := twistedConjugation true b
    let x' := conj xRoot
    let y' := conj y
    let z' := x' * Complex.sqrt y'
    let d' := z' * Complex.sqrt ((1 - y') / y')
    let C := hhbbCorrelation u v w b xRoot y
    y'.im < 0 ∧
      HasSum (aJointTerm u' v' w' b' d' z') (conj C) ∧
      HasSum (bJointTerm false false v' w' u' b' x' z') (-conj C) ∧
      HasSum (bJointTerm false false v' w' u' b' (-x') z') (conj C) := by
  let ξ := Complex.sqrt ((1 - y) / y)
  obtain ⟨ha, hb⟩ := hhbb_actual_complex_sewing_of_states u v w b hx hy hre
    (ξ := ξ) (sqrt_square _)
  have hroot : conj (Complex.sqrt y) = Complex.sqrt (conj y) := by
    apply sqrt_conj_of_arg_ne_pi
    rw [ne_eq, Complex.arg_eq_pi_iff, Complex.conj_im]
    exact fun h => (ne_of_lt (neg_neg_of_pos him)) h.2
  have hξ : conj ξ = Complex.sqrt ((1 - conj y) / conj y) := by
    have hy₀ : y ≠ 0 := fun h => by simp [h] at him
    have hratio : (1 - y) / y = y⁻¹ - 1 := by
      rw [sub_div, div_self hy₀, one_div]
    have himInv : ((1 - y) / y).im ≠ 0 := by
      rw [hratio, Complex.sub_im, Complex.one_im, sub_zero, Complex.inv_im]
      exact div_ne_zero (neg_ne_zero.mpr (ne_of_gt him)) (fun h => hy₀ (Complex.normSq_eq_zero.mp h))
    have harg : (conj ((1 - y) / y)).arg ≠ Real.pi := by
      rw [ne_eq, Complex.arg_eq_pi_iff, Complex.conj_im]
      exact fun h => (neg_ne_zero.mpr himInv) h.2
    simpa only [map_div₀, map_sub, map_one] using sqrt_conj_of_arg_ne_pi harg
  have ha' := Complex.hasSum_conj'.mpr ha
  have hb' := Complex.hasSum_conj'.mpr hb
  dsimp only at ha' hb' ⊢
  simp only [aJointTerm_conj, bJointTerm_conj, map_mul, hroot, hξ, map_neg] at ha' hb'
  refine ⟨by rw [Complex.conj_im]; exact neg_neg_of_pos him, ?_, ?_, ?_⟩
  · simpa only [neg_neg] using ha'.neg
  · simpa only [neg_neg] using hb'.neg
  · exact hb'.congr_fun (fun i => bJointTerm_neg_outer _ _ _ _ _ _ i)

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBLowerReflection
