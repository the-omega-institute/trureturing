import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTNoGhostContravariant
import D5.S3.VertexAlgebra.Energy.OriginalCurrentEnergy
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualTwistedDescendantPositive
import Batteries.Tactic.OpenPrivate

/-!
The two conjugations of the actual Leech orbifold commute with the conformal
zero mode. On fixed coefficients this is reality of the charge and oscillator
energy. On twisted coefficients the reflected monomial and the ground
conjugation preserve the oscillator occupation, which determines the entire
zero-mode eigenvalue. The resulting conjugation of the native spectral weight
space gives the positive contravariant BRST form in a specified null frame.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalBRSTWeightPositive

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeGeneratingFieldLocality (Carrier)
open LatticeInvolution (fixedSpace mem_fixedSpace sigma_monomial)
open LatticePositiveEnergy (Label carrierCoeffEquiv chargeEnergy energy)
open LatticeHalfFockChargedTensorCoefficients (ActualGround ActualTensor groundRank)
open LatticeHalfFockGradedTrace (OddMonomial actualAmbientBasis actual_basis_apply
  actualTensorL0 actualTensorL0_repr oddWeight)
open LatticeTwistedGroundRealization (Half)
open MvPolynomial (coeff_monomial)
open SourceBPZ.OriginalMatterHermitian (Hm Hm_alt Hm_hermitian kappaOsc kappaOsc_coeff
  kappaCarrier kappaCarrier_add kappaCarrier_smul kappaCarrier_theta kappaCarrier_involutive)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open TwistedGround.OriginalOrbifoldConformal (L_zero_fixed_coeff L_zero_twisted)
open TwistedGround.Orbifold.ActualTwistedDescendantPositive (groundRealForm actualConjugation
  actualConjugation_tmul negativeConjugation negativeConjugation_involutive negativeHermitian
  negativeHermitian_conj_symm negativeHermitian_positive)
open OriginalOrbifoldCriticalMatter (Orbifold orbifoldMode hyperbolicData)
open OriginalOrbifoldMatterBPZ (orbifoldBPZ orbifoldBPZ_apply)
open OriginalOrbifoldRelativeQuartet (Frame UCharge exists_frame orbifoldGrade)
open OriginalOrbifoldBRSTMomentum (physicalMomentum)
open OriginalOrbifoldBRSTNoGhostPairing (physicalMomentumEquivOrbifoldGradeInFrame)
open OriginalOrbifoldBRSTContravariant (contravariantBPZ)
open OriginalOrbifoldBRSTNoGhostContravariant (contravariantBPZ_inFrame)
open LatticeRelativeMassShell (massShellCutoff)
open private original_positive from D5.S3.VertexAlgebra.Energy.OriginalCurrentEnergy

local notation "D" => leechData
local notation "hu" => (And.left (And.right leech_spec))
local notation "hpos" => (And.left (And.right (And.right leech_spec)))

private def fixedConjugation : fixedSpace D →ₗ⋆[ℂ] fixedSpace D where
  toFun x := ⟨kappaCarrier x.val, by
    rw [mem_fixedSpace, ← kappaCarrier_theta, (mem_fixedSpace D _).mp x.property]⟩
  map_add' x y := Subtype.ext (kappaCarrier_add x.val y.val)
  map_smul' c x := Subtype.ext (kappaCarrier_smul c x.val)

/-- The block conjugation for the actual fixed and negative parity submodules. -/
def orbifoldConjugation : Orbifold →ₗ⋆[ℂ] Orbifold where
  toFun x := (fixedConjugation x.1, negativeConjugation x.2)
  map_add' x y := Prod.ext (map_add fixedConjugation x.1 y.1)
    (map_add negativeConjugation x.2 y.2)
  map_smul' c x := Prod.ext (fixedConjugation.map_smulₛₗ c x.1)
    (negativeConjugation.map_smulₛₗ c x.2)

theorem orbifoldConjugation_involutive : Function.Involutive orbifoldConjugation := by
  intro x
  exact Prod.ext (Subtype.ext (kappaCarrier_involutive x.1.val))
    (negativeConjugation_involutive x.2)

private theorem carrierCoeff_kappa (x : Carrier D) (i : Label D) :
    carrierCoeffEquiv D (kappaCarrier x) i = starRingEnd ℂ (carrierCoeffEquiv D x i) := by
  change (kappaOsc (x i.1)).coeff i.2 = starRingEnd ℂ ((x i.1).coeff i.2)
  exact kappaOsc_coeff _ _

/-- Coefficient conjugation fixes the charge label and commutes with its real energy. -/
theorem orbifoldConjugation_L0_fixed (x : Orbifold) :
    (orbifoldConjugation (orbifoldMode 0 x)).1.val =
      (orbifoldMode 0 (orbifoldConjugation x)).1.val := by
  change kappaCarrier (orbifoldMode 0 x).1.val = _
  apply (carrierCoeffEquiv D).injective
  apply Finsupp.ext
  intro i
  rw [carrierCoeff_kappa]
  simp only [orbifoldMode, L_zero_fixed_coeff]
  change _ = (energy D i : ℂ) * carrierCoeffEquiv D (kappaCarrier x.1.val) i
  rw [carrierCoeff_kappa, map_mul, map_intCast]

private def twistedEigenvalue (d : OddMonomial D) : ℂ :=
  (leechData.rank : ℂ) / 16 + (oddWeight D d : ℂ) / 2

private theorem twistedEigenvalue_star (d : OddMonomial D) :
    starRingEnd ℂ (twistedEigenvalue d) = twistedEigenvalue d := by
  simp only [twistedEigenvalue, map_add, map_div₀, map_natCast, map_ofNat]

private theorem actualConjugation_monomial_tmul (d : OddMonomial D) (u : ActualGround D hu) :
    actualConjugation (MvPolynomial.monomial d (1 : ℂ) ⊗ₜ[ℂ] u) =
      (-1 : ℂ) ^ (LatticeAllStateField.occurrences D d).length •
        (MvPolynomial.monomial d (1 : ℂ) ⊗ₜ[ℂ] groundRealForm.conjugation u) := by
  have hk : kappaOsc (MvPolynomial.monomial d (1 : ℂ)) =
      MvPolynomial.monomial d 1 := by
    simp [kappaOsc, MvPolynomial.map_monomial]
  rw [actualConjugation_tmul, hk, sigma_monomial, ← TensorProduct.smul_tmul']

/-- Every ground vector at a fixed oscillator occupation has the same eigenvalue. -/
private theorem twistedMonomialL0 (d : OddMonomial D) (u : ActualGround D hu) :
    actualTensorL0 D hu (MvPolynomial.monomial d (1 : ℂ) ⊗ₜ[ℂ] u) =
      twistedEigenvalue d • (MvPolynomial.monomial d (1 : ℂ) ⊗ₜ[ℂ] u) := by
  classical
  apply (actualAmbientBasis D hu).ext_elem_iff.mpr
  rintro ⟨e, b⟩
  simp only [actualTensorL0_repr, map_smul, Finsupp.smul_apply, smul_eq_mul, twistedEigenvalue]
  by_cases h : d = e
  · subst e
    rfl
  · have hcoeff : (actualAmbientBasis D hu).repr
        (MvPolynomial.monomial d (1 : ℂ) ⊗ₜ[ℂ] u) (e, b) = 0 := by
      rw [actualAmbientBasis, Module.Basis.tensorProduct_repr_tmul_apply]
      change (Pi.basisFun ℂ (Half (groundRank D hu))).repr u b •
        (MvPolynomial.monomial d (1 : ℂ)).coeff e = 0
      rw [coeff_monomial, ite_eq_right h, smul_zero]
    rw [hcoeff, mul_zero, mul_zero]

private theorem actualConjugation_tensorL0 (v : ActualTensor D hu) :
    actualConjugation (actualTensorL0 D hu v) = actualTensorL0 D hu (actualConjugation v) := by
  have h : LinearMap.comp actualConjugation (actualTensorL0 D hu) =
      LinearMap.comp (actualTensorL0 D hu) actualConjugation := by
    apply (actualAmbientBasis D hu).ext
    rintro ⟨d, b⟩
    simp only [LinearMap.comp_apply, actual_basis_apply]
    rw [twistedMonomialL0, actualConjugation.map_smulₛₗ, twistedEigenvalue_star,
      actualConjugation_monomial_tmul, map_smul, twistedMonomialL0, smul_comm]
  exact LinearMap.congr_fun h v

/-- The twisted conjugation commutes with the actual negative-block zero mode. -/
theorem orbifoldConjugation_L0_twisted (x : Orbifold) :
    (orbifoldConjugation (orbifoldMode 0 x)).2.val =
      (orbifoldMode 0 (orbifoldConjugation x)).2.val := by
  change actualConjugation (orbifoldMode 0 x).2.val = _
  simp only [orbifoldMode, L_zero_twisted]
  exact actualConjugation_tensorL0 x.2.val

theorem orbifoldConjugation_commutes_L0 (x : Orbifold) :
    orbifoldConjugation (orbifoldMode 0 x) = orbifoldMode 0 (orbifoldConjugation x) :=
  Prod.ext (Subtype.ext (orbifoldConjugation_L0_fixed x))
    (Subtype.ext (orbifoldConjugation_L0_twisted x))

theorem orbifoldConjugation_mem_grade (n : ℕ) (x : Orbifold) (hx : x ∈ orbifoldGrade n) :
    orbifoldConjugation x ∈ orbifoldGrade n := by
  have he : orbifoldMode 0 x = (n : ℂ) • x := Module.End.mem_eigenspace_iff.mp hx
  apply Module.End.mem_eigenspace_iff.mpr
  rw [← orbifoldConjugation_commutes_L0, he, orbifoldConjugation.map_smulₛₗ, map_natCast]

/-- The spectral restriction used at `massShellCutoff hyperbolicData a`. -/
def gradeConjugation (n : ℕ) : orbifoldGrade n →ₗ⋆[ℂ] orbifoldGrade n :=
  orbifoldConjugation.restrict (orbifoldConjugation_mem_grade n)

theorem gradeConjugation_involutive (n : ℕ) : Function.Involutive (gradeConjugation n) :=
  fun x => Subtype.ext (orbifoldConjugation_involutive (x : Orbifold))

/-- The original block-diagonal BPZ form with conjugation in its first slot. -/
def orbifoldHermitian : Orbifold →ₗ⋆[ℂ] Orbifold →ₗ[ℂ] ℂ :=
  LinearMap.comp orbifoldBPZ orbifoldConjugation

theorem orbifoldHermitian_apply (x y : Orbifold) :
    orbifoldHermitian x y = Hm x.1.val y.1.val + negativeHermitian x.2 y.2 := by
  change orbifoldBPZ (orbifoldConjugation x) y = _
  rw [orbifoldBPZ_apply]
  change sourcePairing D (kappaCarrier x.1.val) y.1.val + negativeHermitian x.2 y.2 = _
  rw [Hm_alt, (mem_fixedSpace D _).mp y.1.property]

theorem orbifoldHermitian_conj_symm (x y : Orbifold) :
    star (orbifoldHermitian x y) = orbifoldHermitian y x := by
  simp only [orbifoldHermitian_apply, star_add, negativeHermitian_conj_symm]
  exact congrArg (fun z : ℂ => z + negativeHermitian y.2 x.2)
    (Hm_hermitian y.1.val x.1.val).symm

theorem orbifoldHermitian_positive (x : Orbifold) (hx : x ≠ 0) :
    (orbifoldHermitian x x).im = 0 ∧ 0 < (orbifoldHermitian x x).re := by
  refine ⟨Complex.conj_eq_iff_im.mp (orbifoldHermitian_conj_symm x x), ?_⟩
  rw [orbifoldHermitian_apply, Complex.add_re]
  by_cases hf : x.1 = 0
  · have hn : x.2 ≠ 0 := fun h => hx (Prod.ext hf h)
    have hz : Hm x.1.val x.1.val = 0 := by
      simp [hf, Hm]
    rw [hz, Complex.zero_re, zero_add]
    exact (negativeHermitian_positive _ hn).2
  · refine add_pos_of_pos_of_nonneg
      (original_positive hpos (fun h => hf (Subtype.ext h))).2 ?_
    by_cases hn : x.2 = 0
    · simp [hn]
    · exact (negativeHermitian_positive _ hn).2.le

section Physical

set_option backward.isDefEq.respectTransparency true

variable (F : Frame) (a : UCharge) (hp : F.pPlus a ≠ 0)
  (ha : chargeEnergy hyperbolicData a ≤ 1)

local notation "shellGrade" => massShellCutoff hyperbolicData
local notation "shellEquiv" => physicalMomentumEquivOrbifoldGradeInFrame

/-- The native degree-one conjugation induced by the specified normalized null frame. -/
def physicalConjugationInFrame : physicalMomentum a →ₗ⋆[ℂ] physicalMomentum a :=
  let e := shellEquiv F a hp ha
  e.symm.toLinearMap.comp ((gradeConjugation (shellGrade a)).comp e.toLinearMap)

theorem physicalConjugationInFrame_involutive :
    Function.Involutive (physicalConjugationInFrame F a hp ha) := by
  intro x
  simp only [physicalConjugationInFrame, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  let e := shellEquiv F a hp ha
  exact (congrArg (fun u : orbifoldGrade (shellGrade a) => e.symm u)
    (gradeConjugation_involutive (shellGrade a) (e x))).trans (e.symm_apply_apply x)

/-- The exact contravariant BPZ form on the physical quotient with its first slot conjugated. -/
def physicalHermitianInFrame : physicalMomentum a →ₗ⋆[ℂ] physicalMomentum a →ₗ[ℂ] ℂ :=
  LinearMap.comp (contravariantBPZ.restrict (physicalMomentum a))
    (physicalConjugationInFrame F a hp ha)

theorem physicalHermitianInFrame_apply (x y : physicalMomentum a) :
    physicalHermitianInFrame F a hp ha x y =
      contravariantBPZ (physicalConjugationInFrame F a hp ha x).val y.val := rfl

theorem physicalHermitianInFrame_eq_orbifold (x y : physicalMomentum a) :
    physicalHermitianInFrame F a hp ha x y =
      orbifoldHermitian (shellEquiv F a hp ha x) (shellEquiv F a hp ha y) := by
  let e := shellEquiv F a hp ha
  let u := gradeConjugation (shellGrade a) (e x)
  let b (z : physicalMomentum a) : ℂ := contravariantBPZ (e.symm u).val z.val
  have h : b (e.symm (e y)) = orbifoldHermitian (e x) (e y) :=
    contravariantBPZ_inFrame F a hp ha u (e y)
  exact (congrArg b (e.symm_apply_apply y)).symm.trans h

theorem physicalHermitianInFrame_conj_symm (x y : physicalMomentum a) :
    star (physicalHermitianInFrame F a hp ha x y) = physicalHermitianInFrame F a hp ha y x := by
  let e := shellEquiv F a hp ha
  calc
    _ = star (orbifoldHermitian (e x) (e y)) :=
      congrArg (star : ℂ → ℂ) (physicalHermitianInFrame_eq_orbifold F a hp ha x y)
    _ = orbifoldHermitian (e y) (e x) := orbifoldHermitian_conj_symm _ _
    _ = _ := (physicalHermitianInFrame_eq_orbifold F a hp ha y x).symm

theorem physicalHermitianInFrame_positive (x : physicalMomentum a) (hx : x ≠ 0) :
    (physicalHermitianInFrame F a hp ha x x).im = 0 ∧
      0 < (physicalHermitianInFrame F a hp ha x x).re := by
  let e := shellEquiv F a hp ha
  have hx' : ((e x : orbifoldGrade (shellGrade a)) : Orbifold) ≠ 0 := by
    intro h
    have he : e x = (0 : orbifoldGrade (shellGrade a)) := Subtype.ext h
    exact hx (e.injective (he.trans e.map_zero.symm))
  rw [physicalHermitianInFrame_eq_orbifold F a hp ha x x]
  exact orbifoldHermitian_positive (e x) hx'

end Physical

set_option backward.isDefEq.respectTransparency true in
/-- For each nonzero charge on the exact shell, instantiate the form with a
normalized native frame satisfying the nonvanishing light-cone condition. -/
theorem exists_positivePhysicalHermitian (a : UCharge) (ha0 : a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) :
    ∃ (F : Frame) (hp : F.pPlus a ≠ 0),
      Function.Involutive (physicalConjugationInFrame F a hp ha) ∧
      (∀ x y : physicalMomentum a,
        star (physicalHermitianInFrame F a hp ha x y) = physicalHermitianInFrame F a hp ha y x) ∧
      ∀ x : physicalMomentum a, x ≠ 0 →
        (physicalHermitianInFrame F a hp ha x x).im = 0 ∧
          0 < (physicalHermitianInFrame F a hp ha x x).re := by
  have hFrame : ∃ F : Frame, F.pPlus a ≠ 0 := exists_frame a ha0
  exact hFrame.elim (fun F hp =>
    ⟨F, hp, physicalConjugationInFrame_involutive F a hp ha,
      physicalHermitianInFrame_conj_symm F a hp ha, physicalHermitianInFrame_positive F a hp ha⟩)

#print axioms orbifoldConjugation_commutes_L0
#print axioms orbifoldConjugation_mem_grade
#print axioms orbifoldHermitian_positive
#print axioms physicalHermitianInFrame_apply
#print axioms physicalHermitianInFrame_eq_orbifold
#print axioms exists_positivePhysicalHermitian

end D5.S3.VertexAlgebra.OriginalBRSTWeightPositive
