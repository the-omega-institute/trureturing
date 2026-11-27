import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFullEnergySpectrum
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeVirasoro

/-!
The normalized grading rotation on the full P48q cubic twisted Fock space.
The energy Ward identity controls its phase on each native fractional mode.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeGradingRotation

open HalfFockSpectralFiberSource (actualInverse)
open LatticeSugawaraCurrents (sugawaraMode)
open NativeStandardThirdLift (standardLift)
open P48qAllJetWickField (NativeStates nativeField)
open P48qFullEnergySpectrum (momentumWeight_eq_nat_div_three totalLZero_exact_eigenvalues)
open P48qNativeCurrentLocality (nativeField_inResidue)
open P48qNativeVirasoro (native_LZero_ward)
open P48qThirdTwistedField (Mode State)
open P48qTwistedChargeAction (Momentum lattice g g_cube g_isometry)
open P48qTwistedStateEnergy (Occupation occupationFrequency totalWeight
  totalLZero totalLZero_coeff totalLZero_single_monomial)
open MvPolynomial

noncomputable section

local notation "σ" => standardLift lattice g g_cube g_isometry
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "C" => HVertexOperator.coeff

private theorem zetaPrimitive : IsPrimitiveRoot ζ 3 :=
  IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive

/-- Three times the energy above the twisted vacuum, on a joint basis vector. -/
def gradingIndex (p : Momentum) (d : Occupation) : ℕ :=
  occupationFrequency d + (momentumWeight_eq_nat_div_three p).choose

theorem totalWeight_eq_gradingIndex (p : Momentum) (d : Occupation) :
    (totalWeight p d : ℂ) = 16 / 9 + (gradingIndex p d : ℂ) / 3 := by
  have h : totalWeight p d = 16 / 9 + (gradingIndex p d : ℝ) / 3 := by
    rw [totalWeight, (momentumWeight_eq_nat_div_three p).choose_spec,
      gradingIndex, Nat.cast_add]
    ring
  simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_natCast] using congrArg (fun x : ℝ => (x : ℂ)) h

private def stateRepr : State ≃ₗ[ℂ] (Momentum × Occupation →₀ ℂ) :=
  (Finsupp.mapRange.linearEquiv (basisMonomials Mode ℂ).repr).trans
    (Finsupp.curryLinearEquiv ℂ).symm

private theorem stateRepr_apply (v : State) (p : Momentum) (d : Occupation) :
    stateRepr v (p, d) = (v p).coeff d := rfl

private def rotateCoefficients : Module.End ℂ (Momentum × Occupation →₀ ℂ) :=
  Finsupp.lsum ℂ fun i => (ζ ^ gradingIndex i.1 i.2) • Finsupp.lsingle i

private theorem rotateCoefficients_apply (v : Momentum × Occupation →₀ ℂ)
    (i : Momentum × Occupation) :
    rotateCoefficients v i = ζ ^ gradingIndex i.1 i.2 * v i := by
  classical
  have h : (Finsupp.lapply i).comp rotateCoefficients =
      (ζ ^ gradingIndex i.1 i.2) • (Finsupp.lapply i : (_ →₀ ℂ) →ₗ[ℂ] ℂ) := by
    apply Finsupp.lhom_ext
    intro j c
    simp only [LinearMap.comp_apply, rotateCoefficients, Finsupp.lsum_single,
      LinearMap.smul_apply, Finsupp.lsingle_apply, Finsupp.lapply_apply, Finsupp.smul_apply]
    by_cases h : i = j
    · subst j
      rfl
    · simp only [Finsupp.single_eq_of_ne h, smul_zero]
  exact DFunLike.congr_fun h v

/-- The internal rotation that scales each joint coefficient by `ζ ^ gradingIndex p d`. -/
def gradingRotation : Module.End ℂ State :=
  stateRepr.symm.conj rotateCoefficients

theorem gradingRotation_coeff (v : State) (p : Momentum) (d : Occupation) :
    (gradingRotation v p).coeff d = ζ ^ gradingIndex p d * (v p).coeff d := by
  rw [← stateRepr_apply, gradingRotation, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, rotateCoefficients_apply, stateRepr_apply]

private theorem gradingRotation_single_monomial (p : Momentum) (d : Occupation) (c : ℂ) :
    gradingRotation (Finsupp.single p (monomial d c)) =
      (ζ ^ gradingIndex p d) • Finsupp.single p (monomial d c) := by
  classical
  apply Finsupp.ext
  intro p'
  apply MvPolynomial.ext
  intro d'
  simp only [gradingRotation_coeff, Finsupp.smul_apply, coeff_smul, smul_eq_mul]
  by_cases hp : p' = p
  · subst p'
    rw [Finsupp.single_eq_same]
    by_cases hd : d = d'
    · subst d'
      rfl
    · simp only [coeff_monomial, ite_eq_right hd, mul_zero]
  · simp only [Finsupp.single_eq_of_ne hp, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply, mul_zero]

theorem gradingRotation_cube : gradingRotation ^ 3 = 1 := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro p
  apply MvPolynomial.ext
  intro d
  rw [pow_succ, pow_succ, pow_one]
  simp only [Module.End.mul_apply, Module.End.one_apply, gradingRotation_coeff]
  have hc : (ζ ^ gradingIndex p d) ^ (3 : ℕ) = 1 := by
    rw [pow_right_comm, zetaPrimitive.pow_eq_one, one_pow]
  linear_combination (v p).coeff d * hc

/-- The rotation is nontrivial since the energy `16 / 9 + 1 / 3` occurs. -/
theorem gradingRotation_ne_one : gradingRotation ≠ 1 := by
  intro h
  have henergy : ∃ v : State, v ≠ 0 ∧ totalLZero v = (16 / 9 + (1 : ℂ) / 3) • v :=
    (totalLZero_exact_eigenvalues _).mpr ⟨1, by rw [Nat.cast_one]⟩
  obtain ⟨v, hv, heig⟩ := henergy
  obtain ⟨p, d, hcoeff⟩ : ∃ (p : Momentum) (d : Occupation), (v p).coeff d ≠ 0 := by
    by_contra! hzero
    apply hv
    apply Finsupp.ext
    intro p
    apply MvPolynomial.ext
    intro d
    simpa using hzero p d
  have hw := congrArg (fun w : State => (w p).coeff d) heig
  simp only [totalLZero_coeff, totalWeight_eq_gradingIndex, Finsupp.smul_apply,
    coeff_smul, smul_eq_mul] at hw
  have hindex : (gradingIndex p d : ℂ) = (1 : ℂ) := by
    have := mul_right_cancel₀ hcoeff hw
    linear_combination 3 * this
  have hindexNat : gradingIndex p d = 1 := by exact_mod_cast hindex
  have hrot := congrArg (fun R : Module.End ℂ State => (R v p).coeff d) h
  simp only [gradingRotation_coeff, hindexNat, pow_one, Module.End.one_apply] at hrot
  have hz : ζ ^ (1 : ℕ) = 1 := by
    rw [pow_one]
    exact mul_right_cancel₀ hcoeff (hrot.trans (one_mul _).symm)
  exact (by decide : ¬ (3 : ℕ) ∣ 1) ((zetaPrimitive.pow_eq_one_iff_dvd 1).mp hz)

theorem gradingRotation_orderOf : orderOf gradingRotation = 3 := by
  exact orderOf_eq_prime (hp := ⟨by decide⟩) gradingRotation_cube gradingRotation_ne_one

private theorem nativeMode_grading_shift (a : NativeStates)
    (s : ℤ) (ha : σ a = ζ ^ s • a) (q h : ℤ)
    (hh : sugawaraMode lattice (actualInverse lattice) 0 a = (h : ℂ) • a)
    (p p' : Momentum) (d d' : Occupation)
    (hc : ((C (nativeField a) (s - 3 * (q + 1))
      (Finsupp.single p (monomial d 1))) p').coeff d' ≠ 0) :
    (gradingIndex p' d' : ℤ) - (gradingIndex p d : ℤ) = 3 * (h - q - 1) + s := by
  let B := C (nativeField a) (s - 3 * (q + 1))
  let v : State := Finsupp.single p (monomial d 1)
  have hward := native_LZero_ward a s ha q
  change totalLZero * B - B * totalLZero =
    C (nativeField (sugawaraMode lattice (actualInverse lattice) 0 a)) (s - 3 * (q + 1)) -
      ((q : ℂ) - (s : ℂ) / 3 + 1) • B at hward
  rw [hh, map_smul, map_smul, Pi.smul_apply] at hward
  have hv : totalLZero v = (totalWeight p d : ℂ) • v :=
    totalLZero_single_monomial p d 1
  have he := DFunLike.congr_fun hward v
  change totalLZero (B v) - B (totalLZero v) =
    (h : ℂ) • B v - ((q : ℂ) - (s : ℂ) / 3 + 1) • B v at he
  rw [hv, map_smul] at he
  have hec := congrArg (fun w : State => (w p').coeff d') he
  simp only [Finsupp.sub_apply, Finsupp.smul_apply, coeff_sub, coeff_smul, smul_eq_mul,
    totalLZero_coeff, ← sub_mul] at hec
  have hw := mul_right_cancel₀ hc hec
  rw [totalWeight_eq_gradingIndex, totalWeight_eq_gradingIndex] at hw
  have hcast : (gradingIndex p' d' : ℂ) - (gradingIndex p d : ℂ) =
      3 * ((h : ℂ) - (q : ℂ) - 1) + (s : ℂ) := by
    linear_combination 3 * hw
  exact_mod_cast hcast

/-- Covariance for the physical mode `q - s / 3` of a homogeneous lift eigenstate. -/
theorem gradingRotation_nativeMode (a : NativeStates)
    (s : ℤ) (ha : σ a = ζ ^ s • a) (q h : ℤ)
    (hh : sugawaraMode lattice (actualInverse lattice) 0 a = (h : ℂ) • a) :
    let B := C (nativeField a) (s - 3 * (q + 1))
    gradingRotation * B = ζ ^ s • (B * gradingRotation) := by
  intro B
  apply Finsupp.lhom_ext'
  intro p
  apply (basisMonomials Mode ℂ).ext
  intro d
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, coe_basisMonomials,
    Module.End.mul_apply, LinearMap.smul_apply, gradingRotation_single_monomial,
    map_smul, smul_smul]
  apply Finsupp.ext
  intro p'
  apply MvPolynomial.ext
  intro d'
  simp only [gradingRotation_coeff, Finsupp.smul_apply, coeff_smul, smul_eq_mul]
  by_cases hc : ((B (Finsupp.single p (monomial d 1))) p').coeff d' = 0
  · rw [hc, mul_zero, mul_zero]
  · have hs := nativeMode_grading_shift a s ha q h hh p p' d d' hc
    have hindex : (gradingIndex p' d' : ℤ) =
        3 * (h - q - 1) + (s + (gradingIndex p d : ℤ)) := by omega
    have hm := (zetaPrimitive.zpow_eq_one_iff_dvd (3 * (h - q - 1))).mpr
      ⟨h - q - 1, rfl⟩
    have hz := Units.ne_zero ThirdTwistedChargeCocycle.zeta
    rw [← zpow_natCast ζ (gradingIndex p' d'), hindex, zpow_add₀ hz, hm, one_mul,
      zpow_add₀ hz, zpow_natCast]

/-- Covariance for every cover coefficient, including those forced to vanish by monodromy. -/
theorem gradingRotation_nativeField_coeff (a : NativeStates)
    (s : ℤ) (ha : σ a = ζ ^ s • a) (k h : ℤ)
    (hh : sugawaraMode lattice (actualInverse lattice) 0 a = (h : ℂ) • a) :
    gradingRotation * C (nativeField a) k =
      ζ ^ s • (C (nativeField a) k * gradingRotation) := by
  by_cases hk : k % 3 = s % 3
  · have hindex : k = s - 3 * (((s - k) / 3 - 1) + 1) := by omega
    rw [hindex]
    exact gradingRotation_nativeMode a s ha _ h hh
  · simp only [nativeField_inResidue a s ha k hk, mul_zero, zero_mul, smul_zero]

#print axioms gradingIndex
#print axioms totalWeight_eq_gradingIndex
#print axioms gradingRotation
#print axioms gradingRotation_coeff
#print axioms gradingRotation_cube
#print axioms gradingRotation_ne_one
#print axioms gradingRotation_orderOf
#print axioms gradingRotation_nativeMode
#print axioms gradingRotation_nativeField_coeff

run_cmd do
  for name in [``gradingIndex, ``totalWeight_eq_gradingIndex, ``gradingRotation,
      ``gradingRotation_coeff, ``gradingRotation_cube, ``gradingRotation_ne_one,
      ``gradingRotation_orderOf, ``gradingRotation_nativeMode,
      ``gradingRotation_nativeField_coeff] do
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.contains ``propext &&
        axioms.contains ``Classical.choice && axioms.contains ``Quot.sound do
      throwError "Unexpected axiom closure for {name}: {axioms}"

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeGradingRotation
