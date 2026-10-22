/- GID: D5/S3/VertexAlgebra/LatticeHalfFockCurrentSeed
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockCurrentSeed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial multiplication in the original charged correction field. -/

import D5.S3.VertexAlgebra.LatticeHalfFockAllStateCurrentCommutator

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCurrentSeed

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open LatticeHalfFockFiniteCorrection LatticeHalfFockCurrentCorrection
open LatticeHalfFockFockNormalField LatticeHalfFockAllStateField
open LatticeHalfFockCurrentNormalRecurrence LatticeHalfFockNormalCurrentAction
open LatticeHalfFockChargedTensorCoefficients MvPolynomial
open scoped BigOperators

noncomputable section

def evaluatePolynomial (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) : Polynomial (Oscillator D) →ₗ[ℂ] NativeField D hu :=
  (Finsupp.lsum ℂ (fun shift : ℕ =>
    (shiftLinear D hu shift).comp (normalPolynomial D hu charge))).comp
      (shiftCoefficients D)

def evaluateCorrection (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) : CorrectionPolynomial D →ₗ[ℂ] NativeField D hu :=
  (evaluatePolynomial D hu charge).comp (optionEquivLeft ℂ (Index D)).toLinearMap

private theorem evaluate_lift (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (polynomial : Oscillator D) :
    evaluateCorrection D hu charge (correctionLift D charge polynomial) =
      correctedPolynomial D hu charge polynomial := rfl

private theorem shiftLinear_add (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : ℕ) (field : NativeField D hu) :
    shiftLinear D hu first (shiftLinear D hu second field) =
      shiftLinear D hu (first + second) field := by
  apply HVertexOperator.coeff_inj
  ext exponent vector
  simp only [shiftLinear, shiftField, LinearMap.coe_mk, AddHom.coe_mk,
    HVertexOperator.coeff_of_coeff, Nat.cast_add]
  congr 1
  ring

theorem evaluate_monomial (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (degree : ℕ) (polynomial : Oscillator D) :
    evaluatePolynomial D hu charge (Polynomial.monomial degree polynomial) =
      shiftLinear D hu degree (normalPolynomial D hu charge polynomial) := by
  simp [evaluatePolynomial, shiftCoefficients]

private theorem evaluate_shift (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (degree : ℕ) (polynomial : Polynomial (Oscillator D)) :
    evaluatePolynomial D hu charge (polynomial * Polynomial.X ^ degree) =
      shiftLinear D hu degree (evaluatePolynomial D hu charge polynomial) := by
  induction polynomial using Polynomial.induction_on' with
  | add first second firstProof secondProof =>
    simp only [add_mul, map_add, firstProof, secondProof]
  | monomial shift coefficient =>
    rw [← Polynomial.monomial_one_right_eq_X_pow, Polynomial.monomial_mul_monomial,
      mul_one, evaluate_monomial, evaluate_monomial, shiftLinear_add, Nat.add_comm]

theorem normalInsertion_shift (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (degree : ℕ) (field : NativeField D hu) :
    normalInsertionLinear D hu index (shiftLinear D hu degree field) =
      shiftLinear D hu degree (normalInsertionLinear D hu index field) := by
  exact normalInsertion_coverShift D hu index field (2 * degree)

theorem evaluate_source_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (polynomial : Polynomial (Oscillator D)) :
    evaluatePolynomial D hu charge (polynomial * Polynomial.C (X index)) =
      normalInsertionLinear D hu index (evaluatePolynomial D hu charge polynomial) := by
  induction polynomial using Polynomial.induction_on' with
  | add first second firstProof secondProof =>
    simp only [add_mul, map_add, firstProof, secondProof]
  | monomial shift coefficient =>
    rw [Polynomial.monomial_mul_C, evaluate_monomial, evaluate_monomial,
      normalPolynomial_X_mul, normalInsertion_shift]

theorem evaluate_shift_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (scalar : ℂ) (degree : ℕ) (polynomial : CorrectionPolynomial D) :
    evaluateCorrection D hu charge (C scalar * X none ^ degree * polynomial) =
      scalar • shiftLinear D hu degree (evaluateCorrection D hu charge polynomial) := by
  have scale : C scalar * X none ^ degree * polynomial =
      scalar • (polynomial * X none ^ degree) := by
    rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    ring
  rw [scale, map_smul]
  simp only [evaluateCorrection, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    map_mul, map_pow, optionEquivLeft_X_none]
  rw [evaluate_shift]

private theorem derivative_support {σ : Type*} (polynomial : MvPolynomial σ ℂ)
    (factor : σ → MvPolynomial σ ℂ) :
    Function.HasFiniteSupport (fun index => factor index * pderiv index polynomial) := by
  classical
  apply polynomial.vars.finite_toSet.subset
  intro index nonzero
  by_contra outside
  exact nonzero (by simp [pderiv_eq_zero_of_notMem_vars outside])

private theorem derivation_expansion {σ : Type*} (polynomial : MvPolynomial σ ℂ)
    (factor : σ → MvPolynomial σ ℂ) :
    mkDerivation ℂ factor polynomial =
      ∑ᶠ index, factor index * pderiv index polynomial := by
  classical
  have sum_apply (indices : Finset σ) (argument : MvPolynomial σ ℂ) :
      (∑ index ∈ indices, factor index • pderiv index) argument =
        ∑ index ∈ indices, factor index * pderiv index argument := by
    induction indices using Finset.induction_on with
    | empty => simp [Derivation.zero_apply]
    | @insert index indices outside previous =>
      simp [outside, Derivation.add_apply, Derivation.smul_apply, previous, smul_eq_mul]
  have equal : mkDerivation ℂ factor polynomial =
      (∑ index ∈ polynomial.vars, factor index • pderiv index) polynomial := by
    apply derivation_eq_of_forall_mem_vars
    intro coordinate member
    rw [mkDerivation_X, sum_apply]
    simp [pderiv_X, Pi.single_apply, member]
  rw [equal, sum_apply]
  symm
  apply finsum_eq_sum_of_support_subset
  intro index nonzero
  by_contra outside
  exact nonzero (by simp [pderiv_eq_zero_of_notMem_vars outside])

private theorem pairDerivation_expansion (D : LatticeData) (index : Index D)
    (polynomial : CorrectionPolynomial D) :
    pairDerivation D index polynomial = ∑ᶠ other : Index D,
      pairPolynomial D index other * pderiv (some other) polynomial := by
  rw [pairDerivation, derivation_expansion]
  have finite := (derivative_support polynomial
    (fun coordinate : Option (Index D) => coordinate.elim 0 (pairPolynomial D index))).comp_of_injective
      (Option.some_injective (Index D))
  rw [finsum_option finite]
  simp

private theorem lifted_pair_support (D : LatticeData) (charge : Charge D)
    (index : Index D) (polynomial : Oscillator D) :
    Function.HasFiniteSupport (fun other : Index D => pairPolynomial D index other *
      correctionLift D charge (pderiv other polynomial)) := by
  classical
  apply polynomial.vars.finite_toSet.subset
  intro other nonzero
  by_contra outside
  exact nonzero (by simp [pderiv_eq_zero_of_notMem_vars outside])

theorem correctedPolynomial_X_mul (D : LatticeData) (hu : IsUnit D.G.det)
    (charge : Charge D) (index : Index D) (polynomial : Oscillator D) :
    correctedPolynomial D hu charge (polynomial * X index) =
      normalInsertionLinear D hu index (correctedPolynomial D hu charge polynomial) +
        (halfBinomial (sourceWeight D index) *
          (bilinear D (unitCharge D index.1) charge : ℂ)) •
          shiftLinear D hu (sourceWeight D index) (correctedPolynomial D hu charge polynomial) +
        ∑ᶠ other : Index D,
          (pairScalar (sourceWeight D index) (sourceWeight D other) *
            (D.G index.1 other.1 : ℂ)) •
              shiftLinear D hu (sourceWeight D index + sourceWeight D other)
                (correctedPolynomial D hu charge (pderiv other polynomial)) := by
  rw [← evaluate_lift, correctionLift_X_mul]
  simp only [insertion, LinearMap.add_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, add_mul, map_add]
  have source : evaluateCorrection D hu charge
      (X (some index) * correctionLift D charge polynomial) =
      normalInsertionLinear D hu index (correctedPolynomial D hu charge polynomial) := by
    simp only [evaluateCorrection, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      map_mul, optionEquivLeft_X_some]
    rw [mul_comm, evaluate_source_mul]
    rfl
  rw [source, singletonPolynomial, evaluate_shift_mul, evaluate_lift,
    pairDerivation_expansion]
  simp_rw [correctionLift_partial]
  have mapped : evaluateCorrection D hu charge (∑ᶠ other : Index D,
      pairPolynomial D index other * correctionLift D charge (pderiv other polynomial)) =
      ∑ᶠ other : Index D, evaluateCorrection D hu charge
        (pairPolynomial D index other * correctionLift D charge (pderiv other polynomial)) :=
    (evaluateCorrection D hu charge).toAddMonoidHom.map_finsum
      (lifted_pair_support D charge index polynomial)
  rw [mapped]
  apply congrArg (fun field =>
    normalInsertionLinear D hu index (correctedPolynomial D hu charge polynomial) +
      (halfBinomial (sourceWeight D index) *
        (bilinear D (unitCharge D index.1) charge : ℂ)) •
        shiftLinear D hu (sourceWeight D index) (correctedPolynomial D hu charge polynomial) +
      field)
  apply finsum_congr
  intro other
  rw [pairPolynomial, evaluate_shift_mul, evaluate_lift]

end
end D5.S3.VertexAlgebra.LatticeHalfFockCurrentSeed

#print axioms D5.S3.VertexAlgebra.LatticeHalfFockCurrentSeed.correctedPolynomial_X_mul
