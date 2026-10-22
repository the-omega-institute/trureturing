import D5.S3.VertexAlgebra.ChargedNormalJetComparisonTransient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.ChargedCreationExponentialTransient

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open ChargedNormalJetComparisonTransient LatticeHalfFockFiniteCorrection MvPolynomial
open scoped BigOperators

noncomputable section

local instance power_series_torsion_free {Ring : Type*} [CommRing Ring]
    [IsAddTorsionFree Ring] : IsAddTorsionFree (PowerSeries Ring) where
  nsmul_right_injective multiplier nonzero first second equal := by
    apply PowerSeries.ext
    intro degree
    exact (smul_right_inj nonzero).mp
      (by simpa only [map_nsmul] using congrArg (PowerSeries.coeff degree) equal)

local macro "solution_unique_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.solution_unique))

def formalExp {Ring : Type*} [CommRing Ring] [Algebra ℚ Ring]
    (series : PowerSeries Ring) : PowerSeries Ring :=
  (PowerSeries.exp Ring).subst series

private theorem formal_exp_constant {Ring : Type*} [CommRing Ring] [Algebra ℚ Ring]
    (series : PowerSeries Ring) (zero : PowerSeries.constantCoeff series = 0) :
    PowerSeries.coeff 0 (formalExp series) = 1 := by
  rw [formalExp, PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' zero), finsum_eq_single _ 0]
  · simp
  · intro degree nonzero
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, zero]
    simp [nonzero]

private theorem formal_exp_derivative {Ring : Type*} [CommRing Ring] [Algebra ℚ Ring]
    (series : PowerSeries Ring) (zero : PowerSeries.constantCoeff series = 0) :
    PowerSeries.derivative Ring (formalExp series) =
      formalExp series * PowerSeries.derivative Ring series := by
  rw [formalExp, PowerSeries.derivative_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero' zero), PowerSeries.derivative_exp]

theorem formal_exp_add {Ring : Type*} [CommRing Ring] [Algebra ℚ Ring]
    [IsAddTorsionFree Ring] (first second : PowerSeries Ring)
    (firstZero : PowerSeries.constantCoeff first = 0)
    (secondZero : PowerSeries.constantCoeff second = 0) :
    formalExp (first + second) = formalExp first * formalExp second := by
  apply solution_unique_supplier _ _ (PowerSeries.derivative Ring (first + second))
  · exact formal_exp_derivative _ (by simp [firstZero, secondZero])
  · rw [(PowerSeries.derivative Ring).leibniz,
      formal_exp_derivative first firstZero, formal_exp_derivative second secondZero,
      map_add]
    simp only [smul_eq_mul]
    ring
  · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
    simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [formal_exp_constant first firstZero, formal_exp_constant second secondZero,
      formal_exp_constant (first + second) (by simp [firstZero, secondZero]), one_mul]

private theorem formal_exp_rescale {Ring : Type*} [CommRing Ring] [Algebra ℚ Ring]
    (series : PowerSeries Ring) (zero : PowerSeries.constantCoeff series = 0)
    (scalar : Ring) :
    PowerSeries.rescale scalar (formalExp series) =
      formalExp (PowerSeries.rescale scalar series) := by
  simpa only [formalExp, PowerSeries.rescale_eq_subst] using
    PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero' zero)
      (PowerSeries.HasSubst.smul_X' scalar) (PowerSeries.exp Ring)

private theorem half_creation_log_zero (D : LatticeData) (charge : Charge D) :
    PowerSeries.constantCoeff (halfCreationSeries D charge) = 0 := by
  simp [halfCreationSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]

private theorem lift_log_zero (D : LatticeData) (charge : Charge D) :
    PowerSeries.constantCoeff (originalCreationLogLift D charge) = 0 := by
  simp [originalCreationLogLift, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    halfCreationSeries]

private theorem half_creation_log_add (D : LatticeData) (first second : Charge D) :
    halfCreationSeries D (first + second) =
      halfCreationSeries D first + halfCreationSeries D second := by
  apply PowerSeries.ext
  intro degree
  simp only [halfCreationSeries, PowerSeries.coeff_mk, map_add]
  split_ifs with odd
  · simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib, smul_add]
  · simp

def originalCreationExpLift (D : LatticeData) (charge : Charge D) :
    PowerSeries (PowerSeries (Oscillator D)) :=
  PowerSeries.map (PowerSeries.C : Oscillator D →+* PowerSeries (Oscillator D))
    (halfCreationExponential D charge)

private theorem creation_exp_lift (D : LatticeData) (charge : Charge D) :
    originalCreationExpLift D charge = formalExp (originalCreationLogLift D charge) := by
  have mapped := PowerSeries.map_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero' (half_creation_log_zero D charge))
    (h := (PowerSeries.C : Oscillator D →+* PowerSeries (Oscillator D)))
    (PowerSeries.exp (Oscillator D))
  change PowerSeries.map PowerSeries.C
      ((PowerSeries.exp (Oscillator D)).subst (halfCreationSeries D charge)) =
    PowerSeries.subst (PowerSeries.map PowerSeries.C (halfCreationSeries D charge))
    (PowerSeries.map (PowerSeries.C : Oscillator D →+* PowerSeries (Oscillator D))
      (PowerSeries.exp (Oscillator D))) at mapped
  rw [PowerSeries.map_exp] at mapped
  exact mapped

theorem actual_combined_creation_log (D : LatticeData) (first second : Charge D) :
    PowerSeries.rescale (originalCreationRoot D) (originalCreationLogLift D first) +
      originalCreationLogLift D second =
        originalCreationLogLift D (first + second) + originalCreationJetLog D first := by
  have addition : originalCreationLogLift D (first + second) =
      originalCreationLogLift D first + originalCreationLogLift D second := by
    rw [originalCreationLogLift, half_creation_log_add, map_add]
    rfl
  rw [addition, ← actual_creation_log_all_labels, originalCreationDifference]
  ring

theorem actual_creation_exponential_factorization (D : LatticeData)
    (first second : Charge D) :
    PowerSeries.rescale (originalCreationRoot D) (originalCreationExpLift D first) *
      originalCreationExpLift D second =
        originalCreationExpLift D (first + second) * formalExp (originalCreationJetLog D first) := by
  have rootZero : PowerSeries.constantCoeff
      (PowerSeries.rescale (originalCreationRoot D) (originalCreationLogLift D first)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
      pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff, lift_log_zero]
  have jetZero : PowerSeries.constantCoeff (originalCreationJetLog D first) = 0 := by
    simp [originalCreationJetLog, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [creation_exp_lift, creation_exp_lift, creation_exp_lift,
    formal_exp_rescale _ (lift_log_zero D first),
    ← formal_exp_add _ _ rootZero (lift_log_zero D second),
    actual_combined_creation_log,
    formal_exp_add _ _ (lift_log_zero D (first + second)) jetZero]

#print axioms actual_creation_exponential_factorization

theorem formal_exp_finite_coefficient {Ring : Type*} [CommRing Ring] [Algebra ℚ Ring]
    (series : PowerSeries Ring) (zero : PowerSeries.constantCoeff series = 0)
    (degree : ℕ) :
    PowerSeries.coeff degree (formalExp series) =
      ∑ exponent ∈ Finset.range (degree + 1),
        algebraMap ℚ Ring (1 / exponent.factorial) * PowerSeries.coeff degree (series ^ exponent) := by
  rw [formalExp, PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' zero)]
  rw [finsum_eq_sum_of_support_subset _ (show Function.support
      (fun exponent : ℕ => PowerSeries.coeff exponent (PowerSeries.exp Ring) •
        PowerSeries.coeff degree (series ^ exponent)) ⊆
      (Finset.range (degree + 1) : Set ℕ) from by
    intro exponent supported
    by_contra outside
    have bound : degree < exponent := by
      have := Finset.mem_range.not.mp outside
      omega
    have vanish : PowerSeries.coeff degree (series ^ exponent) = 0 :=
      PowerSeries.coeff_of_lt_order degree (lt_of_lt_of_le
        (by exact_mod_cast bound)
        (PowerSeries.le_order_pow_of_constantCoeff_eq_zero exponent zero))
    exact (Function.mem_support.mp supported) (by rw [vanish, smul_zero]))]
  apply Finset.sum_congr rfl
  intro exponent member
  rw [PowerSeries.coeff_exp, smul_eq_mul]

theorem actual_finite_creation_derivation (D : LatticeData)
    (derivation : Derivation ℂ (Oscillator D) (Oscillator D))
    (series : PowerSeries (Oscillator D)) (zero : PowerSeries.constantCoeff series = 0)
    (degree : ℕ) :
    derivation (∑ exponent ∈ Finset.range (degree + 1),
      algebraMap ℚ (Oscillator D) (1 / exponent.factorial) *
        PowerSeries.coeff degree (series ^ exponent)) =
      ∑ pair ∈ Finset.HasAntidiagonal.antidiagonal degree,
        PowerSeries.coeff pair.1 (formalExp series) *
          derivation (PowerSeries.coeff pair.2 series) := by
  rw [← formal_exp_finite_coefficient series zero]
  have law := congrArg (PowerSeries.coeff degree)
    (ActualSeriesDerivation.actual_exponential_derivation_series D derivation series zero)
  simpa only [formalExp, ActualSeriesDerivation.series_coeff, PowerSeries.coeff_mul]
    using law

#print axioms actual_finite_creation_derivation

end

end D5.S3.VertexAlgebra.ChargedCreationExponentialTransient
