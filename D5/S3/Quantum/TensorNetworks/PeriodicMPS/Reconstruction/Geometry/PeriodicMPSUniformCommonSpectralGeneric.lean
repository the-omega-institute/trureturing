/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralGeneric
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformCommonSpectralGeneric
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: A common native cofactor survives in both generic special spectral algebras. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformCommonSpectralCofactor

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformCommonSpectralRankTransport

open Matrix MvPolynomial
open PeriodicMPSUniformSpecialSpectralDomains
open PeriodicMPSUniformSpecialSpectralBases (commonCoefficients)
open PeriodicMPSUniformSpectralRadicalAlgebra (CoordinateFiber Parameters coordinate)
open UniformNativeCriticalMatrix (criticalMatrix)

open private constantMap commonCoefficients_guard witnessK_sq from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpecialSpectralDomains

noncomputable section

variable (z : Divisor)

/-- Scalar coefficients are extended to `ℂ` for the five Cartesian
coordinates of the actual native matrix. -/
def complexWitnessBase : ChartBase ℂ z →+* ℂ :=
  chartBaseEval ℂ z
    (guardedCoefficientEval ℂ z (RingHom.id ℂ) commonCoefficients
      (commonCoefficients_mem_locus ℂ z) (commonCoefficients_guard ℂ))
    (Units.mk0 3 (by norm_num)) (Units.map Complex.ofRealHom witnessK)

private theorem complexWitnessK_sq : (((witnessK : ℝ) : ℂ)) ^ 2 = 3 := by
  exact_mod_cast witnessK_sq

private def complexWitnessFiber : CoordinateFiber ((chartParameters ℂ z).map (complexWitnessBase z)) where
  d := 1
  db := 3
  e := 0
  eb := -2
  prod_eq := by norm_num [Parameters.map, chartParameters, complexWitnessBase]
  coeff_a := by
    simp [Parameters.map, chartParameters, complexWitnessBase, commonCoefficients, complexWitnessK_sq]
    norm_num
  coeff_b := by norm_num [Parameters.map, chartParameters, complexWitnessBase, commonCoefficients]
  coeff_c := by
    simp [Parameters.map, chartParameters, complexWitnessBase, commonCoefficients, complexWitnessK_sq]
    norm_num

def complexWitnessPoint : DeterminantChart ℂ z →+* ℂ :=
  determinantPoint ℂ z (complexWitnessBase z) (complexWitnessFiber z)

private theorem complexWitnessBase_constantMap (c : ℂ) :
    complexWitnessBase z (constantMap ℂ z c) = c := by
  have h : constantMap ℂ z c = chartConstant ℂ z (guardedClass ℂ z (MvPolynomial.C c)) := rfl
  rw [h]
  simp [complexWitnessBase]

private theorem complexWitnessPoint_base (c : ChartBase ℂ z) :
    complexWitnessPoint z (algebraMap (ChartBase ℂ z) (DeterminantChart ℂ z) c) =
      complexWitnessBase z c := by
  let : Algebra (ChartBase ℂ z) ℂ := (complexWitnessBase z).toAlgebra
  exact AlgHom.commutes (PeriodicMPSUniformSpectralRadicalAlgebra.coordinateLift
    (complexWitnessFiber z)) c

def chartComplexConstants : ℂ →+* DeterminantChart ℂ z :=
  (algebraMap _ _).comp (constantMap ℂ z)

def chartSlice : Fin 5 → DeterminantChart ℂ z :=
  let c := chartComplexConstants z
  let D := coordinate (chartParameters ℂ z)
  ![c (1 / 2) * (D .d + D .db),
    algebraMap (ChartBase ℂ z) (DeterminantChart ℂ z) ↑(chartK ℂ z),
    c (1 / 2) * (D .e + D .eb),
    c ((2 * Complex.I)⁻¹) * (D .d - D .db),
    c ((2 * Complex.I)⁻¹) * (D .e - D .eb)]

private theorem complexWitnessPoint_constant (c : ℂ) :
    complexWitnessPoint z (chartComplexConstants z c) = c :=
  (complexWitnessPoint_base z _).trans (complexWitnessBase_constantMap z c)

private theorem chartSlice_witness :
    complexWitnessPoint z ∘ chartSlice z = nativeWitnessSlice := by
  have hi : ((2 * Complex.I)⁻¹ : ℂ) = -Complex.I / 2 := by
    apply (mul_eq_one_iff_inv_eq₀ (mul_ne_zero (by norm_num) Complex.I_ne_zero)).mp
    ring_nf
    norm_num [Complex.I_sq]
  have hD (i : PeriodicMPSUniformSpectralRadicalAlgebra.Determinant) :
      complexWitnessPoint z (coordinate (chartParameters ℂ z) i) =
        match i with | .d => 1 | .db => 3 | .e => 0 | .eb => -2 := by
    cases i <;> simp [complexWitnessPoint, complexWitnessFiber]
  have hk : complexWitnessBase z ↑(chartK ℂ z) = (witnessK : ℝ) := by
    simp [complexWitnessBase]
  funext i
  fin_cases i <;>
    norm_num [chartSlice, nativeWitnessSlice, Function.comp_apply, complexWitnessPoint_base,
      complexWitnessPoint_constant, hD, hk, hi]

/-- The actual native matrix after the determinant-coordinate substitution. -/
def determinantChartCriticalMatrix (m : ℕ) : Matrix (Fin 10) (Fin 9) (DeterminantChart ℂ z) :=
  (criticalMatrix m).map (eval₂Hom (chartComplexConstants z) (chartSlice z))

theorem determinantChartCriticalMatrix_witness (m : ℕ) :
    (determinantChartCriticalMatrix z m).map (complexWitnessPoint z) =
      (criticalMatrix m).map (eval nativeWitnessSlice) := by
  have he : (complexWitnessPoint z).comp (eval₂Hom (chartComplexConstants z) (chartSlice z)) =
      eval nativeWitnessSlice := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, eval₂Hom_C, eval_C, complexWitnessPoint_constant]
    · intro i
      simp only [RingHom.comp_apply, eval₂Hom_X', eval_X]
      exact congrFun (chartSlice_witness z) i
  apply Matrix.ext
  intro i j
  exact DFunLike.congr_fun he (criticalMatrix m i j)

private theorem generic_cofactor_of_witness {m : ℕ} {i : Fin 10}
    (hi : eval nativeWitnessSlice ((criticalMatrix m).submatrix i.succAbove id).det ≠ 0) :
    (((determinantChartCriticalMatrix z m).submatrix i.succAbove id).map
      (determinantGenericPoint ℂ z)).det ≠ 0 := by
  apply generic_minor_ne_zero_of_eval_ne_zero ℂ z (complexWitnessPoint z)
  let f := eval nativeWitnessSlice
  have h : (((determinantChartCriticalMatrix z m).submatrix i.succAbove id).map
      (complexWitnessPoint z)) = f.mapMatrix ((criticalMatrix m).submatrix i.succAbove id) := by
    apply Matrix.ext
    intro a b
    exact congrFun (congrFun (determinantChartCriticalMatrix_witness z m) (i.succAbove a)) b
  rw [h, ← f.map_det]
  exact hi

/-- For each certified length, a single deleted row works at the common point
and at the generic points of both special spectral divisors. -/
theorem determinantChart_exists_generic_cofactor_ne_zero {m : ℕ} (hm : 5 ≤ m) :
    ∃ i : Fin 10, eval nativeWitnessSlice ((criticalMatrix m).submatrix i.succAbove id).det ≠ 0 ∧
      ∀ z : Divisor, (((determinantChartCriticalMatrix z m).submatrix i.succAbove id).map
        (determinantGenericPoint ℂ z)).det ≠ 0 := by
  obtain ⟨i, hi⟩ := nativeWitness_exists_cofactor_ne_zero hm
  exact ⟨i, hi, fun z => generic_cofactor_of_witness z hi⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformCommonSpectralRankTransport
