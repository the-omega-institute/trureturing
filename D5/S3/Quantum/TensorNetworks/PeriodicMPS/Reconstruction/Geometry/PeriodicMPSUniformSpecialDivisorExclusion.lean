/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpecialDivisorExclusion
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpecialDivisorExclusion
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: A height-one prime of the exact guarded native cofactors avoids both special spectral equations. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformCommonSpectralGeneric
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.Submodule

/-!
# Special spectral divisors in the trace-aligned periodic MPS chart

The variables d, db, e, eb and k are independent. The coefficient rings of
the zero-root and reduced repeated-root preimages are obtained by extending
the coefficient ideals along the transfer-coefficient substitution and
inverting U * k * (c - b^2).
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformSpecialDivisorExclusion

open MvPolynomial
open PeriodicMPSUniformSpecialSpectralBases (CoefficientRing guard)
open PeriodicMPSUniformSpecialSpectralDomains
open PeriodicMPSUniformCommonSpectralRankTransport
  (chartComplexConstants chartSlice determinantChartCriticalMatrix
    determinantChart_exists_generic_cofactor_ne_zero)
open UniformNativeCriticalMatrix (criticalMatrix)
open PeriodicMPSUniformSpectralRadicalAlgebra
  (Determinant CoordinateFiber Parameters coordinate coordinateLift coordinatePoint)
open private polynomialToBase toAway from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpecialSpectralDomains

open private nativeCartesian from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpectralCoefficients

noncomputable section

private theorem map_spectralCoefficients {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : Variable → R) (i : Fin 3) :
    f (spectralCoefficients x i) = spectralCoefficients (f ∘ x) i := by
  fin_cases i <;> simp [spectralCoefficients, map_ofNat]

abbrev Ambient := Localization.Away ambientGuard

def ambientClass : AmbientPolynomials →+* Ambient := algebraMap _ _
def ambientCoefficient : CoefficientRing ℂ →+* Ambient := ambientClass.comp coefficientSubstitution

/-- Scheme-theoretic preimage of the reduced coefficient divisor on the guard open. -/
def pullbackIdeal (z : Divisor) : Ideal Ambient :=
  (coefficientIdeal ℂ z).map ambientCoefficient

abbrev AmbientQuotient (z : Divisor) := Ambient ⧸ pullbackIdeal z

variable (z : Divisor)

def ambientQuotient : Ambient →+* AmbientQuotient z := Ideal.Quotient.mk _

private def chartBaseInclusion : ChartBase ℂ z →+* DeterminantChart ℂ z := algebraMap _ _

private def chartCoefficientBase : CoefficientRing ℂ →+* ChartBase ℂ z :=
  (polynomialToBase ℂ z).comp ((Polynomial.C.comp Polynomial.C).comp
    ((algebraMap (DivisorRing ℂ z) (GuardedCoefficients ℂ z)).comp (coefficientClass ℂ z)))

private theorem chartCoefficientBase_apply (f : CoefficientRing ℂ) :
    chartCoefficientBase z f = chartConstant ℂ z (guardedClass ℂ z f) := rfl

private theorem chartCoefficientBase_isUnit_guard :
    IsUnit (chartCoefficientBase z guard) := by
  rw [chartCoefficientBase_apply]
  exact (IsLocalization.Away.algebraMap_isUnit (S := GuardedCoefficients ℂ z)
    (guardClass ℂ z)).map ((polynomialToBase ℂ z).comp (Polynomial.C.comp Polynomial.C))

/-- Polynomial substitution in the chart sends k to the base unit and each determinant
variable to its literal coordinate. -/
def chartVariables : Variable → DeterminantChart ℂ z
  | none => chartBaseInclusion z ↑(chartK ℂ z)
  | some i => coordinate (chartParameters ℂ z) i

def polynomialToChart : AmbientPolynomials →+* DeterminantChart ℂ z :=
  eval₂Hom ((chartBaseInclusion z).comp ((chartCoefficientBase z).comp C)) (chartVariables z)

@[simp] theorem polynomialToChart_C (r : ℂ) :
    polynomialToChart z (C r) = chartComplexConstants z r := by
  rw [polynomialToChart, eval₂Hom_C]
  rfl

private theorem chartVariables_prod :
    chartVariables z (some .d) * chartVariables z (some .db) =
      chartBaseInclusion z ↑(chartU ℂ z) :=
  (coordinatePoint (chartParameters ℂ z)).prod_eq

private theorem chartCoefficients_match (i : Fin 3) :
    spectralCoefficients (chartVariables z) i =
      chartBaseInclusion z (chartCoefficientBase z (X i)) := by
  let p := chartParameters ℂ z
  let q := coordinatePoint p
  fin_cases i
  · change chartVariables z (some .d) + chartVariables z (some .db) -
      2 * (chartVariables z (some .d) * chartVariables z (some .db) + q.e * q.eb) -
      (chartVariables z none) ^ 2 = _
    rw [chartVariables_prod]
    exact q.coeff_a
  · change chartVariables z (some .d) * chartVariables z (some .db) - q.e * q.eb = _
    rw [chartVariables_prod]
    exact q.coeff_b
  · change (chartVariables z (some .d) * chartVariables z (some .db) - q.e * q.eb) ^ 2 +
      (chartVariables z none) ^ 2 * (q.d + q.eb) * (q.db + q.e) = _
    rw [chartVariables_prod]
    have hb : chartBaseInclusion z ↑(chartU ℂ z) - q.e * q.eb =
      chartBaseInclusion z p.b := q.coeff_b
    rw [hb]
    exact q.coeff_c

private theorem polynomialToChart_coefficients :
    (polynomialToChart z).comp coefficientSubstitution =
      (chartBaseInclusion z).comp (chartCoefficientBase z) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [coefficientSubstitution, polynomialToChart]
  · intro i
    simp only [RingHom.comp_apply, coefficientSubstitution, eval₂Hom_X', map_spectralCoefficients]
    have h : (polynomialToChart z) ∘ (X : Variable → AmbientPolynomials) = chartVariables z := by
      funext i
      simp [polynomialToChart]
    rw [h, chartCoefficients_match]

private theorem polynomialToChart_guard_isUnit :
    IsUnit (polynomialToChart z ambientGuard) := by
  have hU : polynomialToChart z ambientU = chartBaseInclusion z ↑(chartU ℂ z) := by
    simpa [ambientU, polynomialToChart] using chartVariables_prod z
  have hk : polynomialToChart z ambientK = chartBaseInclusion z ↑(chartK ℂ z) := by
    simp [ambientK, polynomialToChart, chartVariables]
  have hg := RingHom.congr_fun (polynomialToChart_coefficients z) (guard : CoefficientRing ℂ)
  change polynomialToChart z (coefficientSubstitution guard) =
    chartBaseInclusion z (chartCoefficientBase z guard) at hg
  rw [ambientGuard, map_mul, map_mul, hU, hk, hg]
  exact (((chartU ℂ z).isUnit.map (chartBaseInclusion z)).mul
    ((chartK ℂ z).isUnit.map (chartBaseInclusion z))).mul
    ((chartCoefficientBase_isUnit_guard z).map (chartBaseInclusion z))

def ambientToChart : Ambient →+* DeterminantChart ℂ z :=
  IsLocalization.Away.lift ambientGuard (polynomialToChart_guard_isUnit z)

@[simp] theorem ambientToChart_class (f : AmbientPolynomials) :
    ambientToChart z (ambientClass f) = polynomialToChart z f :=
  IsLocalization.Away.lift_eq _ _ _

@[simp] theorem ambientToChart_variable (i : Variable) :
    ambientToChart z (ambientClass (X i)) = chartVariables z i := by
  simp [polynomialToChart]

private theorem ambientToChart_coefficient (f : CoefficientRing ℂ) :
    ambientToChart z (ambientCoefficient f) = chartBaseInclusion z (chartCoefficientBase z f) := by
  rw [ambientCoefficient, RingHom.comp_apply, ambientToChart_class]
  exact RingHom.congr_fun (polynomialToChart_coefficients z) f

def quotientToChart : AmbientQuotient z →+* DeterminantChart ℂ z :=
  Ideal.Quotient.lift _ (ambientToChart z) (by
    have h : pullbackIdeal z ≤ RingHom.ker (ambientToChart z) := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro f hf
      change ambientToChart z (ambientCoefficient f) = 0
      have h : coefficientClass ℂ z f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hf
      rw [ambientToChart_coefficient]
      simp [chartCoefficientBase, h]
    exact fun _ hf => RingHom.mem_ker.mp (h hf))

@[simp] theorem quotientToChart_mk (x : Ambient) :
    quotientToChart z (ambientQuotient z x) = ambientToChart z x := rfl

private def coefficientToQuotient : DivisorRing ℂ z →+* AmbientQuotient z :=
  Ideal.Quotient.lift _ ((ambientQuotient z).comp ambientCoefficient) (fun _ hf =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem ambientCoefficient hf))

private def ambientUnit {f : AmbientPolynomials} (hf : f ∣ ambientGuard) : Ambientˣ :=
  (IsLocalization.Away.isUnit_of_dvd ambientGuard (S := Ambient) hf).unit

private theorem ambientUnit_val {f : AmbientPolynomials} (hf : f ∣ ambientGuard) :
    ↑(ambientUnit hf) = ambientClass f :=
  IsUnit.unit_spec _

private def quotientU : (AmbientQuotient z)ˣ :=
  Units.map (ambientQuotient z) (ambientUnit ((dvd_mul_right ambientU ambientK).trans
    (dvd_mul_right _ _)))

private def quotientK : (AmbientQuotient z)ˣ :=
  Units.map (ambientQuotient z) (ambientUnit ((dvd_mul_left ambientK ambientU).trans
    (dvd_mul_right _ _)))

@[simp] private theorem quotientU_val :
    ↑(quotientU z) = ambientQuotient z (ambientClass ambientU) := by
  simp [quotientU, ambientUnit_val]

@[simp] private theorem quotientK_val :
    ↑(quotientK z) = ambientQuotient z (ambientClass ambientK) := by
  simp [quotientK, ambientUnit_val]

private def guardedToQuotient : GuardedCoefficients ℂ z →+* AmbientQuotient z :=
  IsLocalization.Away.lift (guardClass ℂ z) (g := coefficientToQuotient z) (by
    change IsUnit (ambientQuotient z (ambientClass (coefficientSubstitution guard)))
    rw [← ambientUnit_val (dvd_mul_left (coefficientSubstitution guard) (ambientU * ambientK))]
    exact (Units.isUnit _).map (ambientQuotient z))

@[simp] private theorem guardedToQuotient_class (f : CoefficientRing ℂ) :
    guardedToQuotient z (guardedClass ℂ z f) = ambientQuotient z (ambientCoefficient f) :=
  IsLocalization.Away.lift_eq _ _ _

/-- Base parameters are recovered from their polynomial formulas in the ambient quotient. -/
def baseToQuotient : ChartBase ℂ z →+* AmbientQuotient z :=
  IsLocalization.Away.lift (polyU ℂ z * polyK ℂ z)
    (g := Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (guardedToQuotient z)
      ↑(quotientK z)) ↑(quotientU z)) (by
        simp only [polyU, polyK, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
          Polynomial.eval₂_C]
        exact (quotientU z).isUnit.mul (quotientK z).isUnit)

@[simp] theorem baseToQuotient_constant (r : GuardedCoefficients ℂ z) :
    baseToQuotient z (chartConstant ℂ z r) = guardedToQuotient z r := by
  rw [baseToQuotient, chartConstant, polynomialToBase, toAway, IsLocalization.Away.lift_eq]
  simp

@[simp] theorem baseToQuotient_U :
    baseToQuotient z ↑(chartU ℂ z) = ambientQuotient z (ambientClass ambientU) := by
  rw [baseToQuotient, chartU, IsUnit.unit_spec, IsLocalization.Away.lift_eq]
  simp [polyU]

@[simp] theorem baseToQuotient_K :
    baseToQuotient z ↑(chartK ℂ z) = ambientQuotient z (ambientClass ambientK) := by
  rw [baseToQuotient, chartK, IsUnit.unit_spec, IsLocalization.Away.lift_eq]
  simp [polyK]

def quotientVariable (i : Variable) : AmbientQuotient z :=
  ambientQuotient z (ambientClass (X i))

private theorem quotientCoefficient_X (i : Fin 3) :
    ambientQuotient z (ambientCoefficient (X i)) =
      spectralCoefficients (quotientVariable z) i := by
  simp only [ambientCoefficient, RingHom.comp_apply, coefficientSubstitution, eval₂Hom_X']
  rw [map_spectralCoefficients, map_spectralCoefficients]
  rfl

private theorem quotientVariable_prod :
    quotientVariable z (some .d) * quotientVariable z (some .db) =
      ambientQuotient z (ambientClass ambientU) := by
  simp [ambientU, quotientVariable]

private def quotientFiber : CoordinateFiber ((chartParameters ℂ z).map (baseToQuotient z)) where
  d := quotientVariable z (some .d)
  db := quotientVariable z (some .db)
  e := quotientVariable z (some .e)
  eb := quotientVariable z (some .eb)
  prod_eq := by
    simpa [Parameters.map, chartParameters] using quotientVariable_prod z
  coeff_a := by
    change quotientVariable z (some .d) + quotientVariable z (some .db) -
      2 * (baseToQuotient z ↑(chartU ℂ z) + quotientVariable z (some .e) *
        quotientVariable z (some .eb)) - (baseToQuotient z ↑(chartK ℂ z)) ^ 2 =
      baseToQuotient z (chartConstant ℂ z (guardedClass ℂ z (X 0)))
    rw [baseToQuotient_U, baseToQuotient_K, baseToQuotient_constant,
      guardedToQuotient_class, quotientCoefficient_X, ← quotientVariable_prod]
    rfl
  coeff_b := by
    change baseToQuotient z ↑(chartU ℂ z) - quotientVariable z (some .e) *
      quotientVariable z (some .eb) =
      baseToQuotient z (chartConstant ℂ z (guardedClass ℂ z (X 1)))
    rw [baseToQuotient_U, baseToQuotient_constant, guardedToQuotient_class,
      quotientCoefficient_X, ← quotientVariable_prod]
    rfl
  coeff_c := by
    change (baseToQuotient z (chartConstant ℂ z (guardedClass ℂ z (X 1)))) ^ 2 +
      (baseToQuotient z ↑(chartK ℂ z)) ^ 2 *
        (quotientVariable z (some .d) + quotientVariable z (some .eb)) *
        (quotientVariable z (some .db) + quotientVariable z (some .e)) =
      baseToQuotient z (chartConstant ℂ z (guardedClass ℂ z (X 2)))
    simp only [baseToQuotient_K, baseToQuotient_constant, guardedToQuotient_class,
      quotientCoefficient_X]
    rfl

/-- The inverse coordinate map is induced by the four ambient determinant variables. -/
def chartToQuotient : DeterminantChart ℂ z →+* AmbientQuotient z := by
  letI : Algebra (ChartBase ℂ z) (AmbientQuotient z) := (baseToQuotient z).toAlgebra
  exact (coordinateLift (quotientFiber z)).toRingHom

@[simp] theorem chartToQuotient_base (r : ChartBase ℂ z) :
    chartToQuotient z (chartBaseInclusion z r) = baseToQuotient z r := by
  let : Algebra (ChartBase ℂ z) (AmbientQuotient z) := (baseToQuotient z).toAlgebra
  exact (coordinateLift (quotientFiber z)).commutes r

@[simp] theorem chartToQuotient_coordinate (i : Determinant) :
    chartToQuotient z (coordinate (chartParameters ℂ z) i) = quotientVariable z (some i) := by
  let : Algebra (ChartBase ℂ z) (AmbientQuotient z) := (baseToQuotient z).toAlgebra
  cases i <;> exact PeriodicMPSUniformSpectralRadicalAlgebra.coordinateLift_coordinate _ _

private theorem chartBase_hom_ext {S : Type*} [CommRing S] {f g : ChartBase ℂ z →+* S}
    (hC : ∀ r, f (chartConstant ℂ z (guardedClass ℂ z r)) =
      g (chartConstant ℂ z (guardedClass ℂ z r)))
    (hU : f ↑(chartU ℂ z) = g ↑(chartU ℂ z))
    (hK : f ↑(chartK ℂ z) = g ↑(chartK ℂ z)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (polyU ℂ z * polyK ℂ z))
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · have h : (f.comp (polynomialToBase ℂ z)).comp (Polynomial.C.comp Polynomial.C) =
          (g.comp (polynomialToBase ℂ z)).comp (Polynomial.C.comp Polynomial.C) := by
        apply IsLocalization.ringHom_ext (Submonoid.powers (guardClass ℂ z))
        apply Ideal.Quotient.ringHom_ext
        exact RingHom.ext hC
      exact RingHom.congr_fun h
    · change f (polynomialToBase ℂ z (polyK ℂ z)) =
        g (polynomialToBase ℂ z (polyK ℂ z))
      rw [polynomialToBase, toAway]
      simpa only [chartK, IsUnit.unit_spec] using hK
  · change f (polynomialToBase ℂ z (polyU ℂ z)) =
      g (polynomialToBase ℂ z (polyU ℂ z))
    rw [polynomialToBase, toAway]
    simpa only [chartU, IsUnit.unit_spec] using hU

private theorem quotientToChart_baseToQuotient :
    (quotientToChart z).comp (baseToQuotient z) = chartBaseInclusion z := by
  apply chartBase_hom_ext
  · intro r
    simp only [RingHom.comp_apply, baseToQuotient_constant, guardedToQuotient_class,
      quotientToChart_mk, ambientToChart_coefficient, chartCoefficientBase_apply]
  · simp only [RingHom.comp_apply, baseToQuotient_U, quotientToChart_mk]
    simpa [ambientU, polynomialToChart, chartVariables] using chartVariables_prod z
  · change quotientToChart z (baseToQuotient z ↑(chartK ℂ z)) = _
    rw [baseToQuotient_K, quotientToChart_mk, ambientK, ambientToChart_variable]
    rfl

private theorem quotientToChart_chartToQuotient :
    (quotientToChart z).comp (chartToQuotient z) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change quotientToChart z (chartToQuotient z (chartBaseInclusion z r)) =
      chartBaseInclusion z r
    rw [chartToQuotient_base]
    exact RingHom.congr_fun (quotientToChart_baseToQuotient z) r
  · intro i
    change quotientToChart z (chartToQuotient z (coordinate (chartParameters ℂ z) i)) =
      coordinate (chartParameters ℂ z) i
    rw [chartToQuotient_coordinate, quotientVariable, quotientToChart_mk, ambientToChart_variable]
    rfl

private theorem chartToQuotient_quotientToChart :
    (chartToQuotient z).comp (quotientToChart z) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers ambientGuard)
  apply MvPolynomial.ringHom_ext
  · intro r
    change chartToQuotient z (ambientToChart z (ambientClass (C r))) =
      ambientQuotient z (ambientClass (C r))
    simp only [ambientToChart_class, polynomialToChart, eval₂Hom_C, RingHom.comp_apply,
      chartToQuotient_base]
    change baseToQuotient z (chartConstant ℂ z (guardedClass ℂ z (C r))) = _
    simp [ambientCoefficient, coefficientSubstitution]
  · intro i
    change chartToQuotient z (ambientToChart z (ambientClass (X i))) =
      ambientQuotient z (ambientClass (X i))
    rw [ambientToChart_variable]
    cases i with
    | none => exact (chartToQuotient_base z _).trans (baseToQuotient_K z)
    | some i => exact chartToQuotient_coordinate z i

/-- The two explicit maps identify the guarded ambient quotient with the literal
determinant-coordinate ring for either spectral divisor. -/
def quotientEquivDeterminantChart : AmbientQuotient z ≃+* DeterminantChart ℂ z :=
  RingEquiv.ofRingHom (quotientToChart z) (chartToQuotient z)
    (quotientToChart_chartToQuotient z) (chartToQuotient_quotientToChart z)

@[simp] theorem quotientEquivDeterminantChart_variable (i : Variable) :
    quotientEquivDeterminantChart z (quotientVariable z i) = chartVariables z i :=
  ambientToChart_variable z i

@[simp] theorem quotientEquivDeterminantChart_symm_coordinate (i : Determinant) :
    (quotientEquivDeterminantChart z).symm (coordinate (chartParameters ℂ z) i) =
      quotientVariable z (some i) :=
  chartToQuotient_coordinate z i

@[simp] theorem quotientEquivDeterminantChart_constant (r : ℂ) :
    quotientEquivDeterminantChart z (ambientQuotient z (ambientClass (C r))) =
      chartComplexConstants z r :=
  (ambientToChart_class z (C r)).trans (polynomialToChart_C z r)

theorem ambientToChart_ker : RingHom.ker (ambientToChart z) = pullbackIdeal z := by
  have h : ambientToChart z = (quotientToChart z).comp (ambientQuotient z) := rfl
  rw [h, RingHom.ker_comp_of_injective _ (quotientEquivDeterminantChart z).injective]
  exact Ideal.mk_ker

instance pullbackIdeal_isPrime : (pullbackIdeal z).IsPrime := by
  rw [← ambientToChart_ker z]
  exact RingHom.ker_isPrime _

/-- The same quotient in the checked two-radical presentation. -/
def quotientEquivRadicalAlgebra : AmbientQuotient z ≃+* Upstairs ℂ z :=
  (quotientEquivDeterminantChart z).trans (determinantChartEquiv ℂ z).toRingEquiv

open PeriodicMPSUniformSpecialSpectralBases
  (discriminant eval_discriminant quartic transferPolynomial
    zeroRootLocus_eq_zeroLocus repeatedRoot_vanishingIdeal_eq_radical)

def spectralEquation : Divisor → CoefficientRing ℂ
  | .zeroRoot => X 2
  | .repeatedRoot => discriminant

def ambientSpectralEquation (z : Divisor) : Ambient :=
  ambientCoefficient (spectralEquation z)

private theorem coefficientIdeal_eq_radical :
    coefficientIdeal ℂ z = (Ideal.span {spectralEquation z}).radical := by
  cases z
  · change vanishingIdeal ℂ PeriodicMPSUniformSpecialSpectralBases.zeroRootLocus = _
    rw [zeroRootLocus_eq_zeroLocus, vanishingIdeal_zeroLocus_eq_radical]
    rfl
  · exact repeatedRoot_vanishingIdeal_eq_radical

/-- The reduced spectral equation cuts out the prime pullback on the guard open. -/
theorem pullbackIdeal_eq_radical :
    pullbackIdeal z = (Ideal.span {ambientSpectralEquation z}).radical := by
  have hspan :
      (Ideal.span {spectralEquation z}).map ambientCoefficient =
        Ideal.span {ambientSpectralEquation z} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have hle : Ideal.span {ambientSpectralEquation z} ≤ pullbackIdeal z := by
    rw [← hspan, pullbackIdeal, coefficientIdeal_eq_radical]
    exact Ideal.map_mono Ideal.le_radical
  refine le_antisymm ?_ ((pullbackIdeal_isPrime z).radical_le_iff.mpr hle)
  rw [pullbackIdeal, coefficientIdeal_eq_radical, ← hspan]
  exact Ideal.map_radical_le (f := ambientCoefficient)

/-- The zero-root pullback is the principal ideal of the literal constant term. -/
theorem zeroRoot_pullbackIdeal_eq_span :
    pullbackIdeal .zeroRoot = Ideal.span {ambientSpectralEquation .zeroRoot} := by
  have hprime : (Ideal.span {(X 2 : CoefficientRing ℂ)}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime
  rw [pullbackIdeal, coefficientIdeal_eq_radical, spectralEquation, hprime.radical,
    Ideal.map_span, Set.image_singleton]
  rfl

private theorem ambientSpectralEquation_not_isUnit :
    ¬ IsUnit (ambientSpectralEquation z) := by
  intro hu
  have hle : Ideal.span {ambientSpectralEquation z} ≤ pullbackIdeal z := by
    rw [pullbackIdeal_eq_radical]
    exact Ideal.le_radical
  rw [Ideal.span_singleton_eq_top.mpr hu, top_le_iff] at hle
  exact (pullbackIdeal_isPrime z).ne_top hle

private def offDivisorPoint : Variable → ℂ
  | some .d | some .db | none => 1
  | some .e | some .eb => 0

private theorem offDivisorPoint_coefficients :
    spectralCoefficients offDivisorPoint = ![(-1 : ℂ), 1, 2] := by
  funext i
  fin_cases i <;> norm_num [spectralCoefficients, offDivisorPoint]

private theorem offDivisorPoint_eval (f : CoefficientRing ℂ) :
    eval offDivisorPoint (coefficientSubstitution f) = eval ![(-1 : ℂ), 1, 2] f := by
  have h : (eval offDivisorPoint).comp coefficientSubstitution = eval ![(-1 : ℂ), 1, 2] := by
    apply MvPolynomial.ringHom_ext
    · simp [coefficientSubstitution]
    · intro i
      simp only [RingHom.comp_apply, coefficientSubstitution, eval₂Hom_X', eval_X,
        map_spectralCoefficients]
      rw [show (eval offDivisorPoint) ∘ (X : Variable → AmbientPolynomials) =
        offDivisorPoint by funext x; simp, offDivisorPoint_coefficients]
  exact RingHom.congr_fun h f

private def offDivisorEvaluation : Ambient →+* ℂ :=
  IsLocalization.Away.lift ambientGuard (g := eval offDivisorPoint) (by
    rw [ambientGuard, map_mul, map_mul, offDivisorPoint_eval]
    norm_num [ambientU, ambientK, offDivisorPoint,
      PeriodicMPSUniformSpecialSpectralBases.eval_guard])

private theorem offDivisorEvaluation_spectral (z : Divisor) :
    offDivisorEvaluation (ambientSpectralEquation z) =
      eval ![(-1 : ℂ), 1, 2] (spectralEquation z) := by
  change offDivisorEvaluation (algebraMap AmbientPolynomials Ambient
    (coefficientSubstitution (spectralEquation z))) = _
  rw [offDivisorEvaluation, IsLocalization.Away.lift_eq, offDivisorPoint_eval]

private theorem offDivisorQuartic_separable : (quartic (-1 : ℂ) 1 2).Separable := by
  rw [Polynomial.separable_def]
  let Q := quartic (-1 : ℂ) 1 2
  let A : Polynomial ℂ := -148 * Polynomial.X ^ 2 - 69 * Polynomial.X + 21
  let B : Polynomial ℂ := 37 * Polynomial.X ^ 3 + 8 * Polynomial.X ^ 2 - 35 * Polynomial.X - 62
  have hQ : Q = Polynomial.X ^ 4 - Polynomial.X ^ 3 - Polynomial.X ^ 2 - Polynomial.X + 2 := by
    simp [Q, quartic, Polynomial.C_neg, Polynomial.C_ofNat]
    ring
  have hBez : A * Q + B * Q.derivative = Polynomial.C (104 : ℂ) := by
    rw [hQ]
    simp only [A, B, Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_X_pow, Polynomial.derivative_X, Polynomial.derivative_ofNat,
      Nat.cast_ofNat, add_zero, Polynomial.C_ofNat]
    ring
  refine ⟨Polynomial.C (104⁻¹ : ℂ) * A, Polynomial.C (104⁻¹ : ℂ) * B, ?_⟩
  change _ * Q + _ * Q.derivative = _
  rw [mul_assoc, mul_assoc, ← mul_add, hBez, ← map_mul]
  norm_num

private theorem ambientSpectralEquation_ne_zero (z : Divisor) :
    ambientSpectralEquation z ≠ 0 := by
  intro hz
  have h := offDivisorEvaluation_spectral z
  rw [hz, map_zero] at h
  cases z
  · simp [spectralEquation] at h
  · rw [spectralEquation, eval_discriminant] at h
    have hc : transferPolynomial ![(-1 : ℂ), 1, 2] = quartic (-1 : ℂ) 1 2 := rfl
    rw [hc] at h
    exact ((Polynomial.resultant_eq_zero_iff.mp h.symm).2) offDivisorQuartic_separable

private theorem ambientGuard_ne_zero : ambientGuard ≠ 0 := by
  intro h
  have hu := offDivisorEvaluation
  have hm : IsUnit (hu (ambientClass ambientGuard)) :=
    (IsLocalization.Away.algebraMap_isUnit (S := Ambient) ambientGuard).map hu
  change IsUnit (hu (ambientClass ambientGuard)) at hm
  have hz : ambientClass ambientGuard = 0 := (congrArg ambientClass h).trans (map_zero _)
  rw [hz, map_zero] at hm
  exact not_isUnit_zero hm

instance ambient_isDomain : IsDomain Ambient :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors ambientGuard_ne_zero)

local instance : Fintype Determinant := by
  classical
  exact Fintype.ofList [.d, .db, .e, .eb] (by intro i; cases i <;> simp)

/-- Both reduced pulled-back divisor ideals have height exactly one. -/
theorem pullbackIdeal_height : (pullbackIdeal z).height = 1 := by
  rw [pullbackIdeal_eq_radical, Ideal.height_eq_inf_minimalPrimes, Ideal.radical_minimalPrimes,
    ← Ideal.height_eq_inf_minimalPrimes]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr (ambientSpectralEquation_ne_zero z))
    (ambientSpectralEquation_not_isUnit z)

private theorem polynomialToChart_native :
    (polynomialToChart z).comp nativeSliceSubstitution =
      eval₂Hom (chartComplexConstants z) (chartSlice z) := by
  have hX (i : Variable) : polynomialToChart z (X i) = chartVariables z i := by
    simp [polynomialToChart]
  apply MvPolynomial.ringHom_ext
  · intro r
    simpa only [RingHom.comp_apply, nativeSliceSubstitution, eval₂Hom_C] using polynomialToChart_C z r
  · intro i
    simp only [RingHom.comp_apply, nativeSliceSubstitution, eval₂Hom_X']
    fin_cases i <;>
      simp [nativeCartesian, chartSlice, hX, chartVariables, chartBaseInclusion] <;> ring

/-- The i-th native maximal cofactor after the Cartesian substitution and localization. -/
def ambientNativeCofactor (m : ℕ) (i : Fin 10) : Ambient :=
  (ambientClass.comp nativeSliceSubstitution) (((criticalMatrix m).submatrix i.succAbove id).det)

def nativeCofactorIdeal (m : ℕ) : Ideal Ambient :=
  Ideal.span (Set.range (ambientNativeCofactor m))

theorem ambientNativeCofactor_generic (m : ℕ) (i : Fin 10) :
    determinantGenericPoint ℂ z (ambientToChart z (ambientNativeCofactor m i)) =
      (((determinantChartCriticalMatrix z m).submatrix i.succAbove id).map
        (determinantGenericPoint ℂ z)).det := by
  let f := eval₂Hom (chartComplexConstants z) (chartSlice z)
  let g := determinantGenericPoint ℂ z
  let M := (criticalMatrix m).submatrix i.succAbove id
  rw [ambientNativeCofactor, RingHom.comp_apply, ambientToChart_class]
  have he := RingHom.congr_fun (polynomialToChart_native z) M.det
  change polynomialToChart z (nativeSliceSubstitution M.det) = f M.det at he
  change g (polynomialToChart z (nativeSliceSubstitution M.det)) = _
  rw [he, f.map_det, g.map_det]
  rfl

/-- At every certified length the same native cofactor survives both specializations. -/
theorem exists_ambientNativeCofactor_not_mem_pullback {m : ℕ} (hm : 5 ≤ m) :
    ∃ i : Fin 10, ∀ z : Divisor, ambientNativeCofactor m i ∉ pullbackIdeal z := by
  obtain ⟨i, _, hi⟩ := determinantChart_exists_generic_cofactor_ne_zero hm
  refine ⟨i, fun z h => hi z ?_⟩
  rw [← ambientNativeCofactor_generic]
  have hz : ambientToChart z (ambientNativeCofactor m i) = 0 :=
    RingHom.mem_ker.mp ((ambientToChart_ker z).symm ▸ h)
  rw [hz, map_zero]

theorem nativeCofactorIdeal_not_le_pullback {m : ℕ} (hm : 5 ≤ m)
    (z : Divisor) : ¬ nativeCofactorIdeal m ≤ pullbackIdeal z := by
  obtain ⟨i, hi⟩ := exists_ambientNativeCofactor_not_mem_pullback hm
  exact fun h => hi z (h (Ideal.subset_span ⟨i, rfl⟩))

/-- The support of a height-one native cofactor prime cannot be contained in either
special divisor. This direction uses the height of the pulled-back prime. -/
theorem pullback_not_le_nativeCofactor_prime {m : ℕ} (hm : 5 ≤ m)
    (P : Ideal Ambient) [P.IsPrime] (hP : P.height = 1) (hcof : nativeCofactorIdeal m ≤ P)
    (z : Divisor) : ¬ pullbackIdeal z ≤ P := by
  intro h
  have : (pullbackIdeal z).FiniteHeight :=
    Ideal.finiteHeight_iff_lt.mpr (by simp [pullbackIdeal_height])
  have hn : ¬ P ≤ pullbackIdeal z :=
    fun h' => nativeCofactorIdeal_not_le_pullback hm z (hcof.trans h')
  have hlt := Ideal.height_strict_mono_of_isPrime (lt_of_le_not_ge h hn)
  rw [pullbackIdeal_height, hP] at hlt
  exact (lt_irrefl _) hlt

/-- The two spectral equations are both absent from a height-one prime of the
native cofactor ideal on the guarded chart. -/
theorem nativeCofactor_prime_avoids_special_equations {m : ℕ} (hm : 5 ≤ m)
    (P : Ideal Ambient) [P.IsPrime] (hP : P.height = 1) (hcof : nativeCofactorIdeal m ≤ P)
    (z : Divisor) : ambientSpectralEquation z ∉ P := by
  intro h
  apply pullback_not_le_nativeCofactor_prime hm P hP hcof z
  rw [pullbackIdeal_eq_radical]
  apply ‹P.IsPrime›.radical_le_iff.mpr
  rwa [Ideal.span_singleton_le_iff_mem]

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformSpecialDivisorExclusion
