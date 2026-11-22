/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalAmbient
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalAmbient
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Height-one vertical prime exclusion for the exact ordered native cofactors. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalAmbientSection
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformMovingFrameRank
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalAmbient

open MvPolynomial Matrix PeriodicMPSUniformMovingFrame
open PeriodicMPSUniformSpectralRadicalAlgebra
open PeriodicMPSUniformVerticalSectionRank (DivisorRing divisorRoots genericSection)
open PeriodicMPSUniformVerticalPrimeExclusion (Roots rootSum pairing obstruction)
open UniformNativeCriticalMatrix (criticalMatrix)
open private divisorRoots_eq_zero from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSectionRank

noncomputable section

private def spectralA : Roots := elementaryA (X 0) (X 1) (X 2) (X 3)
private def spectralB : Roots := elementaryB (X 0) (X 1) (X 2) (X 3)
private def spectralC : Roots := elementaryC (X 0) (X 1) (X 2) (X 3)

/-- Numerator of the normalized coefficient guard. -/
def spectralGap : Roots := rootSum ^ 2 * spectralC - spectralB ^ 2

def simpleRoots : Roots :=
  (X 0 - X 1) * (X 0 - X 2) * (X 0 - X 3) *
    (X 1 - X 2) * (X 1 - X 3) * (X 2 - X 3)

/-- All spectral inversions on the homogeneous ordered-root cover. -/
def spectralGuard : Roots := rootSum * (∏ i : Fin 4, X i) * simpleRoots * spectralGap

abbrev SpectralBase := Localization.Away spectralGuard
def spectralClass : Roots →+* SpectralBase := algebraMap _ _

private def spectralUnit {g : Roots} (hg : g ∣ spectralGuard) : SpectralBaseˣ :=
  (IsLocalization.Away.isUnit_of_dvd spectralGuard hg).unit

private theorem spectralUnit_val {g : Roots} (hg : g ∣ spectralGuard) :
    (↑(spectralUnit hg) : SpectralBase) = spectralClass g :=
  IsUnit.unit_spec _

private def sumUnit : SpectralBaseˣ := spectralUnit
  ((dvd_mul_right rootSum _).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _)))

private theorem sumUnit_val : (sumUnit : SpectralBase) = spectralClass rootSum :=
  spectralUnit_val _

private def normalizedA : SpectralBase := spectralClass spectralA * (↑sumUnit⁻¹ : SpectralBase)^2
private def normalizedB : SpectralBase := spectralClass spectralB * (↑sumUnit⁻¹ : SpectralBase)^3
private def normalizedC : SpectralBase := spectralClass spectralC * (↑sumUnit⁻¹ : SpectralBase)^4

private def complexTwo : ℂˣ := Units.mk0 2 (by norm_num)

private def spectralComplex : ℂ →+* SpectralBase := spectralClass.comp C

private def spectralTwo : SpectralBaseˣ := complexTwo.map spectralComplex.toMonoidHom
private theorem spectralTwo_val : (spectralTwo : SpectralBase) = 2 :=
  map_ofNat spectralComplex 2

def orderedParameters : Parameters (ParameterRing SpectralBase) :=
  chartParameters spectralTwo spectralTwo_val normalizedA normalizedB normalizedC

/-- The ordered-root determinant chart in the equivalent two-radical
presentation, before inverting the raw mass. -/
abbrev OrderedChart := RadicalAlgebra orderedParameters

def rootToChart : Roots →+* OrderedChart :=
  (algebraMap (ParameterRing SpectralBase) OrderedChart).comp
    (parameterConstant.comp spectralClass)

private def orderedComplex : ℂ →+* OrderedChart := rootToChart.comp C

instance : Algebra ℂ OrderedChart := orderedComplex.toAlgebra

/-- The literal determinant equations and the two-radical presentation
give the same ordered-root chart. -/
def orderedDeterminantChartEquiv : CoordinateAlgebra orderedParameters ≃ₐ[ParameterRing SpectralBase]
    OrderedChart :=
  coordinateEquivRadicalAlgebra orderedParameters

/-- Cartesian coordinates of the universal determinant point, in the
literal native matrix order. -/
def orderedSlice : Fin 5 → OrderedChart :=
  let q := (radicalPoint orderedParameters).toCoordinates
  cartesian q.d q.db q.e q.eb (algebraMap (ParameterRing SpectralBase) _
    (↑(parameterK (R := SpectralBase))))

def orderedCofactor (m : ℕ) (i : Fin 10) : OrderedChart :=
  aeval orderedSlice (((criticalMatrix m).submatrix i.succAbove id).det)

private abbrev divisorIdeal (f : Roots) : Ideal Roots := Ideal.span {f}

variable {f : Roots} [IsDomain (DivisorRing f)]

def residueSpectral (f : Roots) : DivisorRing f :=
  Ideal.Quotient.mk (divisorIdeal f) spectralGuard

abbrev ResidueBase (f : Roots) := Localization.Away (residueSpectral f)

private def spectralSpecialize (f : Roots) : SpectralBase →+* ResidueBase f :=
  IsLocalization.map (ResidueBase f) (M := Submonoid.powers spectralGuard)
    (T := Submonoid.powers (residueSpectral f)) (Ideal.Quotient.mk (divisorIdeal f))
    (Submonoid.map_le_iff_le_comap.mp (by rw [Submonoid.map_powers]; exact le_rfl))

omit [IsDomain (DivisorRing f)] in
private theorem spectralSpecialize_ker :
    RingHom.ker (spectralSpecialize f) = (divisorIdeal f).map spectralClass := by
  rw [spectralSpecialize, IsLocalization.ker_map
    (S := SpectralBase) (T := Submonoid.powers (residueSpectral f)) _ _
    (by rw [Submonoid.map_powers]; rfl)]
  rw [Ideal.mk_ker]
  rfl

omit [IsDomain (DivisorRing f)] in
@[simp] private theorem spectralSpecialize_class (g : Roots) :
    spectralSpecialize f (spectralClass g) =
      algebraMap (DivisorRing f) (ResidueBase f) (Ideal.Quotient.mk (divisorIdeal f) g) := by
  exact IsLocalization.map_eq _ _

private def residueToField (hf : ¬ f ∣ spectralGuard) :
    ResidueBase f →+* FractionRing (DivisorRing f) :=
  IsLocalization.Away.lift (residueSpectral f) (g := algebraMap _ _) (by
    apply isUnit_iff_ne_zero.mpr
    change divisorRoots f spectralGuard ≠ 0
    exact fun h => hf ((divisorRoots_eq_zero f _).mp h))

private theorem residueToField_injective (hf : ¬ f ∣ spectralGuard) :
    Function.Injective (residueToField hf) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (residueSpectral f))
    (residueToField hf)).mpr
  intro a b
  simp only [residueToField, IsLocalization.Away.lift_eq]
  refine ⟨fun h => ?_, fun h => congrArg _ (IsFractionRing.injective (DivisorRing f) _ h)⟩
  simpa only [residueToField, IsLocalization.Away.lift_eq] using congrArg (residueToField hf) h

private theorem residueToField_class (hf : ¬ f ∣ spectralGuard) (g : Roots) :
    residueToField hf (spectralSpecialize f (spectralClass g)) = divisorRoots f g := by
  rw [spectralSpecialize_class, residueToField, IsLocalization.Away.lift_eq]
  rfl

def specializeOrdered (f : Roots) :
    OrderedChart →+* RadicalAlgebra (orderedParameters.map
      (parameterMap (spectralSpecialize f))) :=
  specializeRadicals orderedParameters (parameterMap (spectralSpecialize f))

private theorem spectralSpecialize_surjective (f : Roots) :
    Function.Surjective (spectralSpecialize f) := by
  let : IsLocalization ((Submonoid.powers spectralGuard).map
      (Ideal.Quotient.mk (divisorIdeal f))) (ResidueBase f) := by
    rw [Submonoid.map_powers]
    change IsLocalization (Submonoid.powers (residueSpectral f)) (ResidueBase f)
    infer_instance
  exact IsLocalization.map_surjective_of_surjective (Submonoid.powers spectralGuard)
    SpectralBase (ResidueBase f) Ideal.Quotient.mk_surjective

omit [IsDomain (DivisorRing f)] in
/-- Scheme-theoretic specialization of the finite free chart. -/
theorem specializeOrdered_ker :
    RingHom.ker (specializeOrdered f) = (divisorIdeal f).map rootToChart := by
  rw [specializeOrdered, specializeRadicals_ker, parameterMap_ker, spectralSpecialize_ker,
    Ideal.map_map, Ideal.map_map]
  rfl

/-- The quotient by the extended divisor equation is the literal
specialized two-radical algebra, with all four basis elements retained. -/
def specializeOrdered_quotientEquiv (f : Roots) :
    (OrderedChart ⧸ Ideal.span {rootToChart f}) ≃+*
      RadicalAlgebra (orderedParameters.map (parameterMap (spectralSpecialize f))) := by
  have h : RingHom.ker (specializeOrdered f) = Ideal.span {rootToChart f} := by
    rw [specializeOrdered_ker, divisorIdeal, Ideal.map_span, Set.image_singleton]
  exact h ▸ (specializeOrdered f).quotientKerEquivOfSurjective
    (specializeRadicals_surjective _ _ (parameterMap_surjective _ (spectralSpecialize_surjective f)))

/-- The generic spectral divisor retains a rank-four chart over the
specialized parameter ring. -/
theorem specializeOrdered_finrank (hf : ¬ f ∣ spectralGuard) :
    Module.finrank (ParameterRing (ResidueBase f))
      (RadicalAlgebra (orderedParameters.map (parameterMap (spectralSpecialize f)))) = 4 := by
  let : Nontrivial (ParameterRing (ResidueBase f)) :=
    (parameterEval (residueToField hf) (1 : (FractionRing (DivisorRing f))ˣ) 1).domain_nontrivial
  exact radicalAlgebra_finrank _

private theorem normalized_gap_ne_zero {E : Type*} [Field E] (g : SpectralBase →+* E) :
    g normalizedC - (g normalizedB)^2 ≠ 0 := by
  have hg : g (spectralClass spectralGap) ≠ 0 := by
    rw [← spectralUnit_val (dvd_mul_left spectralGap _)]
    exact (Units.map g.toMonoidHom (spectralUnit (dvd_mul_left spectralGap _))).ne_zero
  have hu : g (↑sumUnit⁻¹ : SpectralBase) ≠ 0 :=
    (Units.map g.toMonoidHom sumUnit⁻¹).ne_zero
  have hs : g (spectralClass rootSum) * g (↑sumUnit⁻¹ : SpectralBase) = 1 := by
    rw [← sumUnit_val, ← map_mul, Units.mul_inv, map_one]
  have he : g normalizedC - (g normalizedB)^2 =
      g (spectralClass spectralGap) * (g (↑sumUnit⁻¹ : SpectralBase))^6 := by
    simp only [normalizedC, normalizedB, spectralGap, map_mul, map_sub, map_pow]
    linear_combination
      -(g (spectralClass spectralC))*(g (↑sumUnit⁻¹ : SpectralBase))^4*
        (g (spectralClass rootSum)*g (↑sumUnit⁻¹ : SpectralBase)+1)*hs
  rw [he]
  exact mul_ne_zero hg (pow_ne_zero _ hu)

/-- The entire specialized algebra is a domain over the ordered-root divisor.
The square classes are tested over its residue fraction field with independent
k and U. -/
theorem specializeOrdered_isDomain (hf : ¬ f ∣ spectralGuard) :
    IsDomain (RadicalAlgebra (orderedParameters.map (parameterMap (spectralSpecialize f)))) := by
  let q := spectralSpecialize f
  let g := residueToField hf
  change IsDomain (RadicalAlgebra
    ((chartParameters spectralTwo spectralTwo_val normalizedA normalizedB normalizedC).map
      (parameterMap q)))
  rw [chartParameters_map]
  have h₂ : (2 : FractionRing (DivisorRing f)) ≠ 0 := by
    let h := (g.comp q).comp spectralComplex
    simpa only [map_ofNat, map_zero] using h.injective.ne (show (2 : ℂ) ≠ 0 by norm_num)
  exact chart_isDomain _ _ _ _ _ g (residueToField_injective hf) h₂
    (normalized_gap_ne_zero (g.comp q))

private theorem no_dvd_guard_of_mem_prime (P : Ideal OrderedChart) [P.IsPrime]
    {p : Roots} (hp : rootToChart p ∈ P) : ¬ p ∣ spectralGuard := by
  intro h
  have hunit : IsUnit (rootToChart spectralGuard) :=
    (IsLocalization.Away.algebraMap_isUnit (S := SpectralBase) spectralGuard).map
      ((algebraMap (ParameterRing SpectralBase) OrderedChart).comp parameterConstant)
  obtain ⟨q, hq⟩ := h
  exact (Ideal.IsPrime.ne_top inferInstance) (P.eq_top_of_isUnit_mem
    (by
      convert Ideal.mul_mem_right (rootToChart q) P hp using 1
      exact (congrArg rootToChart hq).trans (map_mul _ _ _)) hunit)

private theorem rootToChart_injective (hg : spectralGuard ≠ 0) :
    Function.Injective rootToChart := by
  have hloc : Function.Injective spectralClass :=
    IsLocalization.injective SpectralBase (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  let : IsDomain SpectralBase := IsLocalization.isDomain_of_le_nonZeroDivisors (S := SpectralBase)
    (M := Submonoid.powers spectralGuard) (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  have hg' : parameterGuard SpectralBase ≠ 0 := by
    exact mul_ne_zero Polynomial.X_ne_zero (Polynomial.C_ne_zero.mpr Polynomial.X_ne_zero)
  let hpar : Function.Injective (parameterConstant (R := SpectralBase)) :=
    (IsLocalization.injective (ParameterRing SpectralBase)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hg')).comp
        (Polynomial.C_injective.comp Polynomial.C_injective)
  exact (radicalScalar_injective orderedParameters).comp (hpar.comp hloc)

private theorem orderedChart_isDomain (hg : spectralGuard ≠ 0) : IsDomain OrderedChart := by
  let : IsDomain SpectralBase := IsLocalization.isDomain_of_le_nonZeroDivisors (S := SpectralBase)
    (M := Submonoid.powers spectralGuard) (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  let g := algebraMap SpectralBase (FractionRing SpectralBase)
  have h₂ : (2 : FractionRing SpectralBase) ≠ 0 := by
    let c := g.comp spectralComplex
    simpa only [map_ofNat, map_zero] using c.injective.ne (show (2 : ℂ) ≠ 0 by norm_num)
  exact chart_isDomain _ _ _ _ _ g (IsFractionRing.injective SpectralBase _) h₂
    (normalized_gap_ne_zero g)

/-- Every height-one prime containing a nonzero spectral equation is the
scheme-theoretic pullback of its irreducible spectral contraction. -/
theorem heightOne_eq_specializeOrdered_ker (P : Ideal OrderedChart) [P.IsPrime]
    (hP : P.height = 1) (hf : f ≠ 0) (hmem : rootToChart f ∈ P) :
    P = RingHom.ker (specializeOrdered f) := by
  have hguard := no_dvd_guard_of_mem_prime P hmem
  have hg : spectralGuard ≠ 0 := fun hz => hguard (hz ▸ dvd_zero f)
  let : IsDomain OrderedChart := orderedChart_isDomain hg
  let : IsDomain (RadicalAlgebra (orderedParameters.map (parameterMap (spectralSpecialize f)))) :=
    specializeOrdered_isDomain hguard
  let Q := RingHom.ker (specializeOrdered f)
  have hQ : Q.IsPrime := RingHom.ker_isPrime _
  have hQg : Q = Ideal.span {rootToChart f} := by
    change RingHom.ker (specializeOrdered f) = _
    rw [specializeOrdered_ker, divisorIdeal, Ideal.map_span, Set.image_singleton]
  have hQle : Q ≤ P := by rw [hQg, Ideal.span_singleton_le_iff_mem]; exact hmem
  have hQne : Q ≠ ⊥ := by
    rw [hQg, Ne, Ideal.span_singleton_eq_bot]
    exact fun h => hf (rootToChart_injective hg (h.trans (map_zero _).symm))
  apply (eq_of_le_of_not_lt hQle ?_).symm
  intro hlt
  have h := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
  rw [hP] at h
  exact hQne (Ideal.height_eq_zero_iff_eq_bot.mp (Order.lt_one_iff.mp h))

/-- The contraction to the homogeneous root polynomial ring is exactly
the principal prime defining the specialized chart. -/
theorem heightOne_contraction_eq_divisor (P : Ideal OrderedChart) [P.IsPrime]
    (hP : P.height = 1) (hf : f ≠ 0) (hmem : rootToChart f ∈ P) :
    P.comap rootToChart = divisorIdeal f := by
  have hguard := no_dvd_guard_of_mem_prime P hmem
  have hzero : ∀ g : Roots, specializeOrdered f (rootToChart g) = 0 ↔ f ∣ g := by
    intro g
    have hc := residueToField_class hguard g
    change _ = 0 ↔ _
    simp only [specializeOrdered, rootToChart, RingHom.comp_apply, specializeRadicals_scalar,
      parameterMap_constant]
    have hcoeff : Function.Injective
        (algebraMap (ParameterRing (ResidueBase f)) (RadicalAlgebra
          (orderedParameters.map (parameterMap (spectralSpecialize f))))) := by
      exact radicalScalar_injective _
    have hp : Function.Injective (parameterConstant (R := ResidueBase f)) :=
      fun x y h => (residueToField_injective hguard) (by
        simpa only [parameterEval_constant] using congrArg
          (parameterEval (residueToField hguard) (1 : (FractionRing (DivisorRing f))ˣ) 1) h)
    rw [map_eq_zero_iff _ hcoeff, map_eq_zero_iff _ hp]
    rw [← map_eq_zero_iff _ (residueToField_injective hguard), hc, divisorRoots_eq_zero]
  rw [heightOne_eq_specializeOrdered_ker P hP hf hmem]
  ext g
  exact (hzero g).trans Ideal.mem_span_singleton.symm

theorem heightOne_contraction_height (P : Ideal OrderedChart) [P.IsPrime]
    (hP : P.height = 1) (hf : f ≠ 0) (hmem : rootToChart f ∈ P) :
    (P.comap rootToChart).height = 1 := by
  have hprime : (P.comap rootToChart).IsPrime := Ideal.comap_isPrime _ _
  rw [heightOne_contraction_eq_divisor P hP hf hmem]
  apply Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hf)
  intro hu
  have htop : divisorIdeal f = ⊤ := Ideal.span_singleton_eq_top.mpr hu
  exact hprime.ne_top ((heightOne_contraction_eq_divisor P hP hf hmem).trans htop)

private def sectionConstant (f : Roots) [IsDomain (DivisorRing f)] :
    FractionRing (DivisorRing f) →+* SectionField f :=
  (sectionFieldMap f).comp Polynomial.C

private def spectralToSection (h : ¬ f ∣ spectralGuard) : SpectralBase →+* SectionField f :=
  (sectionConstant f).comp ((residueToField h).comp (spectralSpecialize f))

@[simp] private theorem spectralToSection_class (hf : ¬ f ∣ spectralGuard) (g : Roots) :
    spectralToSection hf (spectralClass g) = sectionConstant f (divisorRoots f g) :=
  congrArg (sectionConstant f) (residueToField_class hf g)

private theorem spectralToSection_sum_inv (hf : ¬ f ∣ spectralGuard) :
    spectralToSection hf (↑sumUnit⁻¹ : SpectralBase) =
      (sectionConstant f (divisorRoots f rootSum))⁻¹ := by
  have h : (((sumUnit.map (spectralToSection hf).toMonoidHom : (SectionField f)ˣ)⁻¹ :
      (SectionField f)ˣ) : SectionField f) =
      (spectralToSection hf (↑sumUnit : SpectralBase))⁻¹ :=
    Units.val_inv_eq_inv_val _
  exact h.trans (congrArg Inv.inv ((congrArg (spectralToSection hf) sumUnit_val).trans
    (spectralToSection_class hf rootSum)))

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
private theorem paired_coefficients (f : Roots) [IsDomain (DivisorRing f)] (j : Fin 3) :
    let x := sectionFieldMap f ∘ genericSection (divisorRoots f) j
    let r := x 0
    let s := x 1
    let t := x 2
    let u := x 3
    sectionConstant f (divisorRoots f rootSum) = r+s+(t+u) ∧
    sectionConstant f (divisorRoots f spectralA) = elementaryA r s t u ∧
    sectionConstant f (divisorRoots f spectralB) = elementaryB r s t u ∧
    sectionConstant f (divisorRoots f spectralC) = elementaryC r s t u := by
  let g := (sectionConstant f).comp (divisorRoots f).toRingHom
  change
    g rootSum = g (X (pairing j 0))+g (X (pairing j 1))+(g (X (pairing j 2))+g (X (pairing j 3))) ∧ _
  dsimp only [Function.comp_apply, genericSection]
  fin_cases j <;>
    simp [g, pairing, Equiv.swap_apply_def, rootSum, Fin.sum_univ_four, spectralA, spectralB,
      spectralC, elementaryA, elementaryB, elementaryC, sectionConstant] <;>
    (repeat' apply And.intro) <;> ring_nf
  all_goals simp

private theorem section_point (hf : ¬ f ∣ spectralGuard)
    (m : ℕ) (j : Fin 3) (hj : ¬ f ∣ obstruction m j)
    (τ : SectionField f) (hτ : τ ≠ 0)
    (hbal : let x := sectionFieldMap f ∘ genericSection (divisorRoots f) j
      τ ^ 2 * ((sectionTraceSum x)⁻¹ * sectionImbalance x) =
        (sectionTraceSum x)⁻¹ ^ 3 * sectionInitialBraMixedTrace x) :
    let x := sectionFieldMap f ∘ genericSection (divisorRoots f) j
    ∃ F : OrderedChart →ₐ[ℂ] SectionField f,
      (∀ z : Roots, F (rootToChart z) = sectionConstant f (divisorRoots f z)) ∧
      F ∘ orderedSlice = sectionChart x τ := by
  let x := sectionFieldMap f ∘ genericSection (divisorRoots f) j
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by funext i; fin_cases i <;> rfl
  let g := spectralToSection hf
  obtain ⟨hs, hA, hB, hC⟩ := paired_coefficients f j
  change sectionConstant f (divisorRoots f rootSum) = x 0 + x 1 + (x 2 + x 3) at hs
  change sectionConstant f (divisorRoots f spectralA) = elementaryA (x 0) (x 1) (x 2) (x 3) at hA
  change sectionConstant f (divisorRoots f spectralB) = elementaryB (x 0) (x 1) (x 2) (x 3) at hB
  change sectionConstant f (divisorRoots f spectralC) = elementaryC (x 0) (x 1) (x 2) (x 3) at hC
  have he := spectralToSection_sum_inv hf
  rw [hs] at he
  have hs' : x 0 + x 1 + (x 2 + x 3) ≠ 0 := by
    rw [← hs]
    have hu : IsUnit (g (spectralClass rootSum)) := by
      rw [← sumUnit_val]
      exact (sumUnit.isUnit.map g)
    exact (spectralToSection_class hf rootSum) ▸ hu.ne_zero
  obtain ⟨hα, hβ, h₀, hdb⟩ := genericSection_coordinate_guards m j hj
  obtain ⟨U, k, q, hq⟩ := section_has_coordinateFiber g spectralTwo spectralTwo_val
    normalizedA normalizedB normalizedC (x 0) (x 1) (x 2) (x 3) (x 4) τ hτ
    (by simpa only [← hx] using hbal) hs' hα hβ h₀ hdb
    (by
      simp only [g, normalizedA, map_mul, map_pow, spectralToSection_class, he, hA, add_assoc]
      exact mul_comm _ _)
    (by
      simp only [g, normalizedB, map_mul, map_pow, spectralToSection_class, he, hB, add_assoc]
      exact mul_comm _ _)
    (by
      simp only [g, normalizedC, map_mul, map_pow, spectralToSection_class, he, hC, add_assoc]
      exact mul_comm _ _)
  let base := parameterEval g U k
  let : Algebra (ParameterRing SpectralBase) (SectionField f) := base.toAlgebra
  let point : OrderedChart →ₐ[ParameterRing SpectralBase] SectionField f := radicalLift q.toRadical
  have hroot (z : Roots) : point (rootToChart z) = sectionConstant f (divisorRoots f z) := by
    change point (algebraMap (ParameterRing SpectralBase) OrderedChart
      (parameterConstant (spectralClass z))) = _
    rw [AlgHom.commutes]
    change parameterEval g U k (parameterConstant (spectralClass z)) = _
    rw [parameterEval_constant]
    exact spectralToSection_class hf z
  let F : OrderedChart →ₐ[ℂ] SectionField f :=
    { toRingHom := point.toRingHom
      commutes' := fun z => by
        change point (rootToChart (C z)) = _
        rw [hroot]
        rfl }
  have hpoint : (radicalPoint orderedParameters).toCoordinates.postcompose point = q := by
    rw [← RadicalFiber.toCoordinates_postcompose]
    have h := radicalPoint_postcompose_lift (p := orderedParameters) q.toRadical
    change ((radicalPoint orderedParameters).postcompose point).toCoordinates = q
    exact (congrArg RadicalFiber.toCoordinates h).trans (CoordinateFiber.toRadical_toCoordinates q)
  have hk : point (algebraMap (ParameterRing SpectralBase) OrderedChart
      ↑(parameterK (R := SpectralBase))) = ↑k := by
    rw [AlgHom.commutes]
    exact parameterEval_k g U k
  refine ⟨F, hroot, ?_⟩
  change F ∘ orderedSlice = sectionChart x τ
  rw [hx, hq]
  have hd : F (radicalPoint orderedParameters).toCoordinates.d = q.d :=
    congrArg CoordinateFiber.d hpoint
  have hdb' : F (radicalPoint orderedParameters).toCoordinates.db = q.db :=
    congrArg CoordinateFiber.db hpoint
  have he' : F (radicalPoint orderedParameters).toCoordinates.e = q.e :=
    congrArg CoordinateFiber.e hpoint
  have heb' : F (radicalPoint orderedParameters).toCoordinates.eb = q.eb :=
    congrArg CoordinateFiber.eb hpoint
  have hk' : F (algebraMap (ParameterRing SpectralBase) OrderedChart
      ↑(parameterK (R := SpectralBase))) = ↑k := hk
  funext i
  fin_cases i <;>
    simp [-parameterK_val, orderedSlice, cartesian, half, imaginary, hd, hdb', he', heb', hk']

/-- Common vanishing on the vertical height-one prime supplies the
exact native maximal minors for every unobstructed generic pairing
and every balancing root. -/
theorem genericSectionNativeCritical_of_heightOne {m : ℕ} (P : Ideal OrderedChart) [P.IsPrime]
    (hP : P.height = 1) (hf : f ≠ 0) (hmem : rootToChart f ∈ P)
    (hcof : ∀ i : Fin 10, orderedCofactor m i ∈ P) :
    GenericSectionNativeCritical m f := by
  intro j hj x τ hτ hbal i
  obtain ⟨F, hF, hslice⟩ := section_point (no_dvd_guard_of_mem_prime P hmem) m j hj τ hτ hbal
  have hker : P ≤ RingHom.ker F.toRingHom := by
    rw [heightOne_eq_specializeOrdered_ker P hP hf hmem, specializeOrdered_ker,
      divisorIdeal, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    change F (rootToChart f) = 0
    rw [hF, (divisorRoots_eq_zero f f).mpr dvd_rfl, map_zero]
  have h := RingHom.mem_ker.mp (hker (hcof i))
  have hmap : F.comp (aeval orderedSlice) = aeval (F ∘ orderedSlice) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  change (F.comp (aeval orderedSlice)) (((criticalMatrix m).submatrix i.succAbove id).det) = 0 at h
  rw [hmap, hslice] at h
  rw [Matrix.submatrix_map]
  change ((aeval (sectionChart x τ)).toRingHom.mapMatrix
    ((criticalMatrix m).submatrix i.succAbove id)).det = 0
  rw [← RingHom.map_det]
  exact h

/-- No height-one prime with nonzero contraction can contain the native
maximal minors on the simple nonzero ordered-root chart. -/
theorem no_vertical_prime {m : ℕ} (hm : 3 ≤ m) (P : Ideal OrderedChart) [P.IsPrime]
    (hP : P.height = 1) (hvertical : P.comap rootToChart ≠ ⊥)
    (hcof : ∀ i : Fin 10, orderedCofactor m i ∈ P) : False := by
  have hpr : (P.comap rootToChart).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨f, hmem, hf⟩ := hpr.exists_mem_prime_of_ne_bot hvertical
  let : (divisorIdeal f).IsPrime := (Ideal.span_singleton_prime hf.ne_zero).mpr hf
  let : IsDomain (DivisorRing f) := Ideal.Quotient.isDomain _
  have hg := no_dvd_guard_of_mem_prime P hmem
  have hsum : ¬ f ∣ rootSum := fun h => hg (h.trans (dvd_mul_right rootSum _ |>.trans
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))))
  have hx (i : Fin 4) : ¬ f ∣ (X i : Roots) := fun h =>
    hg (h.trans ((Finset.dvd_prod_of_mem (fun j : Fin 4 => (X j : Roots)) (Finset.mem_univ i)).trans
      ((dvd_mul_left _ rootSum).trans ((dvd_mul_right _ _).trans (dvd_mul_right _ _)))))
  exact no_noncoordinate_prime_of_genericNativeCriticalMatrix hm hf.irreducible hsum hx
    (genericSectionNativeCritical_of_heightOne P hP hf.ne_zero hmem hcof)

/-- The exact raw mass from the radial column of the native matrix. -/
def orderedRawMass (m : ℕ) : OrderedChart :=
  aeval orderedSlice (PeriodicMPSUniformNativeSliceReadout.rawSlicePolynomial m (0, 0))

abbrev MassOpen (m : ℕ) := Localization.Away (orderedRawMass m)

/-- The generic-section implication also holds from a prime on the mass
open. Only the polynomial cofactors are evaluated at the section. -/
theorem genericSectionNativeCritical_of_massOpen_heightOne {m : ℕ}
    (P : Ideal (MassOpen m)) [P.IsPrime] (hP : P.height = 1) (hf : f ≠ 0)
    (hmem : algebraMap OrderedChart (MassOpen m) (rootToChart f) ∈ P)
    (hcof : ∀ i : Fin 10, algebraMap OrderedChart (MassOpen m) (orderedCofactor m i) ∈ P) :
    GenericSectionNativeCritical m f := by
  let Q := P.comap (algebraMap OrderedChart (MassOpen m))
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQ : Q.height = 1 :=
    (IsLocalization.height_under (Submonoid.powers (orderedRawMass m)) P).trans hP
  exact genericSectionNativeCritical_of_heightOne Q hQ hf hmem hcof

/-- Contraction from the mass localization preserves height. Polynomial
cofactor vanishing descends before evaluating a generic section. -/
theorem no_vertical_prime_massOpen {m : ℕ} (hm : 3 ≤ m)
    (P : Ideal (MassOpen m)) [P.IsPrime] (hP : P.height = 1)
    (hvertical : P.comap ((algebraMap OrderedChart (MassOpen m)).comp rootToChart) ≠ ⊥)
    (hcof : ∀ i : Fin 10, algebraMap OrderedChart (MassOpen m) (orderedCofactor m i) ∈ P) :
    False := by
  let Q := P.comap (algebraMap OrderedChart (MassOpen m))
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQ : Q.height = 1 :=
    (IsLocalization.height_under (Submonoid.powers (orderedRawMass m)) P).trans hP
  exact no_vertical_prime hm Q hQ hvertical hcof

end
end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalAmbient
