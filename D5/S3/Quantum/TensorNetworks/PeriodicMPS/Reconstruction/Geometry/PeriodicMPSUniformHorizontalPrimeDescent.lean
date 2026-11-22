/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalPrimeDescent
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalPrimeDescent
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Two projected resultants exclude horizontal height-one primes containing the exact ordered native cofactors. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalAmbient
import D5.S3.Quantum.TensorNetworks.UniformHorizontalTwoProjections
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.GoingUp

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHorizontalPrimeDescent

open PeriodicMPSUniformVerticalAmbient
open PeriodicMPSUniformVerticalPrimeExclusion (Roots rootSum)
open PeriodicMPSUniformSpectralRadicalAlgebra
open UniformHorizontalTwoProjections
open scoped TensorProduct

open private spectralB spectralC orderedChart_isDomain rootToChart_injective from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalAmbient
open private parameterPolynomialMap from
  D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalAmbientAlgebra

noncomputable section

private theorem spectralGuard_ne_zero : spectralGuard ≠ 0 := by
  intro hz
  have h := congrArg (MvPolynomial.eval (fun i : Fin 4 => (i.val : ℂ) + 1)) hz
  norm_num [spectralGuard, spectralGap, simpleRoots, spectralB, spectralC, elementaryB,
    elementaryC, rootSum, Fin.sum_univ_succ, Fin.prod_univ_succ] at h

abbrev GenericField := FractionRing Roots
abbrev GenericTorus := ParameterRing GenericField

private instance : IsDomain GenericTorus :=
  IsLocalization.isDomain_of_le_nonZeroDivisors GenericTorus
    (M := Submonoid.powers (parameterGuard GenericField))
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (mul_ne_zero Polynomial.X_ne_zero (Polynomial.C_ne_zero.mpr Polynomial.X_ne_zero)))

private theorem spectralPowers_le :
    Submonoid.powers spectralGuard ≤ nonZeroDivisors Roots :=
  powers_le_nonZeroDivisors_of_noZeroDivisors spectralGuard_ne_zero

local instance : Algebra SpectralBase GenericField :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ spectralPowers_le

local instance : IsScalarTower Roots SpectralBase GenericField :=
  IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ spectralPowers_le

/-- Invert the nonzero ordered-root coefficients. -/
def spectralToGeneric : SpectralBase →+* GenericField := algebraMap _ _

private abbrev spectralDenominators : Submonoid SpectralBase :=
  (nonZeroDivisors Roots).map spectralClass

private instance spectralFieldLocalization :
    IsLocalization spectralDenominators GenericField :=
  IsLocalization.isLocalization_of_submonoid_le _ _ _ _ spectralPowers_le

def parametersToGeneric : ParameterRing SpectralBase →+* GenericTorus :=
  parameterMap spectralToGeneric

/-- The generic fiber uses the same monic quadratic tower as the ordered chart. -/
def genericParameters : Parameters GenericTorus := orderedParameters.map parametersToGeneric

abbrev GenericChart := RadicalAlgebra genericParameters

/-- Base change of the actual ordered determinant chart. -/
def orderedToGeneric : OrderedChart →+* GenericChart :=
  specializeRadicals orderedParameters parametersToGeneric

local instance : Algebra (ParameterRing SpectralBase) GenericTorus :=
  parametersToGeneric.toAlgebra

local instance : Algebra OrderedChart GenericChart := orderedToGeneric.toAlgebra

attribute [local instance] Polynomial.algebra

private theorem parameterLocalization :
    IsLocalization (spectralDenominators.map parameterConstant) GenericTorus := by
  let R := ParameterPolynomials SpectralBase
  let S := ParameterPolynomials GenericField
  let M := Submonoid.powers (parameterGuard SpectralBase)
  let N : Submonoid R := (spectralDenominators.map Polynomial.C).map Polynomial.C
  let : IsLocalization (spectralDenominators.map Polynomial.C) (Polynomial GenericField) :=
    Polynomial.isLocalization spectralDenominators GenericField
  let : IsLocalization N S :=
    Polynomial.isLocalization (spectralDenominators.map Polynomial.C) (Polynomial GenericField)
  let : Algebra R GenericTorus := Algebra.compHom _ (algebraMap R S)
  let : SMul R GenericTorus := (inferInstance : Algebra R GenericTorus).toSMul
  let : SMul S GenericTorus := (inferInstance : Algebra S GenericTorus).toSMul
  let : SMul (ParameterRing SpectralBase) GenericTorus :=
    (inferInstance : Algebra (ParameterRing SpectralBase) GenericTorus).toSMul
  let : IsScalarTower R S GenericTorus := .of_algebraMap_eq' rfl
  let : IsScalarTower R (ParameterRing SpectralBase) GenericTorus := by
    refine IsScalarTower.of_algebraMap_eq
      (R := R) (S := ParameterRing SpectralBase) (A := GenericTorus) ?_
    intro x
    change algebraMap S GenericTorus (parameterPolynomialMap spectralToGeneric x) =
      parametersToGeneric (algebraMap R (ParameterRing SpectralBase) x)
    unfold parametersToGeneric parameterMap
    rw [IsLocalization.map_eq]
  let : IsLocalization (Algebra.algebraMapSubmonoid S M) GenericTorus := by
    change IsLocalization (M.map (parameterPolynomialMap spectralToGeneric)) GenericTorus
    rw [show M.map (parameterPolynomialMap spectralToGeneric) =
        Submonoid.powers (parameterGuard GenericField) by
      rw [Submonoid.map_powers]
      simp [parameterPolynomialMap, parameterGuard]]
    infer_instance
  have h := IsLocalization.commutes (ParameterRing SpectralBase) S GenericTorus M N
  rwa [show Algebra.algebraMapSubmonoid (ParameterRing SpectralBase) N =
    spectralDenominators.map parameterConstant by
      change ((spectralDenominators.map Polynomial.C.toMonoidHom).map
          Polynomial.C.toMonoidHom).map (algebraMap R (ParameterRing SpectralBase)).toMonoidHom =
        spectralDenominators.map (parameterConstant (R := SpectralBase)).toMonoidHom
      rw [Submonoid.map_map, Submonoid.map_map]
      rfl] at h

private abbrev orderedDenominators : Submonoid OrderedChart :=
  (nonZeroDivisors Roots).map rootToChart

private theorem orderedGenericLocalization :
    IsLocalization orderedDenominators GenericChart := by
  let R := ParameterRing SpectralBase
  let S := GenericTorus
  let M := spectralDenominators.map (parameterConstant (R := SpectralBase))
  let : IsLocalization M S := parameterLocalization
  let : Algebra OrderedChart (S ⊗[R] OrderedChart) := Algebra.TensorProduct.rightAlgebra
  let e : S ⊗[R] OrderedChart ≃ₐ[OrderedChart] GenericChart :=
    { (radicalBaseChange (p := orderedParameters) S).toRingEquiv with
      commutes' := fun _ => rfl }
  have h := IsLocalization.isLocalization_of_algEquiv
    (Algebra.algebraMapSubmonoid OrderedChart M) e
  rwa [show Algebra.algebraMapSubmonoid OrderedChart M = orderedDenominators by
    change (((nonZeroDivisors Roots).map spectralClass.toMonoidHom).map
      (parameterConstant (R := SpectralBase)).toMonoidHom).map
        (algebraMap R OrderedChart).toMonoidHom =
      (nonZeroDivisors Roots).map rootToChart.toMonoidHom
    rw [Submonoid.map_map, Submonoid.map_map]
    rfl] at h

private instance : IsDomain GenericChart := by
  let : IsDomain OrderedChart := orderedChart_isDomain spectralGuard_ne_zero
  let := orderedGenericLocalization
  apply IsLocalization.isDomain_of_le_nonZeroDivisors GenericChart (M := orderedDenominators)
  exact map_le_nonZeroDivisors_of_injective rootToChart
    (rootToChart_injective spectralGuard_ne_zero) le_rfl

/-- A horizontal prime extends to the generic chart with its height and contraction
preserved. The extension is along the canonical specialization map. -/
theorem generic_prime_of_horizontal (P : Ideal OrderedChart) [P.IsPrime]
    (hP : P.height = 1) (horiz : P.comap rootToChart = ⊥) :
    ∃ Q : Ideal GenericChart, Q.IsPrime ∧ Q.height = 1 ∧
      Q.comap orderedToGeneric = P := by
  let := orderedGenericLocalization
  have hd : Disjoint (orderedDenominators : Set OrderedChart) (P : Set OrderedChart) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨r, hr, rfl⟩ hp
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr)
      (Ideal.mem_bot.mp (horiz ▸ (show r ∈ P.comap rootToChart from hp)))
  let Q := P.map orderedToGeneric
  have : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint orderedDenominators GenericChart P ‹_› hd
  have hQ : Q.under OrderedChart = P :=
    IsLocalization.under_map_of_isPrime_disjoint orderedDenominators GenericChart ‹_› hd
  have hh := IsLocalization.height_under orderedDenominators Q
  rw [hQ, hP] at hh
  exact ⟨Q, inferInstance, hh.symm, hQ⟩

/-- The finite free generic chart gives going-down. Integral incomparability
against the zero prime in the chart gives the lower bound. -/
theorem generic_torus_contraction_height (Q : Ideal GenericChart) [Q.IsPrime]
    (hQ : Q.height = 1) : (Q.under GenericTorus).height = 1 := by
  let p := Q.under GenericTorus
  let : Q.LiesOver p := ⟨rfl⟩
  have hup : p.height ≤ 1 := by
    rw [← hQ, (⟨p, inferInstance⟩ : PrimeSpectrum GenericTorus).height_eq_orderHeight,
      (⟨Q, inferInstance⟩ : PrimeSpectrum GenericChart).height_eq_orderHeight]
    refine Order.height_le_iff'.mpr fun l hl => ?_
    have : Q.LiesOver l.last.asIdeal := by rw [hl]; infer_instance
    obtain ⟨L, hlen, hlast, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l Q
    rw [← hlen]
    exact Order.height_le_iff'.mp le_rfl hlast
  have hp : (⊥ : Ideal GenericTorus) < p := by
    have h := Ideal.IsIntegral.under_lt_under (R := GenericTorus)
      (bot_lt_iff_ne_bot.mpr (Ideal.ne_bot_of_height_eq_one hQ))
    change (⊥ : Ideal GenericChart).comap (algebraMap GenericTorus GenericChart) < p at h
    rwa [Ideal.comap_bot_of_injective _ (radicalScalar_injective genericParameters)] at h
  exact le_antisymm hup (Order.one_le_iff_ne_zero.mpr
    (fun hz => hp.ne (Ideal.height_eq_zero_iff_eq_bot.mp hz).symm))

/-- The bivariate presentation takes coordinate 0 to U and coordinate 1 to k. -/
private def bivariateEquiv : Bivariate GenericField ≃+* ParameterPolynomials GenericField :=
  (MvPolynomial.finSuccEquiv GenericField 1).toRingEquiv.trans
    (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv GenericField (Fin 1)).toRingEquiv)

def bivariateToTorus : Bivariate GenericField →+* GenericTorus :=
  (algebraMap (ParameterPolynomials GenericField) GenericTorus).comp bivariateEquiv.toRingHom

local instance : Algebra (Bivariate GenericField) GenericTorus := bivariateToTorus.toAlgebra

open MvPolynomial in
private theorem bivariateEquiv_guard :
    bivariateEquiv ((X 0 : Bivariate GenericField) * X 1) = parameterGuard GenericField := by
  rw [map_mul]
  change _ = Polynomial.X * Polynomial.C Polynomial.X
  change Polynomial.map _ (finSuccEquiv GenericField 1 (X 0)) *
    Polynomial.map _ (finSuccEquiv GenericField 1 (X 1)) = _
  rw [finSuccEquiv_X_zero, show (1 : Fin 2) = (0 : Fin 1).succ by decide,
    finSuccEquiv_X_succ, Polynomial.map_X, Polynomial.map_C]
  simp [uniqueAlgEquiv_apply]

private instance : IsLocalization.Away
    ((MvPolynomial.X 0 : Bivariate GenericField) * MvPolynomial.X 1) GenericTorus :=
  IsLocalization.of_ringEquiv_left bivariateEquiv
    (M₁ := Submonoid.powers (parameterGuard GenericField))
    (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers bivariateEquiv_guard)
    (fun _ => rfl)

/-- A single power of the product of the two torus coordinates clears any
denominator in the parameter ring. -/
theorem exists_monomial_numerator (z : GenericTorus) :
    ∃ (f : Bivariate GenericField) (n : ℕ), bivariateToTorus f =
      (↑(parameterU (R := GenericField)) : GenericTorus) ^ n *
      (↑(parameterK (R := GenericField)) : GenericTorus) ^ n * z := by
  obtain ⟨⟨f, t⟩, ht⟩ :=
    IsLocalization.surj (Submonoid.powers (parameterGuard GenericField)) z
  obtain ⟨n, hn⟩ := t.property
  refine ⟨bivariateEquiv.symm f, n, ?_⟩
  change algebraMap (ParameterPolynomials GenericField) GenericTorus
    (bivariateEquiv (bivariateEquiv.symm f)) = _
  rw [RingEquiv.apply_symm_apply, ← ht, ← hn, map_pow, parameterU_val, parameterK_val]
  change z * (algebraMap (ParameterPolynomials GenericField) GenericTorus
    (Polynomial.X * Polynomial.C Polynomial.X)) ^ n = _
  rw [map_mul, mul_pow, mul_comm z]

/-- A contracted scalar is the product of the linear form and its partial conjugate. -/
theorem scalar_contraction {R : Type*} [CommRing R] (p : Parameters R) (α β : R) :
    let a := algebraMap R (RadicalAlgebra p) α * rootD p
    let b := algebraMap R (RadicalAlgebra p) β * rootS p
    (a + b) * (a - b) =
      algebraMap R (RadicalAlgebra p) (p.deltaD * α ^ 2 - p.deltaS * β ^ 2) := by
  dsimp only
  rw [show ∀ a b : RadicalAlgebra p, (a + b) * (a - b) = a ^ 2 - b ^ 2 by
    intros; ring]
  simp only [mul_pow, rootD_sq, rootS_sq, map_sub, map_mul, map_pow]
  rw [mul_comm (_ ^ 2) _, mul_comm (_ ^ 2) _]

/-- The exact numerator of a selected cofactor contraction belongs to the
contracted prime. Separate axis powers may be used for each numerator. -/
theorem numerator_mem_of_cofactor {m : ℕ} {i : Fin 10}
    (Q : Ideal GenericChart) (hcofactor : orderedToGeneric (orderedCofactor m i) ∈ Q)
    {α β : GenericTorus} {f : Bivariate GenericField} {a b : ℕ}
    (hlinear : orderedToGeneric (orderedCofactor m i) =
      algebraMap GenericTorus GenericChart α * rootD genericParameters +
      algebraMap GenericTorus GenericChart β * rootS genericParameters)
    (hclear : bivariateToTorus f =
      (↑(parameterU (R := GenericField)) : GenericTorus) ^ a *
      (↑(parameterK (R := GenericField)) : GenericTorus) ^ b *
      (genericParameters.deltaD * α ^ 2 - genericParameters.deltaS * β ^ 2)) :
    bivariateToTorus f ∈ Q.under GenericTorus := by
  rw [hlinear] at hcofactor
  have hscalar := Q.mul_mem_right
    (algebraMap GenericTorus GenericChart α * rootD genericParameters -
      algebraMap GenericTorus GenericChart β * rootS genericParameters) hcofactor
  rw [scalar_contraction] at hscalar
  change algebraMap GenericTorus GenericChart (bivariateToTorus f) ∈ Q
  rw [hclear, map_mul]
  exact Q.mul_mem_left _ hscalar

/-- Two exact projected certificates for the cleared contractions of actual
cofactors exclude a horizontal height-one prime containing all the cofactors. -/
theorem no_horizontal_prime {m : ℕ} (i j : Fin 10)
    {α β γ δ : GenericTorus} {f g : Bivariate GenericField} {a b c d : ℕ}
    (hi : orderedToGeneric (orderedCofactor m i) =
      algebraMap GenericTorus GenericChart α * rootD genericParameters +
      algebraMap GenericTorus GenericChart β * rootS genericParameters)
    (hj : orderedToGeneric (orderedCofactor m j) =
      algebraMap GenericTorus GenericChart γ * rootD genericParameters +
      algebraMap GenericTorus GenericChart δ * rootS genericParameters)
    (hf : bivariateToTorus f =
      (↑(parameterU (R := GenericField)) : GenericTorus) ^ a *
      (↑(parameterK (R := GenericField)) : GenericTorus) ^ b *
      (genericParameters.deltaD * α ^ 2 - genericParameters.deltaS * β ^ 2))
    (hg : bivariateToTorus g =
      (↑(parameterU (R := GenericField)) : GenericTorus) ^ c *
      (↑(parameterK (R := GenericField)) : GenericTorus) ^ d *
      (genericParameters.deltaD * γ ^ 2 - genericParameters.deltaS * δ ^ 2))
    (hcert : ProjectedResultants f g)
    (P : Ideal OrderedChart) [P.IsPrime] (hP : P.height = 1)
    (horiz : P.comap rootToChart = ⊥)
    (hmem : ∀ l, orderedCofactor m l ∈ P) : False := by
  obtain ⟨Q, hprime, hheight, hcontract⟩ := generic_prime_of_horizontal P hP horiz
  let := hprime
  have hl (l : Fin 10) : orderedToGeneric (orderedCofactor m l) ∈ Q :=
    show orderedCofactor m l ∈ Q.comap orderedToGeneric from hcontract.symm ▸ hmem l
  exact height_one_torus_prime_cannot_contain_pair (Q.under GenericTorus)
    (generic_torus_contraction_height Q hheight)
    (numerator_mem_of_cofactor Q (hl i) hi hf) (numerator_mem_of_cofactor Q (hl j) hj hg) hcert

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHorizontalPrimeDescent
