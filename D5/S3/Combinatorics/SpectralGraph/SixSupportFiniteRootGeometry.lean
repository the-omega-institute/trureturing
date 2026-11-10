/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual supplied Nikandish tower and finite-root objects, pending current canonical admission. -/

import D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianPolynomial
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Polynomial.Ideal

/-! Actual finite D-root geometry inside the accepted quadratic field H.
The import MatrixPolynomialComplete02 is the immutable supplied Matrix95 file,
which already contains Tower94. Do not also import a duplicate Tower94 module.
All declarations below concern the accepted actual H, D, y, and f.
Canonical admission is separate from the temporary exact-proof source.
-/

namespace NikandishE3.FiniteDRoot
open Polynomial IsLocalRing WithZero
open scoped QuadraticAlgebra
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
noncomputable section
variable (k : Type*) [Field k] [CharZero k]

abbrev R := k[X]
abbrev Order := QuadraticAlgebra (R k) (pk k D) 0
abbrev Closure := integralClosure (R k) (H k)

@[simp] theorem base_H_re (p : R k) :
    (algebraMap (R k) (H k) p).re = algebraMap (R k) (K k) p := rfl
@[simp] theorem base_H_im (p : R k) : (algebraMap (R k) (H k) p).im = 0 := rfl

/-- The polynomial generator in the actual quadratic order. -/
def Y : Order k := QuadraticAlgebra.omega

/-- This sends the two polynomial coefficients to their actual rational functions. -/
def intoH : Order k →ₐ[R k] H k where
  toFun z := ⟨algebraMap (R k) (K k) z.re, algebraMap (R k) (K k) z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' z w := by ext <;> simp
  map_mul' z w := by
    apply QuadraticAlgebra.ext
    · change algebraMap (R k) (K k) (z.re * w.re + pk k D * z.im * w.im) =
        algebraMap (R k) (K k) z.re * algebraMap (R k) (K k) w.re +
        rf k D * algebraMap (R k) (K k) z.im * algebraMap (R k) (K k) w.im
      simp [rf]
    · change algebraMap (R k) (K k) (z.re * w.im + z.im * w.re + 0 * z.im * w.im) =
        algebraMap (R k) (K k) z.re * algebraMap (R k) (K k) w.im +
        algebraMap (R k) (K k) z.im * algebraMap (R k) (K k) w.re + 0 * _ * _
      simp
  commutes' p := by ext <;> simp

theorem intoH_injective : Function.Injective (intoH k) := by
  intro z w h
  apply QuadraticAlgebra.ext
  · exact IsFractionRing.injective (R k) (K k) (congrArg QuadraticAlgebra.re h)
  · exact IsFractionRing.injective (R k) (K k) (congrArg QuadraticAlgebra.im h)

instance orderHAlgebra : Algebra (Order k) (H k) := (intoH k).toRingHom.toAlgebra
instance orderHTower : IsScalarTower (R k) (Order k) (H k) :=
  IsScalarTower.of_algebraMap_eq (fun p => (intoH k).commutes p |>.symm)
instance orderDomain : IsDomain (Order k) :=
  Function.Injective.isDomain (intoH k).toRingHom (intoH_injective k)
instance orderHFaithful : FaithfulSMul (Order k) (H k) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (intoH_injective k)

@[simp] theorem intoH_Y : intoH k (Y k) = y k := by
  apply QuadraticAlgebra.ext <;> simp [intoH, Y, y]
@[simp] theorem intoH_algebraMap (p : R k) :
    intoH k (algebraMap (R k) (Order k) p) = algebraMap (R k) (H k) p :=
  (intoH k).commutes p

theorem Y_squared : (Y k)^2 = algebraMap (R k) (Order k) (pk k D) := by
  simp [Y, pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]

instance orderNoetherian : IsNoetherianRing (Order k) := IsNoetherianRing.of_finite (R k) (Order k)

instance baseHTorsionFree : Module.IsTorsionFree (R k) (H k) :=
  Module.IsTorsionFree.trans (K k)

instance closureHFractions : IsFractionRing (Closure k) (H k) :=
  integralClosure.isFractionRing_of_finite_extension (K k) (H k)
instance closureFinite : Module.Finite (R k) (Closure k) :=
  IsIntegralClosure.finite (R k) (K k) (H k) (Closure k)
instance closureFree : Module.Free (R k) (Closure k) :=
  IsIntegralClosure.module_free (R k) (K k) (H k) (Closure k)
instance closureDedekind : IsDedekindDomain (Closure k) :=
  IsIntegralClosure.isDedekindDomain (R k) (K k) (H k) (Closure k)

/-- Conjugation over k[b], with the scalar compatibility proved componentwise. -/
def conjugation : H k →ₐ[R k] H k where
  __ := starRingEnd (H k)
  commutes' p := by
    change star (algebraMap (R k) (H k) p) = algebraMap (R k) (H k) p
    apply QuadraticAlgebra.ext <;> simp

theorem integral_re (x : H k) (hx : IsIntegral (R k) x) :
    IsIntegral (R k) x.re := by
  have hC2 : (RatFunc.C : k →+* K k) (2 : k) = (2 : K k) := map_ofNat _ 2
  have hs : IsIntegral (R k) (star x) := hx.map (conjugation k)
  have hh : IsIntegral (R k) (algebraMap (R k) (H k) (C (1/2 : k))) :=
    isIntegral_algebraMap
  have hr : IsIntegral (R k) (algebraMap (K k) (H k) x.re) := by
    convert (hx.add hs).mul hh using 1
    apply QuadraticAlgebra.ext <;>
      simp [conjugation, Algebra.smul_def, RatFunc.algebraMap_C, map_div₀, hC2] <;>
      norm_num <;> field_simp <;> ring
  exact isIntegral_algebraMap_iff.mp hr

theorem integral_im_square_times_D (x : H k) (hx : IsIntegral (R k) x) :
    IsIntegral (R k) (x.im^2 * rf k D) := by
  have hr : IsIntegral (R k) (algebraMap (K k) (H k) x.re) :=
    (integral_re k x hx).algebraMap
  have hs : IsIntegral (R k) (algebraMap (K k) (H k) (x.im^2 * rf k D)) := by
    convert (hx.sub hr).pow 2 using 1
    apply QuadraticAlgebra.ext <;> simp [pow_two] <;> ring
  exact isIntegral_algebraMap_iff.mp hs

/-- Squarefreeness of the accepted D removes the actual reduced denominator. -/
theorem integral_im_polynomial (x : H k) (hx : IsIntegral (R k) x) :
    ∃ p : R k, algebraMap (R k) (K k) p = x.im := by
  let u := x.im
  let i := algebraMap (R k) (K k)
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (integral_im_square_times_D k x hx)
  have hden : i u.denom ≠ 0 :=
    by simpa only [map_zero] using
      (IsFractionRing.injective (R k) (K k)).ne (RatFunc.denom_ne_zero u)
  have hnum : i u.num = u * i u.denom :=
    (div_eq_iff hden).mp (RatFunc.num_div_denom u)
  have hcross : u.num^2 * pk k D = c * u.denom^2 := by
    apply IsFractionRing.injective (R k) (K k)
    calc
      i (u.num^2 * pk k D) = (u^2 * rf k D) * (i u.denom)^2 := by
        simp only [map_mul, map_pow]
        change i u.num ^ 2 * i (pk k D) = (u^2 * i (pk k D)) * i u.denom ^ 2
        rw [hnum]
        ring
      _ = i (c * u.denom^2) := by
        rw [← hc, map_mul, map_pow]
  have hdiv : u.denom^2 ∣ u.num^2 * pk k D :=
    ⟨c, by rw [hcross]; ring⟩
  have hdivD : u.denom^2 ∣ pk k D :=
    ((RatFunc.isCoprime_num_denom u).symm.pow (m := 2) (n := 2)).dvd_of_dvd_mul_left hdiv
  have hunit : IsUnit u.denom :=
    (D_separable k).squarefree u.denom (by simpa only [pow_two] using hdivD)
  obtain ⟨a, ha, hea⟩ := Polynomial.isUnit_iff.mp hunit
  have hmono := RatFunc.monic_denom u
  rw [← hea] at hmono
  have ha1 : a = 1 := by simpa only [Polynomial.Monic, Polynomial.leadingCoeff_C] using hmono
  have hd1 : u.denom = 1 := by simpa [ha1] using hea.symm
  refine ⟨u.num, ?_⟩
  simpa [hd1] using RatFunc.num_div_denom u

/-- The explicit quadratic order really is the integral closure, as a conclusion. -/
instance order_isIntegralClosure : IsIntegralClosure (Order k) (R k) (H k) where
  algebraMap_injective := intoH_injective k
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (integral_re k x hx)
      obtain ⟨q, hq⟩ := integral_im_polynomial k x hx
      exact ⟨⟨p, q⟩, QuadraticAlgebra.ext hp hq⟩
    · rintro ⟨z, rfl⟩
      exact (IsIntegral.of_finite (R k) z).map (intoH k)

def orderClosureEquiv : Order k ≃ₐ[R k] Closure k :=
  IsIntegralClosure.equiv (R k) (Order k) (H k) (Closure k)

instance orderHFractions : IsFractionRing (Order k) (H k) :=
  IsIntegralClosure.isFractionRing_of_finite_extension (R k) (K k) (H k) (Order k)
instance orderDedekind : IsDedekindDomain (Order k) :=
  IsIntegralClosure.isDedekindDomain (R k) (K k) (H k) (Order k)

open AlgebraicGeometry CategoryTheory

abbrev affineOrder : Scheme := Spec (CommRingCat.of (Order k))
abbrev affineClosure : Scheme := Spec (CommRingCat.of (Closure k))
abbrev affineLine : Scheme := Spec (CommRingCat.of (R k))
def finiteMap : affineClosure k ⟶ affineLine k :=
  Spec.map (CommRingCat.ofHom (algebraMap (R k) (Closure k)))

instance finiteMapFinite : AlgebraicGeometry.IsFinite (finiteMap k) := by
  apply (AlgebraicGeometry.IsFinite.SpecMap_iff _).mpr
  exact (RingHom.finite_algebraMap).mpr inferInstance

instance closureFunctionFieldAlgebra : Algebra (Closure k) (affineClosure k).functionField :=
  (AlgebraicGeometry.StructureSheaf.toStalk (CommRingCat.of (Closure k))
    (genericPoint (affineClosure k))).hom.toAlgebra
instance closureFunctionFieldFractions : IsFractionRing (Closure k) (affineClosure k).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine (CommRingCat.of (Closure k))

/-- Identification of the actual affine normalization's function field with H. -/
def closureFunctionFieldEquiv : (affineClosure k).functionField ≃ₐ[Closure k] H k :=
  IsLocalization.algEquiv (nonZeroDivisors (Closure k)) (affineClosure k).functionField (H k)

abbrev DRoot := {r : k // (pk k D).eval r = 0}

def baseIdeal (r : DRoot k) : Ideal (R k) := Ideal.span {X - C r.1}
def delta (r : DRoot k) : Order k := algebraMap (R k) (Order k) (X - C r.1)

instance baseIdeal_maximal (r : DRoot k) : (baseIdeal k r).IsMaximal := by
  rw [baseIdeal, ← Polynomial.ker_evalRingHom]
  exact RingHom.ker_isMaximal_of_surjective (evalRingHom r.1) (Polynomial.eval_surjective r.1)

/-- Evaluation at the actual point (r,0), using the actual equation y²=D. -/
def rootEval (r : DRoot k) : Order k →+* k where
  toFun z := z.re.eval r.1
  map_zero' := by simp
  map_one' := by simp
  map_add' z w := by simp
  map_mul' z w := by simp [r.2]

theorem rootEval_surjective (r : DRoot k) : Function.Surjective (rootEval k r) := by
  intro a
  exact ⟨algebraMap (R k) (Order k) (C a), by simp [rootEval]⟩

def rootIdeal (r : DRoot k) : Ideal (Order k) := RingHom.ker (rootEval k r)
instance rootIdeal_maximal (r : DRoot k) : (rootIdeal k r).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (rootEval k r) (rootEval_surjective k r)
instance rootIdeal_prime (r : DRoot k) : (rootIdeal k r).IsPrime :=
  (rootIdeal_maximal k r).isPrime

@[simp] theorem mem_rootIdeal (r : DRoot k) (z : Order k) :
    z ∈ rootIdeal k r ↔ z.re.eval r.1 = 0 := Iff.rfl

theorem delta_mem (r : DRoot k) : delta k r ∈ rootIdeal k r := by
  simp [delta]
theorem Y_mem (r : DRoot k) : Y k ∈ rootIdeal k r := by simp [Y]

theorem rootIdeal_under (r : DRoot k) : (rootIdeal k r).under (R k) = baseIdeal k r := by
  rw [baseIdeal, ← Polynomial.ker_evalRingHom]
  ext p
  rfl

instance rootIdeal_liesOver (r : DRoot k) : (rootIdeal k r).LiesOver (baseIdeal k r) :=
  (Ideal.liesOver_iff _ _).mpr (rootIdeal_under k r).symm

theorem rootIdeal_span (r : DRoot k) :
    rootIdeal k r = Ideal.span {delta k r, Y k} := by
  apply le_antisymm
  · intro z hz
    change z.re.eval r.1 = 0 at hz
    obtain ⟨p, hp⟩ := (Polynomial.dvd_iff_isRoot).mpr hz
    apply Ideal.mem_span_pair.mpr
    refine ⟨algebraMap (R k) (Order k) p,
      algebraMap (R k) (Order k) z.im, ?_⟩
    apply QuadraticAlgebra.ext <;> simp [delta, Y, hp] <;> ring
  · exact Ideal.span_le.mpr (by
      intro z hz
      rcases hz with rfl | rfl
      · exact delta_mem k r
      · exact Y_mem k r)

/-- A specific polynomial quotient, not a chosen valuation or ramification datum. -/
def rootQuotient (r : DRoot k) : R k :=
  Classical.choose ((Polynomial.dvd_iff_isRoot).mpr r.2)

theorem D_factor (r : DRoot k) : pk k D = (X - C r.1) * rootQuotient k r :=
  Classical.choose_spec ((Polynomial.dvd_iff_isRoot).mpr r.2)

theorem rootQuotient_eval (r : DRoot k) :
    (rootQuotient k r).eval r.1 = (pk k D).derivative.eval r.1 := by
  have he := congrArg (fun p : R k => p.derivative.eval r.1) (D_factor k r)
  simpa only [derivative_mul, derivative_sub, derivative_X, derivative_C,
    sub_zero, eval_add, eval_mul, eval_one, eval_sub, eval_X, eval_C,
    sub_self, one_mul, zero_mul, add_zero] using he.symm

theorem rootQuotient_eval_ne_zero (r : DRoot k) : (rootQuotient k r).eval r.1 ≠ 0 := by
  rw [rootQuotient_eval]
  simpa only [eval₂_id] using
    (D_separable k).eval₂_derivative_ne_zero (RingHom.id k) (by simpa using r.2)

theorem Y_square_factor (r : DRoot k) :
    (Y k)^2 = delta k r * algebraMap (R k) (Order k) (rootQuotient k r) := by
  calc
    (Y k)^2 = algebraMap (R k) (Order k) (pk k D) := Y_squared k
    _ = algebraMap (R k) (Order k) ((X - C r.1) * rootQuotient k r) :=
      congrArg (algebraMap (R k) (Order k)) (D_factor k r)
    _ = _ := map_mul _ _ _

/-- Uniqueness among actual prime ideals above (b-r), rather than a point proxy. -/
theorem unique_prime_above (r : DRoot k) (Q : Ideal (Order k)) [Q.IsPrime]
    (hQ : Q.under (R k) = baseIdeal k r) : Q = rootIdeal k r := by
  have hd : delta k r ∈ Q := by
    change X - C r.1 ∈ Q.under (R k)
    rw [hQ]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hy : Y k ∈ Q := Ideal.IsPrime.mem_of_pow_mem inferInstance 2 (by
    rw [Y_square_factor k r]
    exact Q.mul_mem_right _ hd)
  have hle : rootIdeal k r ≤ Q := by
    rw [rootIdeal_span]
    exact Ideal.span_le.mpr (by
      intro z hz
      rcases hz with rfl | rfl
      · exact hd
      · exact hy)
  exact ((rootIdeal_maximal k r).eq_of_le Ideal.IsPrime.ne_top' hle).symm

def orderResidueEquiv (r : DRoot k) : (Order k ⧸ rootIdeal k r) ≃+* k :=
  (rootEval k r).quotientKerEquivOfSurjective (rootEval_surjective k r)

abbrev Local (r : DRoot k) := Localization.AtPrime (rootIdeal k r)
def localY (r : DRoot k) : Local k r := algebraMap (Order k) (Local k r) (Y k)
def localDelta (r : DRoot k) : Local k r := algebraMap (Order k) (Local k r) (delta k r)
def localQuotient (r : DRoot k) : Local k r :=
  algebraMap (Order k) (Local k r)
    (algebraMap (R k) (Order k) (rootQuotient k r))

theorem localQuotient_unit (r : DRoot k) : IsUnit (localQuotient k r) := by
  apply (IsLocalization.AtPrime.isUnit_to_map_iff (Local k r) (rootIdeal k r) _).mpr
  exact rootQuotient_eval_ne_zero k r

theorem localY_square (r : DRoot k) :
    (localY k r)^2 = localDelta k r * localQuotient k r := by
  simpa only [localY, localDelta, localQuotient, map_pow, map_mul] using
    congrArg (algebraMap (Order k) (Local k r)) (Y_square_factor k r)

theorem localDelta_in_y (r : DRoot k) :
    localDelta k r ∈ Ideal.span {localY k r} := by
  obtain ⟨u, hu⟩ := localQuotient_unit k r
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨localY k r * (↑u⁻¹ : Local k r), ?_⟩
  have he := localY_square k r
  rw [← hu] at he
  calc
    (localY k r * ↑u⁻¹) * localY k r = (localY k r)^2 * ↑u⁻¹ := by ring
    _ = localDelta k r := by rw [he]; simp [mul_assoc]

theorem local_maximalIdeal (r : DRoot k) :
    IsLocalRing.maximalIdeal (Local k r) = Ideal.span {localY k r} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  have he := congrArg (Ideal.map (algebraMap (Order k) (Local k r))) (rootIdeal_span k r)
  rw [he, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  change Ideal.span {localDelta k r, localY k r} = Ideal.span {localY k r}
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    rcases hz with rfl | rfl
    · exact localDelta_in_y k r
    · exact Ideal.subset_span (Set.mem_singleton _)
  · exact Ideal.span_mono (by simp)

theorem localY_ne_zero (r : DRoot k) : localY k r ≠ 0 := by
  intro he
  have hY : Y k = 0 := IsLocalization.injective (Local k r)
    (rootIdeal k r).primeCompl_le_nonZeroDivisors (by simpa [localY] using he)
  have him := congrArg QuadraticAlgebra.im hY
  simpa [Y] using him

theorem local_not_field (r : DRoot k) : ¬ IsField (Local k r) := by
  intro h
  apply localY_ne_zero k r
  have hm : IsLocalRing.maximalIdeal (Local k r) = ⊥ :=
    (isField_iff_maximalIdeal_eq).mp h
  rw [local_maximalIdeal] at hm
  exact Ideal.span_singleton_eq_bot.mp hm

instance local_dvr (r : DRoot k) : IsDiscreteValuationRing (Local k r) := by
  apply ((IsDiscreteValuationRing.TFAE (Local k r) (local_not_field k r)).out 5 1).mp
  rw [local_maximalIdeal]
  infer_instance

theorem localY_irreducible (r : DRoot k) : Irreducible (localY k r) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr (local_maximalIdeal k r)

instance orderStalkAlgebra (r : DRoot k) : Algebra (Order k)
    ((affineOrder k).presheaf.stalk (⟨rootIdeal k r, inferInstance⟩ : PrimeSpectrum (Order k))) :=
  AlgebraicGeometry.StructureSheaf.stalkAlgebra (CommRingCat.of (Order k)) _

/-- The affine stalk is the actual localization just constructed. -/
def stalkEquiv (r : DRoot k) : Local k r ≃ₐ[Order k]
    ((affineOrder k).presheaf.stalk (⟨rootIdeal k r, inferInstance⟩ : PrimeSpectrum (Order k))) :=
  AlgebraicGeometry.StructureSheaf.stalkIso (Order k) ⟨rootIdeal k r, inferInstance⟩

/-- Localization embeds into the SAME H by inverting its nonzero denominators. -/
def localIntoH (r : DRoot k) : Local k r →+* H k :=
  IsLocalization.lift (S := Local k r) (g := (intoH k).toRingHom) (fun s => by
    apply isUnit_iff_ne_zero.mpr
    have hs : (s : Order k) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp
      ((rootIdeal k r).primeCompl_le_nonZeroDivisors s.2)
    change intoH k (s : Order k) ≠ 0
    simpa only [map_zero] using (intoH_injective k).ne hs)

instance localHAlgebra (r : DRoot k) : Algebra (Local k r) (H k) :=
  (localIntoH k r).toAlgebra
instance localHTower (r : DRoot k) : IsScalarTower (Order k) (Local k r) (H k) :=
  IsScalarTower.of_algebraMap_eq (fun z => by
    change intoH k z = localIntoH k r (algebraMap (Order k) (Local k r) z)
    exact (IsLocalization.lift_eq _ _).symm)
instance localHFractions (r : DRoot k) : IsFractionRing (Local k r) (H k) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (rootIdeal k r).primeCompl
    (Local k r) (H k)

@[simp] theorem localIntoH_Y (r : DRoot k) :
    algebraMap (Local k r) (H k) (localY k r) = y k := by
  rw [localY, ← IsScalarTower.algebraMap_apply (Order k) (Local k r) (H k)]
  exact intoH_Y k

@[simp] theorem localIntoH_delta (r : DRoot k) :
    algebraMap (Local k r) (H k) (localDelta k r) =
      algebraMap (R k) (H k) (X - C r.1) := by
  rw [localDelta, ← IsScalarTower.algebraMap_apply (Order k) (Local k r) (H k)]
  exact (intoH k).commutes _

def normalizedValuation (r : DRoot k) : Valuation (H k) ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal (Local k r)).valuation (H k)

theorem valuation_y (r : DRoot k) :
    normalizedValuation k r (y k) = WithZero.exp (-1 : ℤ) := by
  rw [← localIntoH_Y k r]
  change (IsDiscreteValuationRing.maximalIdeal (Local k r)).valuation (H k)
    (algebraMap (Local k r) (H k) (localY k r)) = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
    (localY_ne_zero k r) (local_maximalIdeal k r)

theorem valuation_local_unit (r : DRoot k) (z : Local k r) (hz : IsUnit z) :
    normalizedValuation k r (algebraMap (Local k r) (H k) z) = 1 := by
  apply (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (IsDiscreteValuationRing.maximalIdeal (Local k r))).mpr
  change z ∉ IsLocalRing.maximalIdeal (Local k r)
  simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hz

theorem valuation_delta (r : DRoot k) :
    normalizedValuation k r (algebraMap (R k) (H k) (X - C r.1)) =
      WithZero.exp (-2 : ℤ) := by
  have he := congrArg (fun z : Local k r =>
    normalizedValuation k r (algebraMap (Local k r) (H k) z)) (localY_square k r)
  simp only [map_pow, map_mul, localIntoH_Y, localIntoH_delta, valuation_y,
    valuation_local_unit k r _ (localQuotient_unit k r), mul_one] at he
  rw [← he]
  norm_num [pow_two, ← WithZero.exp_add]

theorem mapped_baseIdeal_square (r : DRoot k) :
    (baseIdeal k r).map (algebraMap (R k) (Local k r)) =
      IsLocalRing.maximalIdeal (Local k r)^2 := by
  rw [baseIdeal, Ideal.map_span, Set.image_singleton, local_maximalIdeal,
    Ideal.span_singleton_pow]
  change Ideal.span {localDelta k r} = Ideal.span {(localY k r)^2}
  obtain ⟨u, hu⟩ := localQuotient_unit k r
  rw [localY_square, ← hu, mul_comm (localDelta k r)]
  exact (Ideal.span_singleton_mul_left_unit u.isUnit (localDelta k r)).symm

/-- The library's actual length definition of ramification index gives e=2. -/
theorem ramification_two (r : DRoot k) : (rootIdeal k r).ramificationIdx (R k) = 2 := by
  rw [Ideal.ramificationIdx_eq (baseIdeal k r) (rootIdeal k r), mapped_baseIdeal_square,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]

end
end NikandishE3.FiniteDRoot
