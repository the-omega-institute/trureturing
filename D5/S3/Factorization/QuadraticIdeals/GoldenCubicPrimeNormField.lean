/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicPrimeNormField
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicPrimeNormField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-norm cubic irreducibility and real cyclic splitting fields. -/

import D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Topology.Order.IntermediateValue

open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
open NumberField IsDedekindDomain
open scoped WithZero
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimeNormField

theorem prime_norm_cubic_no_integer_projective_zero (pi : EisensteinOrder) (hpi0 : pi ≠ 0)
    (hprime : (Ideal.span {pi}).IsPrime) (hcop : IsCoprime pi (star pi)) :
    ∀ u v : ℤ, u ≠ 0 ∨ v ≠ 0 →
      (pi.re^2-pi.im^2)*u^3 - 3*(2*pi.re*pi.im-pi.im^2)*u^2*v +
        3*((2*pi.re*pi.im-pi.im^2)-(pi.re^2-pi.im^2))*u*v^2 +
        (pi.re^2-pi.im^2)*v^3 ≠ 0 := by
  classical
  let K := CyclotomicField 3 ℚ
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
  let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 K := Classical.choice eisenstein_cyclotomic_equiv_exists
  letI : IsDomain EisensteinOrder := φ.toRingEquiv.isDomain_iff.mpr inferInstance
  let f : EisensteinOrder →+* K := (algebraMap (𝓞 K) K).comp φ.toRingHom
  have hf : Function.Injective f := RingOfIntegers.coe_injective.comp φ.injective
  let p : 𝓞 K := φ pi
  have hp0 : p ≠ 0 := by simpa only [p, map_zero] using φ.injective.ne hpi0
  have hpPrime : (Ideal.span {p}).IsPrime := by
    apply (Ideal.span_singleton_prime hp0).mpr
    exact (MulEquiv.prime_iff φ).mpr ((Ideal.span_singleton_prime hpi0).mp hprime)
  let V : HeightOneSpectrum (𝓞 K) := {
    asIdeal := Ideal.span {p}
    isPrime := hpPrime
    ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp0
  }
  letI : V.asIdeal.IsPrime := hpPrime
  let ν := V.valuation K
  have hdiag : WithZero.log (ν (f pi)) = -1 := by
    change WithZero.log (V.valuation K (p : K)) = -1
    rw [HeightOneSpectrum.valuation_of_algebraMap, V.intValuation_singleton hp0 rfl]
    rfl
  have hbar : ν (f (star pi)) = 1 := by
    apply (V.valuation_eq_one_iff_notMem (K := K)).mpr
    exact Ideal.IsPrime.notMem_of_isCoprime_of_mem (hcop.map φ.toRingHom)
      (Ideal.subset_span (Set.mem_singleton p))
  have hwUnit : IsUnit (QuadraticAlgebra.omega : EisensteinOrder) := by
    apply IsUnit.of_mul_eq_one (-(1 + QuadraticAlgebra.omega))
    rw [mul_neg, mul_add, mul_one, QuadraticAlgebra.omega_mul_omega_eq_add]
    simp
  have hw : ν (f QuadraticAlgebra.omega) = 1 :=
    (V.valuation_eq_one_iff_notMem (K := K)).mpr
      (Ideal.notMem_of_isUnit V.asIdeal (hwUnit.map φ.toRingHom))
  have hsw : ν (f (star QuadraticAlgebra.omega)) = 1 :=
    (V.valuation_eq_one_iff_notMem (K := K)).mpr
      (Ideal.notMem_of_isUnit V.asIdeal
        ((hwUnit.map (starRingEnd EisensteinOrder)).map φ.toRingHom))
  intro u v huv hfzero
  let z : EisensteinOrder := ⟨u, v⟩
  have hz : z ≠ 0 := by
    intro heq
    have hre := congrArg QuadraticAlgebra.re heq
    have him := congrArg QuadraticAlgebra.im heq
    simp only [z, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero] at hre him
    exact huv.elim (fun hu => hu hre) (fun hv => hv him)
  have hpz : pi^2*z^3 ≠ 0 := mul_ne_zero (pow_ne_zero _ hpi0) (pow_ne_zero _ hz)
  let t := pi^2*z^3
  have htre : t.re = 0 := by
    have hcalc : t.re = (pi.re^2-pi.im^2)*u^3 -
        3*(2*pi.re*pi.im-pi.im^2)*u^2*v +
        3*((2*pi.re*pi.im-pi.im^2)-(pi.re^2-pi.im^2))*u*v^2 +
        (pi.re^2-pi.im^2)*v^3 := by
      norm_num [t, z, pow_succ, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
      ring
    exact hcalc.trans hfzero
  have ht : t = (t.im : EisensteinOrder) * QuadraticAlgebra.omega := by
    apply QuadraticAlgebra.ext
    · simpa [QuadraticAlgebra.re_mul, QuadraticAlgebra.omega,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast] using htre
    · simp [QuadraticAlgebra.im_mul, QuadraticAlgebra.omega,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]
  have hst : star t = (t.im : EisensteinOrder) * star QuadraticAlgebra.omega := by
    simpa only [star_mul, star_intCast, mul_comm] using congrArg star ht
  have hleft : ν (f t) = ν (f (t.im : EisensteinOrder)) := by
    calc
      ν (f t) = ν (f ((t.im : EisensteinOrder) * QuadraticAlgebra.omega)) :=
        congrArg (fun e => ν (f e)) ht
      _ = _ := by rw [map_mul, map_mul, hw, mul_one]
  have hright : ν (f (star t)) = ν (f (t.im : EisensteinOrder)) := by
    calc
      ν (f (star t)) = ν (f ((t.im : EisensteinOrder) * star QuadraticAlgebra.omega)) :=
        congrArg (fun e => ν (f e)) hst
      _ = _ := by rw [map_mul, map_mul, hsw, mul_one]
  have hval : ν (f t) = ν (f (star t)) := hleft.trans hright.symm
  have hs : star t = (star pi)^2*(star z)^3 := by simp [t]
  have hsPi0 : star pi ≠ 0 := star_ne_zero.mpr hpi0
  have hsZ0 : star z ≠ 0 := star_ne_zero.mpr hz
  have hlog := congrArg WithZero.log hval
  change WithZero.log (ν (f (pi^2*z^3))) = _ at hlog
  rw [hs, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    map_mul, map_mul, map_pow, map_pow, map_pow, map_pow] at hlog
  rw [WithZero.log_mul (pow_ne_zero _ (ν.ne_zero_iff.mpr (by simpa only [map_zero] using hf.ne hpi0)))
      (pow_ne_zero _ (ν.ne_zero_iff.mpr (by simpa only [map_zero] using hf.ne hz))),
    WithZero.log_mul (pow_ne_zero _ (ν.ne_zero_iff.mpr (by simpa only [map_zero] using hf.ne hsPi0)))
      (pow_ne_zero _ (ν.ne_zero_iff.mpr (by simpa only [map_zero] using hf.ne hsZ0))),
    WithZero.log_pow, WithZero.log_pow, WithZero.log_pow, WithZero.log_pow,
    hdiag, hbar, WithZero.log_one] at hlog
  simp only [nsmul_eq_mul] at hlog
  omega

-- A rational affine root clears to a nonzero integer projective pair.
private theorem pi_irreducible_actual (pi : EisensteinOrder) (hpi0 : pi ≠ 0)
    (hprime : (Ideal.span {pi}).IsPrime) (hcop : IsCoprime pi (star pi)) :
    let A := pi.re^2-pi.im^2
    let D := 2*pi.re*pi.im-pi.im^2
    Irreducible ((⟨(A : ℚ), (-3*D : ℤ), (3*(D-A) : ℤ), (A : ℚ)⟩ : Cubic ℚ).toPoly) := by
  let A : ℤ := pi.re^2-pi.im^2
  let D : ℤ := 2*pi.re*pi.im-pi.im^2
  let c : Cubic ℚ := ⟨(A : ℚ), (-3*D : ℤ), (3*(D-A) : ℤ), (A : ℚ)⟩
  let p := c.toPoly
  change Irreducible p
  have hnz := prime_norm_cubic_no_integer_projective_zero pi hpi0 hprime hcop
  have hA : A ≠ 0 := by
    simpa [A, D] using hnz 1 0 (Or.inl (by decide : (1 : ℤ) ≠ 0))
  have hdeg : p.natDegree = 3 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (Cubic.degree_of_a_ne_zero (show c.a ≠ 0 from by
        dsimp [c]
        exact_mod_cast hA))
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by rw [hdeg]; decide)
  intro r hr
  have hv : (r.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr r.den_ne_zero
  apply hnz r.num (r.den : ℤ) (Or.inr hv)
  have hd : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_ne_zero
  change p.eval r = 0 at hr
  rw [← Rat.num_div_den r] at hr
  dsimp [p, c, Cubic.toPoly] at hr
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X] at hr
  have he : (A : ℚ)*(r.num : ℚ)^3 - 3*(D : ℚ)*(r.num : ℚ)^2*(r.den : ℚ) +
      3*((D : ℚ)-(A : ℚ))*(r.num : ℚ)*(r.den : ℚ)^2 +
      (A : ℚ)*(r.den : ℚ)^3 = 0 := by
    field_simp [hd] at hr
    push_cast at hr
    linear_combination hr
  have heZ : A*r.num^3 - 3*D*r.num^2*(r.den : ℤ) +
      3*(D-A)*r.num*(r.den : ℤ)^2 + A*(r.den : ℤ)^3 = 0 := by
    exact_mod_cast he
  exact heZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial
open scoped IntermediateField

variable {F : Type*} [Field F]

private def goldenCubic (A D x : F) : F :=
  A*x^3 - 3*D*x^2 + 3*(D-A)*x + A

private def rotate (x : F) : F := 1 / (1-x)
private def rotateTwice (x : F) : F := (x-1) / x

private theorem goldenCubic_field_structure (A D : ℚ) (hA : A ≠ 0)
    (hirr : Irreducible
      ((⟨A, -3*D, 3*(D-A), A⟩ : Cubic ℚ).toPoly)) :
    let p := (⟨A, -3*D, 3*(D-A), A⟩ : Cubic ℚ).toPoly
    Module.finrank ℚ p.SplittingField = 3 ∧
      IsCyclic p.Gal ∧ NumberField.IsTotallyReal p.SplittingField := by
  have goldenCubic_root_orbit : ∀ {F : Type} [Field F] (A D r x : F) (hA : A ≠ 0)
      (hr : goldenCubic A D r = 0) (hx : goldenCubic A D x = 0),
      x = r ∨ x = rotate r ∨ x = rotateTwice r := by
    intro F instField A D r x hA hr hx
    have hr0 : r ≠ 0 := by
      intro h
      subst r
      have hf0 : goldenCubic A D 0 = A := by dsimp [goldenCubic]; ring
      exact hA (hf0 ▸ hr)
    have hr1 : r ≠ 1 := by
      intro h
      subst r
      have hf1 : goldenCubic A D 1 = -A := by dsimp [goldenCubic]; ring
      exact hA (neg_eq_zero.mp (hf1 ▸ hr))
    have hidentity : r*(r-1) *
        (A*(x-r)*(x-rotate r)*(x-rotateTwice r)-goldenCubic A D x) =
        -x*(x-1)*goldenCubic A D r := by
      dsimp [goldenCubic, rotate, rotateTwice]
      field_simp [hr0, sub_ne_zero.mpr hr1.symm]
      ring
    have hfactor : goldenCubic A D x =
        A*(x-r)*(x-rotate r)*(x-rotateTwice r) := by
      simp only [hr, mul_zero] at hidentity
      have hzero : A*(x-r)*(x-rotate r)*(x-rotateTwice r) -
          goldenCubic A D x = 0 :=
        (mul_eq_zero.mp hidentity).resolve_left
          (mul_ne_zero hr0 (sub_ne_zero.mpr hr1))
      exact (sub_eq_zero.mp hzero).symm
    have h := hfactor
    rw [hx] at h
    have hzero : x-r = 0 ∨ x-rotate r = 0 ∨ x-rotateTwice r = 0 := by
      simpa [mul_eq_zero, hA, or_assoc] using h.symm
    rcases hzero with h | h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h))
  classical
  let p : ℚ[X] := (⟨A, -3*D, 3*(D-A), A⟩ : Cubic ℚ).toPoly
  let K := p.SplittingField
  letI : NumberField K := ⟨⟩
  change Module.finrank ℚ K = 3 ∧ IsCyclic p.Gal ∧ NumberField.IsTotallyReal K
  have hdeg : p.natDegree = 3 := Polynomial.natDegree_eq_of_degree_eq_some
    (Cubic.degree_of_a_ne_zero hA)
  have hdegree : p.degree ≠ 0 := by
    rw [show p.degree = 3 from Cubic.degree_of_a_ne_zero hA]
    decide
  have hmap : p.map (algebraMap ℚ K) =
      (⟨(A : K), -3*(D : K), 3*((D : K)-(A : K)), (A : K)⟩ : Cubic K).toPoly := by
    simp [p, Cubic.toPoly]
  have hroot (x : K) (hx : x ∈ p.rootSet K) :
      goldenCubic (A : K) (D : K) x = 0 := by
    have he := (Polynomial.mem_rootSet.mp hx).2
    rw [← eval_map_algebraMap, hmap] at he
    simpa [Cubic.toPoly, goldenCubic, sub_eq_add_neg, mul_assoc] using he
  obtain ⟨α, hαpoly⟩ : ∃ α : K, (p.map (algebraMap ℚ K)).eval α = 0 :=
    (SplittingField.splits p).exists_eval_eq_zero (by rwa [degree_map])
  have hα : goldenCubic (A : K) (D : K) α = 0 := by
    apply hroot
    apply Polynomial.mem_rootSet.mpr
    constructor
    · exact hirr.ne_zero
    · rw [← eval_map_algebraMap]
      exact hαpoly
  have hAK : (A : K) ≠ 0 := by exact_mod_cast hA
  have hrootsettop : IntermediateField.adjoin ℚ (p.rootSet K) = ⊤ :=
    (isSplittingField_iff_intermediateField.mp
      (Polynomial.IsSplittingField.splittingField p)).2
  have hsingle : ℚ⟮α⟯ = (⊤ : IntermediateField ℚ K) := by
    apply top_unique
    rw [← hrootsettop]
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rcases goldenCubic_root_orbit (A : K) (D : K) α x hAK hα (hroot x hx) with
      h | h | h
    · subst x
      exact IntermediateField.mem_adjoin_simple_self ℚ α
    · subst x
      dsimp only [rotate]
      exact div_mem (one_mem _) (sub_mem (one_mem _) (IntermediateField.mem_adjoin_simple_self ℚ α))
    · subst x
      dsimp only [rotateTwice]
      exact div_mem
        (sub_mem (IntermediateField.mem_adjoin_simple_self ℚ α) (one_mem _))
        (IntermediateField.mem_adjoin_simple_self ℚ α)
  have hαeval : aeval α p = 0 := by
    rw [← eval_map_algebraMap]
    exact hαpoly
  have hmin := minpoly.eq_of_irreducible hirr hαeval
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hirr.ne_zero
  have hfinrank : Module.finrank ℚ K = 3 := by
    rw [← IntermediateField.finrank_top', ← hsingle,
      IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ α), ← hmin,
      Polynomial.natDegree_mul_C (inv_ne_zero hlc), hdeg]
  have hcyclic : IsCyclic p.Gal := by
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply isCyclic_of_prime_card (p := 3)
    rw [Polynomial.Gal.card_of_separable hirr.separable]
    exact hfinrank
  have hrealRoot : ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      goldenCubic (A : ℝ) (D : ℝ) r = 0 := by
    have hAR : (A : ℝ) ≠ 0 := by exact_mod_cast hA
    let g : ℝ → ℝ := fun x => (A : ℝ) * goldenCubic (A : ℝ) (D : ℝ) x
    have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
      dsimp [g, goldenCubic]
      fun_prop
    have hg0 : g 0 = (A : ℝ)^2 := by dsimp [g, goldenCubic]; ring
    have hg1 : g 1 = -((A : ℝ)^2) := by dsimp [g, goldenCubic]; ring
    have hsq : 0 < (A : ℝ)^2 := sq_pos_of_ne_zero hAR
    have h0 : (0 : ℝ) ∈ Set.Ioo (g 1) (g 0) := by
      rw [hg0, hg1]
      exact ⟨by linarith, hsq⟩
    obtain ⟨r, hrange, hgr⟩ :=
      (intermediate_value_Ioo' (by norm_num : (0 : ℝ) ≤ 1) hgcont) h0
    refine ⟨r, hrange.1, hrange.2, ?_⟩
    exact (mul_eq_zero.mp hgr).resolve_left hAR
  obtain ⟨r, hr0, hr1, hr⟩ := hrealRoot
  have hrC : goldenCubic (A : ℂ) (D : ℂ) (r : ℂ) = 0 := by
    simpa [goldenCubic] using congrArg (algebraMap ℝ ℂ) hr
  have hAC : (A : ℂ) ≠ 0 := by exact_mod_cast hA
  have hrealroot (z : ℂ) (hz : goldenCubic (A : ℂ) (D : ℂ) z = 0) :
      star z = z := by
    rcases goldenCubic_root_orbit (A : ℂ) (D : ℂ) (r : ℂ) z hAC hrC hz with
      h | h | h
    · rw [h]
      simp
    · rw [h, show rotate (r : ℂ) = ((rotate r : ℝ) : ℂ) by
        simp [rotate]]
      simp
    · rw [h, show rotateTwice (r : ℂ) = ((rotateTwice r : ℝ) : ℂ) by
        simp [rotateTwice]]
      simp
  have hrootReal (f : K →+* ℂ) (x : K) (hx : x ∈ p.rootSet K) :
      star (f x) = f x := by
    have he := congrArg f (hroot x hx)
    have hz : goldenCubic (A : ℂ) (D : ℂ) (f x) = 0 := by
      simpa [goldenCubic, map_add, map_sub, map_mul, map_pow, map_ofNat] using he
    exact hrealroot (f x) hz
  have htotally : NumberField.IsTotallyReal K := by
    refine ⟨fun w => NumberField.InfinitePlace.isReal_iff.mpr ?_⟩
    rw [NumberField.ComplexEmbedding.isReal_iff]
    apply RingHom.ext
    intro x
    change star (w.embedding x) = w.embedding x
    have hx : x ∈ IntermediateField.adjoin ℚ (p.rootSet K) := by
      rw [hrootsettop]
      trivial
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
        exact hrootReal w.embedding y hy
    | algebraMap q =>
        simp
    | add y z _ _ ihy ihz =>
        simpa only [map_add, star_add, ihy, ihz]
    | inv y _ ih =>
        simpa only [map_inv₀, star_inv₀, ih]
    | mul y z _ _ ihy ihz =>
        simpa only [map_mul, star_mul', ihy, ihz]
  exact ⟨hfinrank, hcyclic, htotally⟩
theorem golden_cubic_prime_norm_field (pi : EisensteinOrder) (P : ℕ) (hpi0 : pi ≠ 0)
    (hprime : (Ideal.span {pi}).IsPrime) (hcop : IsCoprime pi (star pi))
    (hnorm : QuadraticAlgebra.norm pi = (P : ℤ)) :
    let A : ℤ := pi.re^2-pi.im^2
    let D : ℤ := 2*pi.re*pi.im-pi.im^2
    let p : ℚ[X] :=
      (⟨(A : ℚ), (-3*D : ℤ), (3*(D-A) : ℤ), (A : ℚ)⟩ : Cubic ℚ).toPoly
    Irreducible p ∧ Module.finrank ℚ p.SplittingField = 3 ∧ IsCyclic p.Gal ∧
      NumberField.IsTotallyReal p.SplittingField ∧
      (⟨A, -3*D, 3*(D-A), A⟩ : Cubic ℤ).discr = 81*(P : ℤ)^4 := by
  let A : ℤ := pi.re^2-pi.im^2
  let D : ℤ := 2*pi.re*pi.im-pi.im^2
  let p : ℚ[X] :=
    (⟨(A : ℚ), (-3*D : ℤ), (3*(D-A) : ℤ), (A : ℚ)⟩ : Cubic ℚ).toPoly
  change Irreducible p ∧ Module.finrank ℚ p.SplittingField = 3 ∧ IsCyclic p.Gal ∧
    NumberField.IsTotallyReal p.SplittingField ∧
    (⟨A, -3*D, 3*(D-A), A⟩ : Cubic ℤ).discr = 81*(P : ℤ)^4
  have hnz := prime_norm_cubic_no_integer_projective_zero pi hpi0 hprime hcop
  have hA : A ≠ 0 := by
    simpa [A, D] using hnz 1 0 (Or.inl (by decide : (1 : ℤ) ≠ 0))
  have hirr : Irreducible p := by
    simpa [p, A, D] using pi_irreducible_actual pi hpi0 hprime hcop
  have hirr' : Irreducible
      ((⟨(A : ℚ), -3*(D : ℚ), 3*((D : ℚ)-(A : ℚ)), (A : ℚ)⟩ : Cubic ℚ).toPoly) := by
    simpa [p] using hirr
  have hp_eq : p =
      ((⟨(A : ℚ), -3*(D : ℚ), 3*((D : ℚ)-(A : ℚ)), (A : ℚ)⟩ : Cubic ℚ).toPoly) := by
    simp [p]
  have hstructure : Module.finrank ℚ p.SplittingField = 3 ∧
      IsCyclic p.Gal ∧ NumberField.IsTotallyReal p.SplittingField := by
    rw [hp_eq]
    exact goldenCubic_field_structure (A : ℚ) (D : ℚ)
      (by exact_mod_cast hA) hirr'
  have hnormCoord : pi.re^2-pi.re*pi.im+pi.im^2 = (P : ℤ) := by
    rw [QuadraticAlgebra.norm_def] at hnorm
    nlinarith [hnorm]
  have hdisc : (⟨A, -3*D, 3*(D-A), A⟩ : Cubic ℤ).discr =
      81*(P : ℤ)^4 := by
    have hformula : (⟨A, -3*D, 3*(D-A), A⟩ : Cubic ℤ).discr =
        81*(A^2-A*D+D^2)^2 := by
      dsimp [Cubic.discr]
      ring
    have hsquare : A^2-A*D+D^2 =
        (pi.re^2-pi.re*pi.im+pi.im^2)^2 := by
      dsimp [A, D]
      ring
    rw [hformula, hsquare, hnormCoord]
    ring
  exact ⟨hirr, hstructure.1, hstructure.2.1, hstructure.2.2, hdisc⟩


end D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimeNormField
