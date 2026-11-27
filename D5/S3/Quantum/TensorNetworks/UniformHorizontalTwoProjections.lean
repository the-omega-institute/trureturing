/- GID: D5/S3/Quantum/TensorNetworks/UniformHorizontalTwoProjections
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/UniformHorizontalTwoProjections
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Two projected Sylvester tests exclude height-one divisors on a bivariate Laurent torus. -/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Excluding a common divisor on the two-coordinate torus by its two projected resultants. -/

set_option autoImplicit false

namespace UniformHorizontalTwoProjections

open MvPolynomial

variable {K : Type*} [Field K]

abbrev Bivariate (K : Type*) [Field K] := MvPolynomial (Fin 2) K

/-- Each projection retains the indicated variable and passes to the fraction field
of the polynomial ring in the other variable. -/
noncomputable def projection (i : Fin 2) :
    Bivariate K →+* Polynomial (FractionRing (MvPolynomial (Fin 1) K)) :=
  (Polynomial.mapRingHom (algebraMap _ _)).comp
    ((finSuccEquiv K 1).toRingHom.comp (rename (Equiv.swap i 0)).toRingHom)

private theorem exponent_mem_projection (i : Fin 2) {f : Bivariate K}
    {a : Fin 2 →₀ ℕ} (ha : a ∈ f.support) :
    a i ∈ (projection i f).support := by
  classical
  let e := Equiv.swap i (0 : Fin 2)
  change a i ∈ (((finSuccEquiv K 1) (rename e f)).map (algebraMap _ _)).support
  rw [Polynomial.support_map_of_injective _
    (IsFractionRing.injective (MvPolynomial (Fin 1) K) _)]
  apply mem_support_finSuccEquiv.mpr
  refine ⟨a.mapDomain e, ?_, ?_⟩
  · rw [support_rename_of_injective e.injective]
    exact Finset.mem_image_of_mem _ ha
  · change a.mapDomain e 0 = a i
    rw [show (0 : Fin 2) = e i by simp [e], Finsupp.mapDomain_apply_of_injective e.injective]

private theorem support_eq_of_dvd_X_pow {F : Type*} [Field F] {p : Polynomial F}
    {n : ℕ} (h : p ∣ Polynomial.X ^ n) :
    ∃ j : ℕ, ∀ i ∈ p.support, i = j := by
  obtain ⟨j, _, ⟨u, hu⟩⟩ := (dvd_prime_pow (Polynomial.prime_X (R := F)) n).mp h
  obtain ⟨c, _, hc⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have he : p = Polynomial.C c⁻¹ * Polynomial.X ^ j := by
    have hc0 : c ≠ 0 := by
      intro hz
      apply u.ne_zero
      rw [← hc, hz, map_zero]
    calc
      p = Polynomial.C c⁻¹ * (p * ↑u) := by
        rw [← hc, mul_comm p, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      _ = Polynomial.C c⁻¹ * Polynomial.X ^ j := by rw [hu]
  exact ⟨j, fun i hi => Polynomial.mem_support_C_mul_X_pow (he ▸ hi)⟩

/-- A nonzero polynomial dividing a coordinate power in each projection is a
single monomial. The two projections together determine both exponents. -/
theorem eq_monomial_of_projected_dvd_powers {f : Bivariate K} (hf : f ≠ 0)
    (h : ∀ i : Fin 2, ∃ n : ℕ, projection i f ∣ Polynomial.X ^ n) :
    ∃ a : Fin 2 →₀ ℕ, ∃ c : K, c ≠ 0 ∧ f = monomial a c := by
  classical
  obtain ⟨a, ha⟩ : f.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (fun he => hf (support_eq_empty.mp he))
  have support_eq : f.support = {a} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨ha, ?_⟩
    intro b hb
    ext i
    obtain ⟨n, hn⟩ := h i
    obtain ⟨s, hs⟩ := support_eq_of_dvd_X_pow hn
    exact (hs _ (exponent_mem_projection i hb)).trans (hs _ (exponent_mem_projection i ha)).symm
  refine ⟨a, f.coeff a, mem_support_iff.mp ha, ?_⟩
  nth_rw 1 [f.as_sum]
  rw [support_eq, Finset.sum_singleton]

private theorem isCoprime_of_fixed_resultant {F : Type*} [Field F]
    (f g : Polynomial F) {d e : ℕ}
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ e) (hdim : d ≠ 0 ∨ e ≠ 0)
    (h : Polynomial.resultant f g d e ≠ 0) : IsCoprime f g := by
  obtain ⟨u, v, _, _, huv⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hdim
  let scale := Polynomial.C (Polynomial.resultant f g d e)⁻¹
  refine ⟨scale * u, scale * v, ?_⟩
  calc
    _ = scale * (f * u + g * v) := by ring
    _ = 1 := by rw [huv]; simp [scale, ← map_mul, h]

/-- Each axis has a nonzero fixed-degree resultant after clearing monomial factors. -/
def ProjectedResultants (f g : Bivariate K) : Prop :=
  ∀ i : Fin 2,
    ∃ (F G : Polynomial (FractionRing (MvPolynomial (Fin 1) K))) (a b d e : ℕ),
      F.natDegree ≤ d ∧ G.natDegree ≤ e ∧ (d ≠ 0 ∨ e ≠ 0) ∧
        Polynomial.resultant F G d e ≠ 0 ∧
        projection i f = Polynomial.X ^ a * F ∧
        projection i g = Polynomial.X ^ b * G

/-- Monomial factors are the only common prime divisors left after the two
fixed-degree Sylvester tests, with arbitrary powers used to clear the axes. -/
theorem height_one_prime_cannot_contain_pair (P : Ideal (Bivariate K)) [P.IsPrime]
    (hP : P.height = 1) (haxis : ∀ i : Fin 2, X i ∉ P)
    {f g : Bivariate K} (hf : f ∈ P) (hg : g ∈ P)
    (h : ProjectedResultants f g) : False := by
  classical
  obtain ⟨p, hpMem, hp⟩ := (‹P.IsPrime›).exists_mem_prime_of_ne_bot
    (Ideal.ne_bot_of_height_eq_one hP)
  have hpP := Ideal.eq_span_singleton_of_height_eq_one hP hpMem hp
  have hpf : p ∣ f := Ideal.mem_span_singleton.mp (hpP ▸ hf)
  have hpg : p ∣ g := Ideal.mem_span_singleton.mp (hpP ▸ hg)
  have hproj (i : Fin 2) : ∃ n : ℕ, projection i p ∣ Polynomial.X ^ n := by
    obtain ⟨F, G, a, b, d, e, hFd, hGe, hdim, hres, heF, heG⟩ := h i
    obtain ⟨u, v, huv⟩ := isCoprime_of_fixed_resultant F G hFd hGe hdim hres
    refine ⟨a + b, ?_⟩
    have hdF := map_dvd (projection i) hpf
    have hdG := map_dvd (projection i) hpg
    rw [heF] at hdF
    rw [heG] at hdG
    have hs := dvd_add (dvd_mul_of_dvd_right hdF (Polynomial.X ^ b * u))
      (dvd_mul_of_dvd_right hdG (Polynomial.X ^ a * v))
    have hsum : (Polynomial.X ^ b * u) * (Polynomial.X ^ a * F) +
          (Polynomial.X ^ a * v) * (Polynomial.X ^ b * G) = Polynomial.X ^ (a + b) := by
      calc
        _ = Polynomial.X ^ (a + b) * (u * F + v * G) := by rw [pow_add]; ring
        _ = _ := by rw [huv, mul_one]
    exact hsum ▸ hs
  obtain ⟨a, c, hc, he⟩ := eq_monomial_of_projected_dvd_powers hp.ne_zero hproj
  have hpmem := hpMem
  rw [he, monomial_eq] at hpmem
  have hprod : a.prod (fun i e => (X i : Bivariate K) ^ e) ∈ P :=
    (‹P.IsPrime›.mem_or_mem hpmem).resolve_left
      (fun hm => (‹P.IsPrime›.ne_top (P.eq_top_of_isUnit_mem hm (hc.isUnit.map C))))
  unfold Finsupp.prod at hprod
  obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
  exact haxis i (‹P.IsPrime›.mem_of_pow_mem _ hi)

/-- The two projected resultant tests exclude every height-one prime on the
torus, including when the two inputs use different Laurent denominators. -/
theorem height_one_torus_prime_cannot_contain_pair
    {A : Type*} [CommRing A] [Algebra (Bivariate K) A]
    [IsLocalization.Away ((X 0 : Bivariate K) * X 1) A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    {f g : Bivariate K}
    (hf : algebraMap (Bivariate K) A f ∈ P) (hg : algebraMap (Bivariate K) A g ∈ P)
    (h : ProjectedResultants f g) : False := by
  let Q := P.under (Bivariate K)
  have hQ : Q.height = 1 := (IsLocalization.height_under
    (Submonoid.powers ((X 0 : Bivariate K) * X 1)) P).trans hP
  have hne (i : Fin 2) : X i ∉ Q := by
    have hdiv : X i ∣ (X 0 : Bivariate K) * X 1 := by
      fin_cases i
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    exact P.notMem_of_isUnit (IsLocalization.Away.isUnit_of_dvd ((X 0 : Bivariate K) * X 1) hdiv)
  exact height_one_prime_cannot_contain_pair Q hQ hne hf hg h

end UniformHorizontalTwoProjections
