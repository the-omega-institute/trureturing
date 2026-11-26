/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPSWeightedLineSpecialization
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPSWeightedLineSpecialization
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous]
   utility: none
   digest: Full weighted degree on a line preserves nonunit divisors of homogeneous polynomials. -/
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

/-! A full-degree specialization of one polynomial suffices to detect any
nonunit divisor shared by two polynomials. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSWeightedLineSpecialization

open MvPolynomial

variable {σ K : Type*} [Field K]

noncomputable section

private def degreeExpansion (w : σ → ℕ) :
    MvPolynomial σ K →+* Polynomial (MvPolynomial σ K) :=
  eval₂Hom (Polynomial.C.comp C) (fun i => Polynomial.C (X i) * Polynomial.X ^ w i)

private lemma degreeExpansion_monomial (w : σ → ℕ) (d : σ →₀ ℕ) (c : K) :
    degreeExpansion w (monomial d c) = Polynomial.monomial (Finsupp.weight w d) (monomial d c) := by
  classical
  unfold degreeExpansion
  rw [eval₂Hom_monomial]
  simp only [RingHom.comp_apply, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    ← map_pow, ← map_prod, ← pow_mul, Finset.prod_pow_eq_pow_sum,
    ← Polynomial.C_mul_X_pow_eq_monomial, monomial_eq, Polynomial.C_mul, mul_assoc]
  congr 2
  apply congrArg (fun n : ℕ => (Polynomial.X : Polynomial (MvPolynomial σ K)) ^ n)
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun i _ => Nat.mul_comm _ _

private lemma degreeExpansion_coeff (w : σ → ℕ) (p : MvPolynomial σ K) (n : ℕ) :
    (degreeExpansion w p).coeff n = weightedHomogeneousComponent w n p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [degreeExpansion_monomial, weightedHomogeneousComponent_of_mem
      (isWeightedHomogeneous_monomial w d c rfl)]
    simp [Polynomial.coeff_monomial, eq_comm]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]

private lemma weight_le_expansion_degree (w : σ → ℕ) {p : MvPolynomial σ K}
    {d : σ →₀ ℕ} (hd : d ∈ p.support) : Finsupp.weight w d ≤ (degreeExpansion w p).natDegree := by
  apply Polynomial.le_natDegree_of_ne_zero
  intro h
  rw [degreeExpansion_coeff] at h
  have hz := congrArg (fun q : MvPolynomial σ K => q.coeff d) h
  simp [coeff_weightedHomogeneousComponent, mem_support_iff.mp hd] at hz

private lemma degreeExpansion_ne_zero (w : σ → ℕ) {p : MvPolynomial σ K} (hp : p ≠ 0) :
    degreeExpansion w p ≠ 0 := by
  intro hz
  apply hp
  apply MvPolynomial.ext
  intro m
  have hh := congrArg (fun P : Polynomial (MvPolynomial σ K) =>
    (P.coeff (Finsupp.weight w m)).coeff m) hz
  simpa [degreeExpansion_coeff, coeff_weightedHomogeneousComponent] using hh

private lemma natDegree_eval_le (w : σ → ℕ) (p : MvPolynomial σ K)
    (L : σ → Polynomial K) (hL : ∀ i, (L i).natDegree ≤ w i) :
    (eval₂Hom Polynomial.C L p).natDegree ≤ (degreeExpansion w p).natDegree := by
  classical
  change (p.eval₂ Polynomial.C L).natDegree ≤ _
  rw [eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  calc
    _ ≤ (∏ i ∈ d.support, L i ^ d i).natDegree := by
      simpa using (Polynomial.natDegree_mul_le (p := Polynomial.C (p.coeff d))
        (q := ∏ i ∈ d.support, L i ^ d i))
    _ ≤ ∑ i ∈ d.support, (L i ^ d i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ d.support, d i * w i := Finset.sum_le_sum fun i _ =>
      Polynomial.natDegree_pow_le_of_le _ (hL i)
    _ = Finsupp.weight w d := by
      rw [Finsupp.weight_apply, Finsupp.sum]
      rfl
    _ ≤ _ := weight_le_expansion_degree w hd

/-- A line substitution of bounded weighted degrees detects common divisors
when it preserves the full degree of a nonzero weighted homogeneous polynomial. -/
theorem isRelPrime_of_full_degree_specialization
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (L : σ → Polynomial K)
    (hL : ∀ i, (L i).natDegree ≤ w i) (p q : MvPolynomial σ K) (n : ℕ)
    (hp : p.IsWeightedHomogeneous w n)
    (hn : (eval₂Hom Polynomial.C L p).natDegree = n)
    (hpn : eval₂Hom Polynomial.C L p ≠ 0)
    (hc : IsCoprime (eval₂Hom Polynomial.C L p) (eval₂Hom Polynomial.C L q)) :
    IsRelPrime p q := by
  classical
  let F := eval₂Hom Polynomial.C L
  let G := degreeExpansion (K := K) w
  intro d hdp hdq
  have hdunit : IsUnit (F d) := hc.isRelPrime (map_dvd F hdp) (map_dvd F hdq)
  obtain ⟨e, he⟩ := hdp
  have hFp : F p ≠ 0 := hpn
  have hFd : F d ≠ 0 := hdunit.ne_zero
  have hFe : F e ≠ 0 := by
    intro hz
    exact hFp (by rw [he, map_mul, hz, mul_zero])
  have hGd : G d ≠ 0 := degreeExpansion_ne_zero w (fun hz => hFd (by rw [hz, map_zero]))
  have hGe : G e ≠ 0 := degreeExpansion_ne_zero w (fun hz => hFe (by rw [hz, map_zero]))
  have hGp : G p = Polynomial.monomial n p := by
    ext k
    rw [degreeExpansion_coeff, weightedHomogeneousComponent_of_mem hp]
    simp [Polynomial.coeff_monomial, eq_comm]
  have hsumG : (G d).natDegree + (G e).natDegree = n := by
    rw [← Polynomial.natDegree_mul hGd hGe, ← map_mul, ← he, hGp]
    simp [Polynomial.natDegree_monomial, show p ≠ 0 from fun hz => hFp (by rw [hz, map_zero])]
  have hsumF : (F d).natDegree + (F e).natDegree = n := by
    rw [← Polynomial.natDegree_mul hFd hFe, ← map_mul, ← he]
    exact hn
  have hFzero := Polynomial.natDegree_eq_zero_of_isUnit hdunit
  have hle := natDegree_eval_le w e L hL
  have hGzero : (G d).natDegree = 0 := by
    change (F e).natDegree ≤ (G e).natDegree at hle
    omega
  have hdconst : d = C (d.coeff 0) := by
    have hh : d.IsWeightedHomogeneous w 0 := by
      intro m hm
      have hb := weight_le_expansion_degree w (mem_support_iff.mpr hm)
      change Finsupp.weight w m ≤ (G d).natDegree at hb
      omega
    rw [← weightedHomogeneousComponent_zero d hw, weightedHomogeneousComponent_eq_self hh]
  have hcoeff : d.coeff 0 ≠ 0 := by
    intro hz
    have hd0 : d = 0 := by simpa [hz] using hdconst
    exact hFd (by simp [hd0])
  rw [hdconst]
  exact (isUnit_iff_ne_zero.mpr hcoeff).map C

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSWeightedLineSpecialization
