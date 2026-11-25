/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSWeightedHomogeneousDivisors
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSWeightedHomogeneousDivisors
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous]
   utility: none
   digest: Weighted homogeneous divisors and the three pairings of four roots. -/
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-! Weighted homogeneity descends to divisors over a domain. The three root
pairing weights and the total degree force a common divisor to be a monomial. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSWeightedLineSpecialization

open MvPolynomial

noncomputable section

section DegreeExpansion

variable {σ K : Type*} [CommSemiring K]

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

private lemma degreeExpansion_ne_zero (w : σ → ℕ) {p : MvPolynomial σ K} (hp : p ≠ 0) :
    degreeExpansion w p ≠ 0 := by
  intro hz
  apply hp
  apply MvPolynomial.ext
  intro m
  have hh := congrArg (fun P : Polynomial (MvPolynomial σ K) =>
    (P.coeff (Finsupp.weight w m)).coeff m) hz
  simpa [degreeExpansion_coeff, coeff_weightedHomogeneousComponent] using hh

end DegreeExpansion

/-- A divisor of a nonzero weighted homogeneous polynomial is homogeneous for
the same natural weight. The least and greatest degrees of the scaling
polynomial are additive under multiplication over a domain. -/
theorem isWeightedHomogeneous_of_dvd {τ R : Type*} [CommRing R] [IsDomain R]
    {w : τ → ℕ} {p f : MvPolynomial τ R} {d : ℕ}
    (hp : p ≠ 0) (hhom : p.IsWeightedHomogeneous w d) (hdiv : f ∣ p) :
    ∃ e : ℕ, f.IsWeightedHomogeneous w e := by
  classical
  obtain ⟨g, hfg⟩ := hdiv
  have hf : f ≠ 0 := fun hz => hp (by rw [hfg, hz, zero_mul])
  have hg : g ≠ 0 := fun hz => hp (by rw [hfg, hz, mul_zero])
  have hscaled : degreeExpansion w p = Polynomial.monomial d p := by
    apply Polynomial.ext
    intro n
    rw [degreeExpansion_coeff, weightedHomogeneousComponent_of_mem hhom]
    by_cases hn : n = d
    · subst n
      simp only [Polynomial.coeff_monomial, if_pos rfl]
    · simp only [Polynomial.coeff_monomial, if_neg hn, if_neg (Ne.symm hn)]
  have hprod : degreeExpansion w f * degreeExpansion w g = Polynomial.monomial d p := by
    rw [← map_mul, ← hfg, hscaled]
  have hfScaled := degreeExpansion_ne_zero w hf
  have hgScaled := degreeExpansion_ne_zero w hg
  have htop := congrArg Polynomial.natDegree hprod
  have hbottom := congrArg Polynomial.natTrailingDegree hprod
  rw [Polynomial.natDegree_mul hfScaled hgScaled,
    Polynomial.natDegree_monomial_eq d hp] at htop
  rw [Polynomial.natTrailingDegree_mul hfScaled hgScaled,
    Polynomial.natTrailingDegree_monomial hp] at hbottom
  have hfLe := Polynomial.natTrailingDegree_le_natDegree (degreeExpansion w f)
  have hgLe := Polynomial.natTrailingDegree_le_natDegree (degreeExpansion w g)
  refine ⟨(degreeExpansion w f).natDegree, ?_⟩
  intro s hs
  have hnonzero : (degreeExpansion w f).coeff (Finsupp.weight w s) ≠ 0 := by
    intro hz
    rw [degreeExpansion_coeff] at hz
    have hzero := congrArg (fun q : MvPolynomial τ R => q.coeff s) hz
    change (weightedHomogeneousComponent w (Finsupp.weight w s) f).coeff s = 0 at hzero
    rw [coeff_weightedHomogeneousComponent, if_pos rfl] at hzero
    exact hs hzero
  have hmin := Polynomial.natTrailingDegree_le_of_ne_zero hnonzero
  have hmax := Polynomial.le_natDegree_of_ne_zero hnonzero
  omega

/-- For a nonzero index `j`, the indicator of the root pair `(0,j)`. -/
def pairingWeight (j : Fin 4) : Fin 4 → ℕ :=
  Pi.single 0 1 + Pi.single j 1

private theorem weight_pairingWeight (j : Fin 4) (s : Fin 4 →₀ ℕ) :
    Finsupp.weight (pairingWeight j) s = s 0 + s j := by
  rw [pairingWeight, Finsupp.weight_eq_sum]
  simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  rw [← Finsupp.weight_eq_sum (Pi.single (0 : Fin 4) (1 : ℕ)) s,
    ← Finsupp.weight_eq_sum (Pi.single j (1 : ℕ)) s]
  simp only [Finsupp.weight_single_one_apply]

private theorem exponent_eq_of_pairing_weights {s t : Fin 4 →₀ ℕ}
    (htotal : Finsupp.weight (1 : Fin 4 → ℕ) s = Finsupp.weight (1 : Fin 4 → ℕ) t)
    (h01 : Finsupp.weight (pairingWeight 1) s = Finsupp.weight (pairingWeight 1) t)
    (h02 : Finsupp.weight (pairingWeight 2) s = Finsupp.weight (pairingWeight 2) t)
    (h03 : Finsupp.weight (pairingWeight 3) s = Finsupp.weight (pairingWeight 3) t) :
    s = t := by
  simp only [Finsupp.weight_eq_sum, Fin.sum_univ_four, Pi.one_apply, smul_eq_mul,
    mul_one] at htotal
  simp only [weight_pairingWeight] at h01 h02 h03
  have h0 : s 0 = t 0 := by omega
  have h1 : s 1 = t 1 := by omega
  have h2 : s 2 = t 2 := by omega
  have h3 : s 3 = t 3 := by omega
  apply Finsupp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- The three pairings of four roots exclude common factors with two distinct
support exponents. The total degree can be inherited from the first polynomial. -/
private theorem support_eq_singleton_of_common_pairing_dvd {R : Type*} [CommRing R] [IsDomain R]
    {f p01 p02 p03 : MvPolynomial (Fin 4) R} {d01 d02 d03 e01 e02 e03 : ℕ}
    (h01 : p01 ≠ 0 ∧ p01.IsHomogeneous d01 ∧
      p01.IsWeightedHomogeneous (pairingWeight 1) e01 ∧ f ∣ p01)
    (h02 : p02 ≠ 0 ∧ p02.IsHomogeneous d02 ∧
      p02.IsWeightedHomogeneous (pairingWeight 2) e02 ∧ f ∣ p02)
    (h03 : p03 ≠ 0 ∧ p03.IsHomogeneous d03 ∧
      p03.IsWeightedHomogeneous (pairingWeight 3) e03 ∧ f ∣ p03) :
    ∃ s : Fin 4 →₀ ℕ, f.support = {s} := by
  classical
  have hf : f ≠ 0 := by
    obtain ⟨g, hfg⟩ := h01.2.2.2
    intro hz
    exact h01.1 (by rw [hfg, hz, zero_mul])
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hf
  have hpTotal : p01.IsWeightedHomogeneous (1 : Fin 4 → ℕ) d01 := h01.2.1
  obtain ⟨_, htotal⟩ := isWeightedHomogeneous_of_dvd h01.1 hpTotal h01.2.2.2
  obtain ⟨_, hf01⟩ := isWeightedHomogeneous_of_dvd h01.1 h01.2.2.1 h01.2.2.2
  obtain ⟨_, hf02⟩ := isWeightedHomogeneous_of_dvd h02.1 h02.2.2.1 h02.2.2.2
  obtain ⟨_, hf03⟩ := isWeightedHomogeneous_of_dvd h03.1 h03.2.2.1 h03.2.2.2
  refine ⟨s, Finset.ext fun t => ?_⟩
  rw [Finset.mem_singleton]
  constructor
  · intro ht
    have ht' := mem_support_iff.mp ht
    exact exponent_eq_of_pairing_weights
      ((htotal ht').trans (htotal hs).symm)
      ((hf01 ht').trans (hf01 hs).symm)
      ((hf02 ht').trans (hf02 hs).symm)
      ((hf03 ht').trans (hf03 hs).symm)
  · rintro rfl
    exact mem_support_iff.mpr hs

variable {K : Type*} [Field K]

/-- Over a field, an irreducible common divisor from the three root pairings
is associated to a coordinate, so its image is a unit on the root torus. -/
theorem associated_X_of_irreducible_common_pairing_dvd
    {f p01 p02 p03 : MvPolynomial (Fin 4) K} {d01 d02 d03 e01 e02 e03 : ℕ}
    (hf : Irreducible f)
    (h01 : p01 ≠ 0 ∧ p01.IsHomogeneous d01 ∧
      p01.IsWeightedHomogeneous (pairingWeight 1) e01 ∧ f ∣ p01)
    (h02 : p02 ≠ 0 ∧ p02.IsHomogeneous d02 ∧
      p02.IsWeightedHomogeneous (pairingWeight 2) e02 ∧ f ∣ p02)
    (h03 : p03 ≠ 0 ∧ p03.IsHomogeneous d03 ∧
      p03.IsWeightedHomogeneous (pairingWeight 3) e03 ∧ f ∣ p03) :
    ∃ i : Fin 4, Associated f (X i) := by
  classical
  obtain ⟨s, hs⟩ := support_eq_singleton_of_common_pairing_dvd h01 h02 h03
  have hc : f.coeff s ≠ 0 :=
    mem_support_iff.mp (by rw [hs]; exact Finset.mem_singleton_self s)
  have hm : f = monomial s (f.coeff s) := by
    apply eq_monomial_of_support_subset_singleton
    intro t ht
    rw [hs, Finset.mem_singleton] at ht
    exact ht
  have hs0 : s ≠ 0 := by
    intro hz
    subst s
    apply hf.not_isUnit
    rw [hm, monomial_zero']
    exact (isUnit_iff_ne_zero.mpr hc).map C
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hs0
  have hXdiv : (X i : MvPolynomial (Fin 4) K) ∣ f := by
    rw [hm, X_dvd_monomial]
    exact Or.inr (Finsupp.mem_support_iff.mp hi)
  have hXprime : Prime (X i : MvPolynomial (Fin 4) K) := X_prime
  exact ⟨i, (hXprime.irreducible.associated_of_dvd hf hXdiv).symm⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSWeightedLineSpecialization
