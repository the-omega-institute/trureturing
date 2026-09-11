/- GID: D5/S3/Quantum/Algebra/RectangularPolynomialNullity
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/RectangularPolynomialNullity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rectangular support bounds a conditionally derivative-closed subspace. -/

import D5.S3.Quantum.Algebra.ConditionalPolynomialRigidity
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.RingTheory.Polynomial.DegreeLT

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Algebra.RectangularPolynomialNullity

open MvPolynomial

variable {K sigma : Type*} [Field K] [Fintype sigma]

private theorem coeff_single_linear_form_pow (c : sigma → K) (i : sigma) (n k : ℕ) :
    coeff (Finsupp.single i n) ((∑ j, c j • (X j : MvPolynomial sigma K)) ^ k) =
      if n = k then (c i) ^ n else 0 := by
  classical
  rw [coeff_linearCombination_X_pow_of_fintype]
  have hprod : (Finsupp.single i n).prod (fun _ m => m.factorial) = n.factorial :=
    Finsupp.prod_single_index (by simp)
  have hquot : n.factorial / n.factorial = 1 := Nat.div_self (Nat.factorial_pos n)
  simp [Finsupp.multinomial, hprod, hquot]

private theorem coeff_single_aeval_linear_form (c : sigma → K) (i : sigma)
    (F : Polynomial K) (n : ℕ) :
    coeff (Finsupp.single i n)
      (Polynomial.aeval (∑ j, c j • (X j : MvPolynomial sigma K)) F) =
      F.coeff n * (c i) ^ n := by
  classical
  rw [Polynomial.aeval_eq_sum_range, coeff_sum]
  simp_rw [coeff_smul, coeff_single_linear_form_pow, smul_eq_mul, mul_ite, mul_zero]
  by_cases hn : n ∈ Finset.range (F.natDegree + 1)
  · simp [hn]
  · have hFn : F.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by
      have : F.natDegree + 1 ≤ n := by
        simpa only [Finset.mem_range, not_lt] using hn
      omega)
    simp [hn, hFn]

private theorem aeval_linear_form_injective (c : sigma → K) (i : sigma) (hi : c i ≠ 0) :
    Function.Injective (Polynomial.aeval (R := K)
      (∑ j, c j • (X j : MvPolynomial sigma K))) := by
  intro F G hFG
  ext n
  have h := congrArg (coeff (Finsupp.single i n)) hFG
  rw [coeff_single_aeval_linear_form, coeff_single_aeval_linear_form] at h
  exact mul_right_cancel₀ (pow_ne_zero n hi) h

private theorem nat_degree_le_of_rectangular_support
    (a : sigma → ℕ) (c : sigma → K) (i : sigma) (hi : c i ≠ 0)
    (F : Polynomial K)
    (hbox : ∀ d ∈ (Polynomial.aeval
      (∑ j, c j • (X j : MvPolynomial sigma K)) F).support, ∀ j, d j ≤ a j) :
    F.natDegree ≤ a i := by
  classical
  by_cases hF : F = 0
  · simp [hF]
  · have hc : coeff (Finsupp.single i F.natDegree)
        (Polynomial.aeval (∑ j, c j • (X j : MvPolynomial sigma K)) F) ≠ 0 := by
      rw [coeff_single_aeval_linear_form, Polynomial.coeff_natDegree]
      exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hF) (pow_ne_zero _ hi)
    simpa using hbox _ (mem_support_iff.mpr hc) i

private theorem finrank_le_pivot_capacity
    (a : sigma → ℕ) (L : Submodule K (MvPolynomial sigma K))
    (hconst : ∀ b : K, C b ∈ L → b = 0)
    (hbox : ∀ p ∈ L, ∀ d ∈ p.support, ∀ j, d j ≤ a j)
    (c : sigma → K) (i : sigma) (hi : c i ≠ 0)
    (hrep : ∀ p ∈ L, ∃ F : Polynomial K,
      p = Polynomial.aeval (∑ j, c j • (X j : MvPolynomial sigma K)) F) :
    Module.finrank K L ≤ a i := by
  classical
  let e := Polynomial.aeval (R := K) (∑ j, c j • (X j : MvPolynomial sigma K))
  let S : Submodule K (Polynomial K) := L.comap e.toLinearMap
  have hle : S ≤ Polynomial.degreeLT K (a i + 1) := by
    intro F hF
    rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE]
    exact Polynomial.natDegree_le_iff_degree_le.mp
      (nat_degree_le_of_rectangular_support a c i hi F (hbox _ hF))
  have hproper : ¬ Polynomial.degreeLT K (a i + 1) ≤ S := by
    intro h
    have hone : (1 : Polynomial K) ∈ Polynomial.degreeLT K (a i + 1) := by
      rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE]
      simp
    have hmem : (C 1 : MvPolynomial sigma K) ∈ L := by
      have hh := h hone
      change e 1 ∈ L at hh
      simpa [e] using hh
    exact one_ne_zero (hconst 1 hmem)
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_not_ge hle hproper)
  have hdim : Module.finrank K (Polynomial.degreeLT K (a i + 1)) = a i + 1 := by
    simpa using Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K (a i + 1))
  let f : S →ₗ[K] L := e.toLinearMap.restrict (fun _ h => h)
  have hf : Function.Bijective f := by
    constructor
    · intro F G hFG
      apply Subtype.ext
      exact aeval_linear_form_injective c i hi (congrArg Subtype.val hFG)
    · intro p
      obtain ⟨F, hF⟩ := hrep p p.property
      have hFS : F ∈ S := by
        change e F ∈ L
        rw [← hF]
        exact p.property
      exact ⟨⟨F, hFS⟩, Subtype.ext hF.symm⟩
  have heq := (LinearEquiv.ofBijective f hf).finrank_eq
  rw [hdim, heq] at hlt
  omega

omit [Fintype sigma] in
private theorem submodule_eq_bot_of_zero_box
    (a : sigma → ℕ) (L : Submodule K (MvPolynomial sigma K))
    (hconst : ∀ b : K, C b ∈ L → b = 0)
    (hbox : ∀ p ∈ L, ∀ d ∈ p.support, ∀ i, d i ≤ a i)
    (ha : ∀ i, a i = 0) : L = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro p hp
  change p = 0
  have he : p = C (coeff 0 p) := by
    apply eq_monomial_of_support_subset_singleton
    intro d hd
    ext i
    exact Nat.eq_zero_of_le_zero (by simpa [ha i] using hbox p hp d hd i)
  have hz : coeff 0 p = 0 := hconst _ (he ▸ hp)
  simpa [hz] using he

/-- A rectangularly supported subspace excluding nonzero constants and closed
under partial derivatives of its zero-constant members has dimension at most
the finite supremum of the side lengths. -/
theorem stationary_rectangular_nullity_bound [CharZero K]
    (a : sigma → ℕ) (L : Submodule K (MvPolynomial sigma K))
    [FiniteDimensional K L]
    (hconst : ∀ b : K, C b ∈ L → b = 0)
    (hclosed : ∀ p ∈ L, constantCoeff p = 0 → ∀ i, pderiv i p ∈ L)
    (hbox : ∀ p ∈ L, ∀ d ∈ p.support, ∀ i, d i ≤ a i) :
    Module.finrank K L ≤ Finset.univ.sup a := by
  classical
  by_cases ha : Finset.univ.sup a = 0
  · have haz : ∀ i, a i = 0 := by
      intro i
      exact Nat.eq_zero_of_le_zero (ha ▸ Finset.le_sup (Finset.mem_univ i))
    rw [submodule_eq_bot_of_zero_box a L hconst hbox haz]
    simp
  · by_cases hdim : 2 ≤ Module.finrank K L
    · obtain ⟨c, hc, hrep⟩ :=
        ConditionalPolynomialRigidity.conditional_derivative_closed_subspace_rigidity
          L hconst hclosed hdim
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
        by_contra hn
        apply hc
        funext i
        simpa using not_exists.mp hn i
      exact (finrank_le_pivot_capacity a L hconst hbox c i hi hrep).trans
        (Finset.le_sup (Finset.mem_univ i))
    · omega

end D5.S3.Quantum.Algebra.RectangularPolynomialNullity
