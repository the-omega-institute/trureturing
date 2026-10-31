/- GID: D5/S3/Quantum/Algebra/PhaseInvariantQuadratic
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PhaseInvariantQuadratic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unique Hermitian representation and real-order positivity of actual invariant quadratics. -/

import D5.S3.Quantum.Algebra.CommonPhasePolynomial
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Complex.Order

noncomputable section
open MvPolynomial Complex
open scoped Matrix ComplexOrder InnerProductSpace
namespace D5.S3.Quantum.Algebra.PhasePolynomial
variable {ι : Type*} [Fintype ι]

def pairExponent (i j : ι) : (ι ⊕ ι) →₀ ℕ :=
  Finsupp.single (.inl i) 1 + Finsupp.single (.inr j) 1

/-- The coefficient c_ij is stored at matrix entry H_ji. -/
def coefficientMatrix (p : Poly ι) : Matrix ι ι ℂ := fun j i => p.coeff (pairExponent i j)

def matrixPolynomial (H : Matrix ι ι ℂ) : Poly ι :=
  ∑ i, ∑ j, monomial (pairExponent i j) (H j i)

private theorem pair_eq_iff (i j k l : ι) :
    pairExponent i j = pairExponent k l ↔ i = k ∧ j = l := by
  classical
  constructor
  · intro h
    have hL := congrArg (fun m : (ι ⊕ ι) →₀ ℕ => m (.inl i)) h
    have hR := congrArg (fun m : (ι ⊕ ι) →₀ ℕ => m (.inr j)) h
    constructor
    · by_contra hn; simp [pairExponent, Finsupp.single_apply, hn] at hL
    · by_contra hn; simp [pairExponent, Finsupp.single_apply, hn] at hR
  · rintro ⟨rfl, rfl⟩; rfl

private theorem matrixPolynomial_coeff (H : Matrix ι ι ℂ) (i j : ι) :
    (matrixPolynomial H).coeff (pairExponent i j) = H j i := by
  classical
  simp [matrixPolynomial, coeff_monomial, pair_eq_iff]

private theorem quadratic_support_pair (p : Poly ι) (hp : Invariant p)
    (hq : p.IsHomogeneous 2) (m : (ι ⊕ ι) →₀ ℕ) (hm : m ∈ p.support) :
    ∃ i j, m = pairExponent i j := by
  classical
  have hb := (common_phase_polynomial_theorem p).1.mp hp m (mem_support_iff.mp hm)
  have hd := hq.degree_eq_sum_deg_support hm
  have ht : holo m + anti m = 2 := by
    have he : m.sum (fun _ n => n) = holo m + anti m := by
      rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]; rfl
    exact he.symm.trans hd.symm
  have hL : holo m = 1 := by omega
  have hR : anti m = 1 := by omega
  let L : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => m (.inl i))
  let R : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => m (.inr i))
  have hLs : L.sum (fun _ n => n) = 1 := by
    simpa [Finsupp.sum_fintype, L, holo] using hL
  have hRs : R.sum (fun _ n => n) = 1 := by
    simpa [Finsupp.sum_fintype, R, anti] using hR
  obtain ⟨i, hi⟩ := (Finsupp.sum_eq_one_iff L).mp hLs
  obtain ⟨j, hj⟩ := (Finsupp.sum_eq_one_iff R).mp hRs
  refine ⟨i, j, ?_⟩
  ext v
  cases v with
  | inl k => simpa [L, pairExponent] using DFunLike.congr_fun hi k
  | inr k => simpa [R, pairExponent] using DFunLike.congr_fun hj k

private theorem quadratic_expansion (p : Poly ι) (hp : Invariant p)
    (hq : p.IsHomogeneous 2) : p = matrixPolynomial (coefficientMatrix p) := by
  classical
  apply MvPolynomial.ext
  intro m
  by_cases hm : ∃ i j, m = pairExponent i j
  · obtain ⟨i,j,rfl⟩ := hm
    exact (matrixPolynomial_coeff (coefficientMatrix p) i j).symm
  · have hz : p.coeff m = 0 := by
      by_contra hn
      exact hm (quadratic_support_pair p hp hq m (mem_support_iff.mpr hn))
    rw [hz]
    simp only [matrixPolynomial, coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rw [coeff_monomial, if_neg (fun h => hm ⟨i,j,h.symm⟩)]

private theorem actual_matrixPolynomial (H : Matrix ι ι ℂ) (z : ι → ℂ) :
    actual (matrixPolynomial H) z = star z ⬝ᵥ (H *ᵥ z) := by
  classical
  simp only [matrixPolynomial, actual, map_sum, eval_monomial, pairExponent,
    Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]),
    Finsupp.prod_single_index (by simp), pow_one, Sum.elim_inl, Sum.elim_inr]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem quadraticMatrix_hermitian (H : Matrix ι ι ℂ)
    (hr : ∀ z, (star z ⬝ᵥ (H *ᵥ z)).im = 0) : H.IsHermitian := by
  classical
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  apply (LinearMap.isSymmetric_iff_inner_map_self_real _).mpr
  intro v
  have hv := hr (WithLp.ofLp v)
  rw [← inner_conj_symm]
  apply Complex.ext <;>
    simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, dotProduct_comm, hv]

/-- Equality of quadratic forms on all actual complex vectors determines the entire matrix. -/
theorem actual_quadratic_matrix_unique (H K : Matrix ι ι ℂ)
    (h : ∀ z, star z ⬝ᵥ (H *ᵥ z) = star z ⬝ᵥ (K *ᵥ z)) : H = K := by
  have he : matrixPolynomial H = matrixPolynomial K := actual_injective (by
    funext z; simpa only [actual_matrixPolynomial] using h z)
  funext j i
  simpa only [matrixPolynomial_coeff] using congrArg (fun p : Poly ι => p.coeff (pairExponent i j)) he

/-- Every real-valued homogeneous quadratic actual invariant has exactly one Hermitian matrix. -/
theorem invariant_quadratic_hermitian (p : Poly ι) (hp : Invariant p)
    (hq : p.IsHomogeneous 2) (hr : ∀ z, (actual p z).im = 0) :
    ∃! H : Matrix ι ι ℂ, H.IsHermitian ∧
      ∀ z, actual p z = star z ⬝ᵥ (H *ᵥ z) := by
  have he := quadratic_expansion p hp hq
  have hev (z) : actual p z = star z ⬝ᵥ ((coefficientMatrix p) *ᵥ z) := by
    rw [he, actual_matrixPolynomial]
  refine ⟨coefficientMatrix p, ⟨quadraticMatrix_hermitian _ (fun z => by
    rw [← hev]; exact hr z), hev⟩, ?_⟩
  intro H hH
  apply actual_quadratic_matrix_unique
  intro z
  exact (hH.2 z).symm.trans (hev z)

/-- Real nonnegativity of actual values is equivalent to the existing complex PSD predicate. -/
theorem invariant_quadratic_nonnegative_iff (p : Poly ι) (hp : Invariant p)
    (hq : p.IsHomogeneous 2) (hr : ∀ z, (actual p z).im = 0) :
    (∀ z, 0 ≤ (actual p z).re) ↔ (coefficientMatrix p).PosSemidef := by
  have hev (z) : actual p z = star z ⬝ᵥ ((coefficientMatrix p) *ᵥ z) := by
    rw [quadratic_expansion p hp hq, actual_matrixPolynomial]
  have hH : (coefficientMatrix p).IsHermitian :=
    quadraticMatrix_hermitian _ (fun z => by rw [← hev]; exact hr z)
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro hn
    refine ⟨hH, fun z => Complex.nonneg_iff.mpr ?_⟩
    rw [← hev]
    exact ⟨hn z, (hr z).symm⟩
  · rintro ⟨_, hn⟩ z
    exact (Complex.nonneg_iff.mp (by simpa only [hev z] using hn z)).1

/-- Complete actual-polynomial common-phase theorem, including zero-dimensional degeneracies. -/
theorem complete_common_phase_polynomial_theorem (p : Poly ι) :
    (∃! q : Poly ι, ∀ z, actual q z = eval (cartesian z) p) ∧
    ((toCartesian p).totalDegree = p.totalDegree) ∧
    (∀ n, (toCartesian p).IsHomogeneous n ↔ p.IsHomogeneous n) ∧
    (Invariant p ↔ Balanced p) ∧
    (Invariant p ↔ p ∈ quadraticAlgebra (ι := ι)) ∧
    (Invariant p → (¬ ∃ c : ℂ, p = C c) → 2 ≤ p.totalDegree) ∧
    (∀ i : ι, Invariant (quadraticGenerator (i,i)) ∧
      (quadraticGenerator (i,i) : Poly ι).totalDegree = 2) ∧
    (p.IsHomogeneous 2 → (∀ z, (actual p z).im = 0) → Invariant p →
      (∃! H : Matrix ι ι ℂ, H.IsHermitian ∧
        ∀ z, actual p z = star z ⬝ᵥ (H *ᵥ z)) ∧
      (∀ i j, coefficientMatrix p j i = p.coeff (pairExponent i j)) ∧
      ((∀ z, 0 ≤ (actual p z).re) ↔ (coefficientMatrix p).PosSemidef)) := by
  refine ⟨real_coordinates_unique p, cartesian_totalDegree p, cartesian_homogeneous p,
    (common_phase_polynomial_theorem p).1, (common_phase_polynomial_theorem p).2,
    invariant_minimum_degree p, invariant_degree_two, ?_⟩
  intro hq hr hp
  exact ⟨invariant_quadratic_hermitian p hp hq hr, fun _ _ => rfl,
    invariant_quadratic_nonnegative_iff p hp hq hr⟩

end D5.S3.Quantum.Algebra.PhasePolynomial
