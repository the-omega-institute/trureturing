/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CoordinateMatchingDeterminant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CoordinateMatchingDeterminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic]
   utility: none
   digest: An ordered matching isolates a coefficient in a signed monomial determinant. -/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Perm.Support

/-! The determinant of a monomial matrix detects a completed greedy coordinate matching. -/

set_option autoImplicit false

public section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CoordinateMatchingDeterminant

open scoped BigOperators
open MvPolynomial

universe u v w

variable {ι : Type u} {κ : Type v} {R : Type w}
  [Fintype ι] [DecidableEq ι] [LinearOrder κ] [CommRing R]

omit [DecidableEq ι] in
private theorem moved_multidegree_ne (label : ι → ι → κ) (a : ι → ι → R)
    (hpriority : ∀ i j, i ≠ j → a i j ≠ 0 →
      label i i < label i j ∨ label j j < label i j)
    (σ : Equiv.Perm ι) (hσ : σ ≠ 1) (hadmissible : ∀ i, a (σ i) i ≠ 0) :
    (∑ i, Finsupp.single (label (σ i) i) (1 : ℕ)) ≠
      ∑ i, Finsupp.single (label i i) (1 : ℕ) := by
  classical
  let priorities := σ.support.image (fun i => label i i)
  have hne : priorities.Nonempty :=
    (Finset.nonempty_iff_ne_empty.mpr (mt Equiv.Perm.support_eq_empty_iff.mp hσ)).image _
  let k := priorities.min' hne
  have hk : k ∈ priorities := Finset.min'_mem priorities hne
  obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hk
  have hmin (i : ι) (hi : i ∈ σ.support) : k ≤ label i i :=
    Finset.min'_le priorities _ (Finset.mem_image_of_mem _ hi)
  have habove (i : ι) (hi : i ∈ σ.support) : k < label (σ i) i := by
    rcases hpriority (σ i) i (Equiv.Perm.mem_support.mp hi) (hadmissible i) with h | h
    · exact (hmin (σ i) (Equiv.Perm.apply_mem_support.mpr hi)).trans_lt h
    · exact (hmin i hi).trans_lt h
  have hlt :
      (∑ i, Finsupp.single (label (σ i) i) (1 : ℕ)) k <
        (∑ i, Finsupp.single (label i i) (1 : ℕ)) k := by
    simp only [Finsupp.finsetSum_apply]
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : i ∈ σ.support
      · simp [Finsupp.single_apply, (habove i hi).ne]
      · rw [Equiv.Perm.notMem_support.mp hi]
    · exact ⟨j, Finset.mem_univ _, by simp [(habove j hj).ne, hjk]⟩
  exact fun h => hlt.ne (congrArg (fun m : κ →₀ ℕ => m k) h)

/-- If every nonzero off-diagonal entry comes later than at least one of its two incident
diagonal entries, the diagonal multidegree has exactly the diagonal product as coefficient.
Over a domain, a nonzero diagonal therefore makes the determinant nonzero. -/
theorem coeff_det_of_diagonal_priority (label : ι → ι → κ) (a : ι → ι → R)
    (hpriority : ∀ i j, i ≠ j → a i j ≠ 0 →
      label i i < label i j ∨ label j j < label i j) :
    let M : Matrix ι ι (MvPolynomial κ R) :=
      Matrix.of fun i j => monomial (Finsupp.single (label i j) 1) (a i j)
    (M.det.coeff (∑ i, Finsupp.single (label i i) 1) = ∏ i, a i i) ∧
      (IsDomain R → (∀ i, a i i ≠ 0) → M.det ≠ 0) := by
  classical
  let M : Matrix ι ι (MvPolynomial κ R) :=
    Matrix.of fun i j => monomial (Finsupp.single (label i j) 1) (a i j)
  have hcoeff : M.det.coeff (∑ i, Finsupp.single (label i i) 1) = ∏ i, a i i := by
    rw [Matrix.det_apply M, coeff_sum, Finset.sum_eq_single (1 : Equiv.Perm ι)]
    · simp [M, ← monomial_sum_prod]
    · intro σ _ hσ
      simp only [coeff_smul, M, Matrix.of_apply, ← monomial_sum_prod, coeff_monomial]
      by_cases hn : ∀ i, a (σ i) i ≠ 0
      · simp [moved_multidegree_ne label a hpriority σ hσ hn]
      · obtain ⟨i, hi⟩ := not_forall.mp hn
        have hz : (∏ j, a (σ j) j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (not_ne_iff.mp hi)
        simp [hz]
    · simp
  change _ ∧ (IsDomain R → (∀ i, a i i ≠ 0) → M.det ≠ 0)
  refine ⟨hcoeff, ?_⟩
  intro hdomain hdiag hzero
  let _ : IsDomain R := hdomain
  apply (Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i : (∏ i, a i i) ≠ 0)
  rw [← hcoeff, hzero]
  simp

#print axioms coeff_det_of_diagonal_priority

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.CoordinateMatchingDeterminant
