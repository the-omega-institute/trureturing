/- GID: D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual source monomials form a basis and recover the leaf projectors. -/

import D5.S3.Quantum.Algebra.DegeneracyGraphDeterminantFactorization
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Idempotents

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Module

namespace D5.S3.Quantum.Algebra.DegeneracyGraphDeterminant

noncomputable local instance {L : ℕ} (T : SourceTree L) :
    Fintype (Exponents T) := by
  unfold Exponents
  infer_instance

noncomputable local instance {n : ℕ} (T : SourceTree (n + 1)) :
    Fintype (Columns T) := by
  unfold Columns
  infer_instance

/-- The projector at a source node, obtained by summing its descendant leaf projectors. -/
def sourceNodeProjector {n : ℕ} (T : SourceTree (n + 1)) {A : Type*}
    [CommRing A] [Algebra ℂ A] (P : Basis (Bottom T) ℂ A)
    (i : Fin (n + 1)) (a : T.V i.succ) : A :=
  ∑ b : Bottom T with T.ancestor (Fin.le_last i.succ) b = a, P b

/-- The source generator at a level, with the actual node labels as eigenvalues. -/
def sourceGenerator {n : ℕ} (T : SourceTree (n + 1)) {A : Type*}
    [CommRing A] [Algebra ℂ A] (P : Basis (Bottom T) ℂ A)
    (i : Fin (n + 1)) : A :=
  ∑ a : T.V i.succ, T.label i a • sourceNodeProjector T P i a

/-- The actual source monomial associated to a surviving exponent column. -/
def sourceMonomial {n : ℕ} (T : SourceTree (n + 1)) {A : Type*}
    [CommRing A] [Algebra ℂ A] (P : Basis (Bottom T) ℂ A)
    (m : Columns T) : A :=
  ∏ i : Fin (n + 1), (sourceGenerator T P i) ^ (m.1 i).val

/-- For any commutative complex algebra with a genuine complete orthogonal
projector basis, the source monomials form a basis.  Their projector expansion
is equation (2.29), and the inverse matrix recovers every projector as in
equation (2.30). -/
theorem source_monomial_basis_and_expansions {n : ℕ} (T : SourceTree (n + 1))
    {A : Type*} [CommRing A] [Algebra ℂ A] (P : Basis (Bottom T) ℂ A)
    (hP : CompleteOrthogonalIdempotents fun b => P b) :
    ∃ B : Basis (Columns T) ℂ A,
      (∀ m, B m = sourceMonomial T P m) ∧
      (∀ m, sourceMonomial T P m = ∑ b, RawM T b m • P b) ∧
      (∀ b, P b = ∑ m,
        (SourceSquare T)⁻¹ ((bottomColumnEquiv T).symm m) b • B m) := by
  classical
  have node_mul (i : Fin (n + 1)) (a : T.V i.succ) (b : Bottom T) :
      sourceNodeProjector T P i a * P b =
        if T.ancestor (Fin.le_last i.succ) b = a then P b else 0 := by
    simp only [sourceNodeProjector, Finset.sum_mul, hP.mul_eq]
    split_ifs with hab
    · rw [Finset.sum_eq_single b]
      · simp
      · intro c _ hcb
        simp [hcb]
      · simp [hab]
    · apply Finset.sum_eq_zero
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      have hcb : c ≠ b := by
        intro h
        subst c
        exact hab hc
      rw [if_neg hcb]
  have generator_mul (i : Fin (n + 1)) (b : Bottom T) :
      sourceGenerator T P i * P b =
        T.label i (T.ancestor (Fin.le_last i.succ) b) • P b := by
    simp only [sourceGenerator, Finset.sum_mul, smul_mul_assoc, node_mul]
    rw [Finset.sum_eq_single (T.ancestor (Fin.le_last i.succ) b)]
    · simp
    · intro a _ ha
      simp [ha.symm]
    · simp
  have generator_pow_mul (i : Fin (n + 1)) (b : Bottom T) (k : ℕ) :
      (sourceGenerator T P i) ^ k * P b =
        (T.label i (T.ancestor (Fin.le_last i.succ) b) ^ k) • P b := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, mul_assoc, generator_mul, mul_smul_comm, ih, smul_smul]
        rw [mul_comm, pow_succ]
  have monomial_mul (m : Columns T) (b : Bottom T) :
      sourceMonomial T P m * P b = RawM T b m • P b := by
    have product_mul (s : Finset (Fin (n + 1))) :
        (∏ i ∈ s, (sourceGenerator T P i) ^ (m.1 i).val) * P b =
          (∏ i ∈ s,
            T.label i (T.ancestor (Fin.le_last i.succ) b) ^ (m.1 i).val) • P b := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_assoc, ih,
            mul_smul_comm, generator_pow_mul, smul_smul]
          rw [mul_comm]
    simpa only [sourceMonomial, RawM] using product_mul Finset.univ
  have forward (m : Columns T) :
      sourceMonomial T P m = ∑ b, RawM T b m • P b := by
    calc
      sourceMonomial T P m = sourceMonomial T P m * 1 := (mul_one _).symm
      _ = sourceMonomial T P m * ∑ b, P b := by rw [hP.complete]
      _ = ∑ b, sourceMonomial T P m * P b := by rw [Finset.mul_sum]
      _ = ∑ b, RawM T b m • P b := by
        apply Finset.sum_congr rfl
        intro b _
        exact monomial_mul m b
  obtain ⟨eps, heps, hdet, _, _⟩ := sourceSquare_det_factorization T
  have factor_ne_zero : sourceFactorProduct T ≠ 0 := by
    unfold sourceFactorProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro pq _
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    intro hlabel
    have hpq : pq.1.1 = pq.1.2 :=
      T.sibling_injective i pq.1.1 pq.1.2 pq.2.2 hlabel
    exact (ne_of_lt pq.2.1) hpq
  have eps_ne_zero : (eps : ℂ) ≠ 0 := by
    rcases heps with rfl | rfl <;> norm_num
  have det_ne_zero : (SourceSquare T).det ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero eps_ne_zero factor_ne_zero
  have det_unit : IsUnit (SourceSquare T).det := isUnit_iff_ne_zero.mpr det_ne_zero
  let E : A ≃ₗ[ℂ] A := (SourceSquare T).toLinearEquiv P det_unit
  let B : Basis (Columns T) ℂ A :=
    (P.map E).reindex (bottomColumnEquiv T)
  have basis_eq (m : Columns T) : B m = sourceMonomial T P m := by
    rw [show B m = E (P ((bottomColumnEquiv T).symm m)) by
      simp [B]]
    rw [show E (P ((bottomColumnEquiv T).symm m)) =
        ∑ b, SourceSquare T b ((bottomColumnEquiv T).symm m) • P b by
      simp [E]]
    simpa [SourceSquare] using (forward m).symm
  refine ⟨B, basis_eq, forward, ?_⟩
  intro b
  rw [← B.sum_repr (P b)]
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  simp only [B, Basis.repr_reindex_apply]
  change P.repr (E.symm (P b)) ((bottomColumnEquiv T).symm m) = _
  rw [show E.symm (P b) = Matrix.toLin P P (SourceSquare T)⁻¹ (P b) by
    rfl]
  rw [Matrix.repr_toLin, Basis.repr_self]
  rw [Matrix.mulVec_apply, Finsupp.single_eq_pi_single,
    dotProduct_single_one]
  rfl

#print axioms source_monomial_basis_and_expansions

end D5.S3.Quantum.Algebra.DegeneracyGraphDeterminant
