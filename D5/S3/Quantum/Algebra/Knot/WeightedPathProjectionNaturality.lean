/- GID: D5/S3/Quantum/Algebra/Knot/WeightedPathProjectionNaturality
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Knot/WeightedPathProjectionNaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal local projections commute with extension; the endpoint trace is cyclic. -/

import D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace

set_option autoImplicit false
set_option maxRecDepth 2048

noncomputable section
open scoped BigOperators Matrix
open D5.S3.Quantum.Algebra.WeightedLegalPathTemperleyLieb
open D5.S3.Quantum.Algebra.Knot.WeightedPathMarkovTrace

namespace D5.S3.Quantum.Algebra.Knot.WeightedPathProjectionNaturality

variable {L : Type*} [Fintype L] [DecidableEq L]

attribute [local instance] Classical.propDecidable
local instance (R : L → L → Prop) (n : ℕ) (s t : L) : DecidableEq (LegalPath R n s t) :=
  Classical.decEq _

/-- Every old local generator, in the full endpoint-block algebra. -/
def localProjection (R : L → L → Prop) (d : L → ℝ) (δ : ℝ)
    (n : ℕ) (s : L) (i : ℕ) (hi : 0 < i ∧ i < n) : C R n s :=
  fun t => pathProjection R d δ n s t i hi

private theorem append_kernel (R : L → L → Prop) (d : L → ℝ) (δ : ℝ)
    (n : ℕ) (s t u : L) (h : R t u) (i : ℕ) (hi : 0 < i ∧ i < n)
    (x y : LegalPath R n s t) :
    pathProjection R d δ (n + 1) s u i ⟨hi.1, by omega⟩
      (append R n s t u h x) (append R n s t u h y) =
      pathProjection R d δ n s t i hi x y := by
  have hcoords :
      (∀ k : Fin (n + 2), k.val ≠ i →
        (append R n s t u h x).val k = (append R n s t u h y).val k) ↔
      (∀ k : Fin (n + 1), k.val ≠ i → x.val k = y.val k) := by
    constructor
    · intro hh k hk
      simpa only [append, Fin.snoc_castSucc] using hh k.castSucc hk
    · intro hh k
      refine Fin.lastCases ?_ (fun j => ?_) k
      · intro _
        simp only [append, Fin.snoc_last]
      · intro hk
        simpa only [append, Fin.snoc_castSucc] using hh j hk
  have hindex (j : ℕ) (hj : j < n + 1) :
      (⟨j, by omega⟩ : Fin (n + 2)) = (⟨j, hj⟩ : Fin (n + 1)).castSucc := rfl
  unfold pathProjection
  simp only [hcoords]
  simp only [hindex (i - 1) (by omega),
    hindex i (by omega), hindex (i + 1) (by omega), append, Fin.snoc_castSucc]

private theorem different_predecessor_kernel
    (R : L → L → Prop) (d : L → ℝ) (δ : ℝ)
    (n : ℕ) (s t v u : L) (ht : R t u) (hv : R v u)
    (i : ℕ) (hi : 0 < i ∧ i < n) (htv : t ≠ v)
    (x : LegalPath R n s t) (y : LegalPath R n s v) :
    pathProjection R d δ (n + 1) s u i ⟨hi.1, by omega⟩
      (append R n s t u ht x) (append R n s v u hv y) = 0 := by
  unfold pathProjection
  split_ifs with h
  · have hh := h.1 (Fin.last n).castSucc (by simp; omega)
    simp only [append, Fin.snoc_castSucc, x.property.2.1, y.property.2.1] at hh
    exact (htv hh).elim
  · rfl

private theorem local_projection_natural
    (R : L → L → Prop) (d : L → ℝ) (δ : ℝ)
    (n : ℕ) (s : L) (i : ℕ) (hi : 0 < i ∧ i < n) :
    iota R n s (localProjection R d δ n s i hi) =
      localProjection R d δ (n + 1) s i ⟨hi.1, by omega⟩ := by
  funext u x y
  obtain ⟨⟨⟨t, ht⟩, p⟩, rfl⟩ := (splitPath R n s u).symm.surjective x
  obtain ⟨⟨⟨v, hv⟩, q⟩, rfl⟩ := (splitPath R n s u).symm.surjective y
  have hsplit_t :
      splitPath R n s u (append R n s t u ht p) = ⟨⟨t, ht⟩, p⟩ :=
    (splitPath R n s u).apply_symm_apply ⟨⟨t, ht⟩, p⟩
  have hsplit_v :
      splitPath R n s u (append R n s v u hv q) = ⟨⟨v, hv⟩, q⟩ :=
    (splitPath R n s u).apply_symm_apply ⟨⟨v, hv⟩, q⟩
  change iota R n s (localProjection R d δ n s i hi) u
    (append R n s t u ht p) (append R n s v u hv q) =
    pathProjection R d δ (n + 1) s u i ⟨hi.1, by omega⟩
      (append R n s t u ht p) (append R n s v u hv q)
  by_cases htv : t = v
  · subst v
    simp only [iota, Matrix.submatrix_apply, hsplit_t, hsplit_v,
      Matrix.blockDiagonal'_apply_eq, localProjection]
    exact (append_kernel R d δ n s t u ht i hi p q).symm
  · rw [different_predecessor_kernel R d δ n s t v u ht hv i hi htv p q]
    simp only [iota, Matrix.submatrix_apply, hsplit_t, hsplit_v]
    apply Matrix.blockDiagonal'_apply_ne
    intro he
    exact htv (congrArg Subtype.val he)

/-- Naturality for the literal projection, together with cyclicity of the existing trace. -/
theorem weighted_path_projection_naturality
    (R : L → L → Prop) (d : L → ℝ) (δ : ℝ) :
    (∀ (n : ℕ) (s : L) (i : ℕ) (hi : 0 < i ∧ i < n),
      iota R n s (localProjection R d δ n s i hi) =
        localProjection R d δ (n + 1) s i ⟨hi.1, by omega⟩) ∧
    (∀ (n : ℕ) (s : L) (X Y : C R n s),
      tau R d δ n s (X * Y) = tau R d δ n s (Y * X)) := by
  refine ⟨local_projection_natural R d δ, ?_⟩
  intro n s X Y
  unfold tau
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  exact Matrix.trace_mul_comm (X t) (Y t)

#print axioms weighted_path_projection_naturality

end D5.S3.Quantum.Algebra.Knot.WeightedPathProjectionNaturality
