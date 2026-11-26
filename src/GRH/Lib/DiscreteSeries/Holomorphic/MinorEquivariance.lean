import GRH.Lib.General.LinearAlgebra.ExpSurjective
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Holomorphic discrete series: highest coefficient and reproducing property (known
result; see Lib.DiscreteSeries.Holomorphic.HolomorphicExtension).

This file: Sums and products of holomorphic functions; semi-invariance of products of minors. -/

attribute [fun_prop] analyticAt_fst analyticAt_snd analyticAt_weightMinors
  ContinuousLinearMap.analyticAt

variable {n} [Fintype n] {ε o w} (ho : o.Injective) (hw : IsKDominant ε o w) {x b : Matrix n n ℂ}
  (hx : x.det ≠ 0) (hb : b ∈ blockDiagAlg ε) {Φ : Type} [Fintype Φ] {u : Φ → _}

lemma IsHolOfWeight.sum {ι T} {f : ι → _} (c : ι → ℂ) (h : ∀ i, IsHolOfWeight ε o u (f i)) :
  IsHolOfWeight ε o u (∑ i ∈ T, c i * f i ·) := (Classical.skolem.1 h).imp' (T.sum <| c • ·)
  (by simp_all [Finset.mul_sum, Finset.analyticAt_sum _ fun _ _ ↦ .const_smul _, mul_left_comm])

lemma IsHolOfWeight.mul {v F G} (ho : o.Injective) : IsHolOfWeight ε o u F → IsHolOfWeight ε o v G →
  IsHolOfWeight ε o (u + v) (F * G) := fun ⟨f, _⟩ ↦ .imp' (f * ·)
  (by simp_all [AnalyticAt.mul, diagChar, zpow_add₀, IsBorelMatrix.diag_ne_zero ho, field])

open Matrix

include ho hw hx hb

lemma IsKDominant.weightMinors_mul_borel (h : IsBorelMatrix o b) : weightMinors w (x * b) =
  weightMinors w x * diagChar w b := by
  erw [mul_comm, ← weightMinors_diagonal_mul hx (h.diag_ne_zero ho)]
  simp (disch := grind [mem_blockDiagAlg, IsBorelMatrix, BlockTriangular, IsKDominant,
    diagonal_apply, of_apply]) [weightMinors, ↓principalMinor_mul,
    principalMinor, toSquareBlockProp_def, det_eq_prod_diag_of_blockTriangular ho,
    det_eq_prod_diag_of_blockTriangular (ho.comp Subtype.val_injective), mul_comm]

lemma IsKDominant.weightMinors_oppBorel_mul (h : IsBorelMatrix (-o) b) : weightMinors w (b * x) =
  diagChar w b * weightMinors w x := by rw [← weightMinors_transpose,
  transpose_mul, hw.weightMinors_mul_borel] <;> simp_all [mem_blockDiagAlg, IsBorelMatrix,
  BlockTriangular, diagChar, comm, weightMinors, field]
