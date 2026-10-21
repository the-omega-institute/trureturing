/- GID: D5/S3/Combinatorics/Graph/RegularCHS/Cubic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RegularCHS/Cubic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Minimum degree lower bounds for even closed walk counts. -/

import D5.S3.Combinatorics.Graph.RegularCHS.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Classical Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.RegularCHS.Interface

namespace D5.S3.Combinatorics.Graph.RegularCHS.Cubic

private lemma pow_symm {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (v w : Fin n) :
    ((G.adjMatrix ℕ) ^ k) v w = ((G.adjMatrix ℕ) ^ k) w v := by
  exact (G.isSymm_adjMatrix.pow k).apply w v

private lemma even_closed_eq {n : ℕ} (G : SimpleGraph (Fin n)) (j : ℕ) :
    closedWalks G (2 * j) = ∑ v, ∑ w, ((G.adjMatrix ℕ) ^ j) v w ^ 2 := by
  simp only [closedWalks, two_mul, pow_add, Matrix.mul_apply]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro w _
  rw [pow_symm G j w v, pow_two]

private lemma row_sum_ge {n r : ℕ} (G : SimpleGraph (Fin n))
    (hr : ∀ v, r ≤ G.degree v) (j : ℕ) (v : Fin n) :
    r ^ j ≤ ∑ w, ((G.adjMatrix ℕ) ^ j) v w := by
  induction j generalizing v with
  | zero => simp [Matrix.one_apply]
  | succ j ih =>
    rw [pow_succ' (G.adjMatrix ℕ)]
    simp only [SimpleGraph.adjMatrix_mul_apply]
    rw [sum_comm]
    calc
      r ^ (j + 1) = r * r ^ j := pow_succ' r j
      _ ≤ G.degree v * r ^ j := Nat.mul_le_mul_right _ (hr v)
      _ = ∑ _u ∈ G.neighborFinset v, r ^ j := by simp
      _ ≤ _ := sum_le_sum fun u _ => ih u

/-- Even closed walks dominate walks of half the length in a minimum-degree graph. -/
theorem closedWalks_ge_of_minDegree {n r : ℕ} (G : SimpleGraph (Fin n))
    (hr : ∀ v, r ≤ G.degree v) (j : ℕ) :
    n * r ^ j ≤ closedWalks G (2 * j) := by
  rw [even_closed_eq]
  calc
    n * r ^ j = ∑ _v : Fin n, r ^ j := by simp
    _ ≤ ∑ v, ∑ w, ((G.adjMatrix ℕ) ^ j) v w :=
      sum_le_sum fun v _ => row_sum_ge G hr j v
    _ ≤ _ := sum_le_sum fun v _ => sum_le_sum fun w _ => by
      simpa [pow_two] using Nat.le_mul_self (((G.adjMatrix ℕ) ^ j) v w)

end D5.S3.Combinatorics.Graph.RegularCHS.Cubic
