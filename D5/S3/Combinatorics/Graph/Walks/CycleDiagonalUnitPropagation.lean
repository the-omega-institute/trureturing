/- GID: D5/S3/Combinatorics/Graph/Walks/CycleDiagonalUnitPropagation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CycleDiagonalUnitPropagation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.CycleGraph]
   utility: none
   digest: Two adjacent diagonal units generate every matrix unit in a cycle algebra. -/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

set_option autoImplicit false

open Matrix
open scoped Fin.NatCast
namespace D5.S3.Combinatorics.Graph.Walks.CycleDiagonalUnitPropagation

set_option maxHeartbeats 1000000 in
-- Two uniform inductions and matrix-entry normalization share this proof budget.
/-- Two adjacent diagonal units force the full real cycle algebra and scalar joint symmetries. -/
theorem cycle_diagonal_units_full (L : ℕ) (hL : 3 ≤ L) (v : Fin L → ℝ)
    (hseed : ∃ j : Fin L,
      Matrix.single j j (1 : ℝ) ∈ Algebra.adjoin ℝ
        {(SimpleGraph.cycleGraph L).lapMatrix ℝ, Matrix.diagonal v} ∧
      Matrix.single (j + ⟨1, by omega⟩) (j + ⟨1, by omega⟩) (1 : ℝ) ∈ Algebra.adjoin ℝ
        {(SimpleGraph.cycleGraph L).lapMatrix ℝ, Matrix.diagonal v}) :
    Algebra.adjoin ℝ {(SimpleGraph.cycleGraph L).lapMatrix ℝ, Matrix.diagonal v} = ⊤ ∧
    (∀ X : Matrix (Fin L) (Fin L) ℂ,
      Commute X (((SimpleGraph.cycleGraph L).lapMatrix ℝ).map Complex.ofReal) →
      Commute X ((Matrix.diagonal v).map Complex.ofReal) →
      ∃ c : ℂ, X = c • (1 : Matrix (Fin L) (Fin L) ℂ)) ∧
    (∀ O : Matrix (Fin L) (Fin L) ℝ,
      O ∈ Matrix.orthogonalGroup (Fin L) ℝ →
      Commute O ((SimpleGraph.cycleGraph L).lapMatrix ℝ) →
      Commute O (Matrix.diagonal v) → O = 1 ∨ O = -1) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 3 := ⟨L - 3, by omega⟩
  let G := SimpleGraph.cycleGraph (n + 3)
  let A := G.adjMatrix ℝ
  let B := Algebra.adjoin ℝ {G.lapMatrix ℝ, Matrix.diagonal v}
  have hone : (⟨1, by omega⟩ : Fin (n+3)) = 1 := by
    ext
    simp [Nat.mod_eq_of_lt (show 1 < n+3 by omega)]
  simp only [hone] at hseed
  change (∃ j, Matrix.single j j (1 : ℝ) ∈ B ∧
    Matrix.single (j + 1) (j + 1) (1 : ℝ) ∈ B) at hseed
  obtain ⟨j, hj, hj1⟩ := hseed
  have hdeg : G.degMatrix ℝ = (2 : ℝ) • (1 : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) := by
    ext a b
    simp [G, SimpleGraph.degMatrix, SimpleGraph.cycleGraph_degree_three_le,
      Matrix.diagonal, Matrix.one_apply, Matrix.smul_apply]
  have hA : A ∈ B := by
    have hd : G.lapMatrix ℝ ∈ B := Algebra.subset_adjoin (by simp)
    have hm := B.sub_mem (B.smul_mem B.one_mem (2 : ℝ)) hd
    convert hm using 1
    dsimp [A]
    rw [SimpleGraph.lapMatrix, hdeg]
    abel
  have hne (k : Fin (n+3)) : k - 1 ≠ k + 1 := by
    intro he
    have hh : (0 : Fin (n+3)) = 2 := by
      calc
        0 = (k - 1) - (k - 1) := by simp
        _ = (k + 1) - (k - 1) := by rw [he]
        _ = 2 := by
          simpa only [one_add_one_eq_two] using
            (show (k + 1) - (k - 1) = (1 : Fin (n+3)) + 1 by abel)
    have hh' := congrArg Fin.val hh
    simp [Nat.mod_eq_of_lt (show 2 < n+3 by omega)] at hh'
  have hcol (k : Fin (n+3)) : A * Matrix.single k k 1 =
      Matrix.single (k-1) k 1 + Matrix.single (k+1) k 1 := by
    ext a b
    by_cases hb : b = k
    · subst b
      have hadj : G.Adj a k ↔ a = k-1 ∨ a = k+1 := by
        have hh := congrArg (fun s => a ∈ s) (SimpleGraph.cycleGraph_neighborSet (v := k))
        simpa [G, SimpleGraph.mem_neighborSet, SimpleGraph.adj_comm] using hh
      simp only [Matrix.mul_single_apply_same, mul_one, Matrix.add_apply]
      by_cases hp : a = k-1
      · subst a
        simp [A, SimpleGraph.adjMatrix_apply, hadj, Matrix.single, hne k, (hne k).symm]
      · by_cases hq : a = k+1
        · subst a
          simp [A, SimpleGraph.adjMatrix_apply, hadj, Matrix.single, hp, hne k]
        · simp [A, SimpleGraph.adjMatrix_apply, hadj, Matrix.single, hp, hq, Ne.symm hp, Ne.symm hq]
    · rw [Matrix.mul_single_apply_of_ne 1 k k a b hb]
      simp [Matrix.single, Ne.symm hb]
  have hrow (k : Fin (n+3)) : Matrix.single k k 1 * A =
      Matrix.single k (k-1) 1 + Matrix.single k (k+1) 1 := by
    have ht := congrArg Matrix.transpose (hcol k)
    simpa [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_single,
      A, SimpleGraph.isSymm_adjMatrix] using ht
  have step (k : Fin (n+3))
      (hp : Matrix.single (k-1) (k-1) (1 : ℝ) ∈ B)
      (hk : Matrix.single k k (1 : ℝ) ∈ B) :
      Matrix.single (k+1) (k+1) (1 : ℝ) ∈ B := by
    let Q : Matrix (Fin (n+3)) (Fin (n+3)) ℝ := 1 - Matrix.single (k-1) (k-1) 1
    have hQ : Q ∈ B := B.sub_mem B.one_mem hp
    have he1 : Q * A * Matrix.single k k 1 = Matrix.single (k+1) k 1 := by
      rw [mul_assoc, hcol]
      simp [Q, sub_mul, mul_add, Matrix.single_mul_single_of_ne, hne k]
    have he2 : Matrix.single k k 1 * A * Q = Matrix.single k (k+1) 1 := by
      rw [hrow]
      simp [Q, mul_sub, add_mul, Matrix.single_mul_single_of_ne, (hne k).symm]
    have hm := B.mul_mem (B.mul_mem (B.mul_mem hQ hA) hk)
      (B.mul_mem (B.mul_mem hk hA) hQ)
    simpa [he1, he2] using hm
  have all_diag : ∀ k : Fin (n+3), Matrix.single k k (1 : ℝ) ∈ B := by
    have hwalk : ∀ t : ℕ,
        Matrix.single (j + (t : Fin (n+3))) (j + (t : Fin (n+3))) (1 : ℝ) ∈ B := by
      apply Nat.twoStepInduction
      · simpa using hj
      · simpa using hj1
      · intro t ht ht1
        have hp : j + ((t+1 : ℕ) : Fin (n+3)) - 1 = j + (t : Fin (n+3)) := by
          push_cast
          abel
        have hq : j + ((t+1 : ℕ) : Fin (n+3)) + 1 = j + ((t+2 : ℕ) : Fin (n+3)) := by
          push_cast
          abel
        have hpk : Matrix.single (j + ((t+1 : ℕ) : Fin (n+3)) - 1)
            (j + ((t+1 : ℕ) : Fin (n+3)) - 1) (1 : ℝ) ∈ B := by
          rw [hp]
          exact ht
        have hs := step (j + ((t+1 : ℕ) : Fin (n+3))) hpk ht1
        rw [hq] at hs
        exact hs
    intro k
    have hh := hwalk (k-j).val
    simpa using hh
  have edge_unit (a b : Fin (n+3)) (hab : G.Adj a b) : Matrix.single a b (1 : ℝ) ∈ B := by
    have hm := B.mul_mem (B.mul_mem (all_diag a) hA) (all_diag b)
    simpa [A, SimpleGraph.adjMatrix_apply, hab] using hm
  have all_units : ∀ a b : Fin (n+3), Matrix.single a b (1 : ℝ) ∈ B := by
    intro a b
    obtain ⟨w⟩ := (SimpleGraph.cycleGraph_preconnected a b)
    induction w with
    | nil => exact all_diag _
    | @cons x y z hxy w ih =>
      have hm := B.mul_mem (edge_unit x y hxy) ih
      simpa using hm
  have hfull : B = ⊤ := by
    apply top_unique
    intro M _
    rw [Matrix.matrix_eq_sum_single M]
    apply B.sum_mem
    intro a _
    apply B.sum_mem
    intro b _
    simpa using B.smul_mem (all_units a b) (M a b)
  let f : Matrix (Fin (n+3)) (Fin (n+3)) ℝ →ₐ[ℝ]
      Matrix (Fin (n+3)) (Fin (n+3)) ℂ := (Algebra.ofId ℝ ℂ).mapMatrix
  have hcomplex : ∀ X : Matrix (Fin (n+3)) (Fin (n+3)) ℂ,
      Commute X ((G.lapMatrix ℝ).map Complex.ofReal) →
      Commute X ((Matrix.diagonal v).map Complex.ofReal) → ∃ c : ℂ, X = c • 1 := by
    intro X hd hv
    have hcentral : B ≤ (Subalgebra.centralizer ℝ {X}).comap f := by
      apply Algebra.adjoin_le
      intro M hM
      rcases Set.mem_insert_iff.mp hM with rfl | hM
      · change f (G.lapMatrix ℝ) ∈ Subalgebra.centralizer ℝ {X}
        rw [Subalgebra.mem_centralizer_iff]
        intro Y hY
        have : Y = X := Set.mem_singleton_iff.mp hY
        subst Y
        exact hd.eq
      · have : M = Matrix.diagonal v := Set.mem_singleton_iff.mp hM
        subst M
        change f (Matrix.diagonal v) ∈ Subalgebra.centralizer ℝ {X}
        rw [Subalgebra.mem_centralizer_iff]
        intro Y hY
        have : Y = X := Set.mem_singleton_iff.mp hY
        subst Y
        exact hv.eq
    have hc : ∀ a b, Commute (Matrix.single a b (1 : ℂ)) X := by
      intro a b
      have hm := hcentral (all_units a b)
      have he := (Subalgebra.mem_centralizer_iff ℝ).mp hm X (by simp)
      apply Commute.symm
      change X * Matrix.single a b (1 : ℂ) = Matrix.single a b (1 : ℂ) * X
      simpa [f, Matrix.map_single] using he
    obtain ⟨c, he⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr hc
    refine ⟨c, ?_⟩
    simpa only [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using he.symm
  refine ⟨hfull, hcomplex, ?_⟩
  intro O ho hd hv
  have hd' : Commute (f O) (f (G.lapMatrix ℝ)) := hd.map f
  have hv' : Commute (f O) (f (Matrix.diagonal v)) := hv.map f
  obtain ⟨c, hc⟩ := hcomplex (f O) hd' hv'
  have hreal : O = c.re • (1 : Matrix (Fin (n+3)) (Fin (n+3)) ℝ) := by
    ext a b
    have he := congrArg (fun M : Matrix (Fin (n+3)) (Fin (n+3)) ℂ => (M a b).re) hc
    by_cases hab : a = b
    · simpa [f, Matrix.smul_apply, Matrix.one_apply, hab] using he
    · simpa [f, Matrix.smul_apply, Matrix.one_apply, hab] using he
  have hs : c.re * c.re = 1 := by
    have hh := ((Matrix.mem_orthogonalGroup_iff (Fin (n+3)) ℝ).mp ho)
    rw [hreal] at hh
    have he := congrArg (fun M : Matrix (Fin (n+3)) (Fin (n+3)) ℝ => M 0 0) hh
    simpa [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      Matrix.smul_apply, smul_eq_mul] using he
  have hcpm : c.re = 1 ∨ c.re = -1 := by exact mul_self_eq_one_iff.mp hs
  rcases hcpm with h | h
  · left
    simpa [h] using hreal
  · right
    simpa [h] using hreal

end D5.S3.Combinatorics.Graph.Walks.CycleDiagonalUnitPropagation
