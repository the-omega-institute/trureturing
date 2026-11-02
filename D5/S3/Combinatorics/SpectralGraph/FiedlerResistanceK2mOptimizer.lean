/- GID: D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mOptimizer
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Fixed-resistance Fiedler optimization on labelled complete bipartite graphs. -/

import D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceInvariantWeightsRefutation
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Tactic

set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer

open FiedlerResistanceInvariantWeightsRefutation

def K2m (m : ℕ) : SimpleGraph (Fin (2 + m)) :=
  (completeBipartiteGraph (Fin 2) (Fin m)).comap finSumFinEquiv.symm

instance (m : ℕ) : DecidableRel (K2m m).Adj := by
  unfold K2m SimpleGraph.comap completeBipartiteGraph
  infer_instance

private def hub (m : ℕ) (j : Fin 2) : Fin (2 + m) := j.castAdd m
private def leaf (m : ℕ) (i : Fin m) : Fin (2 + m) := i.natAdd 2

private lemma adj_hub_hub (m : ℕ) (i j : Fin 2) :
    ¬ (K2m m).Adj (hub m i) (hub m j) := by
  simp [K2m, SimpleGraph.comap, completeBipartiteGraph, hub, finSumFinEquiv]

private lemma adj_leaf_leaf (m : ℕ) (i j : Fin m) :
    ¬ (K2m m).Adj (leaf m i) (leaf m j) := by
  simp [K2m, SimpleGraph.comap, completeBipartiteGraph, leaf, finSumFinEquiv]

private lemma adj_hub_leaf (m : ℕ) (i : Fin 2) (j : Fin m) :
    (K2m m).Adj (hub m i) (leaf m j) := by
  simp [K2m, SimpleGraph.comap, completeBipartiteGraph, hub, leaf, finSumFinEquiv]

private lemma sum_vertices {m : ℕ} (f : Fin (2 + m) → ℝ) :
    ∑ i, f i = f (hub m 0) + f (hub m 1) + ∑ i, f (leaf m i) := by
  rw [Fin.sum_univ_add]
  simp [hub, leaf, Fin.sum_univ_two]

private lemma lap_mul {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    (wLap G w *ᵥ x) i = ∑ j with G.Adj i j, w s(i,j) * (x i - x j) := by
  have he (j : Fin n) : wLap G w i j =
      (if i = j then ∑ k with G.Adj i k, w s(i,k) else 0) -
      (if G.Adj i j then w s(i,j) else 0) := by
    by_cases h : i = j
    · subst j; simp [wLap]
    · simp [wLap, h]; split_ifs <;> ring
  simp only [Matrix.mulVec, dotProduct, he, sub_mul, Finset.sum_sub_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, mem_univ, ite_true]
  simp only [Finset.sum_filter, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.sum_mul]
  congr 1
  all_goals apply Finset.sum_congr rfl; intro j hj; split_ifs <;> ring

private lemma lap_mul_hub {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ)
    (x : Fin (2 + m) → ℝ) (j : Fin 2) :
    (wLap (K2m m) w *ᵥ x) (hub m j) =
      ∑ i, w s(hub m j,leaf m i) * (x (hub m j) - x (leaf m i)) := by
  rw [lap_mul]
  simp only [Finset.sum_filter, sum_vertices, adj_hub_hub, adj_hub_leaf,
    ite_false, ite_true, zero_add]

private lemma lap_mul_leaf {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ)
    (x : Fin (2 + m) → ℝ) (i : Fin m) :
    (wLap (K2m m) w *ᵥ x) (leaf m i) =
      w s(hub m 0,leaf m i) * (x (leaf m i) - x (hub m 0)) +
      w s(hub m 1,leaf m i) * (x (leaf m i) - x (hub m 1)) := by
  rw [lap_mul]
  simp only [Finset.sum_filter, sum_vertices, adj_leaf_leaf,
    (adj_hub_leaf m 0 i).symm, (adj_hub_leaf m 1 i).symm, ite_true, ite_false,
    Finset.sum_const_zero, add_zero]
  congr 2 <;> exact congrArg w Sym2.eq_swap

private lemma energy {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ)
    (x : Fin (2 + m) → ℝ) :
    dotProduct x (wLap (K2m m) w *ᵥ x) =
      ∑ i, (w s(hub m 0,leaf m i) * (x (hub m 0) - x (leaf m i)) ^ 2 +
        w s(hub m 1,leaf m i) * (x (hub m 1) - x (leaf m i)) ^ 2) := by
  simp only [dotProduct, sum_vertices, lap_mul_hub, lap_mul_leaf,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma lap_hermitian {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) : (wLap G w).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i j
  change wLap G w j i = wLap G w i j
  by_cases h : i = j
  · subst j; rfl
  · simp only [wLap, if_neg h, if_neg (Ne.symm h), G.adj_comm]
    rw [Sym2.eq_swap]

private lemma lap_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) : wLap G w *ᵥ (1 : Fin n → ℝ) = 0 := by
  ext i
  simp [lap_mul]

private lemma energy_nonneg {m : ℕ} (w : Sym2 (Fin (2 + m)) → ℝ)
    (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e) (x : Fin (2 + m) → ℝ) :
    0 ≤ dotProduct x (wLap (K2m m) w *ᵥ x) := by
  rw [energy]
  apply Finset.sum_nonneg
  intro i hi
  have ha := hw s(hub m 0,leaf m i) (by simpa using adj_hub_leaf m 0 i)
  have hb := hw s(hub m 1,leaf m i) (by simpa using adj_hub_leaf m 1 i)
  positivity

private lemma energy_zero_iff {m : ℕ} (hm : 0 < m)
    (w : Sym2 (Fin (2 + m)) → ℝ) (hw : ∀ e ∈ (K2m m).edgeSet, 0 < w e)
    (x : Fin (2 + m) → ℝ) :
    dotProduct x (wLap (K2m m) w *ᵥ x) = 0 ↔ ∃ c : ℝ, x = fun _ => c := by
  constructor
  · intro hx
    rw [energy] at hx
    have hterms (i : Fin m) :
        w s(hub m 0,leaf m i) * (x (hub m 0) - x (leaf m i)) ^ 2 +
        w s(hub m 1,leaf m i) * (x (hub m 1) - x (leaf m i)) ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by
        have ha := hw s(hub m 0,leaf m j) (by simpa using adj_hub_leaf m 0 j)
        have hb := hw s(hub m 1,leaf m j) (by simpa using adj_hub_leaf m 1 j)
        positivity)).mp hx i (Finset.mem_univ i)
    have hcoords (i : Fin m) : x (hub m 0) = x (leaf m i) ∧
        x (hub m 1) = x (leaf m i) := by
      have ha := hw s(hub m 0,leaf m i) (by simpa using adj_hub_leaf m 0 i)
      have hb := hw s(hub m 1,leaf m i) (by simpa using adj_hub_leaf m 1 i)
      have hz := hterms i
      have hza : (x (hub m 0) - x (leaf m i)) ^ 2 = 0 := by
        nlinarith [mul_nonneg hb.le (sq_nonneg (x (hub m 1) - x (leaf m i)))]
      have hzb : (x (hub m 1) - x (leaf m i)) ^ 2 = 0 := by
        nlinarith [mul_nonneg ha.le (sq_nonneg (x (hub m 0) - x (leaf m i)))]
      constructor <;> nlinarith
    refine ⟨x (hub m 0), ?_⟩
    funext k
    refine Fin.addCases (fun j => ?_) (fun i => ?_) k
    · fin_cases j
      · rfl
      · exact (hcoords ⟨0,hm⟩).2.trans (hcoords ⟨0,hm⟩).1.symm
    · exact (hcoords i).1.symm
  · rintro ⟨c,rfl⟩
    rw [energy]
    simp

end D5.S3.Combinatorics.SpectralGraph.FiedlerResistanceK2mOptimizer
