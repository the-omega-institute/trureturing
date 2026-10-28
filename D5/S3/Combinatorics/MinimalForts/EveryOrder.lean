/- GID: D5/S3/Combinatorics/MinimalForts/EveryOrder
   generality: I
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/EveryOrder
   mirror-E: none(waiver:every-order-graph-construction)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: none
   digest: Actual connected graphs at every positive order have normalized full minimal-fort counts and successive ratio three halves. -/

import D5.S3.Combinatorics.MinimalForts.CountAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The graph sequence retains every actual vertex subset in its fort count. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.EveryOrder

open Filter Topology
open D5.S3.Combinatorics.MinimalForts.UniversalRoot
open D5.S3.Combinatorics.MinimalForts.BlockParameters

/-- A finite simple graph with explicit finite and decision structures. -/
structure FiniteGraph where
  V : Type
  finite : Fintype V
  eqDec : DecidableEq V
  graph : SimpleGraph V
  adjDec : DecidableRel graph.Adj

attribute [instance] FiniteGraph.finite FiniteGraph.eqDec FiniteGraph.adjDec

/-- The count of all inclusion-minimal nonempty forts of the actual graph. -/
def FiniteGraph.count (A : FiniteGraph) : ℕ := (minimalForts A.graph).card

private def blockIndex (n : ℕ) : ℕ := (n - 3) / 6
private def residue (n : ℕ) : Fin 6 := ⟨(n - 3) % 6, Nat.mod_lt _ (by decide)⟩

private def sequence (x y z : Fin 6 → ℕ → ℕ) (n : ℕ) : FiniteGraph :=
  if n < 3 then
    { V := Fin n, finite := inferInstance, eqDec := inferInstance,
      graph := ⊤, adjDec := inferInstance }
  else
    { V := MixedBlocks.Vertex (x (residue n) (blockIndex n))
        (y (residue n) (blockIndex n)) (z (residue n) (blockIndex n)) (residue n).val,
      finite := inferInstance, eqDec := inferInstance,
      graph := MixedBlocks.graph (x (residue n) (blockIndex n))
        (y (residue n) (blockIndex n)) (z (residue n) (blockIndex n)) (residue n).val,
      adjDec := inferInstance }

private theorem order_decomposition (n : ℕ) (hn : 3 ≤ n) :
    6 * blockIndex n + (residue n).val + 3 = n := by
  have h := Nat.mod_add_div (n - 3) 6
  dsimp [blockIndex, residue]
  omega

private theorem sequence_properties (x y z : Fin 6 → ℕ → ℕ)
    (hsum : ∀ r k, x r k + y r k + z r k = k) (n : ℕ) (hn : 0 < n) :
    Fintype.card (sequence x y z n).V = n ∧
    (sequence x y z n).graph.Connected ∧ 0 < (sequence x y z n).count := by
  by_cases hsmall : n < 3
  · have hcases : n = 1 ∨ n = 2 := by omega
    rcases hcases with rfl | rfl
    · refine ⟨by simp [sequence], ?_, ?_⟩
      · change (⊤ : SimpleGraph (Fin 1)).Connected
        exact SimpleGraph.connected_top
      · change 0 < (minimalForts (⊤ : SimpleGraph (Fin 1))).card
        decide +kernel
    · refine ⟨by simp [sequence], ?_, ?_⟩
      · change (⊤ : SimpleGraph (Fin 2)).Connected
        exact SimpleGraph.connected_top
      · change 0 < (minimalForts (⊤ : SimpleGraph (Fin 2))).card
        decide +kernel
  · have hm := MixedBlocks.mixed_graph_count (x (residue n) (blockIndex n))
        (y (residue n) (blockIndex n)) (z (residue n) (blockIndex n)) (residue n).val
    rw [sequence, if_neg hsmall]
    refine ⟨?_, hm.2.1, ?_⟩
    · rw [hm.1, hsum]
      exact order_decomposition n (by omega)
    · unfold FiniteGraph.count
      rw [hm.2.2]
      positivity

private theorem sequence_normalization (x y z : Fin 6 → ℕ → ℕ)
    (hsum : ∀ r k, x r k + y r k + z r k = k)
    (hlim : ∀ r, Tendsto (fun k => (x r k : ℝ) * negativeIncrement +
      (z r k : ℝ) * positiveIncrement - ((k : ℝ) * slope + offset r)) atTop (𝓝 0)) :
    Tendsto (fun n => ((sequence x y z n).count : ℝ) / rate ^ n) atTop (𝓝 1) := by
  let f (r : Fin 6) (k : ℕ) : ℝ :=
    ((minimalForts (MixedBlocks.graph (x r k) (y r k) (z r k) r.val)).card : ℝ) /
      rate ^ (6 * k + r.val + 3)
  have hf (r : Fin 6) : Tendsto (f r) atTop (𝓝 1) :=
    CountAsymptotics.mixed_count_normalization r (x r) (y r) (z r) (hsum r) (hlim r)
  have hb : Tendsto blockIndex atTop atTop :=
    (Nat.tendsto_div_const_atTop (by decide : 6 ≠ 0)).comp (tendsto_sub_atTop_nat 3)
  apply (CountAsymptotics.finite_diagonal f 1 hf residue blockIndex hb).congr'
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn
  dsimp [f]
  rw [order_decomposition n hn]
  unfold FiniteGraph.count
  rw [sequence, if_neg (by omega : ¬ n < 3)]

private theorem successive_ratio (A : ℕ → ℝ) (hA : ∀ n, 0 < n → 0 < A n)
    (h : Tendsto (fun n => A n / rate ^ n) atTop (𝓝 1)) :
    Tendsto (fun n => A (n + 1) / A n) atTop (𝓝 rate) := by
  have hs := h.comp (tendsto_add_atTop_nat 1)
  have hh := (hs.div h (by norm_num)).const_mul rate
  simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), mul_one] at hh
  apply hh.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hAn : A n ≠ 0 := (hA n (by omega)).ne'
  have hq : rate ≠ 0 := by norm_num [rate]
  dsimp
  rw [pow_succ]
  field_simp

private theorem endpoint_bounds : (3 : ℝ) ^ (1 / 3 : ℝ) < rate ∧ rate < 2 := by
  refine ⟨?_, by norm_num [rate]⟩
  have ht := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 3)
    (by norm_num [rate] : (3 : ℝ) < rate ^ (3 : ℕ))
    (by norm_num : (0 : ℝ) < 1 / 3)
  have he : (rate ^ (3 : ℕ)) ^ (1 / 3 : ℝ) = rate := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num [rate])]
    norm_num
  exact he ▸ ht

/-- Every positive order occurs, with all minimal forts, full normalization and full ratio. -/
theorem result :
    ∃ graphs : ℕ → FiniteGraph,
      (∀ n, 0 < n → Fintype.card (graphs n).V = n ∧ (graphs n).graph.Connected ∧
        0 < (graphs n).count) ∧
      Tendsto (fun n => ((graphs n).count : ℝ) / (3 / 2 : ℝ) ^ n) atTop (𝓝 1) ∧
      Tendsto (fun n => ((graphs (n + 1)).count : ℝ) / (graphs n).count)
        atTop (𝓝 (3 / 2 : ℝ)) ∧
      (3 : ℝ) ^ (1 / 3 : ℝ) < (3 / 2 : ℝ) ∧ (3 / 2 : ℝ) < 2 := by
  obtain ⟨x, y, z, hsum, hlim⟩ := residue_sequences
  have hp := sequence_properties x y z hsum
  have hn := sequence_normalization x y z hsum hlim
  refine ⟨sequence x y z, hp, hn, ?_, endpoint_bounds⟩
  apply successive_ratio (fun n => ((sequence x y z n).count : ℝ)) ?_ hn
  intro n hn
  exact_mod_cast (hp n hn).2.2

end D5.S3.Combinatorics.MinimalForts.EveryOrder
