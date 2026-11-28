/- GID: D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=none
   digest: Hilbert gain bounds at clique numbers four and five, their strict separation from Banach and L1 bounds, and Euclidean reconstruction in dimensions two and three. -/

import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.HilbertTetrahedronInsertion
import OmegaMath.Combinatorics.Graph.HilbertTrianglePlacement
import OmegaMath.Combinatorics.Graph.EuclideanChordalBounds
import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata
import D5.S3.Combinatorics.Graph.Chordal.ThreeTreeBanachSharpBounds

compile_only_with_mathlib

/-! # Hilbert clique phase reversal and finite-dimensional Euclidean bounds

For finite chordal graphs, coupled edge, triangle and tetrahedron estimates
give Hilbert reconstruction coefficients below the Banach and real L1
obstructions in the clique-four and clique-five strata, respectively.
-/

namespace SimpleGraph

open ChordalResidualExtension

variable {V E : Type*} [Finite V] {G : SimpleGraph V}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem scale_gain_bound (hG : G.IsChordal) (C : ℝ)
    (hfit : PairRetention.Upper G E C)
    (g : V → V → E) (δ : ℝ) (hδ : 0 ≤ δ) (hrev : Skew g)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → ‖g a b + g b c - g a c‖ ≤ δ) :
    ∃ p : V → E, ∀ a b, G.Adj a b → ‖g a b - (p b - p a)‖ ≤ C * δ := by
  by_cases h0 : δ = 0
  · subst δ
    obtain ⟨p, hp⟩ := GainReduction.integrate hG g (fun a b _ => hrev a b)
      (fun a b c hab hbc hac => sub_eq_zero.mp (norm_le_zero_iff.mp (htri a b c hab hbc hac)))
    exact ⟨p, fun a b hab => by rw [hp a b hab, sub_self, norm_zero, mul_zero]⟩
  have hpδ : 0 < δ := lt_of_le_of_ne hδ (Ne.symm h0)
  let f (a b : V) := δ⁻¹ • g a b
  have hf : Skew f := fun a b => by simp [f, hrev a b, smul_neg]
  have ht : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → ‖PairRetention.defect f a b c‖ ≤ 1 := by
    intro a b c hab hbc hac
    simp only [PairRetention.defect, f, ← smul_add, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hδ)]
    exact (mul_le_mul_of_nonneg_left (htri a b c hab hbc hac) (inv_nonneg.mpr hδ)).trans_eq
      (inv_mul_cancel₀ h0)
  obtain ⟨q, hq⟩ := hfit f hf ht
  refine ⟨fun a => δ • q a, fun a b hab => ?_⟩
  have he : g a b - (δ • q b - δ • q a) = δ • PairRetention.residual f q a b := by
    simp only [PairRetention.residual, f, smul_sub, smul_smul, mul_inv_cancel₀ h0, one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ, mul_comm C δ]
  exact mul_le_mul_of_nonneg_left (hq a b hab) hpδ.le

section Hilbert

variable [InnerProductSpace ℝ E]

/-- At clique number at most four, the squared triangle invariant gives
edge error at most `259/200` times the triangle-defect budget. -/
theorem IsChordal.exists_cliqueFour_hilbert_gain_potential (hG : G.IsChordal)
    (hclique : ∀ c : Finset V, G.IsClique (c : Set V) → c.card ≤ 4)
    (g : V → V → E) (δ : ℝ) (hδ : 0 ≤ δ) (hrev : Skew g)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → ‖g a b + g b c - g a c‖ ≤ δ) :
    ∃ p : V → E, ∀ a b, G.Adj a b → ‖g a b - (p b - p a)‖ ≤ (259/200) * δ := by
  apply scale_gain_bound hG _ _ g δ hδ hrev htri
  intro f hf ht
  refine reconstruct (k := 3) (R := HilbertTriangleInsertion.R) (U := HilbertTriangleInsertion.R)
    (M := HilbertTriangleInsertion.C) (N := 11) hG (by norm_num [HilbertTriangleInsertion.R])
    le_rfl (by norm_num [HilbertTriangleInsertion.R, HilbertTriangleInsertion.C])
    (by norm_num [HilbertTriangleInsertion.R]) hclique HilbertTriangleInsertion.place f hf ?_
  exact fun a b c h => ht a b c h.1 h.2.1 h.2.2

/-- At clique number at most five, the coupled invariants give edge error at
most `sqrt (10275 / 4576)` times the triangle-defect budget. -/
theorem IsChordal.exists_cliqueFive_hilbert_gain_potential (hG : G.IsChordal)
    (hclique : ∀ c : Finset V, G.IsClique (c : Set V) → c.card ≤ 5)
    (g : V → V → E) (δ : ℝ) (hδ : 0 ≤ δ) (hrev : Skew g)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → ‖g a b + g b c - g a c‖ ≤ δ) :
    ∃ p : V → E, ∀ a b, G.Adj a b → ‖g a b - (p b - p a)‖ ≤ Real.sqrt (10275/4576) * δ := by
  apply scale_gain_bound hG _ _ g δ hδ hrev htri
  intro f hf ht
  refine reconstruct (k := 4) (R := 3 / 2) (M := 329 / 50) (N := 621 / 50) hG
    (Real.sqrt_nonneg _) ((Real.sqrt_le_iff).2 (by norm_num)) (by norm_num) (by norm_num)
    hclique HilbertTetrahedronInsertion.place f hf ?_
  exact fun a b c h => ht a b c h.1 h.2.1 h.2.2

end Hilbert

section Comparison

open BanachPathPower

/-- Unit-defect Hilbert bounds uniform in the finite graph and target. -/
def HilbertCliqueUpper (k : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsChordal →
    (∀ c : Finset (Fin n), G.IsClique (c : Set (Fin n)) → c.card ≤ k) →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H], PairRetention.Upper G H C

/-- The nonnegative uniform reconstruction coefficient at clique cutoff `k`. -/
noncomputable def hilbertCliqueCoefficient (k : ℕ) : ℝ :=
  sInf {C | HilbertCliqueUpper k C}

/-- A bound uniform in finite real L1 targets and finite chordal graphs. -/
def FiniteL1CliqueUpper (k : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsChordal →
    (∀ c : Finset (Fin n), G.IsClique (c : Set (Fin n)) → c.card ≤ k) →
    ∀ (I : Type) [Fintype I], PairRetention.Upper G (PiLp 1 (fun _ : I => ℝ)) C

private theorem powerPath_chordal (n k : ℕ) : (BanachPathPower.pathPower n k).IsChordal := by
  obtain ⟨l, r, _, h, hi⟩ := pathPower_isIntervalGraph n k
  exact (intervalGraph_isChordal_and_two_approximate_gain_potential
    (H := Multiplicative ℝ) l r h hi (fun _ _ => 1) 0 le_rfl (by simp) (by simp)).1

/-- The three-period simplex family and the Hilbert insertion bound place the
clique-four coefficient strictly above one and below the Banach coefficient. -/
theorem hilbert_cliqueFour_phase_separation :
    (1 : ℝ) < 2 / Real.sqrt 3 ∧
    2 / Real.sqrt 3 ≤ hilbertCliqueCoefficient 4 ∧
    hilbertCliqueCoefficient 4 ≤ 259 / 200 ∧
    (259 / 200 : ℝ) < 4 / 3 ∧ 4 / 3 ≤ cliqueFourBanachCoefficient := by
  have hS : HilbertCliqueUpper 4 (259 / 200) := by
    refine ⟨by norm_num, ?_⟩
    intro n G hG hcl H _ _ g hg ht
    simpa only [mul_one] using hG.exists_cliqueFour_hilbert_gain_potential
      hcl g 1 zero_le_one hg ht
  have hb : BddBelow {C | HilbertCliqueUpper 4 C} := ⟨0, fun _ h => h.1⟩
  have hsqrt : Real.sqrt (2 - 2 / (3 : ℝ)) = 2 / Real.sqrt 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_div (sq_nonneg (2 : ℝ))]
    congr 1
    norm_num
  have hOne : (1 : ℝ) < 2 / Real.sqrt 3 := by
    apply (lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num))).2
    simpa using (Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 2)).2
      (by norm_num : (3 : ℝ) < 2 ^ 2)
  refine ⟨hOne, ?_, csInf_le hb hS, by norm_num, cliqueFour_banach_coefficient_bounds.1⟩
  apply le_csInf ⟨_, hS⟩
  intro c hc
  rw [← hsqrt]
  apply hilbert_powerPath_uniform_lower (k := 3) (by decide) hc.1
  intro n
  exact hc.2 n _ (powerPath_chordal n 3) (fun _ h => clique_card_le_width_add_one h) _

/-- At clique number five the Hilbert coefficient lies strictly below every
uniform bound over finite real L1 targets. -/
theorem hilbert_cliqueFive_phase_separation :
    hilbertCliqueCoefficient 5 ≤ Real.sqrt (10275 / 4576) ∧
    Real.sqrt (10275 / 4576) < (2997 / 2000 : ℝ) ∧
    (2997 / 2000 : ℝ) < 3 / 2 ∧
    ∀ C, FiniteL1CliqueUpper 5 C → (3 / 2 : ℝ) ≤ C := by
  have hS : HilbertCliqueUpper 5 (Real.sqrt (10275 / 4576)) := by
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    intro n G hG hcl H _ _ g hg ht
    simpa only [mul_one] using hG.exists_cliqueFive_hilbert_gain_potential
      hcl g 1 zero_le_one hg ht
  have hb : BddBelow {C | HilbertCliqueUpper 5 C} := ⟨0, fun _ h => h.1⟩
  refine ⟨csInf_le hb hS, ?_, by norm_num, ?_⟩
  · exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  · intro C hC
    have hfit : ∀ n, PairRetention.Upper (BanachPathPower.pathPower n (2 * 2))
        (PiLp 1 (fun _ : ChordalL1.BalancedCutCoordinate 2 => ℝ)) C := by
      intro n
      apply hC.2 n _ (powerPath_chordal n _)
      intro s hs
      exact clique_card_le_width_add_one hs
    have h := (l1_even_powerPath_exact 2 (by decide) C).mp ⟨hC.1, hfit⟩
    norm_num at h
    exact h

end Comparison

section Euclidean

open Real EuclideanChordal

variable [Fintype V]

/-- The planar coefficient is at most `4/π` and improves by the finite-order
factor `(n-2)/n` for `n ≥ 3`. -/
theorem IsChordal.exists_euclideanPlane_gain_potential (hG : G.IsChordal)
    (g : V → V → EuclideanSpace ℝ (Fin 2)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrev : ∀ a b, G.Adj a b → g b a = -g a b)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → ‖g a b + g b c - g a c‖ ≤ δ) :
    ∃ p : V → EuclideanSpace ℝ (Fin 2), ∀ a b, G.Adj a b →
      ‖g a b - (p b - p a)‖ ≤ (if 3 ≤ Fintype.card V then orderFactor (Fintype.card V) else 1) *
        (4 / π) * δ := by
  split_ifs with hn
  · exact exists_plane_potential hG hn g hδ hrev htri
  · simpa only [one_mul] using exists_plane_potential_global hG g hδ hrev htri

/-- The three-dimensional coefficient is at most `3/2`, with the same
finite-order improvement. -/
theorem IsChordal.exists_euclideanSpaceThree_gain_potential (hG : G.IsChordal)
    (g : V → V → EuclideanSpace ℝ (Fin 3)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrev : ∀ a b, G.Adj a b → g b a = -g a b)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → ‖g a b + g b c - g a c‖ ≤ δ) :
    ∃ p : V → EuclideanSpace ℝ (Fin 3), ∀ a b, G.Adj a b →
      ‖g a b - (p b - p a)‖ ≤ (if 3 ≤ Fintype.card V then orderFactor (Fintype.card V) else 1) *
        (3 / 2) * δ := by
  split_ifs with hn
  · exact exists_space_potential hG hn g hδ hrev htri
  · simpa only [one_mul] using exists_space_potential_global hG g hδ hrev htri

end Euclidean

end SimpleGraph
