/- GID: D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertCliquePhaseReversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hilbert and L1 clique separation and Euclidean chordal reconstruction. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.HilbertTetrahedronInsertion
import D5.S3.Combinatorics.Graph.Chordal.HilbertTrianglePlacement
import D5.S3.Combinatorics.Graph.Chordal.EuclideanChordalBounds
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

variable {V E : Type*} {G : SimpleGraph V}
variable [NormedAddCommGroup E]

private theorem scale_gain_bound [Finite V] [NormedSpace ℝ E] (hG : G.IsChordal) (C : ℝ)
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

private theorem simplicial_elimination [Finite V] (hG : G.IsChordal)
    (S : Finset V) (hS : S.Nonempty) :
    ∃ a ∈ S, G.IsClique {x | x ∈ S ∧ G.Adj x a} := by
  let : Nonempty (S : Set V) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  obtain ⟨a, ha⟩ := (hG.induce (S : Set V)).exists_isSimplicial
  refine ⟨a, a.property, ?_⟩
  intro x hx y hy hxy
  exact ha (show (⟨x, hx.1⟩ : (S : Set V)) ∈ _ from hx.2.symm)
    (show (⟨y, hy.1⟩ : (S : Set V)) ∈ _ from hy.2.symm)
    (fun heq => hxy (congrArg Subtype.val heq))

section Hilbert

variable [Finite V] [InnerProductSpace ℝ E]

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
    (M := HilbertTriangleInsertion.C) (N := 11) (simplicial_elimination hG) (by norm_num [HilbertTriangleInsertion.R])
    le_rfl (by norm_num [HilbertTriangleInsertion.R, HilbertTriangleInsertion.C])
    (by norm_num [HilbertTriangleInsertion.R]) hclique HilbertTriangleInsertion.place f hf ?_
  exact fun a b c h => ht a b c h.1 h.2.1 h.2.2

/-- An independent one-interval cutoff-four argument, with triangle invariant
`93/20`, gives error at most `13/10` times the triangle-defect budget. -/
theorem IsChordal.exists_cliqueFour_hilbert_gain_potential_zeroSplit (hG : G.IsChordal)
    (hclique : ∀ c : Finset V, G.IsClique (c : Set V) → c.card ≤ 4)
    (g : V → V → E) (δ : ℝ) (hδ : 0 ≤ δ) (hrev : Skew g)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c → ‖g a b + g b c - g a c‖ ≤ δ) :
    ∃ p : V → E, ∀ a b, G.Adj a b → ‖g a b - (p b - p a)‖ ≤ (13/10) * δ := by
  apply scale_gain_bound hG _ _ g δ hδ hrev htri
  intro f hf ht
  refine reconstruct (k := 3) (R := HilbertTriangleInsertion.ZeroSplit.R)
    (U := HilbertTriangleInsertion.ZeroSplit.R) (M := HilbertTriangleInsertion.ZeroSplit.C)
    (N := 11) (simplicial_elimination hG) (by norm_num [HilbertTriangleInsertion.ZeroSplit.R])
    le_rfl (by norm_num [HilbertTriangleInsertion.ZeroSplit.R, HilbertTriangleInsertion.ZeroSplit.C])
    (by norm_num [HilbertTriangleInsertion.ZeroSplit.R]) hclique
    HilbertTriangleInsertion.ZeroSplit.place f hf ?_
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
  refine reconstruct (k := 4) (R := 3 / 2) (M := 329 / 50) (N := 621 / 50)
    (simplicial_elimination hG)
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
    simpa only [mul_one, PairRetention.residual] using hG.exists_cliqueFour_hilbert_gain_potential
      hcl g 1 zero_le_one hg ht
  have hb : BddBelow {C | HilbertCliqueUpper 4 C} := ⟨0, fun _ h => h.1⟩
  have hsqrt : Real.sqrt (2 - 2 / (3 : ℝ)) = 2 / Real.sqrt 3 := by
    rw [show (2 - 2 / (3 : ℝ)) = 2 ^ 2 / 3 by norm_num,
      Real.sqrt_div (sq_nonneg (2 : ℝ)), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hOne : (1 : ℝ) < 2 / Real.sqrt 3 := by
    apply (lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num))).2
    simpa using (Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 2)).2
      (by norm_num : (3 : ℝ) < 2 ^ 2)
  refine ⟨hOne, ?_, csInf_le hb hS, by norm_num, cliqueFour_banach_coefficient_bounds.1⟩
  unfold hilbertCliqueCoefficient
  apply le_csInf (show {c | HilbertCliqueUpper 4 c}.Nonempty from ⟨_, hS⟩)
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
    simpa only [mul_one, PairRetention.residual] using hG.exists_cliqueFive_hilbert_gain_potential
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

open MeasureTheory

/-- Bounds uniform over finite chordal graphs and real L1 spaces of arbitrary measures. -/
def RealL1CliqueUpper (k : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsChordal →
    (∀ c : Finset (Fin n), G.IsClique (c : Set (Fin n)) → c.card ≤ k) →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω), PairRetention.Upper G (Lp ℝ 1 μ) C

/-- Bounds uniform over finite chordal graphs and real Banach spaces. -/
def BanachCliqueUpper (k : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsChordal →
    (∀ c : Finset (Fin n), G.IsClique (c : Set (Fin n)) → c.card ≤ k) →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
      PairRetention.Upper G E C

private theorem banachCliqueUpper_five_three : BanachCliqueUpper 5 3 := by
  refine ⟨by norm_num, ?_⟩
  intro n G hG hcl E _ _ _ g hg ht
  let f (a b : Fin n) : Multiplicative E := Multiplicative.ofAdd (g a b)
  have hf : ∀ a b, G.Adj a b → f b a = (f a b)⁻¹ := by
    intro a b _
    exact congrArg Multiplicative.ofAdd (hg a b)
  have hft : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      Dist.dist (f a b * f b c) (f a c) ≤ 1 := by
    intro a b c hab hbc hac
    change Dist.dist (g a b + g b c) (g a c) ≤ 1
    simpa only [dist_eq_norm, PairRetention.defect] using ht a b c hab hbc hac
  obtain ⟨p, hp⟩ := hG.exists_clique_five_group_gain_potential hcl f zero_le_one hf hft
  refine ⟨fun a => (p a).toAdd, fun a b hab => ?_⟩
  have h := hp a b hab
  change Dist.dist (g a b) (-(p a).toAdd + (p b).toAdd) ≤ 3 * 1 at h
  simpa only [dist_eq_norm, PairRetention.residual, sub_eq_neg_add, mul_one] using h

private theorem realL1CliqueUpper_of_banach {k : ℕ} {C : ℝ}
    (h : BanachCliqueUpper k C) : RealL1CliqueUpper k C := by
  refine ⟨h.1, ?_⟩
  intro n G hG hc Ω _ μ
  exact h.2 n G hG hc (Lp ℝ 1 μ)

private theorem finiteL1CliqueUpper_of_realL1 {k : ℕ} {C : ℝ}
    (h : RealL1CliqueUpper k C) : FiniteL1CliqueUpper k C := by
  refine ⟨h.1, ?_⟩
  intro n G hG hc I _ g hg ht
  let : MeasurableSpace I := ⊤
  let : MeasurableSingletonClass I := ⟨fun _ => trivial⟩
  let e := ChordalL1.countingCoordinates (I := I)
  let f := fun a b => e.symm (g a b)
  have hf : ∀ a b, f b a = -f a b := by
    intro a b
    simp [f, hg a b]
  have hft : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      ‖PairRetention.defect f a b c‖ ≤ 1 := by
    intro a b c hab hbc hac
    simpa only [PairRetention.defect, f, ← map_add, ← map_sub, LinearIsometryEquiv.norm_map]
      using ht a b c hab hbc hac
  obtain ⟨p, hp⟩ := h.2 n G hG hc I (Measure.count : Measure I) f hf hft
  refine ⟨fun a => e (p a), fun a b hab => ?_⟩
  have hp' := hp a b hab
  rw [← e.norm_map] at hp'
  simpa only [PairRetention.residual, f, map_sub, LinearIsometryEquiv.apply_symm_apply] using hp'

private theorem one_le_of_realL1CliqueUpper_four {C : ℝ} (h : RealL1CliqueUpper 4 C) :
    1 ≤ C := by
  let I := Fin 1
  let : MeasurableSpace I := ⊤
  let : MeasurableSingletonClass I := ⟨fun _ => trivial⟩
  let μ : Measure I := Measure.count
  let e := ChordalL1.countingCoordinates (I := I)
  let : Nontrivial (Lp ℝ 1 μ) := e.symm.injective.nontrivial
  apply (l1_clique_four_exact μ C).mp
  intro n G hG hc
  exact h.2 (n + 1) G hG hc I μ

private theorem realL1CliqueUpper_four_one : RealL1CliqueUpper 4 1 := by
  refine ⟨zero_le_one, ?_⟩
  intro n G hG hc Ω _ μ g hrev htri
  obtain ⟨p, hp⟩ := hG.exists_l1_jung_gain_potential 1 (by decide) hc g 1 zero_le_one hrev htri
  norm_num at hp
  exact ⟨p, hp⟩

/-- The exact clique-four real L1 coefficient and the clique-five order
between Hilbert, real L1, and Banach reconstruction. -/
theorem realL1_hilbert_banach_phase_reversal :
    sInf {C | RealL1CliqueUpper 4 C} = 1 ∧
    1 < hilbertCliqueCoefficient 4 ∧
    hilbertCliqueCoefficient 5 < (3 / 2 : ℝ) ∧
    (3 / 2 : ℝ) ≤ sInf {C | RealL1CliqueUpper 5 C} ∧
    sInf {C | RealL1CliqueUpper 5 C} ≤ sInf {C | BanachCliqueUpper 5 C} := by
  have hbelow (k : ℕ) : BddBelow {C | RealL1CliqueUpper k C} := ⟨0, fun _ h => h.1⟩
  have hBan : {C | BanachCliqueUpper 5 C}.Nonempty := ⟨3, banachCliqueUpper_five_three⟩
  have hL : {C | RealL1CliqueUpper 5 C}.Nonempty :=
    ⟨3, realL1CliqueUpper_of_banach banachCliqueUpper_five_three⟩
  obtain ⟨hstrict, hhigh, -, -, -⟩ := hilbert_cliqueFour_phase_separation
  obtain ⟨hupper, hmiddle, hthreshold, hlower⟩ := hilbert_cliqueFive_phase_separation
  refine ⟨le_antisymm (csInf_le (hbelow 4) realL1CliqueUpper_four_one) ?_,
    hstrict.trans_le hhigh, hupper.trans_lt (hmiddle.trans hthreshold), ?_, ?_⟩
  · exact le_csInf ⟨1, realL1CliqueUpper_four_one⟩ fun _ h => one_le_of_realL1CliqueUpper_four h
  · exact le_csInf hL fun C h => hlower C (finiteL1CliqueUpper_of_realL1 h)
  · exact csInf_le_csInf (hbelow 5) hBan fun _ h => realL1CliqueUpper_of_banach h

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
