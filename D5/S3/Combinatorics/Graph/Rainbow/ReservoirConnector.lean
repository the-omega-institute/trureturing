/- GID: D5/S3/Combinatorics/Graph/Rainbow/ReservoirConnector
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Rainbow/ReservoirConnector
   mirror-E: none(waiver:general-random-connector-theorem)
   anchors: [mathlib/module/Mathlib.Combinatorics.Digraph.Basic]
   utility: none
   digest: One literal-colour reservoir outcome supplies all robust rainbow connectors. -/

import D5.S3.Combinatorics.Graph.Rainbow.RankDescent
import D5.S3.Combinatorics.Probability.CommonReservoir

/-!
The original-colour robust random connecting lemma, arXiv:2503.01825v2,
Section 4.3, Lemma 4.3. The deterministic layers and rank descent are consumed
unchanged. The common-reservoir suppliers are auxiliary on this actual path
construction. All robust neighbourhoods use the original number of vertices.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal
noncomputable section
set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Rainbow.ReservoirConnector

open RobustLayers RankDescent TwoEdgeChoices
open D5.S3.Combinatorics.Probability
open TripleReservoir CommonReservoirRows CommonReservoirGraph CommonReservoir

variable {V C : Type*} [Fintype V]

/-- The selected original vertices. -/
def vertexReservoir (G : Digraph V) (c : V → V → C)
    (ω : (V ⊕ ActualPalette G c) → Bool) : Finset V := by
  classical
  exact univ.filter (fun v => ω (Sum.inl v) = true)

/-- A finite set of literal original colours, rather than renamed edge labels. -/
def colourReservoir (G : Digraph V) (c : V → V → C)
    (ω : (V ⊕ ActualPalette G c) → Bool) : Finset C := by
  classical
  exact (univ.filter (fun q => ω (Sum.inr q) = true)).map
    ⟨fun q : ActualPalette G c => q.val, fun _ _ h => Subtype.ext h⟩

/-- B1, both directions of B2, and B3 with all forbidden sets chosen after the
single outcome. Colours outside the actual palette remain allowed in D. -/
def FullEvent (G : Digraph V) (c : V → V → C) (p ν : ℝ)
    (ω : (V ⊕ ActualPalette G c) → Bool) : Prop := by
  classical
  exact
    let R := vertexReservoir G c ω
    let S := colourReservoir G c ω
    let b := p ^ 3 * ν / 100 * Fintype.card V
    (R.card : ℝ) ≤ 2 * p * Fintype.card V ∧
    (∀ u, (1 - 3 * p) * (outNeighbors G u).card ≤
      (((outNeighbors G u).filter (fun x => x ∉ R ∧ c u x ∉ S)).card : ℝ)) ∧
    (∀ w, (1 - 3 * p) * (incoming G univ w).card ≤
      (((incoming G univ w).filter (fun x => x ∉ R ∧ c x w ∉ S)).card : ℝ)) ∧
    (letI : Quiver V := graphQuiver G
     ∀ u v, u ≠ v → ∀ (A : Finset V) (D : Finset C),
       (A.card : ℝ) ≤ b → (D.card : ℝ) ≤ b →
       ∃ P : DPath G u v, Allowed G c R A S D P ∧ (P.length : ℝ) ≤ ν⁻¹ + 1)

private theorem literal_selected (G : Digraph V) (c : V → V → C)
    (ω : (V ⊕ ActualPalette G c) → Bool) (q : ActualPalette G c) :
    q.val ∈ colourReservoir G c ω ↔ ω (Sum.inr q) = true := by
  classical
  change q.val ∈ (univ.filter (fun r : ActualPalette G c => ω (Sum.inr r) = true)).map
    ⟨fun r => r.val, fun _ _ h => Subtype.ext h⟩ ↔ _
  constructor
  · intro h
    obtain ⟨r, hr, he⟩ := Finset.mem_map.mp h
    have : r = q := Subtype.ext he
    subst r
    exact (mem_filter.mp hr).2
  · intro h
    have hq : q ∈ (univ : Finset (ActualPalette G c)) := mem_univ q
    have hs : q ∈ univ.filter (fun r : ActualPalette G c => ω (Sum.inr r) = true) :=
      mem_filter.mpr ⟨hq, h⟩
    exact Finset.mem_map.mpr ⟨q, hs, rfl⟩

private theorem edge_selected (G : Digraph V) (c : V → V → C)
    (q₀ : ActualPalette G c) (ω : (V ⊕ ActualPalette G c) → Bool)
    (u w : V) (h : G.Adj u w) :
    c u w ∈ colourReservoir G c ω ↔
      ω (Sum.inr (paletteColour G c q₀ u w)) = true := by
  have he : (paletteColour G c q₀ u w).val = c u w := by
    simp [paletteColour, h]
  rw [← he]
  exact literal_selected G c ω _

private theorem palette_exceptions (G : Digraph V) (c : V → V → C)
    (q₀ : ActualPalette G c) (u : V) (t : ℝ) :
    exceptions G (paletteColour G c q₀) u t = exceptions G c u t := by
  classical
  have he (w : V) : repeated G (paletteColour G c q₀) u w = repeated G c u w := by
    ext x
    by_cases hux : G.Adj u x
    · by_cases hxw : G.Adj x w
      · simp [repeated, outNeighbors, hux, hxw,
          palette_colour_eq_iff G c q₀ u x x w hux hxw]
      · simp [repeated, outNeighbors, hxw]
    · simp [repeated, outNeighbors, hux]
  simp only [exceptions, he]

omit [Fintype V] in
private theorem filter_count (T : Finset V) (P : V → Prop) [DecidablePred P] :
    (∑ x : T, if P x.val then (1 : ℝ) else 0) = ((T.filter P).card : ℝ) := by
  classical
  rw [Finset.sum_coe_sort (f := fun x => if P x then (1 : ℝ) else 0),
    ← natCast_card_filter]

private theorem incoming_count (G : Digraph V) (c : V → V → C)
    (q₀ : ActualPalette G c) (ω : (V ⊕ ActualPalette G c) → Bool)
    (T : Finset V) (w : V) :
    incomingCount G (paletteColour G c q₀) T w ω =
      ((sampledPred G c (vertexReservoir G c ω) (colourReservoir G c ω) T w).card : ℝ) := by
  classical
  unfold incomingCount pairCount
  simp only [pairEvent, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [filter_count (incoming G T w) (fun x =>
    ω (Sum.inl x) = true ∧ ω (Sum.inr (paletteColour G c q₀ x w)) = true)]
  apply congrArg (fun T : Finset V => (T.card : ℝ))
  ext x
  by_cases hxw : G.Adj x w
  · simp [incoming, sampledPred, predecessors, vertexReservoir, hxw,
      edge_selected G c q₀ ω x w hxw]
  · simp [incoming, sampledPred, predecessors, hxw]

private theorem base_count (G : Digraph V) (c : V → V → C)
    (q₀ : ActualPalette G c) (ω : (V ⊕ ActualPalette G c) → Bool) (u w : V) :
    baseCount G (paletteColour G c q₀) u w ω =
      ((sampledBase G c (vertexReservoir G c ω) (colourReservoir G c ω) u w).card : ℝ) := by
  classical
  unfold baseCount
  simp only [tripleEvent, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [filter_count (rainbow (paletteColour G c q₀) u w (twoStep G u w)) (fun x =>
    ω (Sum.inl x) = true ∧ ω (Sum.inr (paletteColour G c q₀ u x)) = true ∧
      ω (Sum.inr (paletteColour G c q₀ x w)) = true)]
  apply congrArg (fun T : Finset V => (T.card : ℝ))
  ext x
  by_cases hux : G.Adj u x
  · by_cases hxw : G.Adj x w
    · simp [rainbow, twoStep, outNeighbors, sampledBase, layer, vertexReservoir,
        hux, hxw, palette_colour_eq_iff G c q₀ u x x w hux hxw,
        edge_selected G c q₀ ω u x hux, edge_selected G c q₀ ω x w hxw]
    · simp [rainbow, twoStep, outNeighbors, sampledBase, layer, hxw]
  · simp [rainbow, twoStep, outNeighbors, sampledBase, layer, hux]

omit [Fintype V] in
private theorem loss_complement {Q : Type*}
    (T : Finset V) (a : V → Q) (ω : (V ⊕ Q) → Bool) :
    (T.card : ℝ) - lossCount (fun x : T => (x : V)) (fun x => a x) ω =
      ((T.filter (fun x => ¬(ω (Sum.inl x) = true ∨ ω (Sum.inr (a x)) = true))).card : ℝ) := by
  classical
  unfold lossCount
  simp only [lossEvent, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [filter_count T (fun x => ω (Sum.inl x) = true ∨ ω (Sum.inr (a x)) = true)]
  have h := card_filter_add_card_filter_not (s := T)
    (fun x => ω (Sum.inl x) = true ∨ ω (Sum.inr (a x)) = true)
  have hR : (((T.filter (fun x => ω (Sum.inl x) = true ∨
      ω (Sum.inr (a x)) = true)).card : ℝ) +
      (T.filter (fun x => ¬(ω (Sum.inl x) = true ∨ ω (Sum.inr (a x)) = true))).card) = T.card := by
    exact_mod_cast h
  linarith

private theorem retained_out [DecidableEq V] [DecidableEq C] (G : Digraph V) (c : V → V → C)
    (q₀ : ActualPalette G c) (ω : (V ⊕ ActualPalette G c) → Bool) (u : V) :
    retainedOut G (paletteColour G c q₀) u ω =
      (((outNeighbors G u).filter (fun x => x ∉ vertexReservoir G c ω ∧
        c u x ∉ colourReservoir G c ω)).card : ℝ) := by
  classical
  rw [retainedOut, loss_complement (outNeighbors G u) (paletteColour G c q₀ u) ω]
  apply congrArg (fun T : Finset V => (T.card : ℝ))
  ext x
  by_cases hux : G.Adj u x
  · simp [outNeighbors, vertexReservoir, hux, edge_selected G c q₀ ω u x hux]
  · simp [outNeighbors, hux]

private theorem retained_in [DecidableEq V] [DecidableEq C] (G : Digraph V) (c : V → V → C)
    (q₀ : ActualPalette G c) (ω : (V ⊕ ActualPalette G c) → Bool) (w : V) :
    retainedIn G (paletteColour G c q₀) w ω =
      (((incoming G univ w).filter (fun x => x ∉ vertexReservoir G c ω ∧
        c x w ∉ colourReservoir G c ω)).card : ℝ) := by
  classical
  rw [retainedIn, loss_complement (incoming G univ w) (fun x => paletteColour G c q₀ x w) ω]
  apply congrArg (fun T : Finset V => (T.card : ℝ))
  ext x
  by_cases hxw : G.Adj x w
  · simp [incoming, vertexReservoir, hxw, edge_selected G c q₀ ω x w hxw]
  · simp [incoming, hxw]

/-- Original graph and scale hypotheses imply every numerical bound needed by
the probability supplier and put all deterministic ranks inside Fin n. -/
theorem original_parameter_bounds (G : Digraph V) (ν τ α p : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hparams : ν + τ ≤ α) (hloop : ∀ x, ¬ G.Adj x x)
    (hexp : ExteriorExpander G ν τ)
    (hdeg : ∀ u, α * Fintype.card V ≤ ((layer G ν u 0).card : ℝ))
    (hscale : 144 * Real.log (Fintype.card V : ℝ) ≤ p ^ 3 * ν ^ 2 * Fintype.card V)
    (u : V) :
    ν < 1 / 2 ∧ 64 ≤ Fintype.card V ∧ 3 < Real.log (Fintype.card V : ℝ) ∧
      ⌊ν⁻¹⌋₊ < Fintype.card V := by
  obtain ⟨hhalf, _, hupper⟩ := graph_parameter_bounds G ν τ α hν hτ hparams
    hloop hexp u (hdeg u)
  have hn : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty V from ⟨u⟩)
  have hα : 0 < α := lt_of_lt_of_le (add_pos hν hτ) hparams
  have hn2 : (2 : ℝ) ≤ Fintype.card V := by
    have hnat : 1 < Fintype.card V := by
      exact_mod_cast (show (1 : ℝ) < Fintype.card V by nlinarith [mul_pos hα hn])
    exact_mod_cast (show 2 ≤ Fintype.card V by omega)
  have hp3 : p ^ 3 ≤ (1 : ℝ) := pow_le_one₀ hp.le hp1
  have hν1 : ν ≤ 1 := by linarith
  have hνsq : ν ^ 2 ≤ ν := by nlinarith
  have hcoef : p ^ 3 * ν ^ 2 ≤ ν :=
    (mul_le_mul_of_nonneg_right hp3 (sq_nonneg ν)).trans (by simpa using hνsq)
  have hbound := mul_le_mul_of_nonneg_right hcoef hn.le
  have hlog2 : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  have hlogn := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn2
  have hn64R : (64 : ℝ) ≤ Fintype.card V := by nlinarith
  have hn64 : 64 ≤ Fintype.card V := by exact_mod_cast hn64R
  have hlog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 6
    norm_num at h
    exact h
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 64) hn64R
  rw [hlog64] at hl
  have hlog : 3 < Real.log (Fintype.card V : ℝ) := by linarith
  have hνn : 1 < ν * Fintype.card V := by linarith
  have hinv : ν⁻¹ < (Fintype.card V : ℝ) := (inv_lt_iff_one_lt_mul₀ hν).mpr (by nlinarith)
  exact ⟨hhalf, hn64, hlog, (Nat.floor_lt (inv_nonneg.mpr hν.le)).mpr hinv⟩

/-- The supplied finite probability rows are the actual deterministic layers
minus layer zero; there is no sampled or post-revelation layer choice. -/
def rankLayers (G : Digraph V) (ν : ℝ) (u : V) (i : Fin (Fintype.card V)) : Finset V := by
  classical
  exact layer G ν u i.val \ layer G ν u 0

private theorem common_implies_full (G : Digraph V) (c : V → V → C)
    (hloop : ∀ x, ¬ G.Adj x x) (hout : OutProper G c) (hin : InProper G c)
    (ν τ α p : ℝ) (hν : 0 < ν) (hτ : 0 < τ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hparams : ν + τ ≤ α)
    (hscale : 144 * Real.log (Fintype.card V : ℝ) ≤ p ^ 3 * ν ^ 2 * Fintype.card V)
    (hexp : ExteriorExpander G ν τ)
    (hdegO : ∀ u, α * Fintype.card V ≤ ((layer G ν u 0).card : ℝ))
    (hdegI : ∀ w, α * Fintype.card V ≤ ((predecessors G univ w).card : ℝ))
    (hranks : ⌊ν⁻¹⌋₊ < Fintype.card V) (q₀ : ActualPalette G c)
    (ω : (V ⊕ ActualPalette G c) → Bool)
    (hω : CommonEvent G (paletteColour G c q₀) p ν (rankLayers G ν) ω) :
    FullEvent G c p ν ω := by
  classical
  obtain ⟨hsize, hdegree, hbase, hrank, hinc⟩ := hω
  refine ⟨?_, ?_, ?_, ?_⟩
  · have he : vertexCount ω = ((vertexReservoir G c ω).card : ℝ) := by
      simp only [vertexCount, Set.indicator_apply, Set.mem_ofPred_eq]
      rw [← natCast_card_filter]
      rfl
    simpa only [SizeEvent, he] using hsize
  · intro u
    simpa only [retained_out] using hdegree.1 u
  · intro w
    simpa only [retained_in] using hdegree.2 w
  · apply robust_connector G c hloop hout hin ν τ α p
      (p ^ 3 * ν / 100 * Fintype.card V) hν hτ hp hp1 hparams hscale hexp hdegO hdegI
      (vertexReservoir G c ω) (colourReservoir G c ω)
    · intro u w _ hw hbig
      have hw' : w ∉ exceptions G (paletteColour G c q₀) u (ν * Fintype.card V / 16) := by
        simpa only [palette_exceptions] using hw
      have hs : ν * Fintype.card V / 4 ≤ ((twoStep G u w).card : ℝ) := by
        simpa only [robust, mem_filter, mem_univ, true_and, predecessors, layer,
          twoStep, outNeighbors, div_mul_eq_mul_div] using hbig
      have hb := hbase u w hw' hs
      rw [base_count] at hb
      convert hb using 1; ring
    · intro u i hi w hbig
      let j : Fin (Fintype.card V) := ⟨i, by omega⟩
      have hs : ν * Fintype.card V / 4 ≤ ((incoming G (rankLayers G ν u j) w).card : ℝ) := by
        simpa only [robust, mem_filter, mem_univ, true_and, incoming, predecessors,
          rankLayers, j, div_mul_eq_mul_div] using hbig
      have hh := hrank u j w hs
      rw [incoming_count] at hh
      dsimp only [rankLayers, j] at hh
      convert hh using 1; ring
    · intro w
      have hh := hinc w
      rw [incoming_count] at hh
      convert hh using 1; ring

/-- Full B1+B2+B3 of the original-colour random connector. One independent
Bernoulli-p law on vertices and the actual literal-colour palette works for all
ordered distinct endpoints and every post-revelation finite forbidden pair.
The empty vertex type is included; all other numerical bounds are derived. -/
theorem full_original_colour_connector (G : Digraph V) (c : V → V → C)
    (hloop : ∀ x, ¬ G.Adj x x) (hout : OutProper G c) (hin : InProper G c)
    (p : Set.Icc (0 : ℝ) 1) (hp : 0 < (p : ℝ)) (ν τ α : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ) (hparams : ν + τ ≤ α)
    (hscale : 144 * Real.log (Fintype.card V : ℝ) ≤
      (p : ℝ) ^ 3 * ν ^ 2 * Fintype.card V)
    (hexp : ExteriorExpander G ν τ)
    (hdegO : ∀ u, α * Fintype.card V ≤ ((layer G ν u 0).card : ℝ))
    (hdegI : ∀ w, α * Fintype.card V ≤ ((predecessors G univ w).card : ℝ)) :
    1 - 5 / (Fintype.card V : ℝ) ≤
      (reservoirLaw p).real {ω | FullEvent G c (p : ℝ) ν ω} := by
  classical
  let : IsProbabilityMeasure (reservoirLaw p : Measure ((V ⊕ ActualPalette G c) → Bool)) := by
    unfold reservoirLaw
    infer_instance
  cases isEmpty_or_nonempty V with
  | inl hempty =>
    let := hempty
    have he : {ω : (V ⊕ ActualPalette G c) → Bool | FullEvent G c (p : ℝ) ν ω} = Set.univ := by
      ext ω
      simp [FullEvent, vertexReservoir]
    rw [he, probReal_univ]
    simp
  | inr hnonempty =>
    obtain ⟨u⟩ := hnonempty
    obtain ⟨hhalf, hn, hlog, hranks⟩ := original_parameter_bounds G ν τ α (p : ℝ)
      hν hτ hp p.property.2 hparams hloop hexp hdegO hscale u
    have ho : ∀ u, α * Fintype.card V ≤ ((outNeighbors G u).card : ℝ) := hdegO
    have hi : ∀ w, α * Fintype.card V ≤ ((incoming G univ w).card : ℝ) := hdegI
    obtain ⟨q₀, hprob⟩ := actual_palette_common_reservoir G c hout hin hloop p hp ν α
      hν hhalf (by linarith) hn hlog hscale ho hi (rankLayers G ν)
    exact hprob.trans (measureReal_mono (fun ω hω =>
      common_implies_full G c hloop hout hin ν τ α (p : ℝ) hν hτ hp p.property.2
        hparams hscale hexp hdegO hdegI hranks q₀ ω hω))

end D5.S3.Combinatorics.Graph.Rainbow.ReservoirConnector
