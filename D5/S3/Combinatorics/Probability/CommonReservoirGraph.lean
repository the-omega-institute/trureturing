/- GID: D5/S3/Combinatorics/Probability/CommonReservoirGraph
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/CommonReservoirGraph
   mirror-E: none(waiver:symbolic-graph-probability-estimate)
   anchors: []
   utility: none
   digest: Actual rainbow base and fixed predecessor counts share one tagged product law. -/

import D5.S3.Combinatorics.Graph.Rainbow.TwoEdgeChoices
import D5.S3.Combinatorics.Probability.CommonReservoirRows

/-! Actual graph rainbow and incoming counts under the common reservoir law. -/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal
noncomputable section
set_option autoImplicit false

namespace D5.S3.Combinatorics.Probability.CommonReservoirGraph

open D5.S3.Combinatorics.Graph.Rainbow.TwoEdgeChoices
open TripleReservoir CommonReservoirRows

variable {V C : Type*} [Fintype V] [Fintype C]

def incoming (G : Digraph V) (L : Finset V) (w : V) : Finset V := by
  classical
  exact L.filter (fun x => G.Adj x w)

def baseCount (G : Digraph V) (c : V → V → C) (u w : V)
    (ω : (V ⊕ C) → Bool) : ℝ :=
  ∑ x : rainbow c u w (twoStep G u w),
    (tripleEvent (x : V) (c u x) (c x w)).indicator (fun _ => (1 : ℝ)) ω

def incomingCount (G : Digraph V) (c : V → V → C) (L : Finset V) (w : V)
    (ω : (V ⊕ C) → Bool) : ℝ :=
  pairCount (fun x : incoming G L w => (x : V)) (fun x => c x w) ω

def retainedOut (G : Digraph V) (c : V → V → C) (u : V)
    (ω : (V ⊕ C) → Bool) : ℝ :=
  (outNeighbors G u).card -
    lossCount (fun x : outNeighbors G u => (x : V)) (fun x => c u x) ω

def retainedIn (G : Digraph V) (c : V → V → C) (w : V)
    (ω : (V ⊕ C) → Bool) : ℝ :=
  (incoming G univ w).card -
    lossCount (fun x : incoming G univ w => (x : V)) (fun x => c x w) ω

def BaseEvent (G : Digraph V) (c : V → V → C) (ν Tb : ℝ)
    (ω : (V ⊕ C) → Bool) : Prop :=
  ∀ u w, w ∉ exceptions G c u (ν * Fintype.card V / 16) →
    ν * Fintype.card V / 4 ≤ ((twoStep G u w).card : ℝ) → Tb ≤ baseCount G c u w ω

def RankEvent (G : Digraph V) (c : V → V → C) (ν Tr : ℝ)
    (L : V → Fin (Fintype.card V) → Finset V) (ω : (V ⊕ C) → Bool) : Prop :=
  ∀ u i w, ν * Fintype.card V / 4 ≤ ((incoming G (L u i) w).card : ℝ) →
    Tr ≤ incomingCount G c (L u i) w ω

def IncomingEvent (G : Digraph V) (c : V → V → C) (Tr : ℝ)
    (ω : (V ⊕ C) → Bool) : Prop :=
  ∀ w, Tr ≤ incomingCount G c univ w ω

def SizeEvent (p : ℝ) (ω : (V ⊕ C) → Bool) : Prop :=
  vertexCount ω ≤ 2 * p * Fintype.card V

def DegreeEvent (G : Digraph V) (c : V → V → C) (p : ℝ)
    (ω : (V ⊕ C) → Bool) : Prop :=
  (∀ u, (1 - 3 * p) * (outNeighbors G u).card ≤ retainedOut G c u ω) ∧
  (∀ w, (1 - 3 * p) * (incoming G univ w).card ≤ retainedIn G c w ω)

private theorem rainbow_base_data (G : Digraph V) (c : V → V → C)
    (hout : OutProper G c) (hin : InProper G c) (hloop : ∀ x, ¬ G.Adj x x)
    (ν : ℝ) (hν : 0 < ν) (hn : 0 < Fintype.card V) (u w : V)
    (hw : w ∉ exceptions G c u (ν * Fintype.card V / 16))
    (hs : ν * Fintype.card V / 4 ≤ ((twoStep G u w).card : ℝ)) :
    ∃ T : Fin 3 → Finset V,
      ThreeClasses (rainbow c u w (twoStep G u w)) (c u) (fun x => c x w) T ∧
      3 * ν * Fintype.card V / 16 ≤ ((rainbow c u w (twoStep G u w)).card : ℝ) := by
  classical
  by_cases huw : u ≠ w
  · obtain ⟨T, hT, hc, _⟩ := (deterministic_rainbow_choice_core G c hout hin hloop
      ν hν hn u).2 w huw hw (twoStep G u w) (Subset.refl _) hs
    exact ⟨T, hT, hc⟩
  · have hloss : ((repeated G c u w).card : ℝ) ≤ ν * Fintype.card V / 16 := by
      simpa only [exceptions, mem_filter, mem_univ, true_and, not_lt] using hw
    have heq : (twoStep G u w).filter (fun x => c u x = c x w) = repeated G c u w := by
      ext x; simp [twoStep, repeated]; aesop
    have hcount := card_filter_add_card_filter_not (s := twoStep G u w)
      (fun x => c u x = c x w)
    rw [heq] at hcount
    have hcount' : ((repeated G c u w).card : ℝ) +
        (rainbow c u w (twoStep G u w)).card = (twoStep G u w).card := by
      exact_mod_cast hcount
    have ha : Set.InjOn (c u) (rainbow c u w (twoStep G u w)) := by
      intro x hx y hy hxy
      exact hout u (mem_filter.mp (mem_filter.mp (mem_filter.mp hx).1).1).2
        (mem_filter.mp (mem_filter.mp (mem_filter.mp hy).1).1).2 hxy
    have hb : Set.InjOn (fun x => c x w) (rainbow c u w (twoStep G u w)) := by
      intro x hx y hy hxy
      exact hin w (mem_filter.mp (mem_filter.mp hx).1).2
        (mem_filter.mp (mem_filter.mp hy).1).2 hxy
    obtain ⟨T, hT⟩ := exists_three_disjoint_classes _ _ _ ha hb
    exact ⟨T, hT, by linarith⟩

/-- Sparse tail for all actual rainbow two-edge choices, including coincident roots
and endpoints. Repeated-colour choices are removed using the actual exceptional set. -/
theorem graph_base_lower_tail (G : Digraph V) (c : V → V → C)
    (hout : OutProper G c) (hin : InProper G c) (hloop : ∀ x, ¬ G.Adj x x)
    (p : Set.Icc (0 : ℝ) 1) (ν Tb : ℝ) (hν : 0 < ν) (hn : 0 < Fintype.card V)
    (hTb : Tb < 3 * ((p : ℝ) ^ 3 * ν * Fintype.card V) / 64)
    (u w : V) (hw : w ∉ exceptions G c u (ν * Fintype.card V / 16))
    (hs : ν * Fintype.card V / 4 ≤ ((twoStep G u w).card : ℝ)) :
    (reservoirLaw p).real {ω | baseCount G c u w ω < Tb} ≤
      Real.exp (-(9 * ((p : ℝ) ^ 3 * ν * Fintype.card V)) / 512) := by
  classical
  letI : IsProbabilityMeasure (reservoirLaw p : Measure ((V ⊕ C) → Bool)) := by
    unfold reservoirLaw
    infer_instance
  let A := rainbow c u w (twoStep G u w)
  obtain ⟨T, hT, hcard⟩ := rainbow_base_data G c hout hin hloop ν hν hn u w hw hs
  have hmem (x : A) : ∃ i, (x : V) ∈ T i := (hT.2.1 x).mp x.property
  let k : A → Fin 3 := fun x => Classical.choose (hmem x)
  have hk (x : A) : (x : V) ∈ T (k x) := Classical.choose_spec (hmem x)
  have hdisj (x y : A) (hxy : k x = k y) (hne : x ≠ y) :
      Disjoint (tripleSupport (x : V) (c u x) (c x w))
        (tripleSupport (y : V) (c u y) (c y w)) := by
    have hy : (y : V) ∈ T (k x) := hxy.symm ▸ hk y
    exact hT.2.2.2.1 (k x) (hk x) hy
      (fun he => hne (Subtype.ext he))
  have hc (x : A) : c u x ≠ c x w := (mem_filter.mp x.property).2
  have hh := triple_reservoir_lower_tail p (fun x : A => (x : V))
    (fun x => c u x) (fun x => c x w) hc k hdisj (3 / 4) (by norm_num)
  have hm : 3 * ((p : ℝ) ^ 3 * ν * Fintype.card V) / 16 ≤
      (p : ℝ) ^ 3 * Fintype.card A := by
    have h := mul_le_mul_of_nonneg_left hcard (pow_nonneg p.property.1 3)
    simpa [A, mul_div_assoc, mul_assoc, mul_left_comm, mul_comm] using h
  have hsub : {ω | baseCount G c u w ω < Tb} ⊆
      {ω | (∑ x : A, (tripleEvent (x : V) (c u x) (c x w)).indicator
        (fun _ => (1 : ℝ)) ω) ≤ (1 - (3 / 4 : ℝ)) *
          ((p : ℝ) ^ 3 * Fintype.card A)} := by
    intro ω hω
    change baseCount G c u w ω < Tb at hω
    change baseCount G c u w ω ≤ _
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    (hh.trans (Real.exp_le_exp.mpr ?_))
  nlinarith

/-- Incoming properness proves the actual predecessor rows independent; the layer
is a fixed deterministic set and is never sampled or selected after revelation. -/
theorem graph_incoming_lower_tail (G : Digraph V) (c : V → V → C)
    (hin : InProper G c) (p : Set.Icc (0 : ℝ) 1) (L : Finset V) (w : V)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (reservoirLaw p).real {ω | incomingCount G c L w ω ≤
      (1 - δ) * ((p : ℝ) ^ 2 * (incoming G L w).card)} ≤
      Real.exp (-(δ ^ 2 * ((p : ℝ) ^ 2 * (incoming G L w).card)) / 2) := by
  classical
  simpa only [incomingCount, Fintype.card_coe] using
    pair_lower_tail p (fun x : incoming G L w => (x : V)) (fun x => c x w)
    Subtype.val_injective (fun x y h => Subtype.ext
      (hin w (mem_filter.mp x.property).2 (mem_filter.mp y.property).2 h)) δ hδ

end D5.S3.Combinatorics.Probability.CommonReservoirGraph
