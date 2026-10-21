/- GID: D5/S3/Combinatorics/Graph/RegularCHS/Result
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RegularCHS/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: The cycle and complete graph attain the regular connected CHS norm extrema. -/


import D5.S3.Combinatorics.Graph.RegularCHS.Newton
import D5.S3.Combinatorics.Graph.RegularCHS.CycleBound
import D5.S3.Combinatorics.Graph.RegularCHS.Cubic
import D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular
import Mathlib.Combinatorics.SimpleGraph.Acyclic

noncomputable section
open Classical
open scoped BigOperators
open D5.S3.Combinatorics.Graph.RegularCHS.Defs
open D5.S3.Combinatorics.Graph.RegularCHS.Interface
open D5.S3.Combinatorics.Graph.RegularCHS.Newton
open D5.S3.Combinatorics.Graph.RegularCHS.CycleBound
open D5.S3.Combinatorics.Graph.RegularCHS.Cubic
open D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

namespace D5.S3.Combinatorics.Graph.RegularCHS.Result

private theorem two_le_regular {n r : ℕ} (hn : 3 ≤ n) (G : SimpleGraph (Fin n))
    (hconn : G.Connected) (hreg : G.IsRegularOfDegree r) : 2 ≤ r := by
  have hedge : n ≤ G.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, G.card_edgeSet] using
      hconn.card_vert_le_card_edgeSet_add_one
  have hdegree : ∀ v, G.degree v = r := fun v => by
    simpa only [← SimpleGraph.ncard_neighborSet] using hreg v
  have hsum : n * r = 2 * G.edgeFinset.card := by
    simpa only [hdegree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] using G.sum_degrees_eq_twice_card_edges
  by_contra hr
  have hr' : r ≤ 1 := by omega
  have hnr : n * r ≤ n := by simpa using Nat.mul_le_mul_left n hr'
  omega

private theorem chs_cycle_le_regular {n r : ℕ} (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n)) (hreg : G.IsRegularOfDegree r) (hr : 2 ≤ r) (m : ℕ) :
    chs (SimpleGraph.cycleGraph n) (2 * m) ≤ chs G (2 * m) := by
  by_cases hr2 : r = 2
  · subst r
    exact chs_cycle_le_twoRegular hn G hreg _
  by_cases hr3 : r = 3
  · subst r
    exact chs_le_of_closedWalks_le _ G (closedWalks_cubic_ge_cycle G hn hreg) _
  have hdegree : ∀ v, G.degree v = r := fun v => by
    simpa only [← SimpleGraph.ncard_neighborSet] using hreg v
  have hr4 : 4 ≤ r := by omega
  calc
    chs (SimpleGraph.cycleGraph n) (2 * m) ≤ bseq n 4 m := chs_cycle_le_bseq hn m
    _ ≤ bseq n r m := bseq_mono hr4 m
    _ ≤ chs G (2 * m) := chs_ge_bseq G r
      (fun j _ => closedWalks_ge_of_minDegree G (fun v => le_of_eq (hdegree v).symm) j) m

/-- The cycle and complete graph attain the two regular connected CHS extrema. -/
theorem result : claim := by
  intro n m hn hm
  have : NeZero n := ⟨by omega⟩
  have hcycle : (SimpleGraph.cycleGraph n).IsRegularOfDegree 2 := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hn
    intro v
    simpa only [← SimpleGraph.ncard_neighborSet] using
      (SimpleGraph.cycleGraph_degree_three_le (n := q) (v := v))
  have hcconn : (SimpleGraph.cycleGraph n).Connected :=
    ⟨SimpleGraph.preconnected_cycleGraph⟩
  refine ⟨⟨hcconn, ⟨2, hcycle⟩, SimpleGraph.connected_top,
    ⟨n - 1, ?_⟩⟩, ?_⟩
  · simpa only [Fintype.card_fin] using (SimpleGraph.IsRegularOfDegree.top (V := Fin n))
  · intro G hconn hregular
    obtain ⟨r, hreg⟩ := hregular
    have hr : 2 ≤ r := two_le_regular hn G hconn hreg
    have hmpos : 0 < 2 * m := by omega
    have hexp : 0 ≤ (1 : ℝ) / (2 * m : ℕ) :=
      le_of_lt (one_div_pos.mpr (Nat.cast_pos.mpr hmpos))
    constructor
    · exact Real.rpow_le_rpow (chs_two_mul_pos _ m)
        (chs_cycle_le_regular hn G hreg hr m) hexp
    · exact Real.rpow_le_rpow (chs_two_mul_pos G m) (chs_le_top G (2 * m)) hexp

end D5.S3.Combinatorics.Graph.RegularCHS.Result
