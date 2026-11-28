/- GID: D5/S3/Combinatorics/Graph/DeletionResilientCliques/EdgeBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DeletionResilientCliques/EdgeBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Graph/DeletionResilientCliques/CriticalVertexCover, D5/S3/Combinatorics/Graph/DeletionResilientCliques/ColorableInducedSubgraph, mathlib/module/Mathlib.Combinatorics.SimpleGraph.DegreeSum, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Sum, mathlib/module/Mathlib.Algebra.Order.BigOperators.Ring.Finset, mathlib/module/Mathlib.Tactic.FieldSimp, mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.Positivity, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Edge lower bound for clique-free graphs resilient to deletion. -/

import D5.S3.Combinatorics.Graph.DeletionResilientCliques.CriticalVertexCover
import D5.S3.Combinatorics.Graph.DeletionResilientCliques.ColorableInducedSubgraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Edge lower bound for clique-free graphs resilient to deletion -/

open scoped BigOperators ENat
open SimpleGraph

namespace AppendixA

/-- Every deletion of exactly `t` vertices leaves a `w`-clique.
The lower bound assumes `w + t ≤ Fintype.card V` to ensure such deletions exist. -/
def SurvivesDeletion {V : Type*} (G : SimpleGraph V) (w t : ℕ) : Prop :=
  ∀ S : Finset V, S.card = t → ∃ Q : Finset V, G.IsNClique w Q ∧ Disjoint S Q

/-- The exact integer bound in Theorem 3.3.
For `1 ≤ t`, `t / 2` is the ceiling of `(t - 1) / 2` in the paper. -/
def B (w t : ℕ) : ℕ :=
  (w + (t - 1) / 2).choose 2 + (w + t / 2).choose 2

private theorem order_lower_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    {w t : ℕ} (hn : w + t ≤ Fintype.card V) (hfree : G.CliqueFree (w + t))
    (hdelete : SurvivesDeletion G w t) :
    2 * w + t - 1 ≤ Fintype.card V := by
  classical
  let n := Fintype.card V
  let q := n - (w + t)
  have hq : q + (w + t) = n := Nat.sub_add_cancel hn
  have hcover : CriticalVertexCover.CoverAtLeast Gᶜ (q + 1) := by
    change ((q + 1 : ℕ) : ℕ∞) ≤ Gᶜ.vertexCoverNum
    by_contra! h
    have hle : Gᶜ.vertexCoverNum ≤ (q : ℕ∞) :=
      (ENat.lt_add_one_iff (by simp)).mp (by simpa only [Nat.cast_add, Nat.cast_one] using h)
    have hqn : (q : ℕ∞) ≤ ENat.card V := by
      rw [ENat.card_eq_coe_fintype_card]
      exact ENat.natCast_le_natCast.mpr (by omega)
    obtain ⟨C, hCcard, hC⟩ := Gᶜ.exists_of_le_vertexCoverNum q hle hqn
    have hcard : C.toFinset.card = q := by
      have hcast : (C.toFinset.card : ℕ∞) = (q : ℕ∞) := by
        rw [← Set.encard_coe_eq_coe_finsetCard, Set.coe_toFinset]
        exact hCcard
      exact_mod_cast hcast
    have hclique : G.IsClique (C.toFinsetᶜ : Finset V) := by
      rw [Finset.coe_compl, Set.coe_toFinset, ← isIndepSet_compl, ← isVertexCover_compl]
      simpa using hC
    exact hfree _ ⟨hclique, by rw [Finset.card_compl, hcard]; omega⟩
  obtain ⟨J, hJcover, hJsupport⟩ := CriticalVertexCover.exists_small_cover_witness Gᶜ (q + 1) (by omega) hcover
  by_contra! hsmall
  let P := J.spanningCoe.support.toFinset
  have hP : P.card ≤ 2 * (q + 1) := by
    rw [Set.ncard_eq_toFinset_card'] at hJsupport
    exact hJsupport
  have hspace : t ≤ Pᶜ.card := by
    rw [Finset.card_compl]
    omega
  obtain ⟨S, hSP, hScard⟩ := Finset.exists_subset_card_eq hspace
  obtain ⟨Q, hQ, hSQ⟩ := hdelete S hScard
  have hQind : Gᶜ.IsIndepSet (Q : Set V) := (isIndepSet_compl G).mpr hQ.isClique
  have hI : J.spanningCoe.IsIndepSet ((S ∪ Q : Finset V) : Set V) := by
    intro u hu v hv huv hadj
    have hnotS {z : V} (hz : z ∈ J.spanningCoe.support) : z ∉ S := by
      intro hS
      exact (Finset.mem_compl.mp (hSP hS)) (Set.mem_toFinset.mpr hz)
    exact hQind
      ((Finset.mem_union.mp hu).resolve_left (hnotS hadj.mem_support_left))
      ((Finset.mem_union.mp hv).resolve_left (hnotS hadj.mem_support_right)) huv (J.spanningCoe_le hadj)
  have hC := ((isVertexCover_compl).mpr hI).vertexCoverNum_le
  rw [hJcover, ← Finset.coe_compl, Set.encard_coe_eq_coe_finsetCard] at hC
  have hC' := ENat.natCast_le_natCast.mp hC
  rw [Finset.card_compl, Finset.card_union_of_disjoint hSQ, hScard, hQ.card_eq] at hC'
  omega

private theorem reciprocal_upper_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {w t : ℕ} (hw : 1 < w) (hn : t ≤ Fintype.card V)
    (hmin : w - 1 ≤ G.minDegree) (hdelete : SurvivesDeletion G w t) :
    ((w : ℚ) - 1) * (∑ v : V, 1 / ((G.degree v : ℚ) + 1)) ≤
      (Fintype.card V : ℚ) - t - 1 := by
  classical
  obtain ⟨X, hXcolor, hXsum⟩ := ColorableInducedSubgraph.exists_colorable_induce_of_minDegree G (w - 1)
    (by omega) ((Nat.sub_le _ _).trans hmin)
  have hXfree := (cliqueFree_induce_iff G (X : Set V) w).mp (hXcolor.cliqueFree (by omega))
  have hlarge : t < Xᶜ.card := by
    by_contra! hsmall
    obtain ⟨S, hXS, _, hScard⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.subset_univ Xᶜ) hsmall
        (by simpa using hn : t ≤ (Finset.univ : Finset V).card)
    obtain ⟨Q, hQ, hSQ⟩ := hdelete S hScard
    apply hXfree ?_ hQ
    intro v hv
    by_contra hvX
    exact Finset.disjoint_left.mp hSQ (hXS (Finset.mem_compl.mpr hvX)) hv
  have hXcard := X.card_add_card_compl
  have hcast : (X.card : ℚ) + t + 1 ≤ Fintype.card V := by
    exact_mod_cast (show X.card + t + 1 ≤ Fintype.card V by omega)
  rw [Nat.cast_pred (by omega : 0 < w)] at hXsum
  linarith only [hcast, hXsum]

/-- The rational function in Appendix A, with its terms collected over the denominator. -/
def phi (w t x : ℚ) : ℚ := ((w - 1) * (x ^ 2 / (x - t - 1)) - x) / 2

private theorem phi_le_edges {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {w t : ℕ} (hw : 1 < w) (hn : w + t ≤ Fintype.card V)
    (hmin : w - 1 ≤ G.minDegree) (hdelete : SurvivesDeletion G w t) :
    phi w t (Fintype.card V) ≤ (G.edgeFinset.card : ℚ) := by
  let n : ℚ := Fintype.card V
  let e : ℚ := G.edgeFinset.card
  let d (v : V) : ℚ := (G.degree v : ℚ) + 1
  have hn' : (w : ℚ) + t ≤ n := by
    dsimp [n]
    exact_mod_cast hn
  have hw' : (1 : ℚ) < w := by exact_mod_cast hw
  have hden : 0 < n - (t : ℚ) - 1 := by linarith
  have hsum : (∑ v : V, d v) = 2 * e + n := by
    have hnat := G.sum_degrees_eq_twice_card_edges
    have hcast : (∑ v : V, (G.degree v : ℚ)) = 2 * e := by
      dsimp [e]
      exact_mod_cast hnat
    simp [d, Finset.sum_add_distrib, hcast, n]
  have hpos : 0 < 2 * e + n := by
    have he : 0 ≤ e := by dsimp [e]; positivity
    have ht : (0 : ℚ) ≤ t := by positivity
    linarith
  have hcs := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset V) (fun _ => (1 : ℚ))
    (g := d) (fun v _ => by dsimp [d]; positivity)
  have hrecip : n ^ 2 / (2 * e + n) ≤ ∑ v : V, 1 / d v := by
    simpa [hsum, n] using hcs
  have hupper := reciprocal_upper_bound G hw (by omega) hmin hdelete
  have hquot : ((w : ℚ) - 1) * (n ^ 2 / (2 * e + n)) ≤ n - t - 1 :=
    (mul_le_mul_of_nonneg_left hrecip (by linarith)).trans hupper
  rw [← mul_div_assoc] at hquot
  have hcross := (div_le_iff₀ hpos).mp hquot
  have hphi : ((w : ℚ) - 1) * (n ^ 2 / (n - t - 1)) ≤ 2 * e + n := by
    rw [← mul_div_assoc, div_le_iff₀ hden, mul_comm (2 * e + n)]
    exact hcross
  change (((w : ℚ) - 1) * (n ^ 2 / (n - t - 1)) - n) / 2 ≤ e
  linarith only [hphi]

private theorem sq_div_identity {x t : ℚ} (hx : x - t - 1 ≠ 0) :
    x ^ 2 / (x - t - 1) = x + t + 1 + (t + 1) ^ 2 / (x - t - 1) := by
  field_simp [hx]
  ring

private theorem phi_sub_phi {w t x y : ℚ} (hx : x - t - 1 ≠ 0) (hy : y - t - 1 ≠ 0) :
    phi w t y - phi w t x =
      (y - x) / 2 * (w - 2 - (w - 1) * ((t + 1) ^ 2 / ((x - t - 1) * (y - t - 1)))) := by
  simp only [phi, sq_div_identity hx, sq_div_identity hy]
  field_simp [hx, hy]
  ring

private theorem phi_strictMonoOn {w t : ℚ} (ht : 1 ≤ t) (hw : t + 4 ≤ w) :
    StrictMonoOn (phi w t) (Set.Ici (2 * w + t - 1)) := by
  intro x hx y hy hxy
  change 2 * w + t - 1 ≤ x at hx
  change 2 * w + t - 1 ≤ y at hy
  have hxden : 0 < x - t - 1 := by linarith
  have hyden : 0 < y - t - 1 := by linarith
  have hbase : 0 ≤ 2 * (t + 1) := by linarith
  have hprod : (2 * (t + 1)) * (2 * (t + 1)) ≤ (x - t - 1) * (y - t - 1) :=
    mul_le_mul (by linarith) (by linarith) hbase hxden.le
  have hratio : (t + 1) ^ 2 / ((x - t - 1) * (y - t - 1)) ≤ 1 / 4 :=
    (div_le_iff₀ (mul_pos hxden hyden)).mpr (by nlinarith only [hprod])
  have hweighted := mul_le_mul_of_nonneg_left hratio (show 0 ≤ w - 1 by linarith)
  have hfactor : 0 < w - 2 - (w - 1) * ((t + 1) ^ 2 / ((x - t - 1) * (y - t - 1))) :=
    by linarith only [hweighted, ht, hw]
  apply sub_pos.mp
  rw [phi_sub_phi hxden.ne' hyden.ne']
  exact mul_pos (by linarith) hfactor

private theorem phi_at_initial_order {w t : ℚ} (hw : 1 < w) :
    phi w t (2 * w + t - 1) = (2 * w + t - 1) * ((2 * w + t - 1) - 2) / 4 := by
  unfold phi
  have hden : (2 * w + t - 1) - t - 1 = 2 * (w - 1) := by ring
  rw [hden]
  field_simp [show w - 1 ≠ 0 by linarith]
  ring

private theorem two_mul_choose_two_cast {a : ℕ} (ha : 0 < a) :
    2 * (a.choose 2 : ℚ) = (a : ℚ) * ((a : ℚ) - 1) := by
  have hnat : 2 * a.choose 2 = a * (a - 1) := by
    rw [Nat.choose_two_right]
    obtain ⟨k, hk⟩ := Nat.even_mul_pred_self a
    exact Nat.mul_div_cancel' ⟨k, hk.trans (by omega)⟩
  have hcast : 2 * (a.choose 2 : ℚ) = (a : ℚ) * ((a - 1 : ℕ) : ℚ) := by
    exact_mod_cast hnat
  simpa only [Nat.cast_pred ha] using hcast

private theorem B_le_of_phi_at_initial_order {w t e : ℕ} (ht : 1 ≤ t) (hw : 1 < w)
    (hphi : phi w t (2 * w + t - 1) ≤ (e : ℚ)) :
    B w t ≤ e := by
  let a := w + (t - 1) / 2
  let b := w + t / 2
  have hab : a ≤ b := by dsimp [a, b]; omega
  have hba : b ≤ a + 1 := by dsimp [a, b]; omega
  have habSum : a + b = 2 * w + t - 1 := by dsimp [a, b]; omega
  have ha : 0 < a := by dsimp [a]; omega
  have hb : 0 < b := ha.trans_le hab
  have hsum : (a : ℚ) + (b : ℚ) = 2 * (w : ℚ) + t - 1 := by
    have hc : (a : ℚ) + (b : ℚ) + 1 = 2 * (w : ℚ) + t := by
      exact_mod_cast (show a + b + 1 = 2 * w + t by omega)
    linarith only [hc]
  have habQ : (a : ℚ) ≤ b := by exact_mod_cast hab
  have hbaQ : (b : ℚ) ≤ (a : ℚ) + 1 := by exact_mod_cast hba
  have hgap : ((b : ℚ) - (a : ℚ)) ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg (show (0 : ℚ) ≤ b - a by linarith)
      (show (0 : ℚ) ≤ 1 - (b - a) by linarith), hbaQ]
  have hidentity : 4 * (B w t : ℚ) =
      ((a : ℚ) + b) * (((a : ℚ) + b) - 2) + ((b : ℚ) - a) ^ 2 := by
    change 4 * ((a.choose 2 + b.choose 2 : ℕ) : ℚ) = _
    rw [Nat.cast_add]
    linarith only [two_mul_choose_two_cast ha, two_mul_choose_two_cast hb]
  rw [phi_at_initial_order (show (1 : ℚ) < w by exact_mod_cast hw), ← hsum] at hphi
  by_contra! h
  have hcast : (e : ℚ) + 1 ≤ (B w t : ℚ) := by
    exact_mod_cast (show e + 1 ≤ B w t by omega)
  linarith only [hcast, hidentity, hphi, hgap]

/-- The `K_(w+t)`-free edge lower bound in Theorem 3.3, Appendix A. -/
theorem nonclique_edge_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {w t : ℕ} (ht : 1 ≤ t) (hw : t + 3 < w)
    (hn : w + t ≤ Fintype.card V) (hfree : G.CliqueFree (w + t))
    (hmin : w - 1 ≤ G.minDegree) (hdelete : SurvivesDeletion G w t) :
    B w t ≤ G.edgeFinset.card := by
  have horder := order_lower_bound G hn hfree hdelete
  have horderQ : 2 * (w : ℚ) + t - 1 ≤ Fintype.card V := by
    have hc : 2 * (w : ℚ) + t ≤ (Fintype.card V : ℚ) + 1 := by
      exact_mod_cast (show 2 * w + t ≤ Fintype.card V + 1 by omega)
    linarith
  have htQ : (1 : ℚ) ≤ t := by exact_mod_cast ht
  have hwQ : (t : ℚ) + 4 ≤ w := by exact_mod_cast (show t + 4 ≤ w by omega)
  have hw' : 1 < w := by omega
  have hmono := (phi_strictMonoOn htQ hwQ).monotoneOn
    (show 2 * (w : ℚ) + t - 1 ∈ Set.Ici (2 * (w : ℚ) + t - 1) from
      show 2 * (w : ℚ) + t - 1 ≤ 2 * (w : ℚ) + t - 1 from le_rfl)
    (show (Fintype.card V : ℚ) ∈ Set.Ici (2 * (w : ℚ) + t - 1) from horderQ) horderQ
  exact B_le_of_phi_at_initial_order ht hw'
    (hmono.trans (phi_le_edges G hw' hn hmin hdelete))

end AppendixA
