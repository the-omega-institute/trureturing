/- GID: D5/S3/Combinatorics/Graph/TypedPortTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/TypedPortTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.DegreeSum, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Two partial matching graphs force the typed port defect identity. -/

/-
proof_shape: content
escape_witness: D5/S3/Combinatorics/Graph/TypedPortTransport.matching_defect_eq_terminal_difference
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.TypedPortTransport

open Finset
open scoped BigOperators

/-- The three endpoint types in a typed port routing. -/
inductive RouteKind
  | ll
  | hh
  | lh
  deriving DecidableEq

/-- A finite collection of routed paths, recorded only through its endpoint types. -/
structure RouteEndpoints where
  Path : Type
  instPath : Fintype Path
  instPathDecidableEq : DecidableEq Path
  kind : Path → RouteKind
  leftTerminals : ℕ
  slackTerminals : ℕ
  leftCount : Path → ℕ
  slackCount : Path → ℕ
  left_count_spec : ∀ p,
    leftCount p = if kind p = .ll then 2 else if kind p = .lh then 1 else 0
  slack_count_spec : ∀ p,
    slackCount p = if kind p = .hh then 2 else if kind p = .lh then 1 else 0
  left_total_spec : leftTerminals = ∑ p, leftCount p
  slack_total_spec : slackTerminals = ∑ p, slackCount p

attribute [instance] RouteEndpoints.instPath RouteEndpoints.instPathDecidableEq

/-- Ports left unmatched by the local pairing but matched by an actual edge. -/
noncomputable def leftTerminalsOf {P : Type} [Fintype P] [DecidableEq P]
    (actual pairing : SimpleGraph P) [DecidableRel actual.Adj] [DecidableRel pairing.Adj] : Finset P :=
  univ.filter fun v => actual.degree v = 1 ∧ pairing.degree v = 0

/-- Ports left unmatched by an actual edge but matched by the local pairing. -/
noncomputable def slackTerminalsOf {P : Type} [Fintype P] [DecidableEq P]
    (actual pairing : SimpleGraph P) [DecidableRel actual.Adj] [DecidableRel pairing.Adj] : Finset P :=
  univ.filter fun v => actual.degree v = 0 ∧ pairing.degree v = 1

private noncomputable def sharedPorts {P : Type} [Fintype P] [DecidableEq P]
    (actual pairing : SimpleGraph P) [DecidableRel actual.Adj] [DecidableRel pairing.Adj] : Finset P :=
  univ.filter fun v => actual.degree v = 1 ∧ pairing.degree v = 1

theorem matching_defect_eq_terminal_difference {P : Type} [Fintype P] [DecidableEq P]
    (actual pairing : SimpleGraph P) [DecidableRel actual.Adj] [DecidableRel pairing.Adj]
    (hactual : ∀ v, actual.degree v ≤ 1) (hlocal : ∀ v, pairing.degree v ≤ 1) :
    (2 : ℤ) * (actual.edgeFinset.card : ℤ) -
        2 * (pairing.edgeFinset.card : ℤ) =
      (leftTerminalsOf actual pairing).card - (slackTerminalsOf actual pairing).card := by
  classical
  have actual_sum : ∑ v, actual.degree v =
      (leftTerminalsOf actual pairing).card + (sharedPorts actual pairing).card := by
    calc
      (∑ v, actual.degree v) =
          ∑ v, ((if actual.degree v = 1 ∧ pairing.degree v = 0 then 1 else 0) +
            (if actual.degree v = 1 ∧ pairing.degree v = 1 then 1 else 0)) := by
        apply sum_congr rfl
        intro v hv
        have ha_le := hactual v
        have hl_le := hlocal v
        by_cases ha : actual.degree v = 1
        · by_cases hl : pairing.degree v = 1
          · simp [ha, hl]
          · have hl0 : pairing.degree v = 0 := by omega
            simp [ha, hl, hl0]
        · have ha0 : actual.degree v = 0 := by omega
          by_cases hl : pairing.degree v = 1
          · simp [ha, ha0, hl]
          · have hl0 : pairing.degree v = 0 := by omega
            simp [ha, ha0, hl, hl0]
      _ = (leftTerminalsOf actual pairing).card + (sharedPorts actual pairing).card := by
        rw [sum_add_distrib]
        simp [leftTerminalsOf, sharedPorts, Finset.sum_boole]
  have pairing_sum : ∑ v, pairing.degree v =
      (slackTerminalsOf actual pairing).card + (sharedPorts actual pairing).card := by
    calc
      (∑ v, pairing.degree v) =
          ∑ v, ((if actual.degree v = 0 ∧ pairing.degree v = 1 then 1 else 0) +
            (if actual.degree v = 1 ∧ pairing.degree v = 1 then 1 else 0)) := by
        apply sum_congr rfl
        intro v hv
        have ha_le := hactual v
        have hl_le := hlocal v
        by_cases ha : actual.degree v = 1
        · by_cases hl : pairing.degree v = 1
          · simp [ha, hl]
          · have hl0 : pairing.degree v = 0 := by omega
            simp [ha, hl, hl0]
        · have ha0 : actual.degree v = 0 := by omega
          by_cases hl : pairing.degree v = 1
          · simp [ha, ha0, hl]
          · have hl0 : pairing.degree v = 0 := by omega
            simp [ha, ha0, hl, hl0]
      _ = (slackTerminalsOf actual pairing).card + (sharedPorts actual pairing).card := by
        rw [sum_add_distrib]
        simp [slackTerminalsOf, sharedPorts, Finset.sum_boole]
  have actual_edges := SimpleGraph.sum_degrees_eq_twice_card_edges actual
  have pairing_edges := SimpleGraph.sum_degrees_eq_twice_card_edges pairing
  have actual_edges_z : (∑ v, actual.degree v : ℕ) = 2 * actual.edgeFinset.card := actual_edges
  have pairing_edges_z : (∑ v, pairing.degree v : ℕ) = 2 * pairing.edgeFinset.card := pairing_edges
  omega

private theorem left_sum_formula (r : RouteEndpoints) :
    (∑ p, r.leftCount p) =
      2 * (univ.filter (fun p => r.kind p = .ll)).card +
        (univ.filter (fun p => r.kind p = .lh)).card := by
  simp_rw [RouteEndpoints.left_count_spec]
  calc
    (∑ p, if r.kind p = .ll then 2 else if r.kind p = .lh then 1 else 0) =
        ∑ p, ((if r.kind p = .ll then 1 else 0) * 2 +
          (if r.kind p = .lh then 1 else 0)) := by
            apply sum_congr rfl
            intro p hp
            by_cases hll : r.kind p = .ll <;>
              by_cases hlh : r.kind p = .lh <;>
              simp [hll, hlh]
    _ = (∑ p, if r.kind p = .ll then 1 else 0) * 2 +
          ∑ p, if r.kind p = .lh then 1 else 0 := by
            rw [sum_add_distrib, ← Finset.sum_mul]
    _ = 2 * (univ.filter (fun p => r.kind p = .ll)).card +
          (univ.filter (fun p => r.kind p = .lh)).card := by
            simp only [Finset.sum_boole]
            norm_num [Nat.cast_ofNat, Nat.mul_comm]

private theorem slack_sum_formula (r : RouteEndpoints) :
    (∑ p, r.slackCount p) =
      2 * (univ.filter (fun p => r.kind p = .hh)).card +
        (univ.filter (fun p => r.kind p = .lh)).card := by
  simp_rw [RouteEndpoints.slack_count_spec]
  calc
    (∑ p, if r.kind p = .hh then 2 else if r.kind p = .lh then 1 else 0) =
        ∑ p, ((if r.kind p = .hh then 1 else 0) * 2 +
          (if r.kind p = .lh then 1 else 0)) := by
            apply sum_congr rfl
            intro p hp
            by_cases hhh : r.kind p = .hh <;>
              by_cases hlh : r.kind p = .lh <;>
              simp [hhh, hlh]
    _ = (∑ p, if r.kind p = .hh then 1 else 0) * 2 +
          ∑ p, if r.kind p = .lh then 1 else 0 := by
            rw [sum_add_distrib, ← Finset.sum_mul]
    _ = 2 * (univ.filter (fun p => r.kind p = .hh)).card +
          (univ.filter (fun p => r.kind p = .lh)).card := by
            simp only [Finset.sum_boole]
            norm_num [Nat.cast_ofNat, Nat.mul_comm]

/-- The two terminal equations for LL, HH and LH paths are forced by endpoint counting. -/
theorem terminal_counts (r : RouteEndpoints) :
    r.leftTerminals =
        2 * (univ.filter (fun p => r.kind p = .ll)).card +
          (univ.filter (fun p => r.kind p = .lh)).card ∧
      r.slackTerminals =
        2 * (univ.filter (fun p => r.kind p = .hh)).card +
          (univ.filter (fun p => r.kind p = .lh)).card := by
  constructor
  · rw [r.left_total_spec, left_sum_formula]
  · rw [r.slack_total_spec, slack_sum_formula]

/-- The typed port defect `C - R = a - b`, with subtraction interpreted in `ℤ`.

The proof combines endpoint counts with the degree balance for two partial
matching graphs. The matching balance is obtained from the finite graph
degree-sum theorem and a pointwise classification of degree pairs. -/
theorem defect_eq_route_difference (r : RouteEndpoints)
    (actual pairing : SimpleGraph r.Path) [DecidableRel actual.Adj] [DecidableRel pairing.Adj]
    (hactual : ∀ v, actual.degree v ≤ 1) (hlocal : ∀ v, pairing.degree v ≤ 1)
    (hleft : r.leftTerminals = (leftTerminalsOf actual pairing).card)
    (hslack : r.slackTerminals = (slackTerminalsOf actual pairing).card) :
    (actual.edgeFinset.card : ℤ) - pairing.edgeFinset.card =
      ((univ.filter (fun p => r.kind p = .ll)).card : ℤ) -
        (univ.filter (fun p => r.kind p = .hh)).card := by
  obtain ⟨hleftCount, hslackCount⟩ := terminal_counts r
  have hbalance := matching_defect_eq_terminal_difference actual pairing hactual hlocal
  have hbalance' := hbalance
  rw [← hleft, ← hslack] at hbalance'
  have hleftZ : (r.leftTerminals : ℤ) =
      2 * (univ.filter (fun p => r.kind p = .ll)).card +
        (univ.filter (fun p => r.kind p = .lh)).card := by
    exact_mod_cast hleftCount
  have hslackZ : (r.slackTerminals : ℤ) =
      2 * (univ.filter (fun p => r.kind p = .hh)).card +
        (univ.filter (fun p => r.kind p = .lh)).card := by
    exact_mod_cast hslackCount
  omega

end D5.S3.Combinatorics.Graph.TypedPortTransport
