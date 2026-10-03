/- GID: D5/S3/Combinatorics/Graph/TypedPortTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/TypedPortTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Ring.Nat, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Typed terminal counts and an incidence-capacity ledger force the port defect identity. -/

/-
proof_shape: content
escape_witness: D5/S3/Combinatorics/Graph/TypedPortTransport.defect_eq_route_difference
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only)
-/

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

/-- The finite ledger supplied by the actual edge/port incidence construction. -/
structure CapacityLedger where
  actualEdges : ℕ
  capacities : ℕ
  totalDegree : ℕ
  leftTerminals : ℕ
  slackTerminals : ℕ
  incidence : 2 * actualEdges = leftTerminals + totalDegree
  capacity : totalDegree + slackTerminals = 2 * capacities

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

The proof combines the endpoint counts with the two incidence ledgers.  The
incidence equation counts every actual edge twice, while the capacity equation
counts the same positive-capacity vertex incidences as capacity plus slack. -/
theorem defect_eq_route_difference (r : RouteEndpoints) (ledger : CapacityLedger)
    (hleft : r.leftTerminals = ledger.leftTerminals)
    (hslack : r.slackTerminals = ledger.slackTerminals) :
    (ledger.actualEdges : ℤ) - ledger.capacities =
      ((univ.filter (fun p => r.kind p = .ll)).card : ℤ) -
        (univ.filter (fun p => r.kind p = .hh)).card := by
  obtain ⟨hleftCount, hslackCount⟩ := terminal_counts r
  have hinc : (2 : ℤ) * ledger.actualEdges =
      ledger.leftTerminals + ledger.totalDegree := by
    exact_mod_cast ledger.incidence
  have hcap : (ledger.totalDegree : ℤ) + ledger.slackTerminals =
      2 * ledger.capacities := by
    exact_mod_cast ledger.capacity
  have hleftZ : (ledger.leftTerminals : ℤ) =
      2 * (univ.filter (fun p => r.kind p = .ll)).card +
        (univ.filter (fun p => r.kind p = .lh)).card := by
    exact_mod_cast (hleft ▸ hleftCount)
  have hslackZ : (ledger.slackTerminals : ℤ) =
      2 * (univ.filter (fun p => r.kind p = .hh)).card +
        (univ.filter (fun p => r.kind p = .lh)).card := by
    exact_mod_cast (hslack ▸ hslackCount)
  omega

end D5.S3.Combinatorics.Graph.TypedPortTransport
