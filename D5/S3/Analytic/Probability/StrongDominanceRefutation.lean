/- GID: D5/S3/Analytic/Probability/StrongDominanceRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/Probability/StrongDominanceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/Probability/StrongDominanceRefutation.claim; result=D5/S3/Analytic/Probability/StrongDominanceRefutation.result; claim=D5/S3/Analytic/Probability/StrongDominanceRefutation.claim
   digest: A positive four-label, five-draw counterexample to strong dominance. -/

/-
admission_basis: open-problem-resolution (#28951; Refuted)
escape_witness: none
proof_shape: distinctCountPMF: bind-only; consumer: claim, result; escape_witness: none.
proof_shape: StronglyDominates: bind-only; consumer: claim, result; escape_witness: none.
proof_shape: claim: bind-only; consumer: result; escape_witness: none.
proof_shape: result: bind-only; consumer: none; escape_witness: none.
proof_shape: pVec: bind-only; consumer: p, p_moreMixed; escape_witness: none.
proof_shape: qVec: bind-only; consumer: q, p_moreMixed; escape_witness: none.
proof_shape: p: bind-only; consumer: result; escape_witness: none.
proof_shape: q: bind-only; consumer: result; escape_witness: none.
proof_shape: pNat: bind-only; consumer: p_two_nat, p_three_nat, result; escape_witness: none.
proof_shape: qNat: bind-only; consumer: q_two_nat, q_three_nat, result; escape_witness: none.
proof_shape: natPMF: bind-only; consumer: p_two_nat, q_two_nat, p_three_nat, q_three_nat, result; escape_witness: none.
proof_shape: p_moreMixed: bind-only; consumer: result; escape_witness: none.
proof_shape: p_two_nat: bind-only; consumer: result; escape_witness: none.
proof_shape: q_two_nat: bind-only; consumer: result; escape_witness: none.
proof_shape: p_three_nat: bind-only; consumer: result; escape_witness: none.
proof_shape: q_three_nat: bind-only; consumer: result; escape_witness: none.
Direct frozen dependencies (declaration GID + statement_id):
X: D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.X
  sha256:8e1a8a4eb55faa65325f38ad95ad302788d372e4114b324a755279123c21c441
desc: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.desc
  sha256:202c59b217e53e6c388923e06fa6acf48979f254a0e5c1bb35bd4e89c937db55
moreMixed: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.moreMixed
  sha256:565b9b70d03155f061b4fe949164aa173255e7ceac42365730d8420ff3c7616a
prefixSum: D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.prefixSum
  sha256:93ca1f1520e0d21d918273555bd2933d31f2a7bfe3a4b3c132e8c154b2ffdc8b
Direct frozen dependencies by declaration, after inlining same-module helpers:
result: X, desc, moreMixed, prefixSum.
p_moreMixed: desc, moreMixed, prefixSum.
claim: moreMixed.
natPMF, p_two_nat, q_two_nat, p_three_nat, q_three_nat: X.
distinctCountPMF, StronglyDominates, pVec, qVec, p, q, pNat, qNat: none.
The simplex carrier is used directly, without a type alias. The image-card
expression stays literal in distinctCountPMF; the integer computation uses
OrientationEntropyBalance.X, with its defining equality unfolded in the bridge.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.Tactic.IntervalCases
import D5.S0.Certificates.Hypergraphs.OrientationEntropyBalance
import D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing


/-! The finite cylinder law and a positive-risk counterexample to single-crossing dominance. -/

namespace D5.S3.Analytic.Probability.StrongDominanceRefutation

set_option autoImplicit false

open scoped BigOperators
open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing (moreMixed)

/-- Pₚ(Yₙ = k), by summing the cylinder probabilities of all length-n words. -/
def distinctCountPMF {N : ℕ} (p : Convexity.StdSimplex ℝ (Fin N)) (n k : ℕ) : ℝ :=
  ∑ w : Fin n → Fin N, if (Finset.univ.image w).card = k then ∏ j : Fin n, p.weights (w j) else 0

/-- Definition 8.2 (published Definition 7.2), with D = ℕ embedded in ℝ.
The low side includes c; the high side is strictly greater than c. -/
def StronglyDominates (a b : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ k : ℕ,
    ((k : ℝ) ≤ c → a k ≤ b k) ∧
    (c < (k : ℝ) → b k ≤ a k)

/-- For every population size N ≥ 1, number of draws n ≥ 1, and source risk
distributions p and q, p ≺ q implies that Yₙ under p strongly dominates Yₙ under q.
The existing moreMixed sorts decreasingly, compares every proper prefix, and
requires equal totals: it is precisely Definition 6.1, including permutations. -/
def claim : Prop :=
  ∀ N : ℕ, ∀ n : ℕ, 0 < N → 0 < n →
    ∀ p : Convexity.StdSimplex ℝ (Fin N), ∀ q : Convexity.StdSimplex ℝ (Fin N),
      moreMixed (fun i => p.weights i) (fun i => q.weights i) →
        StronglyDominates (distinctCountPMF p n) (distinctCountPMF q n)

end D5.S3.Analytic.Probability.StrongDominanceRefutation

namespace D5.S3.Analytic.Probability.StrongDominanceRefutation
open scoped BigOperators
open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing
noncomputable section

private def pVec : Fin 4 → ℝ := ![48/100, 48/100, 2/100, 2/100]
private def qVec : Fin 4 → ℝ := ![50/100, 46/100, 3/100, 1/100]
private def p : Convexity.StdSimplex ℝ (Fin 4) where
  weights := Finsupp.equivFunOnFinite.symm pVec
  nonneg := by intro i; fin_cases i <;> norm_num [pVec]
  total := by norm_num [Finsupp.sum_fintype, pVec, Fin.sum_univ_succ]
private def q : Convexity.StdSimplex ℝ (Fin 4) where
  weights := Finsupp.equivFunOnFinite.symm qVec
  nonneg := by intro i; fin_cases i <;> norm_num [qVec]
  total := by norm_num [Finsupp.sum_fintype, qVec, Fin.sum_univ_succ]


set_option Elab.async false
set_option maxRecDepth 100000

private theorem p_moreMixed : moreMixed pVec qVec := by
  have hp : desc pVec = List.ofFn pVec := by
    apply List.mergeSort_eq_self (fun a b : ℝ => b ≤ a)
    norm_num [List.ofFn_succ, pVec]
  have hq : desc qVec = List.ofFn qVec := by
    apply List.mergeSort_eq_self (fun a b : ℝ => b ≤ a)
    norm_num [List.ofFn_succ, qVec]
  constructor
  · intro k hk
    rw [hp, hq]
    interval_cases k <;> norm_num [prefixSum, pVec, qVec, List.ofFn_succ]
  · rw [hp, hq]
    norm_num [prefixSum, pVec, qVec, List.ofFn_succ]

private def pNat : Fin 4 → ℕ := ![48,48,2,2]
private def qNat : Fin 4 → ℕ := ![50,46,3,1]
private def natPMF (v : Fin 4 → ℕ) (k : ℕ) : ℕ :=
  ∑ w : Fin 5 → Fin 4,
    if D5.S0.Certificates.Hypergraphs.OrientationEntropyBalance.X (fun _ => ∅) w = k
    then ∏ j, v (w j) else 0

set_option maxHeartbeats 8000000 in
private theorem p_two_nat : natPMF pNat 2 = 7874904000 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem q_two_nat : natPMF qNat 2 = 7873379340 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem p_three_nat : natPMF pNat 3 = 1560192000 := by
  decide +kernel

set_option maxHeartbeats 8000000 in
private theorem q_three_nat : natPMF qNat 3 = 1566757440 := by
  decide +kernel


theorem result : ¬ claim := by
  have pmf_nat (v : Fin 4 → ℕ) (r : Convexity.StdSimplex ℝ (Fin 4))
      (h : ∀ i, r.weights i = (v i : ℝ) / 100) (k : ℕ) :
      distinctCountPMF r 5 k = (natPMF v k : ℝ) / 100^5 := by
    change distinctCountPMF r 5 k =
      ((∑ w : Fin 5 → Fin 4,
        if (Finset.univ.image w).card = k then ∏ j, v (w j) else 0 : ℕ) : ℝ) / 100^5
    rw [distinctCountPMF, Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro w hw
    split_ifs
    · simp only [h, Finset.prod_div_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, Nat.cast_prod]
    · simp
  intro hc
  have hp : ∀ i, p.weights i = (pNat i : ℝ) / 100 := by
    intro i; fin_cases i <;> norm_num [p, pVec, pNat]
  have hq : ∀ i, q.weights i = (qNat i : ℝ) / 100 := by
    intro i; fin_cases i <;> norm_num [q, qVec, qNat]
  have h2 : distinctCountPMF q 5 2 < distinctCountPMF p 5 2 := by
    rw [pmf_nat pNat p hp]
    rw [pmf_nat qNat q hq]
    rw [p_two_nat]
    rw [q_two_nat]
    norm_num
  have h3 : distinctCountPMF p 5 3 < distinctCountPMF q 5 3 := by
    rw [pmf_nat pNat p hp]
    rw [pmf_nat qNat q hq]
    rw [p_three_nat]
    rw [q_three_nat]
    norm_num
  obtain ⟨c, h⟩ := hc 4 5 (by norm_num) (by norm_num) p q p_moreMixed
  have hc2 : c < (2 : ℝ) :=
    lt_of_not_ge fun hh => (not_le_of_gt h2) ((h 2).1 hh)
  exact (not_le_of_gt h3) ((h 3).2 (lt_trans hc2 (by norm_num)))

end
end D5.S3.Analytic.Probability.StrongDominanceRefutation
