/- GID: D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy
   generality: I
   mirror-B: D5/B/S0/Certificates/Hypergraphs/CircularOrientationEntropy
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy.claim; result=D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy.result; claim=D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy.claim
   digest: A four-edge three-uniform multihypergraph has greater entropy than the circle. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#15996; Refuted).
Direct frozen dependencies: none (the imported balance module is in the same delivery).
All private theorems are bind-only, with consumers:
witness_uniform -> result;
witness_counts -> counts_certificate;
circular_counts -> counts_certificate;
counts_certificate -> witness_entropy_gt;
witness_entropy_gt -> result.
The shared entropy uses the literal orientation filter and the explicit r denominator.
The circular coordinates use Mathlib's Fin.ofNat; positivity follows from the vertex index,
without an extra hypothesis.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S0.Certificates.Hypergraphs.OrientationEntropyBalance
namespace D5.S0.Certificates.Hypergraphs.CircularOrientationEntropy
open D5.S0.Certificates.Hypergraphs.OrientationEntropyBalance

def circular (n r : ℕ) : Fin n → Finset (Fin n) :=
  fun i =>
    letI : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)⟩
    (Finset.range r).image (fun j => Fin.ofNat n (i.val + j))

def claim : Prop := ∀ r n : ℕ, 3 ≤ r → r < n →
  ∀ E : Fin n → Finset (Fin n), (∀ i, (E i).card = r) →
    entropyX r E ≤ entropyX r (circular n r)

private def witness : Fin 4 → Finset (Fin 4) := ![{0, 1, 2}, {0, 1, 2}, {0, 1, 3}, {0, 1, 3}]

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem witness_uniform : ∀ i, (witness i).card = 3 := by decide

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem witness_counts : ∀ k : Fin 5,
    ((Fintype.piFinset witness).filter (fun o => X witness o = k)).card =
      (![0, 2, 27, 44, 8] : Fin 5 → ℕ) k := by decide

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem circular_counts : ∀ k : Fin 5,
    ((Fintype.piFinset (circular 4 3)).filter (fun o => X (circular 4 3) o = k)).card =
      (![0, 0, 24, 48, 9] : Fin 5 → ℕ) k := by decide

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem counts_certificate :
    (∑ k ∈ Finset.range 5, ((Fintype.piFinset witness).filter (fun o => X witness o = k)).card) =
      81 ∧
    (∑ k ∈ Finset.range 5, ((Fintype.piFinset (circular 4 3)).filter (fun o => X (circular 4 3) o = k)).card) =
      81 ∧
    (∏ k ∈ Finset.range 5, ((Fintype.piFinset witness).filter (fun o => X witness o = k)).card ^
      ((Fintype.piFinset witness).filter (fun o => X witness o = k)).card) < (∏ k ∈ Finset.range 5, ((Fintype.piFinset (circular 4 3)).filter (fun o => X (circular 4 3) o = k)).card ^
      ((Fintype.piFinset (circular 4 3)).filter (fun o => X (circular 4 3) o = k)).card) := by
  have hw0 := witness_counts 0
  change ((Fintype.piFinset witness).filter (fun o => X witness o = 0)).card =
    0 at hw0
  have hw1 := witness_counts 1
  change ((Fintype.piFinset witness).filter (fun o => X witness o = 1)).card =
    2 at hw1
  have hw2 := witness_counts 2
  change ((Fintype.piFinset witness).filter (fun o => X witness o = 2)).card =
    27 at hw2
  have hw3 := witness_counts 3
  change ((Fintype.piFinset witness).filter (fun o => X witness o = 3)).card =
    44 at hw3
  have hw4 := witness_counts 4
  change ((Fintype.piFinset witness).filter (fun o => X witness o = 4)).card =
    8 at hw4
  have hc0 := circular_counts 0
  change ((Fintype.piFinset (circular 4 3)).filter (fun o => X (circular 4 3) o = 0)).card =
    0 at hc0
  have hc1 := circular_counts 1
  change ((Fintype.piFinset (circular 4 3)).filter (fun o => X (circular 4 3) o = 1)).card =
    0 at hc1
  have hc2 := circular_counts 2
  change ((Fintype.piFinset (circular 4 3)).filter (fun o => X (circular 4 3) o = 2)).card =
    24 at hc2
  have hc3 := circular_counts 3
  change ((Fintype.piFinset (circular 4 3)).filter (fun o => X (circular 4 3) o = 3)).card =
    48 at hc3
  have hc4 := circular_counts 4
  change ((Fintype.piFinset (circular 4 3)).filter (fun o => X (circular 4 3) o = 4)).card =
    9 at hc4
  norm_num [Finset.sum_range_succ, Finset.prod_range_succ, hw0, hw1, hw2, hw3, hw4, hc0, hc1, hc2, hc3, hc4]

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem witness_entropy_gt : entropyX 3 (circular 4 3) < entropyX 3 witness := by
  have formula (E : Fin 4 → Finset (Fin 4))
      (hsum : (∑ k ∈ Finset.range 5,
        ((Fintype.piFinset E).filter (fun o => X E o = k)).card) = 81) :
      entropyX 3 E = Real.logb 2 81 - Real.logb 2
        (∏ k ∈ Finset.range 5,
          ((Fintype.piFinset E).filter (fun o => X E o = k)).card ^
          ((Fintype.piFinset E).filter (fun o => X E o = k)).card : ℕ) / 81 := by
    norm_num only [entropyX, orientations_eq, Nat.cast_ofNat, Nat.cast_pow]
    exact sum_entropy_formula (Finset.range 5)
        (fun k => ((Fintype.piFinset E).filter (fun o => X E o = k)).card)
        81 (by decide) hsum
  have hc := counts_certificate
  rw [formula witness hc.1, formula (circular 4 3) hc.2.1]
  have hp : (0 : ℝ) < (∏ k ∈ Finset.range 5,
      ((Fintype.piFinset witness).filter (fun o => X witness o = k)).card ^
      ((Fintype.piFinset witness).filter (fun o => X witness o = k)).card : ℕ) := by
    have hpN : 0 < (∏ k ∈ Finset.range 5,
      ((Fintype.piFinset witness).filter (fun o => X witness o = k)).card ^
      ((Fintype.piFinset witness).filter (fun o => X witness o = k)).card) := by
      apply Finset.prod_pos
      intro k _
      exact Nat.pow_self_pos
    exact_mod_cast hpN
  have ho : ((∏ k ∈ Finset.range 5,
      ((Fintype.piFinset witness).filter (fun o => X witness o = k)).card ^
      ((Fintype.piFinset witness).filter (fun o => X witness o = k)).card : ℕ) : ℝ) <
      (∏ k ∈ Finset.range 5,
      ((Fintype.piFinset (circular 4 3)).filter (fun o => X (circular 4 3) o = k)).card ^
      ((Fintype.piFinset (circular 4 3)).filter (fun o => X (circular 4 3) o = k)).card : ℕ) := by
    exact_mod_cast hc.2.2
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hp ho
  exact sub_lt_sub_left ((div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 81)).mpr hl) _

theorem result : ¬ claim := by
  intro h
  exact (not_le_of_gt witness_entropy_gt) (h 3 4 (by decide) (by decide) witness witness_uniform)

end D5.S0.Certificates.Hypergraphs.CircularOrientationEntropy
