/- GID: D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance
   generality: I
   mirror-B: D5/B/S0/Certificates/Hypergraphs/OrientationEntropyBalance
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.claim; result=D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.result; claim=D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.claim
   digest: An unbalanced three-edge multigraph maximises orientation-count entropy. -/

/-
result: proof_shape: bind-only; escape_witness: none.
orientations_eq: proof_shape: bind-only; escape_witness: none.
sum_entropy_formula: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#15995; Refuted).
Direct frozen dependencies: none.
All helper theorems are bind-only, with consumers:
orientations_eq -> entropyX_product_formula, CircularOrientationEntropy.witness_entropy_gt;
count_power_pos -> sum_entropy_formula, countProduct_pos;
negMulLog2_div -> sum_entropy_formula;
sum_entropy_formula -> entropyX_product_formula, CircularOrientationEntropy.witness_entropy_gt;
witness_counts -> witness_product;
witness_uniform -> witness_maximises, result;
witness_degrees -> result;
all_counts_certificate -> witness_maximises;
witness_product -> witness_maximises;
countProduct_pos -> entropyX_le_of_product_le;
entropyX_product_formula -> entropyX_le_of_product_le;
entropyX_le_of_product_le -> witness_maximises;
witness_maximises -> result.
The orientation filter stays literal in entropyX; proofs use Fintype.piFinset
through the consumed equality orientations_eq, with no duplicate orientation definition.
The scalar summand is written directly, with no duplicate negMulLog2 definition.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace D5.S0.Certificates.Hypergraphs.OrientationEntropyBalance

def X {n m : ℕ} (_E : Fin m → Finset (Fin n)) (o : Fin m → Fin n) : ℕ :=
  (Finset.univ.image o).card

noncomputable def entropyX {n m : ℕ} (r : ℕ) (E : Fin m → Finset (Fin n)) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    let p := (((Finset.univ.filter (fun o => ∀ i, o i ∈ E i)).filter
      (fun o => X E o = k)).card : ℝ) / (r : ℝ) ^ m;
    -p * Real.logb 2 p

def deg {n m : ℕ} (E : Fin m → Finset (Fin n)) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun i => v ∈ E i)).card

def claim : Prop := ∀ n m r : ℕ, n ≤ m → r < n → 2 ≤ r →
  ∀ E : Fin m → Finset (Fin n), (∀ i, (E i).card = r) →
    (∀ F : Fin m → Finset (Fin n), (∀ i, (F i).card = r) →
      entropyX r F ≤ entropyX r E) →
    ∀ v1 v2, (deg E v1 : ℤ) - deg E v2 ≤ 1

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
theorem orientations_eq {n m : ℕ} (E : Fin m → Finset (Fin n)) :
    Finset.univ.filter (fun o => ∀ i, o i ∈ E i) = Fintype.piFinset E := by
  ext o
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem count_power_pos (c : ℕ) : 0 < c ^ c :=
  Nat.pow_self_pos

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem negMulLog2_div (c N : ℕ) (hN : 0 < N) :
    -((c : ℝ) / N) * Real.logb 2 ((c : ℝ) / N) =
      ((c : ℝ) * Real.logb 2 N - Real.logb 2 (c ^ c : ℕ)) / N := by
  by_cases hc : c = 0
  · simp [hc]
  · have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [Real.logb_div hcR hNR, Nat.cast_pow, Real.logb_pow]
    ring

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
theorem sum_entropy_formula {α : Type*}
    (s : Finset α) (c : α → ℕ) (N : ℕ) (hN : 0 < N) (hsum : ∑ i ∈ s, c i = N) :
    (∑ i ∈ s, -((c i : ℝ) / N) * Real.logb 2 ((c i : ℝ) / N)) =
      Real.logb 2 N - Real.logb 2 (∏ i ∈ s, c i ^ c i : ℕ) / N := by
  classical
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hp : ∀ i ∈ s, ((c i ^ c i : ℕ) : ℝ) ≠ 0 := by
    intro i _
    exact_mod_cast (count_power_pos (c i)).ne'
  have hlog : Real.logb 2 (∏ i ∈ s, c i ^ c i : ℕ) =
      ∑ i ∈ s, Real.logb 2 (c i ^ c i : ℕ) := by
    simpa only [Nat.cast_prod] using Real.logb_prod s (fun i => (c i ^ c i : ℕ)) hp
  have hsumR : (∑ i ∈ s, (c i : ℝ)) = N := by exact_mod_cast hsum
  simp_rw [negMulLog2_div _ _ hN]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumR, ← hlog]
  field_simp

private def count {n m : ℕ} (E : Fin m → Finset (Fin n)) (k : ℕ) : ℕ :=
  ((Fintype.piFinset E).filter (fun o => X E o = k)).card

private def countProduct {n m : ℕ} (E : Fin m → Finset (Fin n)) : ℕ :=
  ∏ k ∈ Finset.range (n + 1), count E k ^ count E k

private def witness : Fin 3 → Finset (Fin 3) := ![{0, 1}, {0, 1}, {0, 2}]

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem witness_counts : ∀ k : Fin 4, count witness k = (![0, 1, 5, 2] : Fin 4 → ℕ) k := by
  decide

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem witness_uniform : ∀ i, (witness i).card = 2 := by decide

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem witness_degrees : ∀ v : Fin 3, deg witness v = (![3, 2, 1] : Fin 3 → ℕ) v := by
  decide

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem all_counts_certificate : ∀ E : Fin 3 → Finset (Fin 3),
    (∀ i, (E i).card = 2) →
      (∑ k ∈ Finset.range 4, count E k) = 8 ∧ 12500 ≤ countProduct E := by
  decide

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem witness_product : countProduct witness = 12500 := by
  have h0 := witness_counts 0
  have h1 := witness_counts 1
  have h2 := witness_counts 2
  have h3 := witness_counts 3
  change count witness 0 = 0 at h0
  change count witness 1 = 1 at h1
  change count witness 2 = 5 at h2
  change count witness 3 = 2 at h3
  norm_num [countProduct, Finset.prod_range_succ, h0, h1, h2, h3]


set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem countProduct_pos {n m : ℕ} (E : Fin m → Finset (Fin n)) :
    0 < countProduct E := by
  exact Finset.prod_pos (fun k _ => count_power_pos (count E k))

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem entropyX_product_formula {n m : ℕ} (r : ℕ) (E : Fin m → Finset (Fin n))
    (hN : 0 < r ^ m) (hsum : ∑ k ∈ Finset.range (n + 1), count E k = r ^ m) :
    entropyX r E = Real.logb 2 (r ^ m : ℕ) -
      Real.logb 2 (countProduct E : ℕ) / (r : ℝ) ^ m := by
  simpa only [entropyX, orientations_eq, count, countProduct, Nat.cast_pow] using
    sum_entropy_formula (Finset.range (n + 1)) (count E) (r ^ m) hN hsum

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem entropyX_le_of_product_le {n m : ℕ} (r : ℕ)
    (E F : Fin m → Finset (Fin n)) (hN : 0 < r ^ m)
    (hE : ∑ k ∈ Finset.range (n + 1), count E k = r ^ m)
    (hF : ∑ k ∈ Finset.range (n + 1), count F k = r ^ m)
    (hprod : countProduct E ≤ countProduct F) : entropyX r F ≤ entropyX r E := by
  rw [entropyX_product_formula r E hN hE, entropyX_product_formula r F hN hF]
  have hp : (0 : ℝ) < countProduct E := by exact_mod_cast countProduct_pos E
  have ho : (countProduct E : ℝ) ≤ countProduct F := by exact_mod_cast hprod
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp ho
  have hd : (0 : ℝ) < (r : ℝ) ^ m := by exact_mod_cast hN
  exact sub_le_sub_left (div_le_div_of_nonneg_right hl hd.le) _

set_option maxHeartbeats 0 in
-- Finite certificates and their log normalisation are checked by the kernel.
set_option maxRecDepth 8192 in
private theorem witness_maximises : ∀ F : Fin 3 → Finset (Fin 3),
    (∀ i, (F i).card = 2) → entropyX 2 F ≤ entropyX 2 witness := by
  intro F hF
  have hc := all_counts_certificate F hF
  apply entropyX_le_of_product_le 2 witness F (by decide)
  · exact (all_counts_certificate witness witness_uniform).1
  · exact hc.1
  · rw [witness_product]
    exact hc.2

theorem result : ¬ claim := by
  intro h
  have hb := h 3 3 2 (by decide) (by decide) (by decide)
    witness witness_uniform witness_maximises 0 2
  have hd0 := witness_degrees 0
  have hd2 := witness_degrees 2
  change deg witness 0 = 3 at hd0
  change deg witness 2 = 1 at hd2
  rw [hd0, hd2] at hb
  norm_num at hb

end D5.S0.Certificates.Hypergraphs.OrientationEntropyBalance
