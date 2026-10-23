/- GID: D5/S3/Entropy/DeletionChannelEntropyOrdering
   generality: I
   mirror-B: D5/B/S3/Entropy/DeletionChannelEntropyOrdering
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Entropy/DeletionChannelEntropyOrdering.claim; result=D5/S3/Entropy/DeletionChannelEntropyOrdering.result; claim=D5/S3/Entropy/DeletionChannelEntropyOrdering.claim
   digest: Positional autocorrelation does not order finite deletion-channel entropy. -/

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19498; embeddings_eq_count. -/

/-
proof_shape: embeddings=not-applicable (definition).
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#16040; Refuted).
Direct frozen dependencies: D5/S3/Entropy/MaxEntropy.shannonEntropy
  (statement_id: sha256:0b9b0250c925b41ffab4b8ab0b198871ccb0bb46dd401760ec0158c98ad42e87),
  D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount
  (statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c),
  D5/S0/Tower/DBonacci/TerminalSampling.blockEquiv
  (statement_id: sha256:0062446dbffebbf0d0a7edf93ff244cbc407ade92f7ee2aa538b06f5b8c5f1e0).
Direct frozen counting theorem: D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.scatteredCount_eq_count_sublistsLen
  (statement_id: sha256:1ef019efa27fa73883b2c484815d0895ff1d4e12bfaa8beb7e837b90c59ca23f).
Direct frozen entropy theorem: D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.sum_entropy_formula.
The source total mass is the frozen CommonPrediction.Capacity.pref binomial factor.
Binary-word enumeration uses the inverse of the existing blockEquiv.
The embeddings definition counts index subsequences; proofs use the
  existing scatteredCount through embeddings_eq_count and its frozen fixed-length count theorem.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
All private theorems have proof_shape: bind-only and escape_witness: none.
Consumers (prerequisite -> consumer): embeddings_eq_count -> weights_u, weights_v; kappa_u, kappa_v -> result;
  mu_eight_five -> entropy_from_hist; weights_u -> hist_u; weights_v -> hist_v;
  hist_u, hist_v -> entropy_order; sum_weights -> sum_histogram;
  sum_histogram -> entropy_from_hist;
  entropy_from_hist, product_lt -> entropy_order; entropy_order -> result.
-/

import Batteries.Tactic.OpenPrivate
import D5.S0.Certificates.Hypergraphs.OrientationEntropyBalance
import D5.S3.Entropy.MaxEntropy
import D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore
import D5.S1.Words.Complexity.VivionBinomialConverseFails
import D5.S0.Tower.DBonacci.TerminalSampling
import D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts

set_option Elab.async false

namespace D5.S3.Entropy.DeletionChannelEntropyOrdering

open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore (scatteredCount_eq_count_sublistsLen)

def embeddings {m n : ℕ} (x : Fin m → Bool) (y : Fin n → Bool) : ℕ := ((List.ofFn y).sublists.filter (fun s => s = List.ofFn x)).length

noncomputable def entropyBits (n : ℕ) {m : ℕ} (x : Fin m → Bool) : ℝ :=
  D5.S3.Entropy.MaxEntropy.shannonEntropy
    (fun y : Fin n → Bool => (embeddings x y : ℝ) / D5.S3.Arith.FibonacciAtomic.CommonPrediction.Capacity.pref n m) / Real.log 2

def kappa2 {m : ℕ} (x : Fin m → Bool) : ℕ :=
  ∑ r : Fin m, ∑ s : Fin m, if x r = x s then
    Nat.choose (r + s) r * Nat.choose (2 * m - 2 - r - s) (m - 1 - r) else 0

def claim : Prop := ∀ m n : ℕ, 1 ≤ m → m < n → ∀ u v : Fin m → Bool,
  kappa2 v < kappa2 u → entropyBits n u ≤ entropyBits n v

theorem embeddings_eq_count {m n : ℕ} (x : Fin m → Bool) (y : Fin n → Bool) :
    embeddings x y =
      scatteredCount (List.ofFn x) (List.ofFn y) := by
  unfold embeddings
  symm
  let xs := List.ofFn x
  let ys := List.ofFn y
  change scatteredCount xs ys = (ys.sublists.filter fun s => s = xs).length
  rw [scatteredCount_eq_count_sublistsLen]
  have hzero (k : ℕ) (hk : k ≠ xs.length) : (ys.sublistsLen k).count xs = 0 := by
    apply List.count_eq_zero.mpr
    intro hmem
    exact hk (List.length_of_sublistsLen hmem).symm
  have hp := (List.range_bind_sublistsLen_perm ys).trans (List.sublists_perm_sublists' ys).symm
  have hc := hp.count_eq xs
  rw [List.count_flatMap] at hc
  have hsum : ((List.range (ys.length + 1)).map (fun k => (ys.sublistsLen k).count xs)).sum = (ys.sublistsLen xs.length).count xs := by
    rw [← List.sum_toFinset _ List.nodup_range]
    simp only [List.toFinset_range]
    have hterm (k : ℕ) : (ys.sublistsLen k).count xs = if k = xs.length then (ys.sublistsLen xs.length).count xs else 0 := by
      split_ifs with h
      · subst k; rfl
      · exact hzero k h
    have hexp : (∑ k ∈ Finset.range (ys.length + 1), (ys.sublistsLen k).count xs) =
        ∑ k ∈ Finset.range (ys.length + 1), if k = xs.length then (ys.sublistsLen xs.length).count xs else 0 := by
      exact Finset.sum_congr rfl (fun k _ => hterm k)
    rw [hexp]
    by_cases hlen : xs.length < ys.length + 1
    · simp [hlen]
    · have hlt : ys.length < xs.length := by omega
      simp [List.sublistsLen_of_length_lt hlt]
  have hcount : (ys.sublistsLen xs.length).count xs = ys.sublists.count xs := by
    exact hsum.symm.trans hc
  rw [hcount, List.count_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro z hz
  exact Bool.beq_eq_decide_eq z xs

private def u : Fin 5 → Bool := ![false, false, true, false, false]
private def v : Fin 5 → Bool := ![false, true, true, true, false]

private theorem kappa_u : kappa2 u = 450 := by decide +kernel
private theorem kappa_v : kappa2 v = 410 := by decide +kernel
private theorem mu_eight_five : D5.S3.Arith.FibonacciAtomic.CommonPrediction.Capacity.pref 8 5 = 448 := by decide +kernel

private def weights (x : Fin 5 → Bool) : List ℕ :=
  List.ofFn fun i : Fin (2 ^ 8) => embeddings x ((D5.S0.Tower.DBonacci.TerminalSampling.blockEquiv 8).symm i)

private def histU : List (ℕ × ℕ) :=
  [(0,163),(1,20),(2,10),(3,24),(4,1),(6,20),(9,8),(10,2),(12,3),(15,2),(18,3)]
private def histV : List (ℕ × ℕ) :=
  [(0,163),(1,20),(2,20),(3,8),(4,12),(5,6),(6,5),(8,6),(9,2),(10,4),
   (11,2),(12,2),(14,2),(16,1),(20,3)]
private def expandHistogram (h : List (ℕ × ℕ)) : List ℕ :=
  h.flatMap fun p => List.replicate p.2 p.1

set_option maxRecDepth 4096
set_option maxHeartbeats 0
private def tableU : Fin (2 ^ 8) → ℕ :=
  ![0,0,0,0,10,0,0,0,18,6,6,0,12,0,0,0,
    18,9,9,3,15,3,3,0,18,6,6,0,9,0,0,0,
    10,6,6,3,12,3,3,1,15,6,6,1,9,1,1,0,
    12,6,6,2,9,2,2,0,9,3,3,0,4,0,0,0,
    0,0,0,0,6,0,0,0,9,3,3,0,6,0,0,0,
    6,3,3,1,6,1,1,0,6,2,2,0,3,0,0,0,
    0,0,0,0,3,0,0,0,3,1,1,0,2,0,0,0,
    0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,6,0,0,0,9,3,3,0,6,0,0,0,
    6,3,3,1,6,1,1,0,6,2,2,0,3,0,0,0,
    0,0,0,0,3,0,0,0,3,1,1,0,2,0,0,0,
    0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,3,0,0,0,3,1,1,0,2,0,0,0,
    0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

private theorem weights_u : weights u = List.ofFn tableU := by
  unfold weights
  apply congrArg List.ofFn
  funext i
  rw [embeddings_eq_count]
  fin_cases i <;> decide +kernel

private theorem hist_u : List.insertionSort (· ≤ ·) (weights u) = expandHistogram histU := by
  rw [weights_u]
  decide +kernel

private def tableV : Fin (2 ^ 8) → ℕ :=
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,
    0,0,0,0,0,0,3,0,0,0,3,0,6,3,12,0,
    0,0,0,0,0,0,2,0,0,0,2,0,4,2,9,0,
    0,0,2,0,4,2,8,0,6,4,10,2,16,8,20,0,
    0,0,0,0,0,0,1,0,0,0,1,0,2,1,6,0,
    0,0,1,0,2,1,5,0,3,2,6,1,10,5,14,0,
    0,0,1,0,2,1,4,0,3,2,5,1,8,4,11,0,
    4,3,6,2,9,5,11,1,12,8,14,4,20,10,20,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,
    0,0,0,0,0,0,2,0,0,0,2,0,4,2,8,0,
    0,0,0,0,0,0,1,0,0,0,1,0,2,1,5,0,
    0,0,1,0,2,1,4,0,3,2,5,1,8,4,10,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,
    0,0,0,0,0,0,1,0,0,0,1,0,2,1,4,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

private theorem weights_v : weights v = List.ofFn tableV := by
  unfold weights
  apply congrArg List.ofFn
  funext i
  rw [embeddings_eq_count]
  fin_cases i <;> decide +kernel

private theorem hist_v : List.insertionSort (· ≤ ·) (weights v) = expandHistogram histV := by
  rw [weights_v]
  decide +kernel

private theorem sum_weights (x : Fin 5 → Bool) (f : ℕ → ℝ) :
    (∑ y : Fin 8 → Bool, f (embeddings x y)) = ((weights x).map f).sum := by
  rw [weights, List.map_ofFn, List.sum_ofFn]
  exact (Fintype.sum_equiv (D5.S0.Tower.DBonacci.TerminalSampling.blockEquiv 8).symm _ _ fun _ => rfl).symm

private theorem sum_histogram (x : Fin 5 → Bool) (h : List (ℕ × ℕ))
    (hc : List.insertionSort (· ≤ ·) (weights x) = expandHistogram h) (f : ℕ → ℝ) :
    (∑ y : Fin 8 → Bool, f (embeddings x y)) =
      ((expandHistogram h).map f).sum := by
  rw [sum_weights]
  have hp := (List.perm_insertionSort (· ≤ ·) (weights x)).symm
  exact (hp.map f).sum_eq.trans (congrArg (fun ws : List ℕ => (ws.map f).sum) hc)

private def weightProduct (ws : List ℕ) : ℕ :=
  (ws.map fun w => w ^ w).prod

private theorem entropy_from_hist (x : Fin 5 → Bool) (h : List (ℕ × ℕ))
    (hc : List.insertionSort (· ≤ ·) (weights x) = expandHistogram h)
    (hm : (expandHistogram h).sum = 448) :
    entropyBits 8 x =
      (Real.log 448 - Real.log (weightProduct (expandHistogram h) : ℝ) / 448) / Real.log 2 := by
  let ws := expandHistogram h
  have hsum : (∑ i : Fin ws.length, ws[i.val]) = 448 := by
    simpa only [Fin.sum_univ_getElem] using hm
  have owner := D5.S0.Certificates.Hypergraphs.OrientationEntropyBalance.sum_entropy_formula
    Finset.univ (fun i : Fin ws.length => ws[i.val]) 448 (by decide) hsum
  simp only [Real.logb, ← mul_div_assoc, Nat.cast_ofNat] at owner
  rw [← Finset.sum_div] at owner
  rw [Fin.sum_univ_fun_getElem ws (fun w : ℕ => -((w : ℝ) / 448) * Real.log ((w : ℝ) / 448)),
    Fin.prod_univ_fun_getElem ws (fun w : ℕ => w ^ w)] at owner
  unfold entropyBits D5.S3.Entropy.MaxEntropy.shannonEntropy
  rw [mu_eight_five]
  change (∑ y : Fin 8 → Bool, Real.negMulLog ((embeddings x y : ℝ) / 448)) / Real.log 2 = _
  rw [sum_histogram x h hc (fun w : ℕ => Real.negMulLog ((w : ℝ) / 448))]
  change (ws.map (fun w : ℕ => Real.negMulLog ((w : ℝ) / 448))).sum / Real.log 2 = _
  simp only [Real.negMulLog] at *
  rw [owner]
  dsimp only [weightProduct]
  ring

private theorem product_lt : weightProduct (expandHistogram histU) <
    weightProduct (expandHistogram histV) := by decide +kernel

private theorem entropy_order : entropyBits 8 v < entropyBits 8 u := by
  have hp : (0 : ℝ) < weightProduct (expandHistogram histU) := by
    exact_mod_cast (show 0 < weightProduct (expandHistogram histU) by decide +kernel)
  have hlt : (weightProduct (expandHistogram histU) : ℝ) <
      weightProduct (expandHistogram histV) := by exact_mod_cast product_lt
  have hlog := Real.log_lt_log hp hlt
  rw [entropy_from_hist v histV hist_v (by decide +kernel),
      entropy_from_hist u histU hist_u (by decide +kernel)]
  apply div_lt_div_of_pos_right _ (Real.log_pos (by norm_num))
  exact sub_lt_sub_left (div_lt_div_of_pos_right hlog (by norm_num)) _

theorem result : ¬ claim := by
  intro h
  have hn := h 5 8 (by decide +kernel) (by decide +kernel) u v (by rw [kappa_v, kappa_u]; decide +kernel)
  exact (not_le_of_gt entropy_order) hn

end D5.S3.Entropy.DeletionChannelEntropyOrdering
