/- GID: D5/S3/Entropy/TwoDeletionChannelEntropy
   generality: I
   mirror-B: D5/B/S3/Entropy/TwoDeletionChannelEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact binary run counts and entropy comparisons for two deletions. -/

/-
admission_basis: escape-witness
Module escape_witness: actual_deletion_run_score.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19498.
Frozen dependency identifiers refer to declarations at the pinned base:
F1: D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.alternatingBit; statement_id: sha256:cf75864c00a72d48d77507be601672dea7f3c33509b8c7ec9c231241206a8c1f.
F2: D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount; statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c.
F3: D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.scatteredCount_eq_count_sublistsLen; statement_id: sha256:1ef019efa27fa73883b2c484815d0895ff1d4e12bfaa8beb7e837b90c59ca23f.
F4: D5/S3/Entropy/DeletionChannelEntropyOrdering.embeddings_eq_count; statement_id: sha256:85d2596a56bc8a6e56b4ca3c21681231f374027a5753ff74a40e37f5d076ba42.
F5: D5/S3/Entropy/DeletionChannelEntropyOrdering.embeddings; statement_id: sha256:c64d6f10bcc70bdad02da8e570c09291631b1e8f893b20c8a0ab6d5a39123a19.
F6: D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount; statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c; generated dependency: D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount.eq_1; generated statement_id: sha256:607874708dedb4dcfc543f03f8a4e0696951869b05e14db52394fc154de855d9.
F7: D5/S1/Words/Complexity/VivionBinomialConverseFails.congr_simp; statement_id: sha256:08caa00f2d10a6074fe321122becd2a661a58047e87908bd0b2e539bd8628b72.
F8: D5/S3/Entropy/MaxEntropy.shannonEntropy; statement_id: sha256:0b9b0250c925b41ffab4b8ab0b198871ccb0bb46dd401760ec0158c98ad42e87.
F9: D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.sum_entropy_formula; statement_id: sha256:544899247b42a924a471c11f851b473f948b5efc3d1b0c0e9eb9a4d617fd11ad.
F10: D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.alternating_bit_succ; statement_id: sha256:6936ec95b02ee5eb5b16201a9e3c9c70a5035dc5763a91e1eb84fb2d55be9f66.
F11: D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount; statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c; generated dependency: D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount.eq_3; generated statement_id: sha256:eeb4ba1dc42c97107933499a696fff58308201b57cdaa0e2d6b01318dfe85988.
F12: D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount; statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c; generated dependency: D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount.eq_2; generated statement_id: sha256:e2e6166b577f67ecd6ee2c1e6d0c309ce958489e403db05cda04ca3d16fa58b1.
F13: D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.clipped; statement_id: sha256:b2ffdfc200a436c0a1a4cbc67a06eacf0e6d019ce38e49368431f82129c4c525.
F14: D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.normalized; statement_id: sha256:827ae10dc47bf8d9de81c4ebb7189aa91a1ee4d77236f049729357214a06c556.
F15: D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.entropyBits; statement_id: sha256:32499184aa9ce85e599f79542c1b612b829a4a39286c40a1deb71b402c059563.
F16: D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.entropyBits; statement_id: sha256:32499184aa9ce85e599f79542c1b612b829a4a39286c40a1deb71b402c059563; generated dependency: D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.entropyBits._proof_1; generated statement_id: sha256:3b98b82db9afbc94853fb7cc09426ad8974cd42c124d4d7aaa0cb9873aa1914e.
F17: D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts.pref; statement_id: sha256:c98cdd02f62521d250fd89c2807d2fefd0bd5e1886d94181a033c22bbceb0e22.
F18: D5/S3/Entropy/DeletionChannelEntropyOrdering.entropyBits; statement_id: sha256:6288ba2b70725aea3cb6d03f4f17559bbac5b631d4c6f62336d1f25eec365c7a.
F19: D5/S3/Entropy/DeletionChannelEntropyOrdering.entropyBits; statement_id: sha256:6288ba2b70725aea3cb6d03f4f17559bbac5b631d4c6f62336d1f25eec365c7a; generated dependency: D5.S3.Entropy.DeletionChannelEntropyOrdering.entropyBits._proof_1; generated statement_id: sha256:c13e5c082f95ba170468e40193bc81dd8b80eadfc4fb1396bf52ac7b3c9cccaa.
altDeletionPhi: proof_shape: bind-only (definition); frozen: F1,F2; escape_witness: none; consumer: altDeletionPhi_one.
f_four: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: altDeletionPhi_step.
twoWordPhi: proof_shape: bind-only (definition); frozen: F2; escape_witness: none; consumer: deletion_phi_eq_twoWordPhi.
sum_binary_functions_succ: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: deletion_total_list.
sum_function_counts: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: insertion_phi_deck.
collisionBlocks_phi: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: actual_run_insertion_lower.
embeddings_sublistsLen: proof_shape: bind-only; frozen: F3,F4,F2,F5; escape_witness: none; consumer: insertion_phi_deck.
sum_count_patterns: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: insertion_total.
empty_embeddings: proof_shape: bind-only; frozen: F6,F7,F4,F2,F5; escape_witness: none; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.insertion_two_zero.
phi: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: deletion_entropy_formula.
entropy_eq_log_weightProduct: proof_shape: bind-only; frozen: F8,F9; escape_witness: none; consumer: entropy_eq_log_sub_phi.
f_product_delta: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: sum_f_product_delta.
coreTerm: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: simpleDeletionScore_long.
bridgeSum: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: simpleDeletionScore.
bridgeRest: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: bridgeSum_long.
ofFn_complement_alternating: proof_shape: bind-only; frozen: F10,F1; escape_witness: none; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.zero_defect_word_alternating.
alternating_embedding_count: proof_shape: content; frozen: F1,F2,F3,F11,F10,F6,F7,F4,F5; escape_witness: D5.S3.Entropy.AlternatingTwoDeletionCounts.count_alt_two; consumer: alternating_insertion_phi.
other_alternating_embedding_le_one: proof_shape: content; frozen: F1,F2,F3,F11,F10,F6,F7,F4,F5; escape_witness: D5.S3.Entropy.AlternatingTwoDeletionCounts.count_alt_two; consumer: alternating_insertion_phi.
deckPhi: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: deckPhi_on_superset.
altDeletionPhi_step: proof_shape: content; frozen: F11,F10,F1,F2,F7,F3,F6; escape_witness: D5.S3.Entropy.AlternatingTwoDeletionCounts.count_alt_two; consumer: altDeletionPhi_closed.
altDeletionPhi_one: proof_shape: bind-only; frozen: F11,F1,F10,F7,F2; escape_witness: none; consumer: altDeletionPhi_closed.
deletion_total_list: proof_shape: content; frozen: F11,F12,F6,F7,F2; escape_witness: D5.S3.Entropy.TwoDeletionChannelEntropy.deletion_total_list; consumer: deletion_total.
twoWordPhi_cons: proof_shape: bind-only; frozen: F2; escape_witness: none; consumer: twoWordPhi_run_step.
insertion_phi_deck: proof_shape: bind-only; frozen: F3,F4,F2,F5; escape_witness: none; consumer: insertion_phi_eq_deckPhi.
deckPhi_perm: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: actual_run_insertion_lower.
RunDeletionCountingLowerBound: proof_shape: bind-only (definition); frozen: F5; escape_witness: none; consumer: actual_run_deletion_lower.
twoWordPhi_nil: proof_shape: bind-only; frozen: F6,F7,F2; escape_witness: none; consumer: twoWordPhi_runs.
deletion_phi_eq_twoWordPhi: proof_shape: bind-only; frozen: F4,F2,F5; escape_witness: none; consumer: actual_deletion_run_score.
alternating_insertion_phi: proof_shape: content; frozen: F1,F2,F3,F11,F10,F6,F7,F4,F5; escape_witness: D5.S3.Entropy.AlternatingTwoDeletionCounts.count_alt_two; consumer: alternating_insertion_closed_form.
insertion_total: proof_shape: bind-only; frozen: F3,F4,F2,F5; escape_witness: none; consumer: insertion_entropy_formula.
log_weightProduct_eq_phi: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: insertion_entropy_product_formula.
sum_f_product_delta: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: twoWordPhi_run_step.
coreSum: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: simpleDeletionScore.
bridgeWeightsAux_decomp: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: bridgeSum_long.
bridgeSum_nil: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: simpleDeletionScore_nil.
coreTerm_one: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: simpleDeletionScore_long.
coreTerm_long: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: coreSum_longRuns.
coreTerm_shift: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: coreSum_shift.
deckPhi_on_superset: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: deckPhi_append_lower.
deckPhi_replicate: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: homogeneous_block_lower.
altDeletionPhi_closed: proof_shape: content; frozen: F11,F10,F1,F2,F7,F3,F6; escape_witness: D5.S3.Entropy.AlternatingTwoDeletionCounts.count_alt_two; consumer: alternating_deletion_phi.
deletion_total: proof_shape: content; frozen: F11,F12,F6,F7,F2,F4,F5; escape_witness: D5.S3.Entropy.TwoDeletionChannelEntropy.deletion_total; consumer: deletion_total_two.
insertion_phi_eq_deckPhi: proof_shape: bind-only; frozen: F3,F4,F2,F5; escape_witness: none; consumer: actual_run_insertion_lower.
entropy_eq_log_sub_phi: proof_shape: bind-only; frozen: F8,F9; escape_witness: none; consumer: deletion_entropy_formula.
twoWordPhi_run_step: proof_shape: content; frozen: F2,F7,F3,F11,F6; escape_witness: D5.S3.Entropy.BinaryRunSupersequenceCounts.jointWordSum_runs; consumer: twoWordPhi_runs.
simpleDeletionScore: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: simpleDeletionScore_long.
bridgeSum_one: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: simpleDeletionScore_long.
bridgeSum_long: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: simpleDeletionScore_long.
bridgeSum_head: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: simpleDeletionScore_one.
coreSum_cons: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: simpleDeletionScore_long.
coreSum_shift: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: simpleDeletionScore_long.
coreSum_longRuns: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: simpleDeletionScore_eq.
deckPhi_append_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: homogeneous_block_lower.
alternating_deletion_phi: proof_shape: content; frozen: F11,F10,F1,F2,F7,F3,F6,F4,F5; escape_witness: D5.S3.Entropy.AlternatingTwoDeletionCounts.count_alt_two; consumer: alternating_deletion_closed_form.
deletion_total_two: proof_shape: content; frozen: F11,F12,F6,F7,F2,F4,F5; escape_witness: D5.S3.Entropy.TwoDeletionChannelEntropy.deletion_total_two; consumer: deletion_entropy_formula.
normalized_insertion_entropy: proof_shape: bind-only; frozen: F13,F8,F14,F5,F15; escape_witness: none; consumer: insertion_entropy_formula.
insertion_entropy_formula: proof_shape: bind-only; frozen: F8,F9,F3,F4,F2,F5,F13,F16,F14,F15; escape_witness: none; consumer: insertion_entropy_product_formula.
simpleDeletionScore_eq: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: actual_deletion_run_score.
simpleDeletionScore_nil: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: twoWordPhi_runs.
simpleDeletionScore_one: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: twoWordPhi_runs.
simpleDeletionScore_long: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: twoWordPhi_runs.
homogeneous_block_lower: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: actual_run_insertion_lower.
twoWordPhi_runs: proof_shape: content; frozen: F2,F7,F3,F11,F6; escape_witness: D5.S3.Entropy.BinaryRunSupersequenceCounts.jointWordSum_runs; consumer: actual_deletion_run_score.
alternating_insertion_closed_form: proof_shape: content; frozen: F1,F2,F3,F11,F10,F6,F7,F4,F5,F8,F9,F13,F16,F14,F15; escape_witness: D5.S3.Entropy.AlternatingTwoDeletionCounts.count_alt_two; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.claim_of_run_deletion_lower.
actual_run_insertion_lower: proof_shape: content; frozen: F3,F4,F2,F5; escape_witness: D5.S1.Words.TwoDeletionRunDecks.twoRunBlocks_linear; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.large_insertion_strict.
normalized_deletion_entropy: proof_shape: bind-only; frozen: F11,F12,F6,F7,F2,F4,F5,F17,F18,F8; escape_witness: none; consumer: deletion_entropy_formula.
deletion_entropy_formula: proof_shape: content; frozen: F11,F12,F6,F7,F2,F4,F5,F8,F9,F19,F17,F18; escape_witness: D5.S3.Entropy.TwoDeletionChannelEntropy.deletion_entropy_formula; consumer: alternating_deletion_closed_form.
insertion_entropy_product_formula: proof_shape: bind-only; frozen: F8,F9,F3,F4,F2,F5,F13,F16,F14,F15; escape_witness: none; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.insertion_entropy_le_iff.
alternating_deletion_closed_form: proof_shape: content; frozen: F11,F10,F1,F2,F7,F3,F6,F4,F5,F12,F8,F9,F19,F17,F18; escape_witness: D5.S3.Entropy.AlternatingTwoDeletionCounts.count_alt_two; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.claim_of_run_deletion_lower.
actual_deletion_run_score: proof_shape: content; frozen: F2,F7,F3,F11,F6,F4,F5; escape_witness: actual_deletion_run_score; consumer: actual_run_deletion_lower.
actual_run_deletion_lower: proof_shape: content; frozen: F2,F7,F3,F11,F6,F4,F5; escape_witness: D5.S3.Entropy.TwoDeletionChannelEntropy.actual_deletion_run_score; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.result.
-/

import D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation
import D5.S3.Arith.FibonacciAtomic.Observer.CommonPredictionWordCounts
import D5.S3.Entropy.AlternatingTwoDeletionCounts
import D5.S3.Entropy.BinaryRunSupersequenceCounts
import D5.S1.Words.TwoDeletionRunDecks
import D5.S3.Entropy.TwoDeletionRunEntropyBounds
import D5.S3.Entropy.DeletionChannelEntropyOrdering
import D5.S3.Entropy.MaxEntropy
import D5.S1.Words.Complexity.VivionBinomialConverseFails
import D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore
import D5.S0.Certificates.Hypergraphs.OrientationEntropyBalance

set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace D5.S3.Entropy.TwoDeletionChannelEntropy

open D5.S1.Words.Complexity.VivionBinomialConverseFails (scatteredCount)
open D5.S1.Words.Complexity.ExactDecks.Growth.ExactDeckCore (scatteredCount_eq_count_sublistsLen)
open D5.S3.Entropy.DeletionChannelEntropyOrdering (embeddings)
open D5.S3.Entropy.DeletionChannelEntropyOrdering (embeddings_eq_count)
open D5.S3.Entropy.AlternatingTwoDeletionCounts
open D5.S3.Entropy.BinaryRunSupersequenceCounts
open D5.S1.Words.TwoDeletionRunDecks
open D5.S3.Entropy.TwoDeletionRunEntropyBounds

private noncomputable def altDeletionPhi (b : Bool) (m : ℕ) : ℝ :=
  ∑ y : Fin (m+2) → Bool,f (scatteredCount (altList b m) (List.ofFn y))

private lemma f_four : f 4=8 := by
  have h := f_mul 2 2
  norm_num [f_two] at h
  exact h

private noncomputable def twoWordPhi (w : List Bool) : ℝ :=
  wordSum (w.length+2) (fun x => f (scatteredCount w x))

private lemma sum_binary_functions_succ {n : ℕ} (f : (Fin (n+1) → Bool) → ℕ) :
    (∑ x, f x) = (∑ x : Fin n → Bool, f (Fin.cons false x)) +
      ∑ x : Fin n → Bool, f (Fin.cons true x) := by
  exact_mod_cast (sum_binary_real_succ (fun x => (f x : ℝ)) false)







private lemma sum_function_counts {m : ℕ} (l : List (List Bool))
    (hl : ∀ w ∈ l, w.length=m) (F : ℕ → ℝ) (hF : F 0=0) :
    (∑ x : Fin m → Bool, F (l.count (List.ofFn x))) =
      ((l.dedup).map (fun w => F (l.count w))).sum := by
  classical
  let s : Finset (List Bool) := Finset.univ.image (fun x : Fin m → Bool => List.ofFn x)
  have hinj : ∀ x ∈ (Finset.univ : Finset (Fin m → Bool)), ∀ y ∈ Finset.univ,
      List.ofFn x=List.ofFn y → x=y := by
    intro x _ y _ h
    exact List.ofFn_injective h
  have hs : (∑ x : Fin m → Bool, F (l.count (List.ofFn x))) =
      ∑ w ∈ s, F (l.count w) := by
    dsimp only [s]
    rw [Finset.sum_image hinj]
  have hsub : l.toFinset ⊆ s := by
    intro w hw
    have hlen := hl w (List.mem_toFinset.mp hw)
    have he : ∃ x : Fin m → Bool, List.ofFn x=w := by
      refine ⟨fun i => w[i.val]'(by omega), ?_⟩
      apply List.ext_getElem
      · simpa using hlen.symm
      · simp
    obtain ⟨x,hx⟩ := he
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,hx⟩
  have hsupport : (∑ w ∈ s, F (l.count w)) = ∑ w ∈ l.toFinset, F (l.count w) := by
    symm
    apply Finset.sum_subset hsub
    intro w _ hw
    have hn : w ∉ l := by simpa using hw
    rw [List.count_eq_zero.mpr hn,hF]
  rw [hs,hsupport]
  have hh := List.sum_toFinset (fun w => F (l.count w)) (List.nodup_dedup l)
  simpa using hh

private lemma collisionBlocks_phi (b : Bool) (rs : List ℕ) :
    ((collisionBlocks b rs).map (fun p => f p.2)).sum=runPhiInsertion rs := by
  have hs := congrArg (fun ns : List ℕ => (ns.map (fun n : ℕ => f n)).sum) (sameBlocks_weights b rs)
  have hn := congrArg (fun ns : List ℕ => (ns.map (fun n : ℕ => f n)).sum) (nonadjBlocks_weights b rs)
  have hc := congrArg (fun ns : List ℕ => (ns.map (fun n : ℕ => f n)).sum) (componentBlocks_weights b rs)
  simp only [List.map_map,Function.comp_def] at hs hn hc
  unfold collisionBlocks runPhiInsertion collisionWeights
  simp only [List.map_append,List.sum_append]
  rw [hs,hn,hc,same_run_phi_formula]

private lemma embeddings_sublistsLen {m n : ℕ} (x : Fin m → Bool) (y : Fin n → Bool) :
    embeddings x y = ((List.ofFn y).sublistsLen m).count (List.ofFn x) := by
  simpa only [embeddings_eq_count, scatteredCount_eq_count_sublistsLen, List.length_ofFn]

private lemma sum_count_patterns (m : ℕ) (l : List (List Bool))
    (hl : ∀ x ∈ l, x.length = m) :
    (∑ x : Fin m → Bool, l.count (List.ofFn x)) = l.length := by
  have h := sum_function_counts l hl (fun n => (n : ℝ)) (by norm_num)
  have hsum := List.sum_map_count_dedup_eq_length l
  have hreal : (∑ x : Fin m → Bool, (l.count (List.ofFn x) : ℝ)) = (l.length : ℝ) := by
    rw [h]
    simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def,
      List.count_eq_countP, beq_eq_decide] using
      congrArg (fun n : ℕ => (n : ℝ)) hsum
  exact_mod_cast hreal

lemma empty_embeddings {n : ℕ} (y : Fin n → Bool) : embeddings (fun i : Fin 0 => Fin.elim0 i) y = 1 := by
  simp [embeddings_eq_count, List.ofFn_zero, scatteredCount]

noncomputable def phi {ι : Type*} [Fintype ι] (c : ι → ℕ) : ℝ :=
  ∑ i, (c i : ℝ) * Real.logb 2 (c i)

private lemma entropy_eq_log_weightProduct {ι : Type*} [Fintype ι] (c : ι → ℕ)
    (N : ℕ) (hN : 0 < N) (hsum : ∑ i, c i = N) :
    D5.S3.Entropy.MaxEntropy.shannonEntropy (fun i => (c i : ℝ) / N) / Real.log 2 =
      Real.logb 2 N - Real.logb 2 ((∏ i, (c) i ^ (c) i : ℕ)) / N := by
  have h := D5.S0.Certificates.Hypergraphs.OrientationEntropyBalance.sum_entropy_formula
    Finset.univ c N hN (by simpa using hsum)
  unfold D5.S3.Entropy.MaxEntropy.shannonEntropy
  simp only [Real.negMulLog]
  simp only [Real.logb, ← mul_div_assoc] at h

  rw [← Finset.sum_div] at h
  exact h

private lemma f_product_delta (u a : ℕ) :
    f (a+u*a:ℕ)-f (u*a:ℕ)=
      (a:ℝ)*(f ((u:ℝ)+1)-f u)+f a := by
  rw [show a+u*a=(u+1)*a by ring]
  push_cast
  rw [f_mul,f_mul]
  ring

private noncomputable def coreTerm (m r : ℕ) : ℝ :=
  f ((r+2).choose 2)+(2*(m:ℝ)-r)*f ((r:ℝ)+1)+(if r=1 then 2 else 0)

private noncomputable def bridgeSum (rs : List ℕ) : ℝ :=
  ((bridgeWeightsAux 0 0 rs).map (fun r : ℕ => f r)).sum

private def bridgeRest : List ℕ → List ℕ
  | [] => []
  | r::rs => if r=1 then bridgeRest rs else bridgeWeightsAux r 0 rs

lemma ofFn_complement_alternating (n : ℕ) :
    List.ofFn (fun i => !(fun i : Fin n => decide (i.val % 2 = 1)) i)=altList true n := by
  rw [List.ofFn_comp',ofFn_alternating]
  exact (altList_not false n).symm

private lemma alternating_embedding_count (m : ℕ) :
    embeddings ((fun i : Fin m => decide (i.val % 2 = 1))) ((fun i : Fin (m+2) => decide (i.val % 2 = 1)))=m+1 := by
  rw [embeddings_eq_count,ofFn_alternating,ofFn_alternating]
  exact (count_alt_two m false).1

private lemma other_alternating_embedding_le_one {m : ℕ} (x : Fin m → Bool) (hx : x≠(fun i : Fin m => decide (i.val % 2 = 1))) :
    embeddings x ((fun i : Fin (m+2) => decide (i.val % 2 = 1))) ≤ 1 := by
  rw [embeddings_eq_count,ofFn_alternating]
  apply (count_alt_two m false).2 (List.ofFn x) (by simp)
  intro he
  apply hx
  apply List.ofFn_injective
  simpa only [ofFn_alternating] using he

private noncomputable def deckPhi {α : Type*} [DecidableEq α] (l : List α) : ℝ :=
  ∑ x ∈ l.toFinset,f (l.count x)

private lemma altDeletionPhi_step (m : ℕ) (hm : 1 ≤ m) (b : Bool) :
    altDeletionPhi b (m+1)=altDeletionPhi (!b) m+8*m+4+3*Real.logb 2 3+
      f ((m:ℝ)+2)-f ((m:ℝ)+1) := by
  have hj := sum_one_two_joint m hm b (fun a d => f (a+d:ℕ)-f d) (by intro d; simp)
  simp only [Finset.sum_sub_distrib] at hj
  have hs := sum_one_extra_alt (m+1) b (fun n : ℕ => f n) (by simpa using f_zero)
  unfold altDeletionPhi
  rw [sum_binary_real_succ _ b]
  simp only [List.ofFn_cons,count_alt_cons_same,count_alt_cons_opposite]
  norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,show 1+1=2 by rfl,
    show 2+1=3 by rfl,show 2+2=4 by rfl,f_two,f_one,f_four] at hj hs
  change _ = _+8*m+4+3*Real.logb 2 3+f ((m:ℝ)+2)-f ((m:ℝ)+1)
  have hf3 : f 3=3*Real.logb 2 3 := rfl
  rw [hf3] at hj
  rw [show (1:ℝ)+((m:ℝ)+1)=(m:ℝ)+2 by ring] at hj
  simp only [Nat.cast_add]
  linarith

private lemma altDeletionPhi_one (b : Bool) : altDeletionPhi b 1=6+3*Real.logb 2 3 := by
  unfold altDeletionPhi
  simp only [sum_binary_real_succ _ false]
  cases b <;> norm_num [List.ofFn_cons,altList_zero,altList_succ,scatteredCount,f_zero,f_one,f_two,f] <;> ring

private lemma deletion_total_list (n : ℕ) (p : List Bool) :
    (∑ y : Fin n → Bool, scatteredCount p (List.ofFn y)) = n.choose p.length * 2^(n-p.length) := by
  induction n generalizing p with
  | zero =>
    cases p with
    | nil => simp [scatteredCount]
    | cons a p => simp [scatteredCount]
  | succ n ih =>
    cases p with
    | nil => simp [scatteredCount]
    | cons a p =>
      rw [sum_binary_functions_succ]
      simp only [List.ofFn_cons, scatteredCount]
      cases a <;>
        simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, add_zero,
          Finset.sum_add_distrib, ih, List.length_cons]
      all_goals
        by_cases hp : p.length < n
        · have he : n - p.length = n - (p.length + 1) + 1 := by omega
          have he' : n + 1 - (p.length + 1) = n - p.length := by exact Nat.add_sub_add_right n 1 p.length
          rw [Nat.choose_succ_succ, he', he, pow_succ]
          ring
        · by_cases he : p.length = n
          · subst n
            simp
          · have hgt : n < p.length := by omega
            have hgt' : n < p.length+1 := by exact Nat.lt_add_right 1 hgt
            have hgt'' : n+1 < p.length+1 := by exact Nat.add_lt_add_right hgt 1
            simp [Nat.choose_eq_zero_of_lt hgt, Nat.choose_eq_zero_of_lt hgt',
              Nat.choose_eq_zero_of_lt hgt'']

private lemma twoWordPhi_cons (b : Bool) (w : List Bool) :
    twoWordPhi (b::w)=twoWordPhi w+oneWordSum (b::w) (fun a => f a)+
      jointWordSum (b::w) (fun a d => f (a+d:ℕ)-f d) := by
  unfold twoWordPhi oneWordSum jointWordSum
  rw [List.length_cons,wordSum_succ (w.length+2) b]
  have hn : b≠!b := by exact Bool.not_eq_not.mpr rfl
  simp only [List.tail_cons,scatteredCount,ite_true,if_neg hn,add_zero,List.length_cons]
  have he : wordSum (w.length+2) (fun q =>
      f (scatteredCount (b::w) q+scatteredCount w q:ℕ))=
      wordSum (w.length+2) (fun q => f (scatteredCount w q))+
      wordSum (w.length+2) (fun q =>
        f (scatteredCount (b::w) q+scatteredCount w q:ℕ)-f (scatteredCount w q)) := by
    rw [←wordSum_add]
    apply wordSum_congr
    intro q _
    ring
  rw [he]
  simp only [List.length_cons,show w.length+1+1=w.length+2 by omega]
  ring
open D5.S1.Words.Complexity.VivionBinomialConverseFails (scatteredCount)







private lemma insertion_phi_deck {m : ℕ} (y : Fin (m+2) → Bool) :
    phi (fun x : Fin m → Bool => embeddings x y) =
      (((((((List.ofFn y).sublistsLen ((List.ofFn y).length - 2))).dedup).map (fun x => (((List.ofFn y).sublistsLen ((List.ofFn y).length - 2))).count x))).map (fun n : ℕ => f n)).sum := by
  have hlen : (List.ofFn y).length-2=m := by simp
  have h := sum_function_counts ((List.ofFn y).sublistsLen m)
    (fun _ hx => List.length_of_sublistsLen hx) (fun n : ℕ => f n) (by simpa using f_zero)
  simp only [phi,embeddings_sublistsLen,f] at h ⊢
  rw [h]
  simp only [hlen,List.map_map]
  rfl

private lemma deckPhi_perm {α : Type*} [DecidableEq α] {l r : List α} (hp : l.Perm r) :
    deckPhi l=deckPhi r := by
  unfold deckPhi
  have he : l.toFinset=r.toFinset := by
    ext x
    simp only [List.mem_toFinset]
    exact hp.mem_iff
  rw [he]
  apply Finset.sum_congr rfl
  intro x _
  rw [hp.count_eq]

def RunDeletionCountingLowerBound : Prop :=
  ∀ (m : ℕ) (y : Fin m → Bool) (b : Bool) (rs : List ℕ),
    (∀ r∈rs,0<r) → List.ofFn y=runWord b rs →
      deletionRunScore rs ≤ phi (fun x : Fin (m+2) → Bool => embeddings y x)

private lemma twoWordPhi_nil : twoWordPhi []=0 := by
  simp [twoWordPhi,wordSum,scatteredCount,f_one]

private lemma deletion_phi_eq_twoWordPhi {m : ℕ} (y : Fin m → Bool) :
    phi (fun x : Fin (m+2) → Bool => embeddings y x)=twoWordPhi (List.ofFn y) := by
  unfold twoWordPhi
  rw [List.length_ofFn]
  simp only [phi,wordSum,embeddings_eq_count,f]

lemma alternating_insertion_phi (m : ℕ) :
    phi (fun x : Fin m → Bool => embeddings x ((fun i : Fin (m+2) => decide (i.val % 2 = 1)))) = f (m+1) := by
  classical
  unfold phi
  rw [Finset.sum_eq_single ((fun i : Fin m => decide (i.val % 2 = 1)))]
  · dsimp only
    rw [alternating_embedding_count]
    simp only [f,Nat.cast_add,Nat.cast_one]
  · intro x _ hx
    have h := other_alternating_embedding_le_one x hx
    have he : embeddings x ((fun i : Fin (m+2) => decide (i.val % 2 = 1)))=0 ∨ embeddings x ((fun i : Fin (m+2) => decide (i.val % 2 = 1)))=1 := by exact Nat.le_one_iff_eq_zero_or_eq_one.mp h
    rcases he with he | he <;> simp [he]
  · simp

private lemma insertion_total {m n : ℕ} (y : Fin n → Bool) :
    (∑ x : Fin m → Bool, embeddings x y) = n.choose m := by
  simp_rw [embeddings_sublistsLen]
  rw [sum_count_patterns m _ (fun _ hx => List.length_of_sublistsLen hx),
    List.length_sublistsLen, List.length_ofFn]

private lemma log_weightProduct_eq_phi {ι : Type*} [Fintype ι] (c : ι → ℕ) :
    Real.logb 2 ((∏ i, (c) i ^ (c) i : ℕ)) = phi c := by
  unfold phi
  rw [Nat.cast_prod, Real.logb_prod]
  · simp [Nat.cast_pow, Real.logb_pow]
  · intro i _
    have h : 0 < c i ^ c i := Nat.pow_self_pos
    exact_mod_cast h.ne'

private lemma sum_f_product_delta (rs : List ℕ) (u : ℕ) :
    (rs.map (fun t => f ((t+1)+u*(t+1):ℕ)-f (u*(t+1):ℕ))).sum=
      ((rs.sum:ℝ)+rs.length)*(f ((u:ℝ)+1)-f u)+
      (rs.map (fun t : ℕ => f ((t:ℝ)+1))).sum := by
  induction rs with
  | nil => simp
  | cons t rs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [f_product_delta,ih]
    simp only [List.length_cons]
    push_cast
    ring

private noncomputable def coreSum (m : ℕ) (rs : List ℕ) : ℝ :=
  (rs.map (coreTerm m)).sum

private lemma bridgeWeightsAux_decomp (rs : List ℕ) (prev singles : ℕ) :
    bridgeWeightsAux prev singles rs=(prev+singles+leadingWeight rs+1)::bridgeRest rs := by
  induction rs generalizing prev singles with
  | nil => simp [bridgeWeightsAux,leadingWeight,bridgeRest]
  | cons r rs ih =>
    by_cases hr : r=1
    · subst r
      simp only [bridgeWeightsAux,ite_true,leadingWeight,bridgeRest]
      rw [ih]
      congr 2
      omega
    · simp only [bridgeWeightsAux,hr,ite_false,leadingWeight,bridgeRest]
      congr 1
      omega

private lemma bridgeSum_nil : bridgeSum []=0 := by
  simp [bridgeSum,bridgeWeightsAux,f_one]

private lemma coreTerm_one (m : ℕ) : coreTerm m 1=f 3+4*m := by
  norm_num [coreTerm,f_two]
  ring

private lemma coreTerm_long (m r : ℕ) (hr : 2 ≤ r) : coreTerm m r=Hrun m r := by
  unfold coreTerm Hrun
  rw [if_neg (by omega : r≠1),Nat.cast_choose_two]
  push_cast
  simp only [add_zero]
  ring_nf

private lemma coreTerm_shift (m r : ℕ) : coreTerm (m+1) r=coreTerm m r+2*f ((r:ℝ)+1) := by
  unfold coreTerm
  push_cast
  ring

private lemma deckPhi_on_superset {α : Type*} [DecidableEq α] (l : List α) (s : Finset α)
    (hs : l.toFinset ⊆ s) : deckPhi l=∑ x ∈ s,f (l.count x) := by
  unfold deckPhi
  apply Finset.sum_subset hs
  intro a _ ha
  have hnot : a∉l := by simpa using ha
  rw [List.count_eq_zero.mpr hnot]
  simpa using f_zero

private lemma deckPhi_replicate {α : Type*} [DecidableEq α] (a : α) (n : ℕ) :
    deckPhi (List.replicate n a)=f n := by
  cases n with
  | zero => simp [deckPhi,f_zero]
  | succ n => simp [deckPhi,List.toFinset_replicate_of_ne_zero (by omega : n+1≠0),List.count_replicate]

private lemma altDeletionPhi_closed (m : ℕ) (hm : 1 ≤ m) (b : Bool) :
    altDeletionPhi b m=4*(m:ℝ)^2+3*m*Real.logb 2 3+f ((m:ℝ)+1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  induction k generalizing b with
  | zero =>
    rw [altDeletionPhi_one]
    norm_num [f_two]
    ring
  | succ k ih =>
    rw [altDeletionPhi_step (k+1) (by omega),ih (!b) (by omega)]
    push_cast
    ring

private lemma deletion_total {m n : ℕ} (x : Fin m → Bool) :
    (∑ y : Fin n → Bool, embeddings x y) = n.choose m * 2^(n-m) := by
  simp_rw [embeddings_eq_count]
  simpa only [List.length_ofFn] using deletion_total_list n (List.ofFn x)

private lemma insertion_phi_eq_deckPhi {m : ℕ} (y : Fin (m+2) → Bool) :
    phi (fun x : Fin m → Bool => embeddings x y)=deckPhi (((List.ofFn y).sublistsLen ((List.ofFn y).length - 2))) := by
  rw [insertion_phi_deck]
  unfold deckPhi
  simp only [List.map_map]
  have h := List.sum_toFinset (fun w => f ((((List.ofFn y).sublistsLen ((List.ofFn y).length - 2))).count w))
    (List.nodup_dedup (((List.ofFn y).sublistsLen ((List.ofFn y).length - 2))))
  simpa only [Function.comp_def,List.count_eq_countP,beq_eq_decide,List.toFinset_dedup] using h.symm

private lemma entropy_eq_log_sub_phi {ι : Type*} [Fintype ι] (c : ι → ℕ)
    (N : ℕ) (hN : 0 < N) (hsum : ∑ i, c i = N) :
    D5.S3.Entropy.MaxEntropy.shannonEntropy (fun i => (c i : ℝ) / N) / Real.log 2 =
      Real.logb 2 N - phi c / N := by
  simpa only [log_weightProduct_eq_phi] using entropy_eq_log_weightProduct c N hN hsum

private lemma twoWordPhi_run_step (b : Bool) (rs : List ℕ) (hp : ∀ t∈rs,0<t) (r : ℕ) :
    twoWordPhi (runWord b ((r+1)::rs))=
      twoWordPhi (List.replicate r b++runWord (!b) rs)+
      f ((r+3).choose 2)-f ((r+2).choose 2)+
      ((r:ℝ)+2+2*rs.sum)*f ((r:ℝ)+2)-
      ((r:ℝ)+1+2*rs.sum)*f ((r:ℝ)+1)+
      2*(rs.map (fun t : ℕ => f ((t:ℝ)+1))).sum+
      f ((r:ℝ)+2+leadingWeight rs)-f ((r:ℝ)+1+leadingWeight rs) := by
  have hpp : ∀ t∈(r+1)::rs,0<t := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · omega
    · exact hp t ht
  let F : ℕ → ℕ → ℝ := fun a d => f (a+d:ℕ)-f d
  have hF : ∀ d,F 0 d=0 := by intro d; simp [F]
  have hj := jointWordSum_runs b rs hp r F hF
  have ho := oneWordSum_runs b ((r+1)::rs) hpp (fun a : ℕ => f a) (by simpa using f_zero)
  have hy : runWord b ((r+1)::rs)=b::(List.replicate r b++runWord (!b) rs) := by simp [runWord,List.replicate_succ]
  rw [hy,twoWordPhi_cons,←hy,ho,hj]
  have hc : (r+2)+(r+2).choose 2=(r+3).choose 2 := by
    have hc := Nat.choose_succ_succ (r+2) 1
    simpa using hc.symm
  dsimp only [F]
  rw [hc,sum_f_product_delta rs (r+1)]
  simp only [List.map_cons,List.sum_cons,f_one,mul_zero,add_zero]
  push_cast
  simp only [f_one,mul_zero,zero_mul,add_zero,sub_zero]
  ring_nf

private noncomputable def simpleDeletionScore (rs : List ℕ) : ℝ := coreSum rs.sum rs+bridgeSum rs

private lemma bridgeSum_one (rs : List ℕ) :
    bridgeSum (1::rs)=f ((leadingWeight rs:ℝ)+2)+
      ((bridgeRest rs).map (fun r : ℕ => f r)).sum := by
  simp only [bridgeSum,bridgeWeightsAux,ite_true]
  rw [bridgeWeightsAux_decomp]
  simp only [List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_zero,Nat.cast_one,zero_add]
  congr 1
  congr 1
  ring

private lemma bridgeSum_long (rs : List ℕ) (r : ℕ) (hr : r≠1) :
    bridgeSum (r::rs)=f ((r:ℝ)+1)+f ((r:ℝ)+leadingWeight rs+1)+
      ((bridgeRest rs).map (fun r : ℕ => f r)).sum := by
  simp only [bridgeSum,bridgeWeightsAux,hr,ite_false]
  rw [bridgeWeightsAux_decomp]
  simp only [List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_zero,Nat.cast_one,add_zero]
  ring

private lemma bridgeSum_head (rs : List ℕ) :
    bridgeSum rs=f ((leadingWeight rs:ℝ)+1)+((bridgeRest rs).map (fun r : ℕ => f r)).sum := by
  rw [bridgeSum,bridgeWeightsAux_decomp]
  simp

private lemma coreSum_cons (m r : ℕ) (rs : List ℕ) :
    coreSum m (r::rs)=coreTerm m r+coreSum m rs := by
  rfl

private lemma coreSum_shift (m : ℕ) (rs : List ℕ) :
    coreSum (m+1) rs=coreSum m rs+2*(rs.map (fun r : ℕ => f ((r:ℝ)+1))).sum := by
  induction rs with
  | nil => simp [coreSum]
  | cons r rs ih =>
    simp only [coreSum,List.map_cons,List.sum_cons] at ih ⊢
    rw [coreTerm_shift,ih]
    ring

private lemma coreSum_longRuns (m : ℕ) (rs : List ℕ) (hp : ∀ r∈rs,0<r) :
    coreSum m rs=((rs.sum-(longRuns rs).sum:ℕ):ℝ)*(f 3+4*m)+
      ((longRuns rs).map (fun r : ℕ => Hrun (m:ℝ) (r:ℝ))).sum := by
  induction rs with
  | nil => simp [coreSum,longRuns]
  | cons r rs ih =>
    have hr := hp r (by simp)
    have ht : ∀ a∈rs,0<a := fun a ha => hp a (by simp [ha])
    have hs := (longRuns_bounds rs ht).2
    have hi := ih ht
    by_cases he : r=1
    · subst r
      simp only [coreSum,List.map_cons,List.sum_cons] at hi ⊢
      rw [coreTerm_one]
      simp only [longRuns,List.filter_cons,show ¬2 ≤ 1 by omega,decide_false,Bool.false_eq_true,ite_false]
      change _=(((1+rs.sum)-(longRuns rs).sum:ℕ):ℝ)*(f 3+4*m)+_
      rw [show 1+rs.sum-(longRuns rs).sum=1+(rs.sum-(longRuns rs).sum) by omega,Nat.cast_add,Nat.cast_one]
      simp only [longRuns] at hi
      rw [hi]
      simp only [longRuns]
      ring
    · have hr2 : 2 ≤ r := by omega
      simp only [coreSum,List.map_cons,List.sum_cons] at hi ⊢
      rw [coreTerm_long m r hr2]
      simp only [longRuns,List.filter_cons,hr2,decide_true,ite_true,List.map_cons,List.sum_cons]
      change _=(((r+rs.sum)-(r+(longRuns rs).sum):ℕ):ℝ)*(f 3+4*m)+_
      rw [show r+rs.sum-(r+(longRuns rs).sum)=rs.sum-(longRuns rs).sum by omega]
      simp only [longRuns] at hi
      rw [hi]
      simp only [longRuns]
      ring

private lemma deckPhi_append_lower {α : Type*} [DecidableEq α] (l r : List α) :
    deckPhi l+deckPhi r ≤ deckPhi (l++r) := by
  classical
  let s := (l++r).toFinset
  rw [deckPhi_on_superset l s (by intro a ha; simp_all [s]),
    deckPhi_on_superset r s (by intro a ha; simp_all [s])]
  unfold deckPhi
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  rw [List.count_append]
  exact f_add_super_nat _ _

lemma alternating_deletion_phi (m : ℕ) (hm : 1 ≤ m) :
    phi (fun x : Fin (m+2) → Bool => embeddings ((fun i : Fin m => decide (i.val % 2 = 1))) x)=
      4*(m:ℝ)^2+3*m*Real.logb 2 3+((m:ℝ)+1)*Real.logb 2 ((m:ℝ)+1) := by
  simpa only [altDeletionPhi,phi,embeddings_eq_count,ofFn_alternating,f] using altDeletionPhi_closed m hm false

private lemma deletion_total_two {m : ℕ} (x : Fin m → Bool) :
    (∑ y : Fin (m+2) → Bool, embeddings x y) = 4 * (m+2).choose 2 := by
  rw [deletion_total, Nat.add_sub_cancel_left]
  have hc : (m+2).choose m = (m+2).choose 2 := Nat.choose_symm_add
  rw [hc]
  ring

private lemma normalized_insertion_entropy {m : ℕ} (y : Fin (m+2) → Bool) :
    D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) y) / Real.log 2 =
      D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.entropyBits
        (D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.normalized
          (fun x : Fin m → Bool => (embeddings x y : ℝ))) := by
  apply congrArg
    (fun p : (Fin m → Bool) → ℝ =>
      D5.S3.Entropy.MaxEntropy.shannonEntropy p / Real.log 2)
  funext x
  simp [D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.normalized,
    D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.clipped]

lemma insertion_entropy_formula {m : ℕ} (y : Fin (m + 2) → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) y) / Real.log 2) = Real.logb 2 ((m + 2).choose m) -
      phi (fun x : Fin m → Bool => embeddings x y) / (m + 2).choose m := by
  have hpos : 0 < (m + 2).choose m := Nat.choose_pos (by omega)
  rw [normalized_insertion_entropy]
  unfold D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.entropyBits
  unfold D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.normalized
  have hclip : D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.clipped
      (fun x : Fin m → Bool => (embeddings x y : ℝ)) =
      (fun x : Fin m → Bool => (embeddings x y : ℝ)) :=
    funext (fun x => max_eq_left (Nat.cast_nonneg (embeddings x y)))
  rw [hclip]
  have htotal : (∑ x : Fin m → Bool, (embeddings x y : ℝ)) = (m + 2).choose m := by
    exact_mod_cast insertion_total (m := m) y
  rw [htotal]
  exact entropy_eq_log_sub_phi _ _ hpos (insertion_total y)

private lemma simpleDeletionScore_eq (rs : List ℕ) (hp : ∀ r∈rs,0<r) :
    simpleDeletionScore rs=deletionRunScore rs := by
  rw [simpleDeletionScore,coreSum_longRuns rs.sum rs hp]
  rfl

private lemma simpleDeletionScore_nil : simpleDeletionScore []=0 := by
  simp [simpleDeletionScore,coreSum,bridgeSum_nil]

private lemma simpleDeletionScore_one (rs : List ℕ) :
    simpleDeletionScore (1::rs)=simpleDeletionScore rs+f 3+4*((rs.sum:ℝ)+1)+
      2*(rs.map (fun r : ℕ => f ((r:ℝ)+1))).sum+
      f ((leadingWeight rs:ℝ)+2)-f ((leadingWeight rs:ℝ)+1) := by
  unfold simpleDeletionScore
  simp only [List.sum_cons,show 1+rs.sum=rs.sum+1 by omega]
  rw [coreSum_cons]
  rw [coreTerm_one,coreSum_shift,bridgeSum_one,bridgeSum_head rs]
  push_cast
  ring

private lemma simpleDeletionScore_long (rs : List ℕ) (r : ℕ) :
    simpleDeletionScore ((r+2)::rs)=simpleDeletionScore ((r+1)::rs)+
      f ((r+4).choose 2)-f ((r+3).choose 2)+
      ((r:ℝ)+3+2*rs.sum)*f ((r:ℝ)+3)-
      ((r:ℝ)+2+2*rs.sum)*f ((r:ℝ)+2)+
      2*(rs.map (fun t : ℕ => f ((t:ℝ)+1))).sum+
      f ((r:ℝ)+3+leadingWeight rs)-f ((r:ℝ)+2+leadingWeight rs) := by
  unfold simpleDeletionScore
  simp only [List.sum_cons]
  rw [show r+2+rs.sum=(r+1+rs.sum)+1 by omega]
  rw [coreSum_cons,coreSum_cons]
  rw [coreSum_shift,bridgeSum_long rs (r+2) (by omega)]
  by_cases hr : r=0
  · subst r
    rw [bridgeSum_one rs,coreTerm_one]
    norm_num [coreTerm,f_two]
    ring
  · rw [bridgeSum_long rs (r+1) (by omega)]
    simp only [coreTerm,if_neg (by omega : r+2≠1),if_neg (by omega : r+1≠1),add_zero,
      show r+2+2=r+4 by omega,show r+1+2=r+3 by omega,
      Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    ring_nf
open D5.S3.Entropy.DeletionChannelEntropyOrdering (embeddings)


private lemma homogeneous_block_lower {α : Type*} [DecidableEq α] (bs : List (α × ℕ)) :
    (bs.map (fun p => f p.2)).sum ≤ deckPhi (realizeBlocks bs) := by
  induction bs with
  | nil => simp [realizeBlocks,deckPhi]
  | cons p bs ih =>
    have h := deckPhi_append_lower (List.replicate p.2 p.1) (realizeBlocks bs)
    rw [deckPhi_replicate] at h
    simp only [List.map_cons,List.sum_cons,realizeBlocks,List.flatMap_cons] at ih ⊢
    simp only [realizeBlocks] at h
    linarith

private lemma twoWordPhi_runs (b : Bool) (rs : List ℕ) (hp : ∀ r∈rs,0<r) :
    twoWordPhi (runWord b rs)=simpleDeletionScore rs := by
  induction rs generalizing b with
  | nil => simp [runWord,twoWordPhi_nil,simpleDeletionScore_nil]
  | cons r rs ih =>
    have hr := hp r (by simp)
    have ht : ∀ a∈rs,0<a := fun a ha => hp a (by simp [ha])
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
    induction n with
    | zero =>
      rw [twoWordPhi_run_step b rs ht 0]
      simp only [List.replicate_zero,List.nil_append,Nat.cast_zero,zero_add]
      rw [ih (!b) ht,simpleDeletionScore_one]
      norm_num [f_one,f_two]
      ring
    | succ n ihn =>
      rw [twoWordPhi_run_step b rs ht (n+1)]
      have heq : twoWordPhi (List.replicate (n+1) b++runWord (!b) rs)=
          twoWordPhi (runWord b ((n+1)::rs)) := rfl
      have hip : ∀ r∈n.succ::rs,0<r := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · omega
        · exact ht r hr
      rw [heq,ihn hip (by omega),simpleDeletionScore_long rs n]
      simp only [Nat.succ_eq_add_one]
      push_cast
      ring_nf

lemma alternating_insertion_closed_form (m : ℕ) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin (m+2) => decide (i.val % 2 = 1)))) / Real.log 2) =
      Real.logb 2 ((m+2).choose 2) -
        ((m:ℝ)+1)*Real.logb 2 ((m:ℝ)+1)/(m+2).choose 2 := by
  rw [insertion_entropy_formula,alternating_insertion_phi]
  have hc : (m+2).choose m=(m+2).choose 2 := Nat.choose_symm_add
  rw [hc]
  rfl

lemma actual_run_insertion_lower {m : ℕ} (y : Fin (m+2) → Bool) (b : Bool) (rs : List ℕ)
    (hp : ∀ r∈rs,0<r) (hw : List.ofFn y=runWord b rs) :
    runPhiInsertion rs ≤ phi (fun x : Fin m → Bool => embeddings x y) := by
  have hsum : rs.sum=m+2 := by
    have h := congrArg List.length hw
    simpa only [List.length_ofFn,runWord_length] using h.symm
  have h := homogeneous_block_lower (collisionBlocks b rs)
  rw [collisionBlocks_phi,deckPhi_perm (collisionBlocks_realize b rs hp)] at h
  rw [insertion_phi_eq_deckPhi,hw,twoDeletionDeck_eq_deletionDeck _ (by rw [runWord_length,hsum];omega)]
  exact h

private lemma normalized_deletion_entropy {m : ℕ} (y : Fin m → Bool) :
    D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) y) / Real.log 2 =
      D5.S3.Entropy.DeletionChannelEntropyOrdering.entropyBits (m+2) y := by
  unfold D5.S3.Entropy.DeletionChannelEntropyOrdering.entropyBits
  apply congrArg (fun p : (Fin (m+2) → Bool) → ℝ =>
    D5.S3.Entropy.MaxEntropy.shannonEntropy p / Real.log 2)
  funext x
  dsimp only
  unfold D5.S3.Arith.FibonacciAtomic.CommonPrediction.Capacity.pref
  rw [← Nat.cast_sum, deletion_total]

lemma deletion_entropy_formula {m : ℕ} (y : Fin m → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) y) / Real.log 2) = Real.logb 2 (4*(m+2).choose 2) -
      phi (fun x : Fin (m+2) → Bool => embeddings y x) / (4*(m+2).choose 2) := by
  have hpos : 0 < 4*(m+2).choose 2 := Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  rw [normalized_deletion_entropy]
  unfold D5.S3.Entropy.DeletionChannelEntropyOrdering.entropyBits
    D5.S3.Arith.FibonacciAtomic.CommonPrediction.Capacity.pref
  have hc : (m+2).choose m = (m+2).choose 2 := Nat.choose_symm_add
  have he : m+2-m=2 := by exact Nat.add_sub_self_left m 2
  rw [hc,he]
  norm_num only [Nat.reducePow]
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  have hmul : ((m+2).choose 2 : ℝ)*4 = 4*(m+2).choose 2 := mul_comm _ _
  simp_rw [hmul]
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    entropy_eq_log_sub_phi _ _ hpos (deletion_total_two y)

lemma insertion_entropy_product_formula {m : ℕ} (y : Fin (m + 2) → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) y) / Real.log 2) = Real.logb 2 ((m + 2).choose m) -
      Real.logb 2 ((∏ i, ((fun x : Fin m → Bool => embeddings x y)) i ^ ((fun x : Fin m → Bool => embeddings x y)) i : ℕ)) / (m + 2).choose m := by
  simpa only [log_weightProduct_eq_phi] using insertion_entropy_formula y

lemma alternating_deletion_closed_form (m : ℕ) (hm : 1 ≤ m) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) ((fun i : Fin m => decide (i.val % 2 = 1)))) / Real.log 2)=Real.logb 2 (4*(m+2).choose 2)-
      (4*(m:ℝ)^2+3*m*Real.logb 2 3+((m:ℝ)+1)*Real.logb 2 ((m:ℝ)+1))/(4*(m+2).choose 2) := by
  rw [deletion_entropy_formula,alternating_deletion_phi m hm]

private lemma actual_deletion_run_score {m : ℕ} (y : Fin m → Bool) (b : Bool) (rs : List ℕ)
    (hp : ∀ r∈rs,0<r) (hw : List.ofFn y=runWord b rs) :
    phi (fun x : Fin (m+2) → Bool => embeddings y x)=deletionRunScore rs := by
  rw [deletion_phi_eq_twoWordPhi,hw,twoWordPhi_runs b rs hp,simpleDeletionScore_eq rs hp]

lemma actual_run_deletion_lower : RunDeletionCountingLowerBound := by
  intro m y b rs hp hw
  exact (actual_deletion_run_score y b rs hp hw).ge

end D5.S3.Entropy.TwoDeletionChannelEntropy
