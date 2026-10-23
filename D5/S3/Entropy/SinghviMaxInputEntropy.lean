/- GID: D5/S3/Entropy/SinghviMaxInputEntropy
   generality: I
   mirror-B: D5/B/S3/Entropy/SinghviMaxInputEntropy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Binary two-deletion and two-insertion input entropy maximizers. -/

/-
admission_basis: open-problem-resolution (#19173; Proved)
Module escape_witness: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19498.
The claim states both normalized Shannon entropies explicitly. The proofs use the frozen entropy
owners through consumed normalization identities, with no duplicate entropy definition.
Frozen dependency identifiers refer to declarations at the pinned base:
F1: D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount; statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c.
F2: D5/S3/Entropy/DeletionChannelEntropyOrdering.embeddings_eq_count; statement_id: sha256:85d2596a56bc8a6e56b4ca3c21681231f374027a5753ff74a40e37f5d076ba42.
F3: D5/S3/Entropy/DeletionChannelEntropyOrdering.embeddings; statement_id: sha256:c64d6f10bcc70bdad02da8e570c09291631b1e8f893b20c8a0ab6d5a39123a19.
F4: D5/S3/Entropy/MaxEntropy.shannonEntropy; statement_id: sha256:0b9b0250c925b41ffab4b8ab0b198871ccb0bb46dd401760ec0158c98ad42e87.
F5: D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount; statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c; generated dependency: D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount.eq_3; generated statement_id: sha256:eeb4ba1dc42c97107933499a696fff58308201b57cdaa0e2d6b01318dfe85988.
F6: D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount; statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c; generated dependency: D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount.eq_2; generated statement_id: sha256:e2e6166b577f67ecd6ee2c1e6d0c309ce958489e403db05cda04ca3d16fa58b1.
F7: D5/S1/Words/Complexity/VivionBinomialConverseFails.scatteredCount; statement_id: sha256:7d49fdc08a9410b5f364dbb0fe82f8a640bfa36352cd87c2fd35ad3dbe45317c; generated dependency: D5.S1.Words.Complexity.VivionBinomialConverseFails.scatteredCount.eq_1; generated statement_id: sha256:607874708dedb4dcfc543f03f8a4e0696951869b05e14db52394fc154de855d9.
F8: D5/S1/Words/Complexity/VivionBinomialConverseFails.congr_simp; statement_id: sha256:08caa00f2d10a6074fe321122becd2a661a58047e87908bd0b2e539bd8628b72.
F9: D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance.sum_entropy_formula; statement_id: sha256:544899247b42a924a471c11f851b473f948b5efc3d1b0c0e9eb9a4d617fd11ad.
F10: D5/S3/Entropy/DeletionChannelEntropyOrdering.entropyBits; statement_id: sha256:6288ba2b70725aea3cb6d03f4f17559bbac5b631d4c6f62336d1f25eec365c7a; generated dependency: D5.S3.Entropy.DeletionChannelEntropyOrdering.entropyBits._proof_1; generated statement_id: sha256:c13e5c082f95ba170468e40193bc81dd8b80eadfc4fb1396bf52ac7b3c9cccaa.
F11: D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts.pref; statement_id: sha256:c98cdd02f62521d250fd89c2807d2fefd0bd5e1886d94181a033c22bbceb0e22.
F12: D5/S3/Entropy/DeletionChannelEntropyOrdering.entropyBits; statement_id: sha256:6288ba2b70725aea3cb6d03f4f17559bbac5b631d4c6f62336d1f25eec365c7a.
F13: D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.scatteredCount_eq_count_sublistsLen; statement_id: sha256:1ef019efa27fa73883b2c484815d0895ff1d4e12bfaa8beb7e837b90c59ca23f.
F14: D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.clipped; statement_id: sha256:b2ffdfc200a436c0a1a4cbc67a06eacf0e6d019ce38e49368431f82129c4c525.
F15: D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.entropyBits; statement_id: sha256:32499184aa9ce85e599f79542c1b612b829a4a39286c40a1deb71b402c059563; generated dependency: D5.S3.Combinatorics.Graph.DomiRankEntropyRefutation.entropyBits._proof_1; generated statement_id: sha256:3b98b82db9afbc94853fb7cc09426ad8974cd42c124d4d7aaa0cb9873aa1914e.
F16: D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.normalized; statement_id: sha256:827ae10dc47bf8d9de81c4ebb7189aa91a1ee4d77236f049729357214a06c556.
F17: D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation.entropyBits; statement_id: sha256:32499184aa9ce85e599f79542c1b612b829a4a39286c40a1deb71b402c059563.
F18: D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.alternating_bit_succ; statement_id: sha256:6936ec95b02ee5eb5b16201a9e3c9c70a5035dc5763a91e1eb84fb2d55be9f66.
F19: D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.alternatingBit; statement_id: sha256:cf75864c00a72d48d77507be601672dea7f3c33509b8c7ec9c231241206a8c1f.
F20: D5/S1/Words/AssociatedMersenne/RunTupleBijection.blockLengths; statement_id: sha256:e3f12e42fd17d7c9355dfc30f184ef2df14db948a5b37cb78dc1839a924c35d2.
F21: D5/S1/Words/AssociatedMersenne/RunTupleBijection.splitData_reconstruct; statement_id: sha256:b8e79b941f58db417f6353fe33118db83888c3ae649cb374665cbe6dbc922482.
F22: D5/S1/Words/AssociatedMersenne/RunTupleBijection.splitData_alternating; statement_id: sha256:432fa419951886376b3b92b39b0f0543ec8c283dcccd6552931cef4cbe3b6588.
F23: D5/S1/Words/AssociatedMersenne/RunTupleBijection.splitData; statement_id: sha256:6e3cc323324665c81638b2ff35725d45de98161ca95937f62867e81732fec0f0.
F24: D5/S1/Words/AssociatedMersenne/RunTupleBijection.splitData_positive; statement_id: sha256:5355f8c314d297cb883cdcfef81c4b1dc2947535c741326cb84ddb5ecdb601fa.
product_five: proof_shape: bind-only; frozen: F1,F2,F3; escape_witness: none; consumer: product_alt_five.
product_alt_five: proof_shape: bind-only; frozen: F1,F2,F3; escape_witness: none; consumer: insertion_five_max.
claim: proof_shape: bind-only (definition); frozen: F4,F3; escape_witness: none; consumer: claim_of_run_deletion_lower.
product_six: proof_shape: bind-only; frozen: F1,F2,F3; escape_witness: none; consumer: insertion_six_max.
product_alt_six: proof_shape: bind-only; frozen: F1,F2,F3; escape_witness: none; consumer: insertion_six_max.
DeletionCountingLowerBound: proof_shape: bind-only (definition); frozen: F3; escape_witness: none; consumer: deletion_counting_lower_of_run_score.
deletion_entropy_lt_phi_iff: proof_shape: bind-only; frozen: F5,F6,F7,F8,F1,F2,F3,F4,F9,F10,F11,F12; escape_witness: none; consumer: deletion_strict_of_count_lower.
product_eight_10: proof_shape: bind-only; frozen: F1,F2,F3; escape_witness: none; consumer: product_eight.
product_seven: proof_shape: bind-only; frozen: F1,F2,F3; escape_witness: none; consumer: insertion_seven_max.
product_alt_seven: proof_shape: bind-only; frozen: F1,F2,F3; escape_witness: none; consumer: insertion_seven_max.
product_eight_11: proof_shape: bind-only; frozen: F1,F2,F3; escape_witness: none; consumer: product_eight.
scatteredCount_not: proof_shape: bind-only; frozen: F1,F2,F3,F8; escape_witness: none; consumer: embeddings_not.
phi_complement_equiv: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: deletion_phi_complement.
product_eight_00: proof_shape: bind-only; frozen: F1,F2,F3; escape_witness: none; consumer: product_eight.
insertion_entropy_lt_phi_iff: proof_shape: bind-only; frozen: F4,F9,F13,F2,F1,F3,F14,F15,F16,F17; escape_witness: none; consumer: large_insertion_strict.
product_eight_01: proof_shape: bind-only; frozen: F1,F2,F3; escape_witness: none; consumer: product_eight.
runWord_ones: proof_shape: bind-only; frozen: F18,F19; escape_witness: none; consumer: zero_defect_word_alternating.
zero_defect_runs: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: zero_defect_word_alternating.
exists_positive_run_profile: proof_shape: bind-only; frozen: F20,F21,F22,F23,F24; escape_witness: none; consumer: deletion_counting_lower_of_run_score.
weightProduct_pos: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: insertion_entropy_le_iff.
insertion_two_zero: proof_shape: bind-only; frozen: F4,F7,F8,F2,F1,F3; escape_witness: none; consumer: claim_of_run_deletion_lower.
product_three: proof_shape: bind-only; frozen: F3; escape_witness: none; consumer: insertion_three_max.
product_alt_three: proof_shape: bind-only; frozen: F3; escape_witness: none; consumer: insertion_three_max.
product_four: proof_shape: bind-only; frozen: F3; escape_witness: none; consumer: product_opt_four.
product_opt_four: proof_shape: bind-only; frozen: F3; escape_witness: none; consumer: insertion_four_max.
product_eight: proof_shape: bind-only; frozen: F1,F2,F3; escape_witness: none; consumer: product_alt_eight.
deletion_strict_of_count_lower: proof_shape: content; frozen: F5,F18,F19,F1,F8,F13,F7,F2,F3,F6,F4,F9,F10,F11,F12; escape_witness: none; consumer: deletion_max_of_count_lower.
embeddings_not: proof_shape: bind-only; frozen: F1,F2,F3,F8; escape_witness: none; consumer: deletion_phi_complement.
zero_defect_word_alternating: proof_shape: bind-only; frozen: F18,F19; escape_witness: none; consumer: defect_pos_of_word_not_alternating.
insertion_entropy_le_iff: proof_shape: bind-only; frozen: F4,F9,F13,F2,F1,F3,F14,F15,F16,F17; escape_witness: none; consumer: insertion_entropy_eq_iff.
product_alt_eight: proof_shape: bind-only; frozen: F1,F2,F3; escape_witness: none; consumer: insertion_eight_max.
insertion_phi_complement: proof_shape: bind-only; frozen: F1,F2,F3,F8; escape_witness: none; consumer: insertion_entropy_complement.
deletion_phi_complement: proof_shape: bind-only; frozen: F1,F2,F3,F8; escape_witness: none; consumer: deletion_entropy_complement.
defect_pos_of_word_not_alternating: proof_shape: bind-only; frozen: F18,F19; escape_witness: none; consumer: deletion_counting_lower_of_run_score.
insertion_entropy_eq_iff: proof_shape: bind-only; frozen: F4,F9,F13,F2,F1,F3,F14,F15,F16,F17; escape_witness: none; consumer: insertion_seven_max.
insertion_five_max: proof_shape: bind-only; frozen: F1,F2,F3,F4,F9,F13,F14,F15,F16,F17; escape_witness: none; consumer: insertion_strict.
insertion_six_max: proof_shape: bind-only; frozen: F1,F2,F3,F4,F9,F13,F14,F15,F16,F17; escape_witness: none; consumer: insertion_strict.
insertion_eight_max: proof_shape: bind-only; frozen: F4,F9,F13,F2,F1,F3,F14,F15,F16,F17; escape_witness: none; consumer: insertion_strict.
deletion_counting_lower_of_run_score: proof_shape: bind-only; frozen: F18,F19,F20,F21,F22,F23,F24,F3; escape_witness: none; consumer: claim_of_run_deletion_lower.
insertion_seven_max: proof_shape: bind-only; frozen: F1,F2,F3,F4,F9,F13,F14,F15,F16,F17; escape_witness: none; consumer: insertion_strict.
large_insertion_strict: proof_shape: content; frozen: F19,F1,F13,F5,F18,F7,F8,F2,F3,F4,F9,F14,F15,F16,F17,F20,F21,F22,F23,F24; escape_witness: none; consumer: insertion_strict.
insertion_entropy_complement: proof_shape: bind-only; frozen: F1,F2,F3,F4,F8,F9,F13,F14,F15,F16,F17; escape_witness: none; consumer: insertion_max.
deletion_entropy_complement: proof_shape: bind-only; frozen: F5,F6,F7,F8,F1,F2,F3,F4,F9,F10,F11,F12; escape_witness: none; consumer: deletion_max_of_count_lower.
insertion_three_max: proof_shape: bind-only; frozen: F3,F4,F9,F13,F2,F1,F14,F15,F16,F17; escape_witness: none; consumer: claim_of_run_deletion_lower.
insertion_four_max: proof_shape: bind-only; frozen: F3,F4,F9,F13,F2,F1,F14,F15,F16,F17; escape_witness: none; consumer: claim_of_run_deletion_lower.
deletion_max_of_count_lower: proof_shape: content; frozen: F5,F18,F19,F1,F8,F13,F7,F2,F3,F6,F4,F9,F10,F11,F12; escape_witness: none; consumer: claim_of_run_deletion_lower.
insertion_strict: proof_shape: content; frozen: F1,F2,F3,F4,F9,F13,F14,F15,F16,F17,F19,F5,F18,F7,F8,F20,F21,F22,F23,F24; escape_witness: none; consumer: insertion_max.
insertion_max: proof_shape: content; frozen: F1,F2,F3,F4,F5,F7,F8,F9,F13,F14,F15,F16,F17,F18,F19,F20,F21,F22,F23,F24; escape_witness: none; consumer: claim_of_run_deletion_lower.
claim_of_run_deletion_lower: proof_shape: content; frozen: F3,F4,F9,F13,F2,F1,F14,F15,F16,F17,F7,F8,F19,F5,F18,F20,F21,F22,F23,F24,F6,F10,F11,F12; escape_witness: none; consumer: result.
result: proof_shape: content; frozen: F1,F8,F13,F5,F7,F2,F3,F4,F9,F14,F15,F16,F17,F19,F18,F20,F21,F22,F23,F24,F6,F10,F11,F12; escape_witness: none; consumer: none.
-/

import D5.S3.Entropy.AlternatingTwoDeletionCounts
import D5.S3.Entropy.TwoDeletionChannelEntropy
import D5.S1.Words.TwoDeletionRunDecks
import D5.S3.Entropy.TwoDeletionRunEntropyBounds
import D5.S1.Words.AssociatedMersenne.RunTupleBijection
import D5.S3.Entropy.DeletionChannelEntropyOrdering
import D5.S3.Entropy.MaxEntropy
import D5.S1.Words.Complexity.VivionBinomialConverseFails

set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace D5.S3.Entropy.SinghviMaxInputEntropy

open D5.S1.Words.Complexity.VivionBinomialConverseFails (scatteredCount)
open D5.S3.Entropy.DeletionChannelEntropyOrdering (embeddings)
open D5.S3.Entropy.DeletionChannelEntropyOrdering (embeddings_eq_count)
open D5.S1.Words.AssociatedMersenne.RunTupleBijection (blockLengths)
open D5.S3.Entropy.AlternatingTwoDeletionCounts
open D5.S3.Entropy.TwoDeletionChannelEntropy
open D5.S1.Words.TwoDeletionRunDecks
open D5.S3.Entropy.TwoDeletionRunEntropyBounds

private lemma product_five (y : Fin 5 → Bool) :
    256 ≤ (∏ a : Fin (3) → Bool, embeddings a y ^ embeddings a y : ℕ) ∧
    ((∏ a : Fin (3) → Bool, embeddings a y ^ embeddings a y : ℕ) = 256 ↔
      y = (fun i : Fin 5 => decide (i.val % 2 = 1)) ∨ y = fun i => !(fun i : Fin 5 => decide (i.val % 2 = 1)) i) := by
  simp only [embeddings_eq_count]
  fin_cases y <;> decide +kernel

private lemma product_alt_five : (∏ a : Fin (3) → Bool, embeddings a ((fun i : Fin 5 => decide (i.val % 2 = 1))) ^ embeddings a ((fun i : Fin 5 => decide (i.val % 2 = 1))) : ℕ)=256 := by
  exact (product_five (fun i : Fin 5 => decide (i.val % 2 = 1))).2.mpr (Or.inl rfl)


def claim : Prop :=
  let deletionPosterior := (fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ));
  let insertionPosterior := (fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ));
  (∀ m : ℕ, 1 ≤ m → ∀ y : Fin m → Bool,
      (D5.S3.Entropy.MaxEntropy.shannonEntropy (deletionPosterior y) / Real.log 2) ≤ (D5.S3.Entropy.MaxEntropy.shannonEntropy (deletionPosterior ((fun i : Fin m => decide (i.val % 2 = 1)))) / Real.log 2) ∧
      ((D5.S3.Entropy.MaxEntropy.shannonEntropy (deletionPosterior y) / Real.log 2) = (D5.S3.Entropy.MaxEntropy.shannonEntropy (deletionPosterior ((fun i : Fin m => decide (i.val % 2 = 1)))) / Real.log 2) ↔
        y = (fun i : Fin m => decide (i.val % 2 = 1)) ∨ y = fun i => !(fun i : Fin m => decide (i.val % 2 = 1)) i)) ∧
  (∀ m : ℕ, 1 ≤ m → (D5.S3.Entropy.MaxEntropy.shannonEntropy (deletionPosterior ((fun i : Fin m => decide (i.val % 2 = 1)))) / Real.log 2) =
      Real.logb 2 (4 * (m + 2).choose 2) -
        (4 * (m : ℝ) ^ 2 + 3 * m * Real.logb 2 3 + (m + 1) * Real.logb 2 (m + 1)) /
          (4 * (m + 2).choose 2)) ∧
  (∀ m : ℕ, 3 ≤ m → ∀ y : Fin (m + 2) → Bool,
      (D5.S3.Entropy.MaxEntropy.shannonEntropy (insertionPosterior y) / Real.log 2) ≤ (D5.S3.Entropy.MaxEntropy.shannonEntropy (insertionPosterior ((fun i : Fin (m + 2) => decide (i.val % 2 = 1)))) / Real.log 2) ∧
      ((D5.S3.Entropy.MaxEntropy.shannonEntropy (insertionPosterior y) / Real.log 2) = (D5.S3.Entropy.MaxEntropy.shannonEntropy (insertionPosterior ((fun i : Fin (m + 2) => decide (i.val % 2 = 1)))) / Real.log 2) ↔
        y = (fun i : Fin (m + 2) => decide (i.val % 2 = 1)) ∨ y = fun i => !(fun i : Fin (m + 2) => decide (i.val % 2 = 1)) i)) ∧
  (∀ m : ℕ, 3 ≤ m → (D5.S3.Entropy.MaxEntropy.shannonEntropy (insertionPosterior ((fun i : Fin (m + 2) => decide (i.val % 2 = 1)))) / Real.log 2) =
      Real.logb 2 ((m + 2).choose 2) - (m + 1) * Real.logb 2 (m + 1) / (m + 2).choose 2) ∧
  (∀ y : Fin 2 → Bool, (D5.S3.Entropy.MaxEntropy.shannonEntropy (insertionPosterior (m := 0) y) / Real.log 2) = 0) ∧
  (∀ y : Fin 3 → Bool,
      (D5.S3.Entropy.MaxEntropy.shannonEntropy (insertionPosterior (m := 1) y) / Real.log 2) ≤ (D5.S3.Entropy.MaxEntropy.shannonEntropy (insertionPosterior ((fun i : Fin 3 => decide (i.val % 2 = 1)))) / Real.log 2) ∧
      ((D5.S3.Entropy.MaxEntropy.shannonEntropy (insertionPosterior (m := 1) y) / Real.log 2) = (D5.S3.Entropy.MaxEntropy.shannonEntropy (insertionPosterior ((fun i : Fin 3 => decide (i.val % 2 = 1)))) / Real.log 2) ↔ ∃ i j, y i ≠ y j)) ∧
  (∀ y : Fin 4 → Bool,
      (D5.S3.Entropy.MaxEntropy.shannonEntropy (insertionPosterior (m := 2) y) / Real.log 2) ≤ (D5.S3.Entropy.MaxEntropy.shannonEntropy (insertionPosterior (m := 2) ![false, true, true, false]) / Real.log 2) ∧
      ((D5.S3.Entropy.MaxEntropy.shannonEntropy (insertionPosterior (m := 2) y) / Real.log 2) = (D5.S3.Entropy.MaxEntropy.shannonEntropy (insertionPosterior (m := 2) ![false, true, true, false]) / Real.log 2) ↔
        y = ![false, true, true, false] ∨ y = ![true, false, false, true]))

private lemma product_six (y : Fin 6 → Bool) :
    3125 ≤ (∏ a : Fin (4) → Bool, embeddings a y ^ embeddings a y : ℕ) ∧
    ((∏ a : Fin (4) → Bool, embeddings a y ^ embeddings a y : ℕ) = 3125 ↔
      y = (fun i : Fin 6 => decide (i.val % 2 = 1)) ∨ y = fun i => !(fun i : Fin 6 => decide (i.val % 2 = 1)) i) := by
  simp only [embeddings_eq_count]
  fin_cases y <;> decide +kernel

private lemma product_alt_six : (∏ a : Fin (4) → Bool, embeddings a ((fun i : Fin 6 => decide (i.val % 2 = 1))) ^ embeddings a ((fun i : Fin 6 => decide (i.val % 2 = 1))) : ℕ)=3125 := by
  exact (product_six (fun i : Fin 6 => decide (i.val % 2 = 1))).2.mpr (Or.inl rfl)


private def DeletionCountingLowerBound : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ y : Fin m → Bool,
    ¬(y=(fun i : Fin m => decide (i.val % 2 = 1)) ∨ y=fun i => !(fun i : Fin m => decide (i.val % 2 = 1)) i) →
    ∃ us ws : List ℕ, us ≠ [] ∧ (∀ u∈us,2 ≤ u ∧ u ≤ m) ∧ us.sum ≤ m ∧
      ws.length=us.length+1 ∧ m+us.sum+us.length+1 ≤ ws.sum ∧
      ((m-us.sum:ℕ):ℝ)*(f 3+4*m)+(us.map (fun u : ℕ => Hrun (m:ℝ) (u:ℝ))).sum+
        (ws.map (fun n : ℕ => f n)).sum ≤
          phi (fun x : Fin (m+2) → Bool => embeddings y x)

private lemma deletion_entropy_lt_phi_iff {m : ℕ} (y z : Fin m → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) y) / Real.log 2)<(D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) z) / Real.log 2) ↔
      phi (fun x : Fin (m+2) → Bool => embeddings z x)<
        phi (fun x : Fin (m+2) → Bool => embeddings y x) := by
  rw [deletion_entropy_formula,deletion_entropy_formula]
  have hn : (0:ℝ)<4*(m+2).choose 2 := by
    exact_mod_cast Nat.mul_pos (by omega : 0<4) (Nat.choose_pos (show 2 ≤ m+2 by omega))
  rw [sub_lt_sub_iff_left,div_lt_div_iff_of_pos_right hn]

private lemma product_eight_10 (x : Fin 6 → Bool) :
    823543 ≤ (∏ a : Fin (6) → Bool, embeddings a (Fin.cons true (Fin.cons false x)) ^ embeddings a (Fin.cons true (Fin.cons false x)) : ℕ) ∧
    ((∏ a : Fin (6) → Bool, embeddings a (Fin.cons true (Fin.cons false x)) ^ embeddings a (Fin.cons true (Fin.cons false x)) : ℕ) = 823543 ↔
      (Fin.cons true (Fin.cons false x)) = (fun i : Fin 8 => decide (i.val % 2 = 1)) ∨ (Fin.cons true (Fin.cons false x)) = fun i => !(fun i : Fin 8 => decide (i.val % 2 = 1)) i) := by
  simp only [embeddings_eq_count]
  fin_cases x <;> decide +kernel

private lemma product_seven (y : Fin 7 → Bool) :
    46656 ≤ (∏ a : Fin (5) → Bool, embeddings a y ^ embeddings a y : ℕ) ∧
    ((∏ a : Fin (5) → Bool, embeddings a y ^ embeddings a y : ℕ) = 46656 ↔
      y = (fun i : Fin 7 => decide (i.val % 2 = 1)) ∨ y = fun i => !(fun i : Fin 7 => decide (i.val % 2 = 1)) i) := by
  simp only [embeddings_eq_count]
  fin_cases y <;> decide +kernel

private lemma product_alt_seven : (∏ a : Fin (5) → Bool, embeddings a ((fun i : Fin 7 => decide (i.val % 2 = 1))) ^ embeddings a ((fun i : Fin 7 => decide (i.val % 2 = 1))) : ℕ)=46656 := by
  exact (product_seven (fun i : Fin 7 => decide (i.val % 2 = 1))).2.mpr (Or.inl rfl)


private lemma product_eight_11 (x : Fin 6 → Bool) :
    823543 ≤ (∏ a : Fin (6) → Bool, embeddings a (Fin.cons true (Fin.cons true x)) ^ embeddings a (Fin.cons true (Fin.cons true x)) : ℕ) ∧
    ((∏ a : Fin (6) → Bool, embeddings a (Fin.cons true (Fin.cons true x)) ^ embeddings a (Fin.cons true (Fin.cons true x)) : ℕ) = 823543 ↔
      (Fin.cons true (Fin.cons true x)) = (fun i : Fin 8 => decide (i.val % 2 = 1)) ∨ (Fin.cons true (Fin.cons true x)) = fun i => !(fun i : Fin 8 => decide (i.val % 2 = 1)) i) := by
  simp only [embeddings_eq_count]
  fin_cases x <;> decide +kernel

private lemma scatteredCount_not (p q : List Bool) :
    scatteredCount (p.map Bool.not) (q.map Bool.not)=scatteredCount p q := by
  simpa only [embeddings_eq_count, List.ofFn_comp', List.ofFn_get] using
    (show embeddings (fun i => !p.get i) (fun i => !q.get i) =
        embeddings p.get q.get from by
      unfold embeddings
      simp only [List.ofFn_comp', List.sublists_map]
      simp only [List.filter_map, Function.comp_def,
        List.map_inj_right (fun a b h => Bool.not_inj h), List.length_map])

private lemma phi_complement_equiv {n : ℕ} (c : (Fin n → Bool) → ℕ) :
    phi (fun x : Fin n → Bool => c (fun i => !x i))=phi c := by
  classical
  unfold phi
  apply Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin n => Equiv.boolNot))
  intro x
  rfl

private lemma product_eight_00 (x : Fin 6 → Bool) :
    823543 ≤ (∏ a : Fin (6) → Bool, embeddings a (Fin.cons false (Fin.cons false x)) ^ embeddings a (Fin.cons false (Fin.cons false x)) : ℕ) ∧
    ((∏ a : Fin (6) → Bool, embeddings a (Fin.cons false (Fin.cons false x)) ^ embeddings a (Fin.cons false (Fin.cons false x)) : ℕ) = 823543 ↔
      (Fin.cons false (Fin.cons false x)) = (fun i : Fin 8 => decide (i.val % 2 = 1)) ∨ (Fin.cons false (Fin.cons false x)) = fun i => !(fun i : Fin 8 => decide (i.val % 2 = 1)) i) := by
  simp only [embeddings_eq_count]
  fin_cases x <;> decide +kernel

private lemma insertion_entropy_lt_phi_iff {m : ℕ} (y z : Fin (m+2) → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) y) / Real.log 2) < (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) z) / Real.log 2) ↔
      phi (fun x : Fin m → Bool => embeddings x z) < phi (fun x : Fin m → Bool => embeddings x y) := by
  rw [insertion_entropy_formula,insertion_entropy_formula]
  have hn : (0:ℝ)<(m+2).choose m := by
    exact_mod_cast Nat.choose_pos (show m ≤ m+2 by omega)
  rw [sub_lt_sub_iff_left,div_lt_div_iff_of_pos_right hn]

private lemma product_eight_01 (x : Fin 6 → Bool) :
    823543 ≤ (∏ a : Fin (6) → Bool, embeddings a (Fin.cons false (Fin.cons true x)) ^ embeddings a (Fin.cons false (Fin.cons true x)) : ℕ) ∧
    ((∏ a : Fin (6) → Bool, embeddings a (Fin.cons false (Fin.cons true x)) ^ embeddings a (Fin.cons false (Fin.cons true x)) : ℕ) = 823543 ↔
      (Fin.cons false (Fin.cons true x)) = (fun i : Fin 8 => decide (i.val % 2 = 1)) ∨ (Fin.cons false (Fin.cons true x)) = fun i => !(fun i : Fin 8 => decide (i.val % 2 = 1)) i) := by
  simp only [embeddings_eq_count]
  fin_cases x <;> decide +kernel

private lemma runWord_ones (b : Bool) (n : ℕ) : runWord b (List.replicate n 1)=altList b n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp [runWord,altList_succ,List.replicate_succ,ih]

private lemma zero_defect_runs (rs : List ℕ) (hp : ∀ r ∈ rs,0<r) (h0 : runDefect rs=0) :
    rs=List.replicate rs.length 1 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hr := hp r (by simp)
    have ht : ∀ a ∈ rs,0<a := fun a ha => hp a (by simp [ha])
    have he : (r-1)+runDefect rs=0 := by exact Eq.symm (Nat.right_eq_add.mpr h0)
    have hr1 : r=1 := by omega
    have ht0 : runDefect rs=0 := by exact Nat.eq_zero_of_add_eq_zero_left h0
    subst r
    simpa only [List.length_cons,List.replicate_succ] using congrArg (List.cons 1) (ih ht ht0)

private lemma exists_positive_run_profile (w : List Bool) :
    ∃ (b : Bool) (rs : List ℕ), (∀ r ∈ rs,0<r) ∧ runWord b rs=w ∧ rs.sum=w.length := by
  refine ⟨w.headD false,blockLengths w,blockLengths_positive w,runWord_blockLengths w,?_⟩
  have h := congrArg List.length (runWord_blockLengths w)
  simpa only [runWord_length] using h

private lemma weightProduct_pos {ι : Type*} [Fintype ι] (c : ι → ℕ) : 0 < (∏ i, (c) i ^ (c) i : ℕ) := by
  exact Finset.prod_pos (fun _ _ => Nat.pow_self_pos)

private lemma insertion_two_zero (y : Fin 2 → Bool) : (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 0) y) / Real.log 2) = 0 := by
  have he (x : Fin 0 → Bool) : embeddings x y = 1 := by
    have hx : x = (fun i : Fin 0 => Fin.elim0 i) := Subsingleton.elim _ _
    rw [hx]
    exact empty_embeddings y
  dsimp only
  unfold D5.S3.Entropy.MaxEntropy.shannonEntropy
  simp_rw [he]
  simp [Real.negMulLog]

private lemma product_three (y : Fin 3 → Bool) :
    4 ≤ (∏ a : Fin (1) → Bool, embeddings a y ^ embeddings a y : ℕ) ∧
    ((∏ a : Fin (1) → Bool, embeddings a y ^ embeddings a y : ℕ) = 4 ↔ ∃ i j, y i ≠ y j) := by
  fin_cases y <;> decide +kernel

private lemma product_alt_three : (∏ a : Fin (1) → Bool, embeddings a ((fun i : Fin 3 => decide (i.val % 2 = 1))) ^ embeddings a ((fun i : Fin 3 => decide (i.val % 2 = 1))) : ℕ) = 4 := by
  exact (product_three (fun i : Fin 3 => decide (i.val % 2 = 1))).2.mpr ⟨0,1,by decide⟩

private lemma product_four (y : Fin 4 → Bool) :
    16 ≤ (∏ a : Fin (2) → Bool, embeddings a y ^ embeddings a y : ℕ) ∧
    ((∏ a : Fin (2) → Bool, embeddings a y ^ embeddings a y : ℕ) = 16 ↔
      y = ![false, true, true, false] ∨ y = ![true, false, false, true]) := by
  fin_cases y <;> decide +kernel

private lemma product_opt_four : (∏ a : Fin (2) → Bool, embeddings a ![false, true, true, false] ^ embeddings a ![false, true, true, false] : ℕ) = 16 := by
  exact (product_four ![false, true, true, false]).2.mpr (Or.inl rfl)


private lemma product_eight (y : Fin 8 → Bool) :
    823543 ≤ (∏ a : Fin (6) → Bool, embeddings a y ^ embeddings a y : ℕ) ∧
    ((∏ a : Fin (6) → Bool, embeddings a y ^ embeddings a y : ℕ) = 823543 ↔
      y = (fun i : Fin 8 => decide (i.val % 2 = 1)) ∨ y = fun i => !(fun i : Fin 8 => decide (i.val % 2 = 1)) i) := by
  obtain ⟨⟨b,z⟩,rfl⟩ := (Fin.consEquiv (fun _ : Fin 8 => Bool)).surjective y
  obtain ⟨⟨c,x⟩,rfl⟩ := (Fin.consEquiv (fun _ : Fin 7 => Bool)).surjective z
  cases b
  · cases c
    · exact product_eight_00 x
    · exact product_eight_01 x
  · cases c
    · exact product_eight_10 x
    · exact product_eight_11 x

private lemma deletion_strict_of_count_lower (hc : DeletionCountingLowerBound)
    {m : ℕ} (hm : 2 ≤ m) (y : Fin m → Bool)
    (hne : ¬(y=(fun i : Fin m => decide (i.val % 2 = 1)) ∨ y=fun i => !(fun i : Fin m => decide (i.val % 2 = 1)) i)) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) y) / Real.log 2)<(D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) ((fun i : Fin m => decide (i.val % 2 = 1)))) / Real.log 2) := by
    obtain ⟨us,ws,hu,hp,hU,hc,hS,hP⟩ := hc m hm y hne
    have hgap := deletion_abstract_bridge_gap m us ws hm hu hp hU hc hS
    apply (deletion_entropy_lt_phi_iff y ((fun i : Fin m => decide (i.val % 2 = 1)))).mpr
    rw [alternating_deletion_phi m (by omega)]
    exact hgap.trans_le hP

private lemma embeddings_not {m n : ℕ} (x : Fin m → Bool) (y : Fin n → Bool) :
    embeddings (fun i => !x i) (fun i => !y i)=embeddings x y := by
  simp only [embeddings_eq_count,List.ofFn_comp',scatteredCount_not]

private lemma zero_defect_word_alternating {m : ℕ} (y : Fin m → Bool) (b : Bool) (rs : List ℕ)
    (hp : ∀ r ∈ rs,0<r) (hword : List.ofFn y=runWord b rs) (h0 : runDefect rs=0) :
    y=(fun i : Fin m => decide (i.val % 2 = 1)) ∨ y=fun i => !(fun i : Fin m => decide (i.val % 2 = 1)) i := by
  have hlen : rs.sum=m := by
    have h := congrArg List.length hword
    simpa only [List.length_ofFn,runWord_length] using h.symm
  have hdef := runDefect_eq rs hp
  have hR : rs.length=m := by omega
  rw [zero_defect_runs rs hp h0,hR,runWord_ones] at hword
  cases b with
  | false =>
    left
    apply List.ofFn_injective
    simpa only [ofFn_alternating] using hword
  | true =>
    right
    apply List.ofFn_injective
    simpa only [ofFn_complement_alternating] using hword

private lemma insertion_entropy_le_iff {m : ℕ} (x y : Fin (m+2) → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) x) / Real.log 2) ≤ (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) y) / Real.log 2) ↔ (∏ a : Fin (m) → Bool, embeddings a y ^ embeddings a y : ℕ) ≤ (∏ a : Fin (m) → Bool, embeddings a x ^ embeddings a x : ℕ) := by
  rw [insertion_entropy_product_formula, insertion_entropy_product_formula]
  have hN : (0 : ℝ) < (m+2).choose m := by exact_mod_cast Nat.choose_pos (show m ≤ m+2 by omega)
  have hx : (0 : ℝ) < (∏ a : Fin (m) → Bool, embeddings a x ^ embeddings a x : ℕ) := by exact_mod_cast weightProduct_pos (fun a : Fin m → Bool => embeddings a x)
  have hy : (0 : ℝ) < (∏ a : Fin (m) → Bool, embeddings a y ^ embeddings a y : ℕ) := by exact_mod_cast weightProduct_pos (fun a : Fin m → Bool => embeddings a y)
  change _ ≤ _ ↔ (∏ a : Fin (m) → Bool, embeddings a y ^ embeddings a y : ℕ) ≤ (∏ a : Fin (m) → Bool, embeddings a x ^ embeddings a x : ℕ)
  rw [sub_le_sub_iff_left, div_le_div_iff_of_pos_right hN]
  change Real.logb 2 ((∏ a : Fin (m) → Bool, embeddings a y ^ embeddings a y : ℕ)) ≤ Real.logb 2 ((∏ a : Fin (m) → Bool, embeddings a x ^ embeddings a x : ℕ)) ↔ _
  rw [Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hy hx]
  exact_mod_cast (Iff.rfl : (∏ a : Fin (m) → Bool, embeddings a y ^ embeddings a y : ℕ) ≤ (∏ a : Fin (m) → Bool, embeddings a x ^ embeddings a x : ℕ) ↔ _)

private lemma product_alt_eight : (∏ a : Fin (6) → Bool, embeddings a ((fun i : Fin 8 => decide (i.val % 2 = 1))) ^ embeddings a ((fun i : Fin 8 => decide (i.val % 2 = 1))) : ℕ)=823543 := by
  exact (product_eight ((fun i : Fin 8 => decide (i.val % 2 = 1)))).2.mpr (Or.inl rfl)

private lemma insertion_phi_complement {m : ℕ} (y : Fin (m+2) → Bool) :
    phi (fun x : Fin m → Bool => embeddings x (fun i => !y i)) =
      phi (fun x : Fin m → Bool => embeddings x y) := by
  have h := phi_complement_equiv (fun x : Fin m → Bool => embeddings x (fun i => !y i))
  simpa only [embeddings_not] using h.symm

private lemma deletion_phi_complement {m : ℕ} (y : Fin m → Bool) :
    phi (fun x : Fin (m+2) → Bool => embeddings (fun i => !y i) x) =
      phi (fun x : Fin (m+2) → Bool => embeddings y x) := by
  have h := phi_complement_equiv (fun x : Fin (m+2) → Bool => embeddings (fun i => !y i) x)
  simpa only [embeddings_not] using h.symm

private lemma defect_pos_of_word_not_alternating {m : ℕ} (y : Fin m → Bool) (b : Bool) (rs : List ℕ)
    (hp : ∀ r ∈ rs,0<r) (hword : List.ofFn y=runWord b rs)
    (hne : ¬(y=(fun i : Fin m => decide (i.val % 2 = 1)) ∨ y=fun i => !(fun i : Fin m => decide (i.val % 2 = 1)) i)) : 0<runDefect rs := by
  by_contra h
  have h0 : runDefect rs=0 := by exact Nat.eq_zero_of_not_pos h
  exact hne (zero_defect_word_alternating y b rs hp hword h0)

private lemma insertion_entropy_eq_iff {m : ℕ} (x y : Fin (m+2) → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) x) / Real.log 2) = (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) y) / Real.log 2) ↔ (∏ a : Fin (m) → Bool, embeddings a x ^ embeddings a x : ℕ) = (∏ a : Fin (m) → Bool, embeddings a y ^ embeddings a y : ℕ) := by
  rw [le_antisymm_iff, insertion_entropy_le_iff, insertion_entropy_le_iff]
  exact ⟨fun h => Nat.le_antisymm h.2 h.1, fun h => by simp [h]⟩

private lemma insertion_five_max (y : Fin 5 → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 3) y) / Real.log 2) ≤ (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin 5 => decide (i.val % 2 = 1)))) / Real.log 2) ∧
    ((D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 3) y) / Real.log 2) = (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin 5 => decide (i.val % 2 = 1)))) / Real.log 2) ↔
      y = (fun i : Fin 5 => decide (i.val % 2 = 1)) ∨ y = fun i => !(fun i : Fin 5 => decide (i.val % 2 = 1)) i) := by
  rw [insertion_entropy_le_iff,insertion_entropy_eq_iff,product_alt_five]
  exact product_five y

private lemma insertion_six_max (y : Fin 6 → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 4) y) / Real.log 2) ≤ (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin 6 => decide (i.val % 2 = 1)))) / Real.log 2) ∧
    ((D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 4) y) / Real.log 2) = (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin 6 => decide (i.val % 2 = 1)))) / Real.log 2) ↔
      y = (fun i : Fin 6 => decide (i.val % 2 = 1)) ∨ y = fun i => !(fun i : Fin 6 => decide (i.val % 2 = 1)) i) := by
  rw [insertion_entropy_le_iff,insertion_entropy_eq_iff,product_alt_six]
  exact product_six y

private lemma insertion_eight_max (y : Fin 8 → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 6) y) / Real.log 2) ≤ (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin 8 => decide (i.val % 2 = 1)))) / Real.log 2) ∧
    ((D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 6) y) / Real.log 2) = (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin 8 => decide (i.val % 2 = 1)))) / Real.log 2) ↔
      y = (fun i : Fin 8 => decide (i.val % 2 = 1)) ∨ y = fun i => !(fun i : Fin 8 => decide (i.val % 2 = 1)) i) := by
  have hp := product_eight y
  have ha := product_alt_eight
  constructor
  · apply (insertion_entropy_le_iff y ((fun i : Fin 8 => decide (i.val % 2 = 1)))).mpr
    exact ha.le.trans hp.1
  · constructor
    · intro he
      exact hp.2.mp (((insertion_entropy_eq_iff y ((fun i : Fin 8 => decide (i.val % 2 = 1)))).mp he).trans ha)
    · intro he
      exact (insertion_entropy_eq_iff y ((fun i : Fin 8 => decide (i.val % 2 = 1)))).mpr ((hp.2.mpr he).trans ha.symm)

private lemma deletion_counting_lower_of_run_score (h : RunDeletionCountingLowerBound) :
    DeletionCountingLowerBound := by
  intro m hm y hne
  obtain ⟨b,rs,hp,hw,hs⟩ := exists_positive_run_profile (List.ofFn y)
  have hsum : rs.sum=m := by simpa only [List.length_ofFn] using hs
  have hword : List.ofFn y=runWord b rs := hw.symm
  have hd := defect_pos_of_word_not_alternating y b rs hp hword hne
  have hu := longRuns_nonempty_of_defect rs hp hd
  have hb := bridgeWeights_constraints rs hp
  have hbounds := longRuns_bounds rs hp
  refine ⟨longRuns rs,bridgeWeightsAux 0 0 rs,hu,?_,?_,hb.1,?_,?_⟩
  · simpa only [hsum] using hbounds.1
  · simpa only [hsum] using hbounds.2
  · simpa only [hsum] using hb.2.ge
  · simpa only [deletionRunScore,hsum] using h m y b rs hp hword

private lemma insertion_seven_max (y : Fin 7 → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 5) y) / Real.log 2) ≤ (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin 7 => decide (i.val % 2 = 1)))) / Real.log 2) ∧
    ((D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 5) y) / Real.log 2) = (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin 7 => decide (i.val % 2 = 1)))) / Real.log 2) ↔
      y = (fun i : Fin 7 => decide (i.val % 2 = 1)) ∨ y = fun i => !(fun i : Fin 7 => decide (i.val % 2 = 1)) i) := by
  rw [insertion_entropy_le_iff,insertion_entropy_eq_iff,product_alt_seven]
  exact product_seven y

private lemma large_insertion_strict
    {m : ℕ} (hm : 7 ≤ m) (y : Fin (m+2) → Bool)
    (hne : ¬(y=(fun i : Fin (m+2) => decide (i.val % 2 = 1)) ∨ y=fun i => !(fun i : Fin (m+2) => decide (i.val % 2 = 1)) i)) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) y) / Real.log 2) < (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin (m+2) => decide (i.val % 2 = 1)))) / Real.log 2) := by
  obtain ⟨b,rs,hp,hw,hs⟩ := exists_positive_run_profile (List.ofFn y)
  have hsum : rs.sum=m+2 := by simpa only [List.length_ofFn] using hs
  have hword : List.ofFn y=runWord b rs := hw.symm
  have hd := defect_pos_of_word_not_alternating y b rs hp hword hne
  have hdef := runDefect_eq rs hp
  have hdefR : (runDefect rs:ℝ)+(rs.length:ℝ)=(rs.sum:ℝ) := by exact_mod_cast hdef
  have hdEq : (rs.sum:ℝ)-rs.length=(runDefect rs:ℝ) := by exact Eq.symm (eq_sub_of_add_eq hdefR)
  have hco := run_coarse_insertion_bound rs hp
  rw [hdEq] at hco
  have hstrict := large_insertion_comparison rs.sum (runDefect rs) (runPhiInsertion rs)
    (by omega) hd hco (by
      intro hcase
      have hR : 3 ≤ rs.length := by omega
      exact run_fine_insertion_bound rs hp hR)
  have hphi := actual_run_insertion_lower y b rs hp hword
  have hfinal := hstrict.trans_le hphi
  rw [hsum] at hfinal
  have he : (m+2)-1=m+1 := by exact Nat.add_succ_sub_one m 1
  rw [he] at hfinal
  apply (insertion_entropy_lt_phi_iff y ((fun i : Fin (m+2) => decide (i.val % 2 = 1)))).mpr
  rw [alternating_insertion_phi]
  simpa only [Nat.cast_add,Nat.cast_one] using hfinal

private lemma insertion_entropy_complement {m : ℕ} (y : Fin (m+2) → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (fun i => !y i)) / Real.log 2)=(D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) y) / Real.log 2) := by
  rw [insertion_entropy_formula,insertion_entropy_formula,insertion_phi_complement]

private lemma deletion_entropy_complement {m : ℕ} (y : Fin m → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) (fun i => !y i)) / Real.log 2)=(D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) y) / Real.log 2) := by
  rw [deletion_entropy_formula,deletion_entropy_formula,deletion_phi_complement]

private lemma insertion_three_max (y : Fin 3 → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 1) y) / Real.log 2) ≤ (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin 3 => decide (i.val % 2 = 1)))) / Real.log 2) ∧
    ((D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 1) y) / Real.log 2) = (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin 3 => decide (i.val % 2 = 1)))) / Real.log 2) ↔ ∃ i j, y i ≠ y j) := by
  rw [insertion_entropy_le_iff, insertion_entropy_eq_iff, product_alt_three]
  exact product_three y

private lemma insertion_four_max (y : Fin 4 → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 2) y) / Real.log 2) ≤ (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 2) ![false, true, true, false]) / Real.log 2) ∧
    ((D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 2) y) / Real.log 2) = (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) (m := 2) ![false, true, true, false]) / Real.log 2) ↔
      y = ![false, true, true, false] ∨ y = ![true, false, false, true]) := by
  rw [insertion_entropy_le_iff, insertion_entropy_eq_iff, product_opt_four]
  exact product_four y

private lemma deletion_max_of_count_lower (hc : DeletionCountingLowerBound)
    {m : ℕ} (hm : 1 ≤ m) (y : Fin m → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) y) / Real.log 2) ≤ (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) ((fun i : Fin m => decide (i.val % 2 = 1)))) / Real.log 2) ∧
    ((D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) y) / Real.log 2)=(D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) ((fun i : Fin m => decide (i.val % 2 = 1)))) / Real.log 2) ↔
      y=(fun i : Fin m => decide (i.val % 2 = 1)) ∨ y=fun i => !(fun i : Fin m => decide (i.val % 2 = 1)) i) := by
  by_cases ha : y=(fun i : Fin m => decide (i.val % 2 = 1)) ∨ y=fun i => !(fun i : Fin m => decide (i.val % 2 = 1)) i
  · have he : (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) y) / Real.log 2)=(D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin m → Bool) (x : Fin (m + 2) → Bool) => (embeddings y x : ℝ) / ∑ x' : Fin (m + 2) → Bool, (embeddings y x' : ℝ)) ((fun i : Fin m => decide (i.val % 2 = 1)))) / Real.log 2) := by
      rcases ha with rfl | rfl
      · rfl
      · exact deletion_entropy_complement _
    exact ⟨he.le,⟨fun _ => ha,fun _ => he⟩⟩
  · have hm2 : 2 ≤ m := by
      by_contra hn
      have he : m=1 := by omega
      subst m
      fin_cases y <;> exact (ha (by decide +kernel)).elim
    have hlt := deletion_strict_of_count_lower hc hm2 y ha
    exact ⟨hlt.le,⟨fun he => (ne_of_lt hlt he).elim,fun h => (ha h).elim⟩⟩
open D5.S3.Entropy.DeletionChannelEntropyOrdering (embeddings)


private lemma insertion_strict
    {m : ℕ} (hm : 3 ≤ m) (y : Fin (m+2) → Bool)
    (hne : ¬(y=(fun i : Fin (m+2) => decide (i.val % 2 = 1)) ∨ y=fun i => !(fun i : Fin (m+2) => decide (i.val % 2 = 1)) i)) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) y) / Real.log 2) < (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin (m+2) => decide (i.val % 2 = 1)))) / Real.log 2) := by
  by_cases hlarge : 7 ≤ m
  · exact large_insertion_strict hlarge y hne
  have hm6 : m ≤ 6 := by exact Nat.le_of_not_lt hlarge
  interval_cases m
  all_goals
    have h := by first | exact insertion_five_max y | exact insertion_six_max y |
      exact insertion_seven_max y | exact insertion_eight_max y
    by_contra hn
    have he := le_antisymm h.1 (le_of_not_gt hn)
    exact hne (h.2.mp he)

private lemma insertion_max
    {m : ℕ} (hm : 3 ≤ m) (y : Fin (m+2) → Bool) :
    (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) y) / Real.log 2) ≤ (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin (m+2) => decide (i.val % 2 = 1)))) / Real.log 2) ∧
    ((D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) y) / Real.log 2)=(D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin (m+2) => decide (i.val % 2 = 1)))) / Real.log 2) ↔
      y=(fun i : Fin (m+2) => decide (i.val % 2 = 1)) ∨ y=fun i => !(fun i : Fin (m+2) => decide (i.val % 2 = 1)) i) := by
  by_cases ha : y=(fun i : Fin (m+2) => decide (i.val % 2 = 1)) ∨ y=fun i => !(fun i : Fin (m+2) => decide (i.val % 2 = 1)) i
  · have he : (D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) y) / Real.log 2)=(D5.S3.Entropy.MaxEntropy.shannonEntropy ((fun {m : ℕ} (y : Fin (m + 2) → Bool) (x : Fin m → Bool) => (embeddings x y : ℝ) / ∑ x' : Fin m → Bool, (embeddings x' y : ℝ)) ((fun i : Fin (m+2) => decide (i.val % 2 = 1)))) / Real.log 2) := by
      rcases ha with rfl | rfl
      · rfl
      · exact insertion_entropy_complement _
    exact ⟨he.le,⟨fun _ => ha,fun _ => he⟩⟩
  · have hlt := insertion_strict hm y ha
    exact ⟨hlt.le,⟨fun he => (ne_of_lt hlt he).elim,fun h => (ha h).elim⟩⟩

private lemma claim_of_run_deletion_lower (h : RunDeletionCountingLowerBound) :
    claim := by
  refine ⟨(fun _ hm y => deletion_max_of_count_lower (deletion_counting_lower_of_run_score h) hm y),
    alternating_deletion_closed_form, (fun _ hm y => insertion_max hm y), ?_, insertion_two_zero,
    insertion_three_max,insertion_four_max⟩
  intro m _
  exact alternating_insertion_closed_form m
open D5.S3.Entropy.DeletionChannelEntropyOrdering (embeddings)
open D5.S1.Words.Complexity.VivionBinomialConverseFails (scatteredCount)
open D5.S3.Entropy.DeletionChannelEntropyOrdering (embeddings_eq_count)

theorem result : claim := by
  exact claim_of_run_deletion_lower actual_run_deletion_lower

end D5.S3.Entropy.SinghviMaxInputEntropy
