/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73CorrelationBlock6
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Correlations.correlation_spec; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73CorrelationData.correlationAt
   digest: Checked partial and total correlation sums for order-73 block 6. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73CorrelationData

/-! Exact data and kernel checks for the order-73 chirped construction. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Chirped73

open ChirpedFinite

private theorem corr_18_0_0 : ∀ i : Fin 8, part 18 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 18 i.val) := by
  decide +kernel

private theorem corr_18_0_8 : ∀ i : Fin 8, part 18 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 18 (8 + i.val)) := by
  decide +kernel

private theorem corr_18_0_16 : ∀ i : Fin 8, part 18 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 18 (16 + i.val)) := by
  decide +kernel

private theorem corr_18_0_24 : ∀ i : Fin 8, part 18 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 18 (24 + i.val)) := by
  decide +kernel

private theorem corr_18_0_32 : ∀ i : Fin 6, part 18 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 18 (32 + i.val)) := by
  decide +kernel

private theorem corr_18_0 : ∀ i : ℕ, i < 38 → part 18 0 i = sumWindow (0 * width) (chunkLen n 0) (term 18 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_18_0_0) corr_18_0_8) corr_18_0_16) corr_18_0_24) corr_18_0_32

private theorem corr_18_1_0 : ∀ i : Fin 8, part 18 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 18 i.val) := by
  decide +kernel

private theorem corr_18_1_8 : ∀ i : Fin 8, part 18 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 18 (8 + i.val)) := by
  decide +kernel

private theorem corr_18_1_16 : ∀ i : Fin 8, part 18 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 18 (16 + i.val)) := by
  decide +kernel

private theorem corr_18_1_24 : ∀ i : Fin 8, part 18 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 18 (24 + i.val)) := by
  decide +kernel

private theorem corr_18_1_32 : ∀ i : Fin 6, part 18 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 18 (32 + i.val)) := by
  decide +kernel

private theorem corr_18_1 : ∀ i : ℕ, i < 38 → part 18 1 i = sumWindow (1 * width) (chunkLen n 1) (term 18 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_18_1_0) corr_18_1_8) corr_18_1_16) corr_18_1_24) corr_18_1_32

private theorem corr_18_2_0 : ∀ i : Fin 8, part 18 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 18 i.val) := by
  decide +kernel

private theorem corr_18_2_8 : ∀ i : Fin 8, part 18 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 18 (8 + i.val)) := by
  decide +kernel

private theorem corr_18_2_16 : ∀ i : Fin 8, part 18 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 18 (16 + i.val)) := by
  decide +kernel

private theorem corr_18_2_24 : ∀ i : Fin 8, part 18 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 18 (24 + i.val)) := by
  decide +kernel

private theorem corr_18_2_32 : ∀ i : Fin 6, part 18 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 18 (32 + i.val)) := by
  decide +kernel

private theorem corr_18_2 : ∀ i : ℕ, i < 38 → part 18 2 i = sumWindow (2 * width) (chunkLen n 2) (term 18 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_18_2_0) corr_18_2_8) corr_18_2_16) corr_18_2_24) corr_18_2_32

private theorem corr_18_3_0 : ∀ i : Fin 8, part 18 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 18 i.val) := by
  decide +kernel

private theorem corr_18_3_8 : ∀ i : Fin 8, part 18 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 18 (8 + i.val)) := by
  decide +kernel

private theorem corr_18_3_16 : ∀ i : Fin 8, part 18 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 18 (16 + i.val)) := by
  decide +kernel

private theorem corr_18_3_24 : ∀ i : Fin 8, part 18 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 18 (24 + i.val)) := by
  decide +kernel

private theorem corr_18_3_32 : ∀ i : Fin 6, part 18 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 18 (32 + i.val)) := by
  decide +kernel

private theorem corr_18_3 : ∀ i : ℕ, i < 38 → part 18 3 i = sumWindow (3 * width) (chunkLen n 3) (term 18 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_18_3_0) corr_18_3_8) corr_18_3_16) corr_18_3_24) corr_18_3_32

private theorem corr_18_4_0 : ∀ i : Fin 8, part 18 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 18 i.val) := by
  decide +kernel

private theorem corr_18_4_8 : ∀ i : Fin 8, part 18 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 18 (8 + i.val)) := by
  decide +kernel

private theorem corr_18_4_16 : ∀ i : Fin 8, part 18 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 18 (16 + i.val)) := by
  decide +kernel

private theorem corr_18_4_24 : ∀ i : Fin 8, part 18 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 18 (24 + i.val)) := by
  decide +kernel

private theorem corr_18_4_32 : ∀ i : Fin 6, part 18 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 18 (32 + i.val)) := by
  decide +kernel

private theorem corr_18_4 : ∀ i : ℕ, i < 38 → part 18 4 i = sumWindow (4 * width) (chunkLen n 4) (term 18 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_18_4_0) corr_18_4_8) corr_18_4_16) corr_18_4_24) corr_18_4_32

private theorem corr_18_5_0 : ∀ i : Fin 8, part 18 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 18 i.val) := by
  decide +kernel

private theorem corr_18_5_8 : ∀ i : Fin 8, part 18 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 18 (8 + i.val)) := by
  decide +kernel

private theorem corr_18_5_16 : ∀ i : Fin 8, part 18 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 18 (16 + i.val)) := by
  decide +kernel

private theorem corr_18_5_24 : ∀ i : Fin 8, part 18 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 18 (24 + i.val)) := by
  decide +kernel

private theorem corr_18_5_32 : ∀ i : Fin 6, part 18 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 18 (32 + i.val)) := by
  decide +kernel

private theorem corr_18_5 : ∀ i : ℕ, i < 38 → part 18 5 i = sumWindow (5 * width) (chunkLen n 5) (term 18 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_18_5_0) corr_18_5_8) corr_18_5_16) corr_18_5_24) corr_18_5_32

private theorem corr_18_6_0 : ∀ i : Fin 8, part 18 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 18 i.val) := by
  decide +kernel

private theorem corr_18_6_8 : ∀ i : Fin 8, part 18 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 18 (8 + i.val)) := by
  decide +kernel

private theorem corr_18_6_16 : ∀ i : Fin 8, part 18 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 18 (16 + i.val)) := by
  decide +kernel

private theorem corr_18_6_24 : ∀ i : Fin 8, part 18 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 18 (24 + i.val)) := by
  decide +kernel

private theorem corr_18_6_32 : ∀ i : Fin 6, part 18 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 18 (32 + i.val)) := by
  decide +kernel

private theorem corr_18_6 : ∀ i : ℕ, i < 38 → part 18 6 i = sumWindow (6 * width) (chunkLen n 6) (term 18 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_18_6_0) corr_18_6_8) corr_18_6_16) corr_18_6_24) corr_18_6_32

private theorem corr_18_7_0 : ∀ i : Fin 8, part 18 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 18 i.val) := by
  decide +kernel

private theorem corr_18_7_8 : ∀ i : Fin 8, part 18 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 18 (8 + i.val)) := by
  decide +kernel

private theorem corr_18_7_16 : ∀ i : Fin 8, part 18 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 18 (16 + i.val)) := by
  decide +kernel

private theorem corr_18_7_24 : ∀ i : Fin 8, part 18 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 18 (24 + i.val)) := by
  decide +kernel

private theorem corr_18_7_32 : ∀ i : Fin 6, part 18 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 18 (32 + i.val)) := by
  decide +kernel

private theorem corr_18_7 : ∀ i : ℕ, i < 38 → part 18 7 i = sumWindow (7 * width) (chunkLen n 7) (term 18 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_18_7_0) corr_18_7_8) corr_18_7_16) corr_18_7_24) corr_18_7_32

private theorem corr_18_8_0 : ∀ i : Fin 8, part 18 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 18 i.val) := by
  decide +kernel

private theorem corr_18_8_8 : ∀ i : Fin 8, part 18 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 18 (8 + i.val)) := by
  decide +kernel

private theorem corr_18_8_16 : ∀ i : Fin 8, part 18 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 18 (16 + i.val)) := by
  decide +kernel

private theorem corr_18_8_24 : ∀ i : Fin 8, part 18 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 18 (24 + i.val)) := by
  decide +kernel

private theorem corr_18_8_32 : ∀ i : Fin 6, part 18 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 18 (32 + i.val)) := by
  decide +kernel

private theorem corr_18_8 : ∀ i : ℕ, i < 38 → part 18 8 i = sumWindow (8 * width) (chunkLen n 8) (term 18 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_18_8_0) corr_18_8_8) corr_18_8_16) corr_18_8_24) corr_18_8_32

private theorem corr_18_9_0 : ∀ i : Fin 8, part 18 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 18 i.val) := by
  decide +kernel

private theorem corr_18_9_8 : ∀ i : Fin 8, part 18 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 18 (8 + i.val)) := by
  decide +kernel

private theorem corr_18_9_16 : ∀ i : Fin 8, part 18 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 18 (16 + i.val)) := by
  decide +kernel

private theorem corr_18_9_24 : ∀ i : Fin 8, part 18 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 18 (24 + i.val)) := by
  decide +kernel

private theorem corr_18_9_32 : ∀ i : Fin 6, part 18 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 18 (32 + i.val)) := by
  decide +kernel

private theorem corr_18_9 : ∀ i : ℕ, i < 38 → part 18 9 i = sumWindow (9 * width) (chunkLen n 9) (term 18 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_18_9_0) corr_18_9_8) corr_18_9_16) corr_18_9_24) corr_18_9_32

theorem corr_18 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 18 b slot = sumWindow (b * width) (chunkLen n b) (term 18 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_18_0) corr_18_1) corr_18_2) corr_18_3) corr_18_4) corr_18_5) corr_18_6) corr_18_7) corr_18_8) corr_18_9

private theorem total_18_0 : ∀ i : Fin 8, correlationAt 18 i.val = sumChunks n (fun b => part 18 b i.val) := by
  decide +kernel

private theorem total_18_8 : ∀ i : Fin 8, correlationAt 18 (8 + i.val) = sumChunks n (fun b => part 18 b (8 + i.val)) := by
  decide +kernel

private theorem total_18_16 : ∀ i : Fin 8, correlationAt 18 (16 + i.val) = sumChunks n (fun b => part 18 b (16 + i.val)) := by
  decide +kernel

private theorem total_18_24 : ∀ i : Fin 8, correlationAt 18 (24 + i.val) = sumChunks n (fun b => part 18 b (24 + i.val)) := by
  decide +kernel

private theorem total_18_32 : ∀ i : Fin 6, correlationAt 18 (32 + i.val) = sumChunks n (fun b => part 18 b (32 + i.val)) := by
  decide +kernel

theorem total_18 : ∀ i : ℕ, i < 38 → correlationAt 18 i = sumChunks n (fun b => part 18 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_18_0) total_18_8) total_18_16) total_18_24) total_18_32

end Chirped73
