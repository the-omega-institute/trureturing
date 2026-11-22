/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73CorrelationBlock5
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Correlations.correlation_spec; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73CorrelationData.correlationAt
   digest: Checked partial and total correlation sums for order-73 block 5. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73CorrelationData

/-! Exact data and kernel checks for the order-73 chirped construction. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Chirped73

open ChirpedFinite

private theorem corr_15_0_0 : ∀ i : Fin 8, part 15 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 15 i.val) := by
  decide +kernel

private theorem corr_15_0_8 : ∀ i : Fin 8, part 15 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 15 (8 + i.val)) := by
  decide +kernel

private theorem corr_15_0_16 : ∀ i : Fin 8, part 15 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 15 (16 + i.val)) := by
  decide +kernel

private theorem corr_15_0_24 : ∀ i : Fin 8, part 15 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 15 (24 + i.val)) := by
  decide +kernel

private theorem corr_15_0_32 : ∀ i : Fin 6, part 15 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 15 (32 + i.val)) := by
  decide +kernel

private theorem corr_15_0 : ∀ i : ℕ, i < 38 → part 15 0 i = sumWindow (0 * width) (chunkLen n 0) (term 15 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_15_0_0) corr_15_0_8) corr_15_0_16) corr_15_0_24) corr_15_0_32

private theorem corr_15_1_0 : ∀ i : Fin 8, part 15 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 15 i.val) := by
  decide +kernel

private theorem corr_15_1_8 : ∀ i : Fin 8, part 15 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 15 (8 + i.val)) := by
  decide +kernel

private theorem corr_15_1_16 : ∀ i : Fin 8, part 15 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 15 (16 + i.val)) := by
  decide +kernel

private theorem corr_15_1_24 : ∀ i : Fin 8, part 15 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 15 (24 + i.val)) := by
  decide +kernel

private theorem corr_15_1_32 : ∀ i : Fin 6, part 15 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 15 (32 + i.val)) := by
  decide +kernel

private theorem corr_15_1 : ∀ i : ℕ, i < 38 → part 15 1 i = sumWindow (1 * width) (chunkLen n 1) (term 15 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_15_1_0) corr_15_1_8) corr_15_1_16) corr_15_1_24) corr_15_1_32

private theorem corr_15_2_0 : ∀ i : Fin 8, part 15 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 15 i.val) := by
  decide +kernel

private theorem corr_15_2_8 : ∀ i : Fin 8, part 15 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 15 (8 + i.val)) := by
  decide +kernel

private theorem corr_15_2_16 : ∀ i : Fin 8, part 15 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 15 (16 + i.val)) := by
  decide +kernel

private theorem corr_15_2_24 : ∀ i : Fin 8, part 15 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 15 (24 + i.val)) := by
  decide +kernel

private theorem corr_15_2_32 : ∀ i : Fin 6, part 15 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 15 (32 + i.val)) := by
  decide +kernel

private theorem corr_15_2 : ∀ i : ℕ, i < 38 → part 15 2 i = sumWindow (2 * width) (chunkLen n 2) (term 15 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_15_2_0) corr_15_2_8) corr_15_2_16) corr_15_2_24) corr_15_2_32

private theorem corr_15_3_0 : ∀ i : Fin 8, part 15 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 15 i.val) := by
  decide +kernel

private theorem corr_15_3_8 : ∀ i : Fin 8, part 15 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 15 (8 + i.val)) := by
  decide +kernel

private theorem corr_15_3_16 : ∀ i : Fin 8, part 15 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 15 (16 + i.val)) := by
  decide +kernel

private theorem corr_15_3_24 : ∀ i : Fin 8, part 15 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 15 (24 + i.val)) := by
  decide +kernel

private theorem corr_15_3_32 : ∀ i : Fin 6, part 15 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 15 (32 + i.val)) := by
  decide +kernel

private theorem corr_15_3 : ∀ i : ℕ, i < 38 → part 15 3 i = sumWindow (3 * width) (chunkLen n 3) (term 15 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_15_3_0) corr_15_3_8) corr_15_3_16) corr_15_3_24) corr_15_3_32

private theorem corr_15_4_0 : ∀ i : Fin 8, part 15 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 15 i.val) := by
  decide +kernel

private theorem corr_15_4_8 : ∀ i : Fin 8, part 15 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 15 (8 + i.val)) := by
  decide +kernel

private theorem corr_15_4_16 : ∀ i : Fin 8, part 15 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 15 (16 + i.val)) := by
  decide +kernel

private theorem corr_15_4_24 : ∀ i : Fin 8, part 15 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 15 (24 + i.val)) := by
  decide +kernel

private theorem corr_15_4_32 : ∀ i : Fin 6, part 15 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 15 (32 + i.val)) := by
  decide +kernel

private theorem corr_15_4 : ∀ i : ℕ, i < 38 → part 15 4 i = sumWindow (4 * width) (chunkLen n 4) (term 15 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_15_4_0) corr_15_4_8) corr_15_4_16) corr_15_4_24) corr_15_4_32

private theorem corr_15_5_0 : ∀ i : Fin 8, part 15 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 15 i.val) := by
  decide +kernel

private theorem corr_15_5_8 : ∀ i : Fin 8, part 15 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 15 (8 + i.val)) := by
  decide +kernel

private theorem corr_15_5_16 : ∀ i : Fin 8, part 15 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 15 (16 + i.val)) := by
  decide +kernel

private theorem corr_15_5_24 : ∀ i : Fin 8, part 15 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 15 (24 + i.val)) := by
  decide +kernel

private theorem corr_15_5_32 : ∀ i : Fin 6, part 15 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 15 (32 + i.val)) := by
  decide +kernel

private theorem corr_15_5 : ∀ i : ℕ, i < 38 → part 15 5 i = sumWindow (5 * width) (chunkLen n 5) (term 15 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_15_5_0) corr_15_5_8) corr_15_5_16) corr_15_5_24) corr_15_5_32

private theorem corr_15_6_0 : ∀ i : Fin 8, part 15 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 15 i.val) := by
  decide +kernel

private theorem corr_15_6_8 : ∀ i : Fin 8, part 15 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 15 (8 + i.val)) := by
  decide +kernel

private theorem corr_15_6_16 : ∀ i : Fin 8, part 15 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 15 (16 + i.val)) := by
  decide +kernel

private theorem corr_15_6_24 : ∀ i : Fin 8, part 15 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 15 (24 + i.val)) := by
  decide +kernel

private theorem corr_15_6_32 : ∀ i : Fin 6, part 15 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 15 (32 + i.val)) := by
  decide +kernel

private theorem corr_15_6 : ∀ i : ℕ, i < 38 → part 15 6 i = sumWindow (6 * width) (chunkLen n 6) (term 15 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_15_6_0) corr_15_6_8) corr_15_6_16) corr_15_6_24) corr_15_6_32

private theorem corr_15_7_0 : ∀ i : Fin 8, part 15 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 15 i.val) := by
  decide +kernel

private theorem corr_15_7_8 : ∀ i : Fin 8, part 15 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 15 (8 + i.val)) := by
  decide +kernel

private theorem corr_15_7_16 : ∀ i : Fin 8, part 15 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 15 (16 + i.val)) := by
  decide +kernel

private theorem corr_15_7_24 : ∀ i : Fin 8, part 15 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 15 (24 + i.val)) := by
  decide +kernel

private theorem corr_15_7_32 : ∀ i : Fin 6, part 15 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 15 (32 + i.val)) := by
  decide +kernel

private theorem corr_15_7 : ∀ i : ℕ, i < 38 → part 15 7 i = sumWindow (7 * width) (chunkLen n 7) (term 15 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_15_7_0) corr_15_7_8) corr_15_7_16) corr_15_7_24) corr_15_7_32

private theorem corr_15_8_0 : ∀ i : Fin 8, part 15 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 15 i.val) := by
  decide +kernel

private theorem corr_15_8_8 : ∀ i : Fin 8, part 15 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 15 (8 + i.val)) := by
  decide +kernel

private theorem corr_15_8_16 : ∀ i : Fin 8, part 15 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 15 (16 + i.val)) := by
  decide +kernel

private theorem corr_15_8_24 : ∀ i : Fin 8, part 15 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 15 (24 + i.val)) := by
  decide +kernel

private theorem corr_15_8_32 : ∀ i : Fin 6, part 15 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 15 (32 + i.val)) := by
  decide +kernel

private theorem corr_15_8 : ∀ i : ℕ, i < 38 → part 15 8 i = sumWindow (8 * width) (chunkLen n 8) (term 15 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_15_8_0) corr_15_8_8) corr_15_8_16) corr_15_8_24) corr_15_8_32

private theorem corr_15_9_0 : ∀ i : Fin 8, part 15 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 15 i.val) := by
  decide +kernel

private theorem corr_15_9_8 : ∀ i : Fin 8, part 15 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 15 (8 + i.val)) := by
  decide +kernel

private theorem corr_15_9_16 : ∀ i : Fin 8, part 15 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 15 (16 + i.val)) := by
  decide +kernel

private theorem corr_15_9_24 : ∀ i : Fin 8, part 15 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 15 (24 + i.val)) := by
  decide +kernel

private theorem corr_15_9_32 : ∀ i : Fin 6, part 15 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 15 (32 + i.val)) := by
  decide +kernel

private theorem corr_15_9 : ∀ i : ℕ, i < 38 → part 15 9 i = sumWindow (9 * width) (chunkLen n 9) (term 15 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_15_9_0) corr_15_9_8) corr_15_9_16) corr_15_9_24) corr_15_9_32

theorem corr_15 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 15 b slot = sumWindow (b * width) (chunkLen n b) (term 15 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_15_0) corr_15_1) corr_15_2) corr_15_3) corr_15_4) corr_15_5) corr_15_6) corr_15_7) corr_15_8) corr_15_9

private theorem total_15_0 : ∀ i : Fin 8, correlationAt 15 i.val = sumChunks n (fun b => part 15 b i.val) := by
  decide +kernel

private theorem total_15_8 : ∀ i : Fin 8, correlationAt 15 (8 + i.val) = sumChunks n (fun b => part 15 b (8 + i.val)) := by
  decide +kernel

private theorem total_15_16 : ∀ i : Fin 8, correlationAt 15 (16 + i.val) = sumChunks n (fun b => part 15 b (16 + i.val)) := by
  decide +kernel

private theorem total_15_24 : ∀ i : Fin 8, correlationAt 15 (24 + i.val) = sumChunks n (fun b => part 15 b (24 + i.val)) := by
  decide +kernel

private theorem total_15_32 : ∀ i : Fin 6, correlationAt 15 (32 + i.val) = sumChunks n (fun b => part 15 b (32 + i.val)) := by
  decide +kernel

theorem total_15 : ∀ i : ℕ, i < 38 → correlationAt 15 i = sumChunks n (fun b => part 15 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_15_0) total_15_8) total_15_16) total_15_24) total_15_32

private theorem corr_16_0_0 : ∀ i : Fin 8, part 16 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 16 i.val) := by
  decide +kernel

private theorem corr_16_0_8 : ∀ i : Fin 8, part 16 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 16 (8 + i.val)) := by
  decide +kernel

private theorem corr_16_0_16 : ∀ i : Fin 8, part 16 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 16 (16 + i.val)) := by
  decide +kernel

private theorem corr_16_0_24 : ∀ i : Fin 8, part 16 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 16 (24 + i.val)) := by
  decide +kernel

private theorem corr_16_0_32 : ∀ i : Fin 6, part 16 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 16 (32 + i.val)) := by
  decide +kernel

private theorem corr_16_0 : ∀ i : ℕ, i < 38 → part 16 0 i = sumWindow (0 * width) (chunkLen n 0) (term 16 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_16_0_0) corr_16_0_8) corr_16_0_16) corr_16_0_24) corr_16_0_32

private theorem corr_16_1_0 : ∀ i : Fin 8, part 16 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 16 i.val) := by
  decide +kernel

private theorem corr_16_1_8 : ∀ i : Fin 8, part 16 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 16 (8 + i.val)) := by
  decide +kernel

private theorem corr_16_1_16 : ∀ i : Fin 8, part 16 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 16 (16 + i.val)) := by
  decide +kernel

private theorem corr_16_1_24 : ∀ i : Fin 8, part 16 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 16 (24 + i.val)) := by
  decide +kernel

private theorem corr_16_1_32 : ∀ i : Fin 6, part 16 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 16 (32 + i.val)) := by
  decide +kernel

private theorem corr_16_1 : ∀ i : ℕ, i < 38 → part 16 1 i = sumWindow (1 * width) (chunkLen n 1) (term 16 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_16_1_0) corr_16_1_8) corr_16_1_16) corr_16_1_24) corr_16_1_32

private theorem corr_16_2_0 : ∀ i : Fin 8, part 16 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 16 i.val) := by
  decide +kernel

private theorem corr_16_2_8 : ∀ i : Fin 8, part 16 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 16 (8 + i.val)) := by
  decide +kernel

private theorem corr_16_2_16 : ∀ i : Fin 8, part 16 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 16 (16 + i.val)) := by
  decide +kernel

private theorem corr_16_2_24 : ∀ i : Fin 8, part 16 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 16 (24 + i.val)) := by
  decide +kernel

private theorem corr_16_2_32 : ∀ i : Fin 6, part 16 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 16 (32 + i.val)) := by
  decide +kernel

private theorem corr_16_2 : ∀ i : ℕ, i < 38 → part 16 2 i = sumWindow (2 * width) (chunkLen n 2) (term 16 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_16_2_0) corr_16_2_8) corr_16_2_16) corr_16_2_24) corr_16_2_32

private theorem corr_16_3_0 : ∀ i : Fin 8, part 16 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 16 i.val) := by
  decide +kernel

private theorem corr_16_3_8 : ∀ i : Fin 8, part 16 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 16 (8 + i.val)) := by
  decide +kernel

private theorem corr_16_3_16 : ∀ i : Fin 8, part 16 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 16 (16 + i.val)) := by
  decide +kernel

private theorem corr_16_3_24 : ∀ i : Fin 8, part 16 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 16 (24 + i.val)) := by
  decide +kernel

private theorem corr_16_3_32 : ∀ i : Fin 6, part 16 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 16 (32 + i.val)) := by
  decide +kernel

private theorem corr_16_3 : ∀ i : ℕ, i < 38 → part 16 3 i = sumWindow (3 * width) (chunkLen n 3) (term 16 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_16_3_0) corr_16_3_8) corr_16_3_16) corr_16_3_24) corr_16_3_32

private theorem corr_16_4_0 : ∀ i : Fin 8, part 16 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 16 i.val) := by
  decide +kernel

private theorem corr_16_4_8 : ∀ i : Fin 8, part 16 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 16 (8 + i.val)) := by
  decide +kernel

private theorem corr_16_4_16 : ∀ i : Fin 8, part 16 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 16 (16 + i.val)) := by
  decide +kernel

private theorem corr_16_4_24 : ∀ i : Fin 8, part 16 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 16 (24 + i.val)) := by
  decide +kernel

private theorem corr_16_4_32 : ∀ i : Fin 6, part 16 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 16 (32 + i.val)) := by
  decide +kernel

private theorem corr_16_4 : ∀ i : ℕ, i < 38 → part 16 4 i = sumWindow (4 * width) (chunkLen n 4) (term 16 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_16_4_0) corr_16_4_8) corr_16_4_16) corr_16_4_24) corr_16_4_32

private theorem corr_16_5_0 : ∀ i : Fin 8, part 16 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 16 i.val) := by
  decide +kernel

private theorem corr_16_5_8 : ∀ i : Fin 8, part 16 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 16 (8 + i.val)) := by
  decide +kernel

private theorem corr_16_5_16 : ∀ i : Fin 8, part 16 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 16 (16 + i.val)) := by
  decide +kernel

private theorem corr_16_5_24 : ∀ i : Fin 8, part 16 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 16 (24 + i.val)) := by
  decide +kernel

private theorem corr_16_5_32 : ∀ i : Fin 6, part 16 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 16 (32 + i.val)) := by
  decide +kernel

private theorem corr_16_5 : ∀ i : ℕ, i < 38 → part 16 5 i = sumWindow (5 * width) (chunkLen n 5) (term 16 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_16_5_0) corr_16_5_8) corr_16_5_16) corr_16_5_24) corr_16_5_32

private theorem corr_16_6_0 : ∀ i : Fin 8, part 16 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 16 i.val) := by
  decide +kernel

private theorem corr_16_6_8 : ∀ i : Fin 8, part 16 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 16 (8 + i.val)) := by
  decide +kernel

private theorem corr_16_6_16 : ∀ i : Fin 8, part 16 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 16 (16 + i.val)) := by
  decide +kernel

private theorem corr_16_6_24 : ∀ i : Fin 8, part 16 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 16 (24 + i.val)) := by
  decide +kernel

private theorem corr_16_6_32 : ∀ i : Fin 6, part 16 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 16 (32 + i.val)) := by
  decide +kernel

private theorem corr_16_6 : ∀ i : ℕ, i < 38 → part 16 6 i = sumWindow (6 * width) (chunkLen n 6) (term 16 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_16_6_0) corr_16_6_8) corr_16_6_16) corr_16_6_24) corr_16_6_32

private theorem corr_16_7_0 : ∀ i : Fin 8, part 16 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 16 i.val) := by
  decide +kernel

private theorem corr_16_7_8 : ∀ i : Fin 8, part 16 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 16 (8 + i.val)) := by
  decide +kernel

private theorem corr_16_7_16 : ∀ i : Fin 8, part 16 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 16 (16 + i.val)) := by
  decide +kernel

private theorem corr_16_7_24 : ∀ i : Fin 8, part 16 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 16 (24 + i.val)) := by
  decide +kernel

private theorem corr_16_7_32 : ∀ i : Fin 6, part 16 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 16 (32 + i.val)) := by
  decide +kernel

private theorem corr_16_7 : ∀ i : ℕ, i < 38 → part 16 7 i = sumWindow (7 * width) (chunkLen n 7) (term 16 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_16_7_0) corr_16_7_8) corr_16_7_16) corr_16_7_24) corr_16_7_32

private theorem corr_16_8_0 : ∀ i : Fin 8, part 16 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 16 i.val) := by
  decide +kernel

private theorem corr_16_8_8 : ∀ i : Fin 8, part 16 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 16 (8 + i.val)) := by
  decide +kernel

private theorem corr_16_8_16 : ∀ i : Fin 8, part 16 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 16 (16 + i.val)) := by
  decide +kernel

private theorem corr_16_8_24 : ∀ i : Fin 8, part 16 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 16 (24 + i.val)) := by
  decide +kernel

private theorem corr_16_8_32 : ∀ i : Fin 6, part 16 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 16 (32 + i.val)) := by
  decide +kernel

private theorem corr_16_8 : ∀ i : ℕ, i < 38 → part 16 8 i = sumWindow (8 * width) (chunkLen n 8) (term 16 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_16_8_0) corr_16_8_8) corr_16_8_16) corr_16_8_24) corr_16_8_32

private theorem corr_16_9_0 : ∀ i : Fin 8, part 16 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 16 i.val) := by
  decide +kernel

private theorem corr_16_9_8 : ∀ i : Fin 8, part 16 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 16 (8 + i.val)) := by
  decide +kernel

private theorem corr_16_9_16 : ∀ i : Fin 8, part 16 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 16 (16 + i.val)) := by
  decide +kernel

private theorem corr_16_9_24 : ∀ i : Fin 8, part 16 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 16 (24 + i.val)) := by
  decide +kernel

private theorem corr_16_9_32 : ∀ i : Fin 6, part 16 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 16 (32 + i.val)) := by
  decide +kernel

private theorem corr_16_9 : ∀ i : ℕ, i < 38 → part 16 9 i = sumWindow (9 * width) (chunkLen n 9) (term 16 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_16_9_0) corr_16_9_8) corr_16_9_16) corr_16_9_24) corr_16_9_32

theorem corr_16 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 16 b slot = sumWindow (b * width) (chunkLen n b) (term 16 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_16_0) corr_16_1) corr_16_2) corr_16_3) corr_16_4) corr_16_5) corr_16_6) corr_16_7) corr_16_8) corr_16_9

private theorem total_16_0 : ∀ i : Fin 8, correlationAt 16 i.val = sumChunks n (fun b => part 16 b i.val) := by
  decide +kernel

private theorem total_16_8 : ∀ i : Fin 8, correlationAt 16 (8 + i.val) = sumChunks n (fun b => part 16 b (8 + i.val)) := by
  decide +kernel

private theorem total_16_16 : ∀ i : Fin 8, correlationAt 16 (16 + i.val) = sumChunks n (fun b => part 16 b (16 + i.val)) := by
  decide +kernel

private theorem total_16_24 : ∀ i : Fin 8, correlationAt 16 (24 + i.val) = sumChunks n (fun b => part 16 b (24 + i.val)) := by
  decide +kernel

private theorem total_16_32 : ∀ i : Fin 6, correlationAt 16 (32 + i.val) = sumChunks n (fun b => part 16 b (32 + i.val)) := by
  decide +kernel

theorem total_16 : ∀ i : ℕ, i < 38 → correlationAt 16 i = sumChunks n (fun b => part 16 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_16_0) total_16_8) total_16_16) total_16_24) total_16_32

private theorem corr_17_0_0 : ∀ i : Fin 8, part 17 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 17 i.val) := by
  decide +kernel

private theorem corr_17_0_8 : ∀ i : Fin 8, part 17 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 17 (8 + i.val)) := by
  decide +kernel

private theorem corr_17_0_16 : ∀ i : Fin 8, part 17 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 17 (16 + i.val)) := by
  decide +kernel

private theorem corr_17_0_24 : ∀ i : Fin 8, part 17 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 17 (24 + i.val)) := by
  decide +kernel

private theorem corr_17_0_32 : ∀ i : Fin 6, part 17 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 17 (32 + i.val)) := by
  decide +kernel

private theorem corr_17_0 : ∀ i : ℕ, i < 38 → part 17 0 i = sumWindow (0 * width) (chunkLen n 0) (term 17 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_17_0_0) corr_17_0_8) corr_17_0_16) corr_17_0_24) corr_17_0_32

private theorem corr_17_1_0 : ∀ i : Fin 8, part 17 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 17 i.val) := by
  decide +kernel

private theorem corr_17_1_8 : ∀ i : Fin 8, part 17 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 17 (8 + i.val)) := by
  decide +kernel

private theorem corr_17_1_16 : ∀ i : Fin 8, part 17 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 17 (16 + i.val)) := by
  decide +kernel

private theorem corr_17_1_24 : ∀ i : Fin 8, part 17 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 17 (24 + i.val)) := by
  decide +kernel

private theorem corr_17_1_32 : ∀ i : Fin 6, part 17 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 17 (32 + i.val)) := by
  decide +kernel

private theorem corr_17_1 : ∀ i : ℕ, i < 38 → part 17 1 i = sumWindow (1 * width) (chunkLen n 1) (term 17 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_17_1_0) corr_17_1_8) corr_17_1_16) corr_17_1_24) corr_17_1_32

private theorem corr_17_2_0 : ∀ i : Fin 8, part 17 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 17 i.val) := by
  decide +kernel

private theorem corr_17_2_8 : ∀ i : Fin 8, part 17 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 17 (8 + i.val)) := by
  decide +kernel

private theorem corr_17_2_16 : ∀ i : Fin 8, part 17 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 17 (16 + i.val)) := by
  decide +kernel

private theorem corr_17_2_24 : ∀ i : Fin 8, part 17 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 17 (24 + i.val)) := by
  decide +kernel

private theorem corr_17_2_32 : ∀ i : Fin 6, part 17 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 17 (32 + i.val)) := by
  decide +kernel

private theorem corr_17_2 : ∀ i : ℕ, i < 38 → part 17 2 i = sumWindow (2 * width) (chunkLen n 2) (term 17 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_17_2_0) corr_17_2_8) corr_17_2_16) corr_17_2_24) corr_17_2_32

private theorem corr_17_3_0 : ∀ i : Fin 8, part 17 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 17 i.val) := by
  decide +kernel

private theorem corr_17_3_8 : ∀ i : Fin 8, part 17 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 17 (8 + i.val)) := by
  decide +kernel

private theorem corr_17_3_16 : ∀ i : Fin 8, part 17 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 17 (16 + i.val)) := by
  decide +kernel

private theorem corr_17_3_24 : ∀ i : Fin 8, part 17 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 17 (24 + i.val)) := by
  decide +kernel

private theorem corr_17_3_32 : ∀ i : Fin 6, part 17 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 17 (32 + i.val)) := by
  decide +kernel

private theorem corr_17_3 : ∀ i : ℕ, i < 38 → part 17 3 i = sumWindow (3 * width) (chunkLen n 3) (term 17 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_17_3_0) corr_17_3_8) corr_17_3_16) corr_17_3_24) corr_17_3_32

private theorem corr_17_4_0 : ∀ i : Fin 8, part 17 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 17 i.val) := by
  decide +kernel

private theorem corr_17_4_8 : ∀ i : Fin 8, part 17 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 17 (8 + i.val)) := by
  decide +kernel

private theorem corr_17_4_16 : ∀ i : Fin 8, part 17 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 17 (16 + i.val)) := by
  decide +kernel

private theorem corr_17_4_24 : ∀ i : Fin 8, part 17 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 17 (24 + i.val)) := by
  decide +kernel

private theorem corr_17_4_32 : ∀ i : Fin 6, part 17 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 17 (32 + i.val)) := by
  decide +kernel

private theorem corr_17_4 : ∀ i : ℕ, i < 38 → part 17 4 i = sumWindow (4 * width) (chunkLen n 4) (term 17 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_17_4_0) corr_17_4_8) corr_17_4_16) corr_17_4_24) corr_17_4_32

private theorem corr_17_5_0 : ∀ i : Fin 8, part 17 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 17 i.val) := by
  decide +kernel

private theorem corr_17_5_8 : ∀ i : Fin 8, part 17 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 17 (8 + i.val)) := by
  decide +kernel

private theorem corr_17_5_16 : ∀ i : Fin 8, part 17 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 17 (16 + i.val)) := by
  decide +kernel

private theorem corr_17_5_24 : ∀ i : Fin 8, part 17 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 17 (24 + i.val)) := by
  decide +kernel

private theorem corr_17_5_32 : ∀ i : Fin 6, part 17 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 17 (32 + i.val)) := by
  decide +kernel

private theorem corr_17_5 : ∀ i : ℕ, i < 38 → part 17 5 i = sumWindow (5 * width) (chunkLen n 5) (term 17 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_17_5_0) corr_17_5_8) corr_17_5_16) corr_17_5_24) corr_17_5_32

private theorem corr_17_6_0 : ∀ i : Fin 8, part 17 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 17 i.val) := by
  decide +kernel

private theorem corr_17_6_8 : ∀ i : Fin 8, part 17 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 17 (8 + i.val)) := by
  decide +kernel

private theorem corr_17_6_16 : ∀ i : Fin 8, part 17 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 17 (16 + i.val)) := by
  decide +kernel

private theorem corr_17_6_24 : ∀ i : Fin 8, part 17 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 17 (24 + i.val)) := by
  decide +kernel

private theorem corr_17_6_32 : ∀ i : Fin 6, part 17 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 17 (32 + i.val)) := by
  decide +kernel

private theorem corr_17_6 : ∀ i : ℕ, i < 38 → part 17 6 i = sumWindow (6 * width) (chunkLen n 6) (term 17 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_17_6_0) corr_17_6_8) corr_17_6_16) corr_17_6_24) corr_17_6_32

private theorem corr_17_7_0 : ∀ i : Fin 8, part 17 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 17 i.val) := by
  decide +kernel

private theorem corr_17_7_8 : ∀ i : Fin 8, part 17 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 17 (8 + i.val)) := by
  decide +kernel

private theorem corr_17_7_16 : ∀ i : Fin 8, part 17 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 17 (16 + i.val)) := by
  decide +kernel

private theorem corr_17_7_24 : ∀ i : Fin 8, part 17 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 17 (24 + i.val)) := by
  decide +kernel

private theorem corr_17_7_32 : ∀ i : Fin 6, part 17 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 17 (32 + i.val)) := by
  decide +kernel

private theorem corr_17_7 : ∀ i : ℕ, i < 38 → part 17 7 i = sumWindow (7 * width) (chunkLen n 7) (term 17 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_17_7_0) corr_17_7_8) corr_17_7_16) corr_17_7_24) corr_17_7_32

private theorem corr_17_8_0 : ∀ i : Fin 8, part 17 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 17 i.val) := by
  decide +kernel

private theorem corr_17_8_8 : ∀ i : Fin 8, part 17 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 17 (8 + i.val)) := by
  decide +kernel

private theorem corr_17_8_16 : ∀ i : Fin 8, part 17 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 17 (16 + i.val)) := by
  decide +kernel

private theorem corr_17_8_24 : ∀ i : Fin 8, part 17 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 17 (24 + i.val)) := by
  decide +kernel

private theorem corr_17_8_32 : ∀ i : Fin 6, part 17 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 17 (32 + i.val)) := by
  decide +kernel

private theorem corr_17_8 : ∀ i : ℕ, i < 38 → part 17 8 i = sumWindow (8 * width) (chunkLen n 8) (term 17 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_17_8_0) corr_17_8_8) corr_17_8_16) corr_17_8_24) corr_17_8_32

private theorem corr_17_9_0 : ∀ i : Fin 8, part 17 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 17 i.val) := by
  decide +kernel

private theorem corr_17_9_8 : ∀ i : Fin 8, part 17 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 17 (8 + i.val)) := by
  decide +kernel

private theorem corr_17_9_16 : ∀ i : Fin 8, part 17 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 17 (16 + i.val)) := by
  decide +kernel

private theorem corr_17_9_24 : ∀ i : Fin 8, part 17 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 17 (24 + i.val)) := by
  decide +kernel

private theorem corr_17_9_32 : ∀ i : Fin 6, part 17 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 17 (32 + i.val)) := by
  decide +kernel

private theorem corr_17_9 : ∀ i : ℕ, i < 38 → part 17 9 i = sumWindow (9 * width) (chunkLen n 9) (term 17 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_17_9_0) corr_17_9_8) corr_17_9_16) corr_17_9_24) corr_17_9_32

theorem corr_17 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 17 b slot = sumWindow (b * width) (chunkLen n b) (term 17 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_17_0) corr_17_1) corr_17_2) corr_17_3) corr_17_4) corr_17_5) corr_17_6) corr_17_7) corr_17_8) corr_17_9

private theorem total_17_0 : ∀ i : Fin 8, correlationAt 17 i.val = sumChunks n (fun b => part 17 b i.val) := by
  decide +kernel

private theorem total_17_8 : ∀ i : Fin 8, correlationAt 17 (8 + i.val) = sumChunks n (fun b => part 17 b (8 + i.val)) := by
  decide +kernel

private theorem total_17_16 : ∀ i : Fin 8, correlationAt 17 (16 + i.val) = sumChunks n (fun b => part 17 b (16 + i.val)) := by
  decide +kernel

private theorem total_17_24 : ∀ i : Fin 8, correlationAt 17 (24 + i.val) = sumChunks n (fun b => part 17 b (24 + i.val)) := by
  decide +kernel

private theorem total_17_32 : ∀ i : Fin 6, correlationAt 17 (32 + i.val) = sumChunks n (fun b => part 17 b (32 + i.val)) := by
  decide +kernel

theorem total_17 : ∀ i : ℕ, i < 38 → correlationAt 17 i = sumChunks n (fun b => part 17 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_17_0) total_17_8) total_17_16) total_17_24) total_17_32

end Chirped73
