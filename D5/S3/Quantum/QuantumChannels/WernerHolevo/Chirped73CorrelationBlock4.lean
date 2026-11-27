/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73CorrelationBlock4
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Correlations.correlation_spec; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73CorrelationData.correlationAt
   digest: Checked partial and total correlation sums for order-73 block 4. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73CorrelationData

/-! Exact data and kernel checks for the order-73 chirped construction. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Chirped73

open ChirpedFinite

private theorem corr_12_0_0 : ∀ i : Fin 8, part 12 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 12 i.val) := by
  decide +kernel

private theorem corr_12_0_8 : ∀ i : Fin 8, part 12 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 12 (8 + i.val)) := by
  decide +kernel

private theorem corr_12_0_16 : ∀ i : Fin 8, part 12 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 12 (16 + i.val)) := by
  decide +kernel

private theorem corr_12_0_24 : ∀ i : Fin 8, part 12 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 12 (24 + i.val)) := by
  decide +kernel

private theorem corr_12_0_32 : ∀ i : Fin 6, part 12 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 12 (32 + i.val)) := by
  decide +kernel

private theorem corr_12_0 : ∀ i : ℕ, i < 38 → part 12 0 i = sumWindow (0 * width) (chunkLen n 0) (term 12 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_12_0_0) corr_12_0_8) corr_12_0_16) corr_12_0_24) corr_12_0_32

private theorem corr_12_1_0 : ∀ i : Fin 8, part 12 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 12 i.val) := by
  decide +kernel

private theorem corr_12_1_8 : ∀ i : Fin 8, part 12 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 12 (8 + i.val)) := by
  decide +kernel

private theorem corr_12_1_16 : ∀ i : Fin 8, part 12 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 12 (16 + i.val)) := by
  decide +kernel

private theorem corr_12_1_24 : ∀ i : Fin 8, part 12 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 12 (24 + i.val)) := by
  decide +kernel

private theorem corr_12_1_32 : ∀ i : Fin 6, part 12 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 12 (32 + i.val)) := by
  decide +kernel

private theorem corr_12_1 : ∀ i : ℕ, i < 38 → part 12 1 i = sumWindow (1 * width) (chunkLen n 1) (term 12 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_12_1_0) corr_12_1_8) corr_12_1_16) corr_12_1_24) corr_12_1_32

private theorem corr_12_2_0 : ∀ i : Fin 8, part 12 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 12 i.val) := by
  decide +kernel

private theorem corr_12_2_8 : ∀ i : Fin 8, part 12 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 12 (8 + i.val)) := by
  decide +kernel

private theorem corr_12_2_16 : ∀ i : Fin 8, part 12 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 12 (16 + i.val)) := by
  decide +kernel

private theorem corr_12_2_24 : ∀ i : Fin 8, part 12 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 12 (24 + i.val)) := by
  decide +kernel

private theorem corr_12_2_32 : ∀ i : Fin 6, part 12 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 12 (32 + i.val)) := by
  decide +kernel

private theorem corr_12_2 : ∀ i : ℕ, i < 38 → part 12 2 i = sumWindow (2 * width) (chunkLen n 2) (term 12 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_12_2_0) corr_12_2_8) corr_12_2_16) corr_12_2_24) corr_12_2_32

private theorem corr_12_3_0 : ∀ i : Fin 8, part 12 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 12 i.val) := by
  decide +kernel

private theorem corr_12_3_8 : ∀ i : Fin 8, part 12 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 12 (8 + i.val)) := by
  decide +kernel

private theorem corr_12_3_16 : ∀ i : Fin 8, part 12 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 12 (16 + i.val)) := by
  decide +kernel

private theorem corr_12_3_24 : ∀ i : Fin 8, part 12 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 12 (24 + i.val)) := by
  decide +kernel

private theorem corr_12_3_32 : ∀ i : Fin 6, part 12 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 12 (32 + i.val)) := by
  decide +kernel

private theorem corr_12_3 : ∀ i : ℕ, i < 38 → part 12 3 i = sumWindow (3 * width) (chunkLen n 3) (term 12 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_12_3_0) corr_12_3_8) corr_12_3_16) corr_12_3_24) corr_12_3_32

private theorem corr_12_4_0 : ∀ i : Fin 8, part 12 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 12 i.val) := by
  decide +kernel

private theorem corr_12_4_8 : ∀ i : Fin 8, part 12 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 12 (8 + i.val)) := by
  decide +kernel

private theorem corr_12_4_16 : ∀ i : Fin 8, part 12 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 12 (16 + i.val)) := by
  decide +kernel

private theorem corr_12_4_24 : ∀ i : Fin 8, part 12 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 12 (24 + i.val)) := by
  decide +kernel

private theorem corr_12_4_32 : ∀ i : Fin 6, part 12 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 12 (32 + i.val)) := by
  decide +kernel

private theorem corr_12_4 : ∀ i : ℕ, i < 38 → part 12 4 i = sumWindow (4 * width) (chunkLen n 4) (term 12 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_12_4_0) corr_12_4_8) corr_12_4_16) corr_12_4_24) corr_12_4_32

private theorem corr_12_5_0 : ∀ i : Fin 8, part 12 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 12 i.val) := by
  decide +kernel

private theorem corr_12_5_8 : ∀ i : Fin 8, part 12 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 12 (8 + i.val)) := by
  decide +kernel

private theorem corr_12_5_16 : ∀ i : Fin 8, part 12 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 12 (16 + i.val)) := by
  decide +kernel

private theorem corr_12_5_24 : ∀ i : Fin 8, part 12 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 12 (24 + i.val)) := by
  decide +kernel

private theorem corr_12_5_32 : ∀ i : Fin 6, part 12 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 12 (32 + i.val)) := by
  decide +kernel

private theorem corr_12_5 : ∀ i : ℕ, i < 38 → part 12 5 i = sumWindow (5 * width) (chunkLen n 5) (term 12 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_12_5_0) corr_12_5_8) corr_12_5_16) corr_12_5_24) corr_12_5_32

private theorem corr_12_6_0 : ∀ i : Fin 8, part 12 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 12 i.val) := by
  decide +kernel

private theorem corr_12_6_8 : ∀ i : Fin 8, part 12 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 12 (8 + i.val)) := by
  decide +kernel

private theorem corr_12_6_16 : ∀ i : Fin 8, part 12 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 12 (16 + i.val)) := by
  decide +kernel

private theorem corr_12_6_24 : ∀ i : Fin 8, part 12 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 12 (24 + i.val)) := by
  decide +kernel

private theorem corr_12_6_32 : ∀ i : Fin 6, part 12 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 12 (32 + i.val)) := by
  decide +kernel

private theorem corr_12_6 : ∀ i : ℕ, i < 38 → part 12 6 i = sumWindow (6 * width) (chunkLen n 6) (term 12 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_12_6_0) corr_12_6_8) corr_12_6_16) corr_12_6_24) corr_12_6_32

private theorem corr_12_7_0 : ∀ i : Fin 8, part 12 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 12 i.val) := by
  decide +kernel

private theorem corr_12_7_8 : ∀ i : Fin 8, part 12 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 12 (8 + i.val)) := by
  decide +kernel

private theorem corr_12_7_16 : ∀ i : Fin 8, part 12 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 12 (16 + i.val)) := by
  decide +kernel

private theorem corr_12_7_24 : ∀ i : Fin 8, part 12 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 12 (24 + i.val)) := by
  decide +kernel

private theorem corr_12_7_32 : ∀ i : Fin 6, part 12 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 12 (32 + i.val)) := by
  decide +kernel

private theorem corr_12_7 : ∀ i : ℕ, i < 38 → part 12 7 i = sumWindow (7 * width) (chunkLen n 7) (term 12 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_12_7_0) corr_12_7_8) corr_12_7_16) corr_12_7_24) corr_12_7_32

private theorem corr_12_8_0 : ∀ i : Fin 8, part 12 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 12 i.val) := by
  decide +kernel

private theorem corr_12_8_8 : ∀ i : Fin 8, part 12 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 12 (8 + i.val)) := by
  decide +kernel

private theorem corr_12_8_16 : ∀ i : Fin 8, part 12 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 12 (16 + i.val)) := by
  decide +kernel

private theorem corr_12_8_24 : ∀ i : Fin 8, part 12 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 12 (24 + i.val)) := by
  decide +kernel

private theorem corr_12_8_32 : ∀ i : Fin 6, part 12 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 12 (32 + i.val)) := by
  decide +kernel

private theorem corr_12_8 : ∀ i : ℕ, i < 38 → part 12 8 i = sumWindow (8 * width) (chunkLen n 8) (term 12 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_12_8_0) corr_12_8_8) corr_12_8_16) corr_12_8_24) corr_12_8_32

private theorem corr_12_9_0 : ∀ i : Fin 8, part 12 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 12 i.val) := by
  decide +kernel

private theorem corr_12_9_8 : ∀ i : Fin 8, part 12 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 12 (8 + i.val)) := by
  decide +kernel

private theorem corr_12_9_16 : ∀ i : Fin 8, part 12 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 12 (16 + i.val)) := by
  decide +kernel

private theorem corr_12_9_24 : ∀ i : Fin 8, part 12 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 12 (24 + i.val)) := by
  decide +kernel

private theorem corr_12_9_32 : ∀ i : Fin 6, part 12 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 12 (32 + i.val)) := by
  decide +kernel

private theorem corr_12_9 : ∀ i : ℕ, i < 38 → part 12 9 i = sumWindow (9 * width) (chunkLen n 9) (term 12 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_12_9_0) corr_12_9_8) corr_12_9_16) corr_12_9_24) corr_12_9_32

theorem corr_12 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 12 b slot = sumWindow (b * width) (chunkLen n b) (term 12 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_12_0) corr_12_1) corr_12_2) corr_12_3) corr_12_4) corr_12_5) corr_12_6) corr_12_7) corr_12_8) corr_12_9

private theorem total_12_0 : ∀ i : Fin 8, correlationAt 12 i.val = sumChunks n (fun b => part 12 b i.val) := by
  decide +kernel

private theorem total_12_8 : ∀ i : Fin 8, correlationAt 12 (8 + i.val) = sumChunks n (fun b => part 12 b (8 + i.val)) := by
  decide +kernel

private theorem total_12_16 : ∀ i : Fin 8, correlationAt 12 (16 + i.val) = sumChunks n (fun b => part 12 b (16 + i.val)) := by
  decide +kernel

private theorem total_12_24 : ∀ i : Fin 8, correlationAt 12 (24 + i.val) = sumChunks n (fun b => part 12 b (24 + i.val)) := by
  decide +kernel

private theorem total_12_32 : ∀ i : Fin 6, correlationAt 12 (32 + i.val) = sumChunks n (fun b => part 12 b (32 + i.val)) := by
  decide +kernel

theorem total_12 : ∀ i : ℕ, i < 38 → correlationAt 12 i = sumChunks n (fun b => part 12 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_12_0) total_12_8) total_12_16) total_12_24) total_12_32

private theorem corr_13_0_0 : ∀ i : Fin 8, part 13 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 13 i.val) := by
  decide +kernel

private theorem corr_13_0_8 : ∀ i : Fin 8, part 13 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 13 (8 + i.val)) := by
  decide +kernel

private theorem corr_13_0_16 : ∀ i : Fin 8, part 13 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 13 (16 + i.val)) := by
  decide +kernel

private theorem corr_13_0_24 : ∀ i : Fin 8, part 13 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 13 (24 + i.val)) := by
  decide +kernel

private theorem corr_13_0_32 : ∀ i : Fin 6, part 13 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 13 (32 + i.val)) := by
  decide +kernel

private theorem corr_13_0 : ∀ i : ℕ, i < 38 → part 13 0 i = sumWindow (0 * width) (chunkLen n 0) (term 13 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_13_0_0) corr_13_0_8) corr_13_0_16) corr_13_0_24) corr_13_0_32

private theorem corr_13_1_0 : ∀ i : Fin 8, part 13 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 13 i.val) := by
  decide +kernel

private theorem corr_13_1_8 : ∀ i : Fin 8, part 13 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 13 (8 + i.val)) := by
  decide +kernel

private theorem corr_13_1_16 : ∀ i : Fin 8, part 13 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 13 (16 + i.val)) := by
  decide +kernel

private theorem corr_13_1_24 : ∀ i : Fin 8, part 13 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 13 (24 + i.val)) := by
  decide +kernel

private theorem corr_13_1_32 : ∀ i : Fin 6, part 13 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 13 (32 + i.val)) := by
  decide +kernel

private theorem corr_13_1 : ∀ i : ℕ, i < 38 → part 13 1 i = sumWindow (1 * width) (chunkLen n 1) (term 13 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_13_1_0) corr_13_1_8) corr_13_1_16) corr_13_1_24) corr_13_1_32

private theorem corr_13_2_0 : ∀ i : Fin 8, part 13 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 13 i.val) := by
  decide +kernel

private theorem corr_13_2_8 : ∀ i : Fin 8, part 13 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 13 (8 + i.val)) := by
  decide +kernel

private theorem corr_13_2_16 : ∀ i : Fin 8, part 13 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 13 (16 + i.val)) := by
  decide +kernel

private theorem corr_13_2_24 : ∀ i : Fin 8, part 13 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 13 (24 + i.val)) := by
  decide +kernel

private theorem corr_13_2_32 : ∀ i : Fin 6, part 13 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 13 (32 + i.val)) := by
  decide +kernel

private theorem corr_13_2 : ∀ i : ℕ, i < 38 → part 13 2 i = sumWindow (2 * width) (chunkLen n 2) (term 13 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_13_2_0) corr_13_2_8) corr_13_2_16) corr_13_2_24) corr_13_2_32

private theorem corr_13_3_0 : ∀ i : Fin 8, part 13 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 13 i.val) := by
  decide +kernel

private theorem corr_13_3_8 : ∀ i : Fin 8, part 13 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 13 (8 + i.val)) := by
  decide +kernel

private theorem corr_13_3_16 : ∀ i : Fin 8, part 13 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 13 (16 + i.val)) := by
  decide +kernel

private theorem corr_13_3_24 : ∀ i : Fin 8, part 13 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 13 (24 + i.val)) := by
  decide +kernel

private theorem corr_13_3_32 : ∀ i : Fin 6, part 13 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 13 (32 + i.val)) := by
  decide +kernel

private theorem corr_13_3 : ∀ i : ℕ, i < 38 → part 13 3 i = sumWindow (3 * width) (chunkLen n 3) (term 13 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_13_3_0) corr_13_3_8) corr_13_3_16) corr_13_3_24) corr_13_3_32

private theorem corr_13_4_0 : ∀ i : Fin 8, part 13 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 13 i.val) := by
  decide +kernel

private theorem corr_13_4_8 : ∀ i : Fin 8, part 13 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 13 (8 + i.val)) := by
  decide +kernel

private theorem corr_13_4_16 : ∀ i : Fin 8, part 13 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 13 (16 + i.val)) := by
  decide +kernel

private theorem corr_13_4_24 : ∀ i : Fin 8, part 13 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 13 (24 + i.val)) := by
  decide +kernel

private theorem corr_13_4_32 : ∀ i : Fin 6, part 13 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 13 (32 + i.val)) := by
  decide +kernel

private theorem corr_13_4 : ∀ i : ℕ, i < 38 → part 13 4 i = sumWindow (4 * width) (chunkLen n 4) (term 13 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_13_4_0) corr_13_4_8) corr_13_4_16) corr_13_4_24) corr_13_4_32

private theorem corr_13_5_0 : ∀ i : Fin 8, part 13 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 13 i.val) := by
  decide +kernel

private theorem corr_13_5_8 : ∀ i : Fin 8, part 13 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 13 (8 + i.val)) := by
  decide +kernel

private theorem corr_13_5_16 : ∀ i : Fin 8, part 13 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 13 (16 + i.val)) := by
  decide +kernel

private theorem corr_13_5_24 : ∀ i : Fin 8, part 13 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 13 (24 + i.val)) := by
  decide +kernel

private theorem corr_13_5_32 : ∀ i : Fin 6, part 13 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 13 (32 + i.val)) := by
  decide +kernel

private theorem corr_13_5 : ∀ i : ℕ, i < 38 → part 13 5 i = sumWindow (5 * width) (chunkLen n 5) (term 13 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_13_5_0) corr_13_5_8) corr_13_5_16) corr_13_5_24) corr_13_5_32

private theorem corr_13_6_0 : ∀ i : Fin 8, part 13 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 13 i.val) := by
  decide +kernel

private theorem corr_13_6_8 : ∀ i : Fin 8, part 13 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 13 (8 + i.val)) := by
  decide +kernel

private theorem corr_13_6_16 : ∀ i : Fin 8, part 13 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 13 (16 + i.val)) := by
  decide +kernel

private theorem corr_13_6_24 : ∀ i : Fin 8, part 13 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 13 (24 + i.val)) := by
  decide +kernel

private theorem corr_13_6_32 : ∀ i : Fin 6, part 13 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 13 (32 + i.val)) := by
  decide +kernel

private theorem corr_13_6 : ∀ i : ℕ, i < 38 → part 13 6 i = sumWindow (6 * width) (chunkLen n 6) (term 13 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_13_6_0) corr_13_6_8) corr_13_6_16) corr_13_6_24) corr_13_6_32

private theorem corr_13_7_0 : ∀ i : Fin 8, part 13 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 13 i.val) := by
  decide +kernel

private theorem corr_13_7_8 : ∀ i : Fin 8, part 13 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 13 (8 + i.val)) := by
  decide +kernel

private theorem corr_13_7_16 : ∀ i : Fin 8, part 13 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 13 (16 + i.val)) := by
  decide +kernel

private theorem corr_13_7_24 : ∀ i : Fin 8, part 13 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 13 (24 + i.val)) := by
  decide +kernel

private theorem corr_13_7_32 : ∀ i : Fin 6, part 13 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 13 (32 + i.val)) := by
  decide +kernel

private theorem corr_13_7 : ∀ i : ℕ, i < 38 → part 13 7 i = sumWindow (7 * width) (chunkLen n 7) (term 13 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_13_7_0) corr_13_7_8) corr_13_7_16) corr_13_7_24) corr_13_7_32

private theorem corr_13_8_0 : ∀ i : Fin 8, part 13 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 13 i.val) := by
  decide +kernel

private theorem corr_13_8_8 : ∀ i : Fin 8, part 13 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 13 (8 + i.val)) := by
  decide +kernel

private theorem corr_13_8_16 : ∀ i : Fin 8, part 13 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 13 (16 + i.val)) := by
  decide +kernel

private theorem corr_13_8_24 : ∀ i : Fin 8, part 13 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 13 (24 + i.val)) := by
  decide +kernel

private theorem corr_13_8_32 : ∀ i : Fin 6, part 13 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 13 (32 + i.val)) := by
  decide +kernel

private theorem corr_13_8 : ∀ i : ℕ, i < 38 → part 13 8 i = sumWindow (8 * width) (chunkLen n 8) (term 13 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_13_8_0) corr_13_8_8) corr_13_8_16) corr_13_8_24) corr_13_8_32

private theorem corr_13_9_0 : ∀ i : Fin 8, part 13 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 13 i.val) := by
  decide +kernel

private theorem corr_13_9_8 : ∀ i : Fin 8, part 13 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 13 (8 + i.val)) := by
  decide +kernel

private theorem corr_13_9_16 : ∀ i : Fin 8, part 13 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 13 (16 + i.val)) := by
  decide +kernel

private theorem corr_13_9_24 : ∀ i : Fin 8, part 13 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 13 (24 + i.val)) := by
  decide +kernel

private theorem corr_13_9_32 : ∀ i : Fin 6, part 13 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 13 (32 + i.val)) := by
  decide +kernel

private theorem corr_13_9 : ∀ i : ℕ, i < 38 → part 13 9 i = sumWindow (9 * width) (chunkLen n 9) (term 13 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_13_9_0) corr_13_9_8) corr_13_9_16) corr_13_9_24) corr_13_9_32

theorem corr_13 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 13 b slot = sumWindow (b * width) (chunkLen n b) (term 13 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_13_0) corr_13_1) corr_13_2) corr_13_3) corr_13_4) corr_13_5) corr_13_6) corr_13_7) corr_13_8) corr_13_9

private theorem total_13_0 : ∀ i : Fin 8, correlationAt 13 i.val = sumChunks n (fun b => part 13 b i.val) := by
  decide +kernel

private theorem total_13_8 : ∀ i : Fin 8, correlationAt 13 (8 + i.val) = sumChunks n (fun b => part 13 b (8 + i.val)) := by
  decide +kernel

private theorem total_13_16 : ∀ i : Fin 8, correlationAt 13 (16 + i.val) = sumChunks n (fun b => part 13 b (16 + i.val)) := by
  decide +kernel

private theorem total_13_24 : ∀ i : Fin 8, correlationAt 13 (24 + i.val) = sumChunks n (fun b => part 13 b (24 + i.val)) := by
  decide +kernel

private theorem total_13_32 : ∀ i : Fin 6, correlationAt 13 (32 + i.val) = sumChunks n (fun b => part 13 b (32 + i.val)) := by
  decide +kernel

theorem total_13 : ∀ i : ℕ, i < 38 → correlationAt 13 i = sumChunks n (fun b => part 13 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_13_0) total_13_8) total_13_16) total_13_24) total_13_32

private theorem corr_14_0_0 : ∀ i : Fin 8, part 14 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 14 i.val) := by
  decide +kernel

private theorem corr_14_0_8 : ∀ i : Fin 8, part 14 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 14 (8 + i.val)) := by
  decide +kernel

private theorem corr_14_0_16 : ∀ i : Fin 8, part 14 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 14 (16 + i.val)) := by
  decide +kernel

private theorem corr_14_0_24 : ∀ i : Fin 8, part 14 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 14 (24 + i.val)) := by
  decide +kernel

private theorem corr_14_0_32 : ∀ i : Fin 6, part 14 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 14 (32 + i.val)) := by
  decide +kernel

private theorem corr_14_0 : ∀ i : ℕ, i < 38 → part 14 0 i = sumWindow (0 * width) (chunkLen n 0) (term 14 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_14_0_0) corr_14_0_8) corr_14_0_16) corr_14_0_24) corr_14_0_32

private theorem corr_14_1_0 : ∀ i : Fin 8, part 14 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 14 i.val) := by
  decide +kernel

private theorem corr_14_1_8 : ∀ i : Fin 8, part 14 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 14 (8 + i.val)) := by
  decide +kernel

private theorem corr_14_1_16 : ∀ i : Fin 8, part 14 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 14 (16 + i.val)) := by
  decide +kernel

private theorem corr_14_1_24 : ∀ i : Fin 8, part 14 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 14 (24 + i.val)) := by
  decide +kernel

private theorem corr_14_1_32 : ∀ i : Fin 6, part 14 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 14 (32 + i.val)) := by
  decide +kernel

private theorem corr_14_1 : ∀ i : ℕ, i < 38 → part 14 1 i = sumWindow (1 * width) (chunkLen n 1) (term 14 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_14_1_0) corr_14_1_8) corr_14_1_16) corr_14_1_24) corr_14_1_32

private theorem corr_14_2_0 : ∀ i : Fin 8, part 14 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 14 i.val) := by
  decide +kernel

private theorem corr_14_2_8 : ∀ i : Fin 8, part 14 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 14 (8 + i.val)) := by
  decide +kernel

private theorem corr_14_2_16 : ∀ i : Fin 8, part 14 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 14 (16 + i.val)) := by
  decide +kernel

private theorem corr_14_2_24 : ∀ i : Fin 8, part 14 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 14 (24 + i.val)) := by
  decide +kernel

private theorem corr_14_2_32 : ∀ i : Fin 6, part 14 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 14 (32 + i.val)) := by
  decide +kernel

private theorem corr_14_2 : ∀ i : ℕ, i < 38 → part 14 2 i = sumWindow (2 * width) (chunkLen n 2) (term 14 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_14_2_0) corr_14_2_8) corr_14_2_16) corr_14_2_24) corr_14_2_32

private theorem corr_14_3_0 : ∀ i : Fin 8, part 14 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 14 i.val) := by
  decide +kernel

private theorem corr_14_3_8 : ∀ i : Fin 8, part 14 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 14 (8 + i.val)) := by
  decide +kernel

private theorem corr_14_3_16 : ∀ i : Fin 8, part 14 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 14 (16 + i.val)) := by
  decide +kernel

private theorem corr_14_3_24 : ∀ i : Fin 8, part 14 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 14 (24 + i.val)) := by
  decide +kernel

private theorem corr_14_3_32 : ∀ i : Fin 6, part 14 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 14 (32 + i.val)) := by
  decide +kernel

private theorem corr_14_3 : ∀ i : ℕ, i < 38 → part 14 3 i = sumWindow (3 * width) (chunkLen n 3) (term 14 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_14_3_0) corr_14_3_8) corr_14_3_16) corr_14_3_24) corr_14_3_32

private theorem corr_14_4_0 : ∀ i : Fin 8, part 14 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 14 i.val) := by
  decide +kernel

private theorem corr_14_4_8 : ∀ i : Fin 8, part 14 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 14 (8 + i.val)) := by
  decide +kernel

private theorem corr_14_4_16 : ∀ i : Fin 8, part 14 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 14 (16 + i.val)) := by
  decide +kernel

private theorem corr_14_4_24 : ∀ i : Fin 8, part 14 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 14 (24 + i.val)) := by
  decide +kernel

private theorem corr_14_4_32 : ∀ i : Fin 6, part 14 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 14 (32 + i.val)) := by
  decide +kernel

private theorem corr_14_4 : ∀ i : ℕ, i < 38 → part 14 4 i = sumWindow (4 * width) (chunkLen n 4) (term 14 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_14_4_0) corr_14_4_8) corr_14_4_16) corr_14_4_24) corr_14_4_32

private theorem corr_14_5_0 : ∀ i : Fin 8, part 14 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 14 i.val) := by
  decide +kernel

private theorem corr_14_5_8 : ∀ i : Fin 8, part 14 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 14 (8 + i.val)) := by
  decide +kernel

private theorem corr_14_5_16 : ∀ i : Fin 8, part 14 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 14 (16 + i.val)) := by
  decide +kernel

private theorem corr_14_5_24 : ∀ i : Fin 8, part 14 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 14 (24 + i.val)) := by
  decide +kernel

private theorem corr_14_5_32 : ∀ i : Fin 6, part 14 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 14 (32 + i.val)) := by
  decide +kernel

private theorem corr_14_5 : ∀ i : ℕ, i < 38 → part 14 5 i = sumWindow (5 * width) (chunkLen n 5) (term 14 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_14_5_0) corr_14_5_8) corr_14_5_16) corr_14_5_24) corr_14_5_32

private theorem corr_14_6_0 : ∀ i : Fin 8, part 14 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 14 i.val) := by
  decide +kernel

private theorem corr_14_6_8 : ∀ i : Fin 8, part 14 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 14 (8 + i.val)) := by
  decide +kernel

private theorem corr_14_6_16 : ∀ i : Fin 8, part 14 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 14 (16 + i.val)) := by
  decide +kernel

private theorem corr_14_6_24 : ∀ i : Fin 8, part 14 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 14 (24 + i.val)) := by
  decide +kernel

private theorem corr_14_6_32 : ∀ i : Fin 6, part 14 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 14 (32 + i.val)) := by
  decide +kernel

private theorem corr_14_6 : ∀ i : ℕ, i < 38 → part 14 6 i = sumWindow (6 * width) (chunkLen n 6) (term 14 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_14_6_0) corr_14_6_8) corr_14_6_16) corr_14_6_24) corr_14_6_32

private theorem corr_14_7_0 : ∀ i : Fin 8, part 14 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 14 i.val) := by
  decide +kernel

private theorem corr_14_7_8 : ∀ i : Fin 8, part 14 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 14 (8 + i.val)) := by
  decide +kernel

private theorem corr_14_7_16 : ∀ i : Fin 8, part 14 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 14 (16 + i.val)) := by
  decide +kernel

private theorem corr_14_7_24 : ∀ i : Fin 8, part 14 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 14 (24 + i.val)) := by
  decide +kernel

private theorem corr_14_7_32 : ∀ i : Fin 6, part 14 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 14 (32 + i.val)) := by
  decide +kernel

private theorem corr_14_7 : ∀ i : ℕ, i < 38 → part 14 7 i = sumWindow (7 * width) (chunkLen n 7) (term 14 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_14_7_0) corr_14_7_8) corr_14_7_16) corr_14_7_24) corr_14_7_32

private theorem corr_14_8_0 : ∀ i : Fin 8, part 14 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 14 i.val) := by
  decide +kernel

private theorem corr_14_8_8 : ∀ i : Fin 8, part 14 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 14 (8 + i.val)) := by
  decide +kernel

private theorem corr_14_8_16 : ∀ i : Fin 8, part 14 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 14 (16 + i.val)) := by
  decide +kernel

private theorem corr_14_8_24 : ∀ i : Fin 8, part 14 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 14 (24 + i.val)) := by
  decide +kernel

private theorem corr_14_8_32 : ∀ i : Fin 6, part 14 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 14 (32 + i.val)) := by
  decide +kernel

private theorem corr_14_8 : ∀ i : ℕ, i < 38 → part 14 8 i = sumWindow (8 * width) (chunkLen n 8) (term 14 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_14_8_0) corr_14_8_8) corr_14_8_16) corr_14_8_24) corr_14_8_32

private theorem corr_14_9_0 : ∀ i : Fin 8, part 14 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 14 i.val) := by
  decide +kernel

private theorem corr_14_9_8 : ∀ i : Fin 8, part 14 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 14 (8 + i.val)) := by
  decide +kernel

private theorem corr_14_9_16 : ∀ i : Fin 8, part 14 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 14 (16 + i.val)) := by
  decide +kernel

private theorem corr_14_9_24 : ∀ i : Fin 8, part 14 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 14 (24 + i.val)) := by
  decide +kernel

private theorem corr_14_9_32 : ∀ i : Fin 6, part 14 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 14 (32 + i.val)) := by
  decide +kernel

private theorem corr_14_9 : ∀ i : ℕ, i < 38 → part 14 9 i = sumWindow (9 * width) (chunkLen n 9) (term 14 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_14_9_0) corr_14_9_8) corr_14_9_16) corr_14_9_24) corr_14_9_32

theorem corr_14 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 14 b slot = sumWindow (b * width) (chunkLen n b) (term 14 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_14_0) corr_14_1) corr_14_2) corr_14_3) corr_14_4) corr_14_5) corr_14_6) corr_14_7) corr_14_8) corr_14_9

private theorem total_14_0 : ∀ i : Fin 8, correlationAt 14 i.val = sumChunks n (fun b => part 14 b i.val) := by
  decide +kernel

private theorem total_14_8 : ∀ i : Fin 8, correlationAt 14 (8 + i.val) = sumChunks n (fun b => part 14 b (8 + i.val)) := by
  decide +kernel

private theorem total_14_16 : ∀ i : Fin 8, correlationAt 14 (16 + i.val) = sumChunks n (fun b => part 14 b (16 + i.val)) := by
  decide +kernel

private theorem total_14_24 : ∀ i : Fin 8, correlationAt 14 (24 + i.val) = sumChunks n (fun b => part 14 b (24 + i.val)) := by
  decide +kernel

private theorem total_14_32 : ∀ i : Fin 6, correlationAt 14 (32 + i.val) = sumChunks n (fun b => part 14 b (32 + i.val)) := by
  decide +kernel

theorem total_14 : ∀ i : ℕ, i < 38 → correlationAt 14 i = sumChunks n (fun b => part 14 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_14_0) total_14_8) total_14_16) total_14_24) total_14_32

end Chirped73
