/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73CorrelationBlock3
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Correlations.correlation_spec; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73CorrelationData.correlationAt
   digest: Checked partial and total correlation sums for order-73 block 3. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73CorrelationData

/-! Exact data and kernel checks for the order-73 chirped construction. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Chirped73

open ChirpedFinite

private theorem corr_9_0_0 : ∀ i : Fin 8, part 9 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 9 i.val) := by
  decide +kernel

private theorem corr_9_0_8 : ∀ i : Fin 8, part 9 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 9 (8 + i.val)) := by
  decide +kernel

private theorem corr_9_0_16 : ∀ i : Fin 8, part 9 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 9 (16 + i.val)) := by
  decide +kernel

private theorem corr_9_0_24 : ∀ i : Fin 8, part 9 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 9 (24 + i.val)) := by
  decide +kernel

private theorem corr_9_0_32 : ∀ i : Fin 6, part 9 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 9 (32 + i.val)) := by
  decide +kernel

private theorem corr_9_0 : ∀ i : ℕ, i < 38 → part 9 0 i = sumWindow (0 * width) (chunkLen n 0) (term 9 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_9_0_0) corr_9_0_8) corr_9_0_16) corr_9_0_24) corr_9_0_32

private theorem corr_9_1_0 : ∀ i : Fin 8, part 9 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 9 i.val) := by
  decide +kernel

private theorem corr_9_1_8 : ∀ i : Fin 8, part 9 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 9 (8 + i.val)) := by
  decide +kernel

private theorem corr_9_1_16 : ∀ i : Fin 8, part 9 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 9 (16 + i.val)) := by
  decide +kernel

private theorem corr_9_1_24 : ∀ i : Fin 8, part 9 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 9 (24 + i.val)) := by
  decide +kernel

private theorem corr_9_1_32 : ∀ i : Fin 6, part 9 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 9 (32 + i.val)) := by
  decide +kernel

private theorem corr_9_1 : ∀ i : ℕ, i < 38 → part 9 1 i = sumWindow (1 * width) (chunkLen n 1) (term 9 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_9_1_0) corr_9_1_8) corr_9_1_16) corr_9_1_24) corr_9_1_32

private theorem corr_9_2_0 : ∀ i : Fin 8, part 9 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 9 i.val) := by
  decide +kernel

private theorem corr_9_2_8 : ∀ i : Fin 8, part 9 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 9 (8 + i.val)) := by
  decide +kernel

private theorem corr_9_2_16 : ∀ i : Fin 8, part 9 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 9 (16 + i.val)) := by
  decide +kernel

private theorem corr_9_2_24 : ∀ i : Fin 8, part 9 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 9 (24 + i.val)) := by
  decide +kernel

private theorem corr_9_2_32 : ∀ i : Fin 6, part 9 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 9 (32 + i.val)) := by
  decide +kernel

private theorem corr_9_2 : ∀ i : ℕ, i < 38 → part 9 2 i = sumWindow (2 * width) (chunkLen n 2) (term 9 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_9_2_0) corr_9_2_8) corr_9_2_16) corr_9_2_24) corr_9_2_32

private theorem corr_9_3_0 : ∀ i : Fin 8, part 9 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 9 i.val) := by
  decide +kernel

private theorem corr_9_3_8 : ∀ i : Fin 8, part 9 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 9 (8 + i.val)) := by
  decide +kernel

private theorem corr_9_3_16 : ∀ i : Fin 8, part 9 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 9 (16 + i.val)) := by
  decide +kernel

private theorem corr_9_3_24 : ∀ i : Fin 8, part 9 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 9 (24 + i.val)) := by
  decide +kernel

private theorem corr_9_3_32 : ∀ i : Fin 6, part 9 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 9 (32 + i.val)) := by
  decide +kernel

private theorem corr_9_3 : ∀ i : ℕ, i < 38 → part 9 3 i = sumWindow (3 * width) (chunkLen n 3) (term 9 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_9_3_0) corr_9_3_8) corr_9_3_16) corr_9_3_24) corr_9_3_32

private theorem corr_9_4_0 : ∀ i : Fin 8, part 9 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 9 i.val) := by
  decide +kernel

private theorem corr_9_4_8 : ∀ i : Fin 8, part 9 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 9 (8 + i.val)) := by
  decide +kernel

private theorem corr_9_4_16 : ∀ i : Fin 8, part 9 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 9 (16 + i.val)) := by
  decide +kernel

private theorem corr_9_4_24 : ∀ i : Fin 8, part 9 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 9 (24 + i.val)) := by
  decide +kernel

private theorem corr_9_4_32 : ∀ i : Fin 6, part 9 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 9 (32 + i.val)) := by
  decide +kernel

private theorem corr_9_4 : ∀ i : ℕ, i < 38 → part 9 4 i = sumWindow (4 * width) (chunkLen n 4) (term 9 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_9_4_0) corr_9_4_8) corr_9_4_16) corr_9_4_24) corr_9_4_32

private theorem corr_9_5_0 : ∀ i : Fin 8, part 9 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 9 i.val) := by
  decide +kernel

private theorem corr_9_5_8 : ∀ i : Fin 8, part 9 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 9 (8 + i.val)) := by
  decide +kernel

private theorem corr_9_5_16 : ∀ i : Fin 8, part 9 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 9 (16 + i.val)) := by
  decide +kernel

private theorem corr_9_5_24 : ∀ i : Fin 8, part 9 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 9 (24 + i.val)) := by
  decide +kernel

private theorem corr_9_5_32 : ∀ i : Fin 6, part 9 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 9 (32 + i.val)) := by
  decide +kernel

private theorem corr_9_5 : ∀ i : ℕ, i < 38 → part 9 5 i = sumWindow (5 * width) (chunkLen n 5) (term 9 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_9_5_0) corr_9_5_8) corr_9_5_16) corr_9_5_24) corr_9_5_32

private theorem corr_9_6_0 : ∀ i : Fin 8, part 9 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 9 i.val) := by
  decide +kernel

private theorem corr_9_6_8 : ∀ i : Fin 8, part 9 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 9 (8 + i.val)) := by
  decide +kernel

private theorem corr_9_6_16 : ∀ i : Fin 8, part 9 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 9 (16 + i.val)) := by
  decide +kernel

private theorem corr_9_6_24 : ∀ i : Fin 8, part 9 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 9 (24 + i.val)) := by
  decide +kernel

private theorem corr_9_6_32 : ∀ i : Fin 6, part 9 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 9 (32 + i.val)) := by
  decide +kernel

private theorem corr_9_6 : ∀ i : ℕ, i < 38 → part 9 6 i = sumWindow (6 * width) (chunkLen n 6) (term 9 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_9_6_0) corr_9_6_8) corr_9_6_16) corr_9_6_24) corr_9_6_32

private theorem corr_9_7_0 : ∀ i : Fin 8, part 9 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 9 i.val) := by
  decide +kernel

private theorem corr_9_7_8 : ∀ i : Fin 8, part 9 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 9 (8 + i.val)) := by
  decide +kernel

private theorem corr_9_7_16 : ∀ i : Fin 8, part 9 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 9 (16 + i.val)) := by
  decide +kernel

private theorem corr_9_7_24 : ∀ i : Fin 8, part 9 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 9 (24 + i.val)) := by
  decide +kernel

private theorem corr_9_7_32 : ∀ i : Fin 6, part 9 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 9 (32 + i.val)) := by
  decide +kernel

private theorem corr_9_7 : ∀ i : ℕ, i < 38 → part 9 7 i = sumWindow (7 * width) (chunkLen n 7) (term 9 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_9_7_0) corr_9_7_8) corr_9_7_16) corr_9_7_24) corr_9_7_32

private theorem corr_9_8_0 : ∀ i : Fin 8, part 9 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 9 i.val) := by
  decide +kernel

private theorem corr_9_8_8 : ∀ i : Fin 8, part 9 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 9 (8 + i.val)) := by
  decide +kernel

private theorem corr_9_8_16 : ∀ i : Fin 8, part 9 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 9 (16 + i.val)) := by
  decide +kernel

private theorem corr_9_8_24 : ∀ i : Fin 8, part 9 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 9 (24 + i.val)) := by
  decide +kernel

private theorem corr_9_8_32 : ∀ i : Fin 6, part 9 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 9 (32 + i.val)) := by
  decide +kernel

private theorem corr_9_8 : ∀ i : ℕ, i < 38 → part 9 8 i = sumWindow (8 * width) (chunkLen n 8) (term 9 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_9_8_0) corr_9_8_8) corr_9_8_16) corr_9_8_24) corr_9_8_32

private theorem corr_9_9_0 : ∀ i : Fin 8, part 9 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 9 i.val) := by
  decide +kernel

private theorem corr_9_9_8 : ∀ i : Fin 8, part 9 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 9 (8 + i.val)) := by
  decide +kernel

private theorem corr_9_9_16 : ∀ i : Fin 8, part 9 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 9 (16 + i.val)) := by
  decide +kernel

private theorem corr_9_9_24 : ∀ i : Fin 8, part 9 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 9 (24 + i.val)) := by
  decide +kernel

private theorem corr_9_9_32 : ∀ i : Fin 6, part 9 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 9 (32 + i.val)) := by
  decide +kernel

private theorem corr_9_9 : ∀ i : ℕ, i < 38 → part 9 9 i = sumWindow (9 * width) (chunkLen n 9) (term 9 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_9_9_0) corr_9_9_8) corr_9_9_16) corr_9_9_24) corr_9_9_32

theorem corr_9 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 9 b slot = sumWindow (b * width) (chunkLen n b) (term 9 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_9_0) corr_9_1) corr_9_2) corr_9_3) corr_9_4) corr_9_5) corr_9_6) corr_9_7) corr_9_8) corr_9_9

private theorem total_9_0 : ∀ i : Fin 8, correlationAt 9 i.val = sumChunks n (fun b => part 9 b i.val) := by
  decide +kernel

private theorem total_9_8 : ∀ i : Fin 8, correlationAt 9 (8 + i.val) = sumChunks n (fun b => part 9 b (8 + i.val)) := by
  decide +kernel

private theorem total_9_16 : ∀ i : Fin 8, correlationAt 9 (16 + i.val) = sumChunks n (fun b => part 9 b (16 + i.val)) := by
  decide +kernel

private theorem total_9_24 : ∀ i : Fin 8, correlationAt 9 (24 + i.val) = sumChunks n (fun b => part 9 b (24 + i.val)) := by
  decide +kernel

private theorem total_9_32 : ∀ i : Fin 6, correlationAt 9 (32 + i.val) = sumChunks n (fun b => part 9 b (32 + i.val)) := by
  decide +kernel

theorem total_9 : ∀ i : ℕ, i < 38 → correlationAt 9 i = sumChunks n (fun b => part 9 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_9_0) total_9_8) total_9_16) total_9_24) total_9_32

private theorem corr_10_0_0 : ∀ i : Fin 8, part 10 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 10 i.val) := by
  decide +kernel

private theorem corr_10_0_8 : ∀ i : Fin 8, part 10 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 10 (8 + i.val)) := by
  decide +kernel

private theorem corr_10_0_16 : ∀ i : Fin 8, part 10 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 10 (16 + i.val)) := by
  decide +kernel

private theorem corr_10_0_24 : ∀ i : Fin 8, part 10 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 10 (24 + i.val)) := by
  decide +kernel

private theorem corr_10_0_32 : ∀ i : Fin 6, part 10 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 10 (32 + i.val)) := by
  decide +kernel

private theorem corr_10_0 : ∀ i : ℕ, i < 38 → part 10 0 i = sumWindow (0 * width) (chunkLen n 0) (term 10 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_10_0_0) corr_10_0_8) corr_10_0_16) corr_10_0_24) corr_10_0_32

private theorem corr_10_1_0 : ∀ i : Fin 8, part 10 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 10 i.val) := by
  decide +kernel

private theorem corr_10_1_8 : ∀ i : Fin 8, part 10 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 10 (8 + i.val)) := by
  decide +kernel

private theorem corr_10_1_16 : ∀ i : Fin 8, part 10 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 10 (16 + i.val)) := by
  decide +kernel

private theorem corr_10_1_24 : ∀ i : Fin 8, part 10 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 10 (24 + i.val)) := by
  decide +kernel

private theorem corr_10_1_32 : ∀ i : Fin 6, part 10 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 10 (32 + i.val)) := by
  decide +kernel

private theorem corr_10_1 : ∀ i : ℕ, i < 38 → part 10 1 i = sumWindow (1 * width) (chunkLen n 1) (term 10 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_10_1_0) corr_10_1_8) corr_10_1_16) corr_10_1_24) corr_10_1_32

private theorem corr_10_2_0 : ∀ i : Fin 8, part 10 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 10 i.val) := by
  decide +kernel

private theorem corr_10_2_8 : ∀ i : Fin 8, part 10 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 10 (8 + i.val)) := by
  decide +kernel

private theorem corr_10_2_16 : ∀ i : Fin 8, part 10 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 10 (16 + i.val)) := by
  decide +kernel

private theorem corr_10_2_24 : ∀ i : Fin 8, part 10 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 10 (24 + i.val)) := by
  decide +kernel

private theorem corr_10_2_32 : ∀ i : Fin 6, part 10 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 10 (32 + i.val)) := by
  decide +kernel

private theorem corr_10_2 : ∀ i : ℕ, i < 38 → part 10 2 i = sumWindow (2 * width) (chunkLen n 2) (term 10 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_10_2_0) corr_10_2_8) corr_10_2_16) corr_10_2_24) corr_10_2_32

private theorem corr_10_3_0 : ∀ i : Fin 8, part 10 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 10 i.val) := by
  decide +kernel

private theorem corr_10_3_8 : ∀ i : Fin 8, part 10 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 10 (8 + i.val)) := by
  decide +kernel

private theorem corr_10_3_16 : ∀ i : Fin 8, part 10 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 10 (16 + i.val)) := by
  decide +kernel

private theorem corr_10_3_24 : ∀ i : Fin 8, part 10 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 10 (24 + i.val)) := by
  decide +kernel

private theorem corr_10_3_32 : ∀ i : Fin 6, part 10 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 10 (32 + i.val)) := by
  decide +kernel

private theorem corr_10_3 : ∀ i : ℕ, i < 38 → part 10 3 i = sumWindow (3 * width) (chunkLen n 3) (term 10 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_10_3_0) corr_10_3_8) corr_10_3_16) corr_10_3_24) corr_10_3_32

private theorem corr_10_4_0 : ∀ i : Fin 8, part 10 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 10 i.val) := by
  decide +kernel

private theorem corr_10_4_8 : ∀ i : Fin 8, part 10 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 10 (8 + i.val)) := by
  decide +kernel

private theorem corr_10_4_16 : ∀ i : Fin 8, part 10 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 10 (16 + i.val)) := by
  decide +kernel

private theorem corr_10_4_24 : ∀ i : Fin 8, part 10 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 10 (24 + i.val)) := by
  decide +kernel

private theorem corr_10_4_32 : ∀ i : Fin 6, part 10 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 10 (32 + i.val)) := by
  decide +kernel

private theorem corr_10_4 : ∀ i : ℕ, i < 38 → part 10 4 i = sumWindow (4 * width) (chunkLen n 4) (term 10 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_10_4_0) corr_10_4_8) corr_10_4_16) corr_10_4_24) corr_10_4_32

private theorem corr_10_5_0 : ∀ i : Fin 8, part 10 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 10 i.val) := by
  decide +kernel

private theorem corr_10_5_8 : ∀ i : Fin 8, part 10 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 10 (8 + i.val)) := by
  decide +kernel

private theorem corr_10_5_16 : ∀ i : Fin 8, part 10 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 10 (16 + i.val)) := by
  decide +kernel

private theorem corr_10_5_24 : ∀ i : Fin 8, part 10 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 10 (24 + i.val)) := by
  decide +kernel

private theorem corr_10_5_32 : ∀ i : Fin 6, part 10 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 10 (32 + i.val)) := by
  decide +kernel

private theorem corr_10_5 : ∀ i : ℕ, i < 38 → part 10 5 i = sumWindow (5 * width) (chunkLen n 5) (term 10 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_10_5_0) corr_10_5_8) corr_10_5_16) corr_10_5_24) corr_10_5_32

private theorem corr_10_6_0 : ∀ i : Fin 8, part 10 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 10 i.val) := by
  decide +kernel

private theorem corr_10_6_8 : ∀ i : Fin 8, part 10 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 10 (8 + i.val)) := by
  decide +kernel

private theorem corr_10_6_16 : ∀ i : Fin 8, part 10 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 10 (16 + i.val)) := by
  decide +kernel

private theorem corr_10_6_24 : ∀ i : Fin 8, part 10 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 10 (24 + i.val)) := by
  decide +kernel

private theorem corr_10_6_32 : ∀ i : Fin 6, part 10 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 10 (32 + i.val)) := by
  decide +kernel

private theorem corr_10_6 : ∀ i : ℕ, i < 38 → part 10 6 i = sumWindow (6 * width) (chunkLen n 6) (term 10 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_10_6_0) corr_10_6_8) corr_10_6_16) corr_10_6_24) corr_10_6_32

private theorem corr_10_7_0 : ∀ i : Fin 8, part 10 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 10 i.val) := by
  decide +kernel

private theorem corr_10_7_8 : ∀ i : Fin 8, part 10 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 10 (8 + i.val)) := by
  decide +kernel

private theorem corr_10_7_16 : ∀ i : Fin 8, part 10 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 10 (16 + i.val)) := by
  decide +kernel

private theorem corr_10_7_24 : ∀ i : Fin 8, part 10 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 10 (24 + i.val)) := by
  decide +kernel

private theorem corr_10_7_32 : ∀ i : Fin 6, part 10 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 10 (32 + i.val)) := by
  decide +kernel

private theorem corr_10_7 : ∀ i : ℕ, i < 38 → part 10 7 i = sumWindow (7 * width) (chunkLen n 7) (term 10 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_10_7_0) corr_10_7_8) corr_10_7_16) corr_10_7_24) corr_10_7_32

private theorem corr_10_8_0 : ∀ i : Fin 8, part 10 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 10 i.val) := by
  decide +kernel

private theorem corr_10_8_8 : ∀ i : Fin 8, part 10 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 10 (8 + i.val)) := by
  decide +kernel

private theorem corr_10_8_16 : ∀ i : Fin 8, part 10 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 10 (16 + i.val)) := by
  decide +kernel

private theorem corr_10_8_24 : ∀ i : Fin 8, part 10 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 10 (24 + i.val)) := by
  decide +kernel

private theorem corr_10_8_32 : ∀ i : Fin 6, part 10 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 10 (32 + i.val)) := by
  decide +kernel

private theorem corr_10_8 : ∀ i : ℕ, i < 38 → part 10 8 i = sumWindow (8 * width) (chunkLen n 8) (term 10 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_10_8_0) corr_10_8_8) corr_10_8_16) corr_10_8_24) corr_10_8_32

private theorem corr_10_9_0 : ∀ i : Fin 8, part 10 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 10 i.val) := by
  decide +kernel

private theorem corr_10_9_8 : ∀ i : Fin 8, part 10 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 10 (8 + i.val)) := by
  decide +kernel

private theorem corr_10_9_16 : ∀ i : Fin 8, part 10 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 10 (16 + i.val)) := by
  decide +kernel

private theorem corr_10_9_24 : ∀ i : Fin 8, part 10 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 10 (24 + i.val)) := by
  decide +kernel

private theorem corr_10_9_32 : ∀ i : Fin 6, part 10 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 10 (32 + i.val)) := by
  decide +kernel

private theorem corr_10_9 : ∀ i : ℕ, i < 38 → part 10 9 i = sumWindow (9 * width) (chunkLen n 9) (term 10 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_10_9_0) corr_10_9_8) corr_10_9_16) corr_10_9_24) corr_10_9_32

theorem corr_10 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 10 b slot = sumWindow (b * width) (chunkLen n b) (term 10 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_10_0) corr_10_1) corr_10_2) corr_10_3) corr_10_4) corr_10_5) corr_10_6) corr_10_7) corr_10_8) corr_10_9

private theorem total_10_0 : ∀ i : Fin 8, correlationAt 10 i.val = sumChunks n (fun b => part 10 b i.val) := by
  decide +kernel

private theorem total_10_8 : ∀ i : Fin 8, correlationAt 10 (8 + i.val) = sumChunks n (fun b => part 10 b (8 + i.val)) := by
  decide +kernel

private theorem total_10_16 : ∀ i : Fin 8, correlationAt 10 (16 + i.val) = sumChunks n (fun b => part 10 b (16 + i.val)) := by
  decide +kernel

private theorem total_10_24 : ∀ i : Fin 8, correlationAt 10 (24 + i.val) = sumChunks n (fun b => part 10 b (24 + i.val)) := by
  decide +kernel

private theorem total_10_32 : ∀ i : Fin 6, correlationAt 10 (32 + i.val) = sumChunks n (fun b => part 10 b (32 + i.val)) := by
  decide +kernel

theorem total_10 : ∀ i : ℕ, i < 38 → correlationAt 10 i = sumChunks n (fun b => part 10 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_10_0) total_10_8) total_10_16) total_10_24) total_10_32

private theorem corr_11_0_0 : ∀ i : Fin 8, part 11 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 11 i.val) := by
  decide +kernel

private theorem corr_11_0_8 : ∀ i : Fin 8, part 11 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 11 (8 + i.val)) := by
  decide +kernel

private theorem corr_11_0_16 : ∀ i : Fin 8, part 11 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 11 (16 + i.val)) := by
  decide +kernel

private theorem corr_11_0_24 : ∀ i : Fin 8, part 11 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 11 (24 + i.val)) := by
  decide +kernel

private theorem corr_11_0_32 : ∀ i : Fin 6, part 11 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 11 (32 + i.val)) := by
  decide +kernel

private theorem corr_11_0 : ∀ i : ℕ, i < 38 → part 11 0 i = sumWindow (0 * width) (chunkLen n 0) (term 11 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_11_0_0) corr_11_0_8) corr_11_0_16) corr_11_0_24) corr_11_0_32

private theorem corr_11_1_0 : ∀ i : Fin 8, part 11 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 11 i.val) := by
  decide +kernel

private theorem corr_11_1_8 : ∀ i : Fin 8, part 11 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 11 (8 + i.val)) := by
  decide +kernel

private theorem corr_11_1_16 : ∀ i : Fin 8, part 11 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 11 (16 + i.val)) := by
  decide +kernel

private theorem corr_11_1_24 : ∀ i : Fin 8, part 11 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 11 (24 + i.val)) := by
  decide +kernel

private theorem corr_11_1_32 : ∀ i : Fin 6, part 11 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 11 (32 + i.val)) := by
  decide +kernel

private theorem corr_11_1 : ∀ i : ℕ, i < 38 → part 11 1 i = sumWindow (1 * width) (chunkLen n 1) (term 11 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_11_1_0) corr_11_1_8) corr_11_1_16) corr_11_1_24) corr_11_1_32

private theorem corr_11_2_0 : ∀ i : Fin 8, part 11 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 11 i.val) := by
  decide +kernel

private theorem corr_11_2_8 : ∀ i : Fin 8, part 11 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 11 (8 + i.val)) := by
  decide +kernel

private theorem corr_11_2_16 : ∀ i : Fin 8, part 11 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 11 (16 + i.val)) := by
  decide +kernel

private theorem corr_11_2_24 : ∀ i : Fin 8, part 11 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 11 (24 + i.val)) := by
  decide +kernel

private theorem corr_11_2_32 : ∀ i : Fin 6, part 11 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 11 (32 + i.val)) := by
  decide +kernel

private theorem corr_11_2 : ∀ i : ℕ, i < 38 → part 11 2 i = sumWindow (2 * width) (chunkLen n 2) (term 11 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_11_2_0) corr_11_2_8) corr_11_2_16) corr_11_2_24) corr_11_2_32

private theorem corr_11_3_0 : ∀ i : Fin 8, part 11 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 11 i.val) := by
  decide +kernel

private theorem corr_11_3_8 : ∀ i : Fin 8, part 11 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 11 (8 + i.val)) := by
  decide +kernel

private theorem corr_11_3_16 : ∀ i : Fin 8, part 11 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 11 (16 + i.val)) := by
  decide +kernel

private theorem corr_11_3_24 : ∀ i : Fin 8, part 11 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 11 (24 + i.val)) := by
  decide +kernel

private theorem corr_11_3_32 : ∀ i : Fin 6, part 11 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 11 (32 + i.val)) := by
  decide +kernel

private theorem corr_11_3 : ∀ i : ℕ, i < 38 → part 11 3 i = sumWindow (3 * width) (chunkLen n 3) (term 11 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_11_3_0) corr_11_3_8) corr_11_3_16) corr_11_3_24) corr_11_3_32

private theorem corr_11_4_0 : ∀ i : Fin 8, part 11 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 11 i.val) := by
  decide +kernel

private theorem corr_11_4_8 : ∀ i : Fin 8, part 11 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 11 (8 + i.val)) := by
  decide +kernel

private theorem corr_11_4_16 : ∀ i : Fin 8, part 11 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 11 (16 + i.val)) := by
  decide +kernel

private theorem corr_11_4_24 : ∀ i : Fin 8, part 11 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 11 (24 + i.val)) := by
  decide +kernel

private theorem corr_11_4_32 : ∀ i : Fin 6, part 11 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 11 (32 + i.val)) := by
  decide +kernel

private theorem corr_11_4 : ∀ i : ℕ, i < 38 → part 11 4 i = sumWindow (4 * width) (chunkLen n 4) (term 11 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_11_4_0) corr_11_4_8) corr_11_4_16) corr_11_4_24) corr_11_4_32

private theorem corr_11_5_0 : ∀ i : Fin 8, part 11 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 11 i.val) := by
  decide +kernel

private theorem corr_11_5_8 : ∀ i : Fin 8, part 11 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 11 (8 + i.val)) := by
  decide +kernel

private theorem corr_11_5_16 : ∀ i : Fin 8, part 11 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 11 (16 + i.val)) := by
  decide +kernel

private theorem corr_11_5_24 : ∀ i : Fin 8, part 11 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 11 (24 + i.val)) := by
  decide +kernel

private theorem corr_11_5_32 : ∀ i : Fin 6, part 11 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 11 (32 + i.val)) := by
  decide +kernel

private theorem corr_11_5 : ∀ i : ℕ, i < 38 → part 11 5 i = sumWindow (5 * width) (chunkLen n 5) (term 11 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_11_5_0) corr_11_5_8) corr_11_5_16) corr_11_5_24) corr_11_5_32

private theorem corr_11_6_0 : ∀ i : Fin 8, part 11 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 11 i.val) := by
  decide +kernel

private theorem corr_11_6_8 : ∀ i : Fin 8, part 11 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 11 (8 + i.val)) := by
  decide +kernel

private theorem corr_11_6_16 : ∀ i : Fin 8, part 11 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 11 (16 + i.val)) := by
  decide +kernel

private theorem corr_11_6_24 : ∀ i : Fin 8, part 11 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 11 (24 + i.val)) := by
  decide +kernel

private theorem corr_11_6_32 : ∀ i : Fin 6, part 11 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 11 (32 + i.val)) := by
  decide +kernel

private theorem corr_11_6 : ∀ i : ℕ, i < 38 → part 11 6 i = sumWindow (6 * width) (chunkLen n 6) (term 11 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_11_6_0) corr_11_6_8) corr_11_6_16) corr_11_6_24) corr_11_6_32

private theorem corr_11_7_0 : ∀ i : Fin 8, part 11 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 11 i.val) := by
  decide +kernel

private theorem corr_11_7_8 : ∀ i : Fin 8, part 11 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 11 (8 + i.val)) := by
  decide +kernel

private theorem corr_11_7_16 : ∀ i : Fin 8, part 11 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 11 (16 + i.val)) := by
  decide +kernel

private theorem corr_11_7_24 : ∀ i : Fin 8, part 11 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 11 (24 + i.val)) := by
  decide +kernel

private theorem corr_11_7_32 : ∀ i : Fin 6, part 11 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 11 (32 + i.val)) := by
  decide +kernel

private theorem corr_11_7 : ∀ i : ℕ, i < 38 → part 11 7 i = sumWindow (7 * width) (chunkLen n 7) (term 11 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_11_7_0) corr_11_7_8) corr_11_7_16) corr_11_7_24) corr_11_7_32

private theorem corr_11_8_0 : ∀ i : Fin 8, part 11 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 11 i.val) := by
  decide +kernel

private theorem corr_11_8_8 : ∀ i : Fin 8, part 11 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 11 (8 + i.val)) := by
  decide +kernel

private theorem corr_11_8_16 : ∀ i : Fin 8, part 11 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 11 (16 + i.val)) := by
  decide +kernel

private theorem corr_11_8_24 : ∀ i : Fin 8, part 11 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 11 (24 + i.val)) := by
  decide +kernel

private theorem corr_11_8_32 : ∀ i : Fin 6, part 11 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 11 (32 + i.val)) := by
  decide +kernel

private theorem corr_11_8 : ∀ i : ℕ, i < 38 → part 11 8 i = sumWindow (8 * width) (chunkLen n 8) (term 11 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_11_8_0) corr_11_8_8) corr_11_8_16) corr_11_8_24) corr_11_8_32

private theorem corr_11_9_0 : ∀ i : Fin 8, part 11 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 11 i.val) := by
  decide +kernel

private theorem corr_11_9_8 : ∀ i : Fin 8, part 11 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 11 (8 + i.val)) := by
  decide +kernel

private theorem corr_11_9_16 : ∀ i : Fin 8, part 11 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 11 (16 + i.val)) := by
  decide +kernel

private theorem corr_11_9_24 : ∀ i : Fin 8, part 11 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 11 (24 + i.val)) := by
  decide +kernel

private theorem corr_11_9_32 : ∀ i : Fin 6, part 11 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 11 (32 + i.val)) := by
  decide +kernel

private theorem corr_11_9 : ∀ i : ℕ, i < 38 → part 11 9 i = sumWindow (9 * width) (chunkLen n 9) (term 11 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_11_9_0) corr_11_9_8) corr_11_9_16) corr_11_9_24) corr_11_9_32

theorem corr_11 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 11 b slot = sumWindow (b * width) (chunkLen n b) (term 11 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_11_0) corr_11_1) corr_11_2) corr_11_3) corr_11_4) corr_11_5) corr_11_6) corr_11_7) corr_11_8) corr_11_9

private theorem total_11_0 : ∀ i : Fin 8, correlationAt 11 i.val = sumChunks n (fun b => part 11 b i.val) := by
  decide +kernel

private theorem total_11_8 : ∀ i : Fin 8, correlationAt 11 (8 + i.val) = sumChunks n (fun b => part 11 b (8 + i.val)) := by
  decide +kernel

private theorem total_11_16 : ∀ i : Fin 8, correlationAt 11 (16 + i.val) = sumChunks n (fun b => part 11 b (16 + i.val)) := by
  decide +kernel

private theorem total_11_24 : ∀ i : Fin 8, correlationAt 11 (24 + i.val) = sumChunks n (fun b => part 11 b (24 + i.val)) := by
  decide +kernel

private theorem total_11_32 : ∀ i : Fin 6, correlationAt 11 (32 + i.val) = sumChunks n (fun b => part 11 b (32 + i.val)) := by
  decide +kernel

theorem total_11 : ∀ i : ℕ, i < 38 → correlationAt 11 i = sumChunks n (fun b => part 11 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_11_0) total_11_8) total_11_16) total_11_24) total_11_32

end Chirped73
