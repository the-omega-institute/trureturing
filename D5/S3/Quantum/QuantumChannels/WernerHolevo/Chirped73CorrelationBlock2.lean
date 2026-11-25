/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73CorrelationBlock2
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Correlations.correlation_spec; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73CorrelationData.correlationAt
   digest: Checked partial and total correlation sums for order-73 block 2. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73CorrelationData

/-! Exact data and kernel checks for the order-73 chirped construction. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Chirped73

open ChirpedFinite

private theorem corr_6_0_0 : ∀ i : Fin 8, part 6 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 6 i.val) := by
  decide +kernel

private theorem corr_6_0_8 : ∀ i : Fin 8, part 6 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 6 (8 + i.val)) := by
  decide +kernel

private theorem corr_6_0_16 : ∀ i : Fin 8, part 6 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 6 (16 + i.val)) := by
  decide +kernel

private theorem corr_6_0_24 : ∀ i : Fin 8, part 6 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 6 (24 + i.val)) := by
  decide +kernel

private theorem corr_6_0_32 : ∀ i : Fin 6, part 6 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 6 (32 + i.val)) := by
  decide +kernel

private theorem corr_6_0 : ∀ i : ℕ, i < 38 → part 6 0 i = sumWindow (0 * width) (chunkLen n 0) (term 6 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_6_0_0) corr_6_0_8) corr_6_0_16) corr_6_0_24) corr_6_0_32

private theorem corr_6_1_0 : ∀ i : Fin 8, part 6 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 6 i.val) := by
  decide +kernel

private theorem corr_6_1_8 : ∀ i : Fin 8, part 6 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 6 (8 + i.val)) := by
  decide +kernel

private theorem corr_6_1_16 : ∀ i : Fin 8, part 6 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 6 (16 + i.val)) := by
  decide +kernel

private theorem corr_6_1_24 : ∀ i : Fin 8, part 6 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 6 (24 + i.val)) := by
  decide +kernel

private theorem corr_6_1_32 : ∀ i : Fin 6, part 6 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 6 (32 + i.val)) := by
  decide +kernel

private theorem corr_6_1 : ∀ i : ℕ, i < 38 → part 6 1 i = sumWindow (1 * width) (chunkLen n 1) (term 6 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_6_1_0) corr_6_1_8) corr_6_1_16) corr_6_1_24) corr_6_1_32

private theorem corr_6_2_0 : ∀ i : Fin 8, part 6 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 6 i.val) := by
  decide +kernel

private theorem corr_6_2_8 : ∀ i : Fin 8, part 6 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 6 (8 + i.val)) := by
  decide +kernel

private theorem corr_6_2_16 : ∀ i : Fin 8, part 6 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 6 (16 + i.val)) := by
  decide +kernel

private theorem corr_6_2_24 : ∀ i : Fin 8, part 6 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 6 (24 + i.val)) := by
  decide +kernel

private theorem corr_6_2_32 : ∀ i : Fin 6, part 6 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 6 (32 + i.val)) := by
  decide +kernel

private theorem corr_6_2 : ∀ i : ℕ, i < 38 → part 6 2 i = sumWindow (2 * width) (chunkLen n 2) (term 6 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_6_2_0) corr_6_2_8) corr_6_2_16) corr_6_2_24) corr_6_2_32

private theorem corr_6_3_0 : ∀ i : Fin 8, part 6 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 6 i.val) := by
  decide +kernel

private theorem corr_6_3_8 : ∀ i : Fin 8, part 6 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 6 (8 + i.val)) := by
  decide +kernel

private theorem corr_6_3_16 : ∀ i : Fin 8, part 6 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 6 (16 + i.val)) := by
  decide +kernel

private theorem corr_6_3_24 : ∀ i : Fin 8, part 6 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 6 (24 + i.val)) := by
  decide +kernel

private theorem corr_6_3_32 : ∀ i : Fin 6, part 6 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 6 (32 + i.val)) := by
  decide +kernel

private theorem corr_6_3 : ∀ i : ℕ, i < 38 → part 6 3 i = sumWindow (3 * width) (chunkLen n 3) (term 6 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_6_3_0) corr_6_3_8) corr_6_3_16) corr_6_3_24) corr_6_3_32

private theorem corr_6_4_0 : ∀ i : Fin 8, part 6 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 6 i.val) := by
  decide +kernel

private theorem corr_6_4_8 : ∀ i : Fin 8, part 6 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 6 (8 + i.val)) := by
  decide +kernel

private theorem corr_6_4_16 : ∀ i : Fin 8, part 6 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 6 (16 + i.val)) := by
  decide +kernel

private theorem corr_6_4_24 : ∀ i : Fin 8, part 6 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 6 (24 + i.val)) := by
  decide +kernel

private theorem corr_6_4_32 : ∀ i : Fin 6, part 6 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 6 (32 + i.val)) := by
  decide +kernel

private theorem corr_6_4 : ∀ i : ℕ, i < 38 → part 6 4 i = sumWindow (4 * width) (chunkLen n 4) (term 6 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_6_4_0) corr_6_4_8) corr_6_4_16) corr_6_4_24) corr_6_4_32

private theorem corr_6_5_0 : ∀ i : Fin 8, part 6 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 6 i.val) := by
  decide +kernel

private theorem corr_6_5_8 : ∀ i : Fin 8, part 6 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 6 (8 + i.val)) := by
  decide +kernel

private theorem corr_6_5_16 : ∀ i : Fin 8, part 6 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 6 (16 + i.val)) := by
  decide +kernel

private theorem corr_6_5_24 : ∀ i : Fin 8, part 6 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 6 (24 + i.val)) := by
  decide +kernel

private theorem corr_6_5_32 : ∀ i : Fin 6, part 6 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 6 (32 + i.val)) := by
  decide +kernel

private theorem corr_6_5 : ∀ i : ℕ, i < 38 → part 6 5 i = sumWindow (5 * width) (chunkLen n 5) (term 6 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_6_5_0) corr_6_5_8) corr_6_5_16) corr_6_5_24) corr_6_5_32

private theorem corr_6_6_0 : ∀ i : Fin 8, part 6 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 6 i.val) := by
  decide +kernel

private theorem corr_6_6_8 : ∀ i : Fin 8, part 6 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 6 (8 + i.val)) := by
  decide +kernel

private theorem corr_6_6_16 : ∀ i : Fin 8, part 6 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 6 (16 + i.val)) := by
  decide +kernel

private theorem corr_6_6_24 : ∀ i : Fin 8, part 6 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 6 (24 + i.val)) := by
  decide +kernel

private theorem corr_6_6_32 : ∀ i : Fin 6, part 6 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 6 (32 + i.val)) := by
  decide +kernel

private theorem corr_6_6 : ∀ i : ℕ, i < 38 → part 6 6 i = sumWindow (6 * width) (chunkLen n 6) (term 6 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_6_6_0) corr_6_6_8) corr_6_6_16) corr_6_6_24) corr_6_6_32

private theorem corr_6_7_0 : ∀ i : Fin 8, part 6 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 6 i.val) := by
  decide +kernel

private theorem corr_6_7_8 : ∀ i : Fin 8, part 6 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 6 (8 + i.val)) := by
  decide +kernel

private theorem corr_6_7_16 : ∀ i : Fin 8, part 6 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 6 (16 + i.val)) := by
  decide +kernel

private theorem corr_6_7_24 : ∀ i : Fin 8, part 6 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 6 (24 + i.val)) := by
  decide +kernel

private theorem corr_6_7_32 : ∀ i : Fin 6, part 6 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 6 (32 + i.val)) := by
  decide +kernel

private theorem corr_6_7 : ∀ i : ℕ, i < 38 → part 6 7 i = sumWindow (7 * width) (chunkLen n 7) (term 6 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_6_7_0) corr_6_7_8) corr_6_7_16) corr_6_7_24) corr_6_7_32

private theorem corr_6_8_0 : ∀ i : Fin 8, part 6 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 6 i.val) := by
  decide +kernel

private theorem corr_6_8_8 : ∀ i : Fin 8, part 6 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 6 (8 + i.val)) := by
  decide +kernel

private theorem corr_6_8_16 : ∀ i : Fin 8, part 6 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 6 (16 + i.val)) := by
  decide +kernel

private theorem corr_6_8_24 : ∀ i : Fin 8, part 6 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 6 (24 + i.val)) := by
  decide +kernel

private theorem corr_6_8_32 : ∀ i : Fin 6, part 6 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 6 (32 + i.val)) := by
  decide +kernel

private theorem corr_6_8 : ∀ i : ℕ, i < 38 → part 6 8 i = sumWindow (8 * width) (chunkLen n 8) (term 6 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_6_8_0) corr_6_8_8) corr_6_8_16) corr_6_8_24) corr_6_8_32

private theorem corr_6_9_0 : ∀ i : Fin 8, part 6 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 6 i.val) := by
  decide +kernel

private theorem corr_6_9_8 : ∀ i : Fin 8, part 6 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 6 (8 + i.val)) := by
  decide +kernel

private theorem corr_6_9_16 : ∀ i : Fin 8, part 6 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 6 (16 + i.val)) := by
  decide +kernel

private theorem corr_6_9_24 : ∀ i : Fin 8, part 6 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 6 (24 + i.val)) := by
  decide +kernel

private theorem corr_6_9_32 : ∀ i : Fin 6, part 6 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 6 (32 + i.val)) := by
  decide +kernel

private theorem corr_6_9 : ∀ i : ℕ, i < 38 → part 6 9 i = sumWindow (9 * width) (chunkLen n 9) (term 6 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_6_9_0) corr_6_9_8) corr_6_9_16) corr_6_9_24) corr_6_9_32

theorem corr_6 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 6 b slot = sumWindow (b * width) (chunkLen n b) (term 6 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_6_0) corr_6_1) corr_6_2) corr_6_3) corr_6_4) corr_6_5) corr_6_6) corr_6_7) corr_6_8) corr_6_9

private theorem total_6_0 : ∀ i : Fin 8, correlationAt 6 i.val = sumChunks n (fun b => part 6 b i.val) := by
  decide +kernel

private theorem total_6_8 : ∀ i : Fin 8, correlationAt 6 (8 + i.val) = sumChunks n (fun b => part 6 b (8 + i.val)) := by
  decide +kernel

private theorem total_6_16 : ∀ i : Fin 8, correlationAt 6 (16 + i.val) = sumChunks n (fun b => part 6 b (16 + i.val)) := by
  decide +kernel

private theorem total_6_24 : ∀ i : Fin 8, correlationAt 6 (24 + i.val) = sumChunks n (fun b => part 6 b (24 + i.val)) := by
  decide +kernel

private theorem total_6_32 : ∀ i : Fin 6, correlationAt 6 (32 + i.val) = sumChunks n (fun b => part 6 b (32 + i.val)) := by
  decide +kernel

theorem total_6 : ∀ i : ℕ, i < 38 → correlationAt 6 i = sumChunks n (fun b => part 6 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_6_0) total_6_8) total_6_16) total_6_24) total_6_32

private theorem corr_7_0_0 : ∀ i : Fin 8, part 7 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 7 i.val) := by
  decide +kernel

private theorem corr_7_0_8 : ∀ i : Fin 8, part 7 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 7 (8 + i.val)) := by
  decide +kernel

private theorem corr_7_0_16 : ∀ i : Fin 8, part 7 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 7 (16 + i.val)) := by
  decide +kernel

private theorem corr_7_0_24 : ∀ i : Fin 8, part 7 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 7 (24 + i.val)) := by
  decide +kernel

private theorem corr_7_0_32 : ∀ i : Fin 6, part 7 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 7 (32 + i.val)) := by
  decide +kernel

private theorem corr_7_0 : ∀ i : ℕ, i < 38 → part 7 0 i = sumWindow (0 * width) (chunkLen n 0) (term 7 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_7_0_0) corr_7_0_8) corr_7_0_16) corr_7_0_24) corr_7_0_32

private theorem corr_7_1_0 : ∀ i : Fin 8, part 7 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 7 i.val) := by
  decide +kernel

private theorem corr_7_1_8 : ∀ i : Fin 8, part 7 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 7 (8 + i.val)) := by
  decide +kernel

private theorem corr_7_1_16 : ∀ i : Fin 8, part 7 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 7 (16 + i.val)) := by
  decide +kernel

private theorem corr_7_1_24 : ∀ i : Fin 8, part 7 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 7 (24 + i.val)) := by
  decide +kernel

private theorem corr_7_1_32 : ∀ i : Fin 6, part 7 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 7 (32 + i.val)) := by
  decide +kernel

private theorem corr_7_1 : ∀ i : ℕ, i < 38 → part 7 1 i = sumWindow (1 * width) (chunkLen n 1) (term 7 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_7_1_0) corr_7_1_8) corr_7_1_16) corr_7_1_24) corr_7_1_32

private theorem corr_7_2_0 : ∀ i : Fin 8, part 7 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 7 i.val) := by
  decide +kernel

private theorem corr_7_2_8 : ∀ i : Fin 8, part 7 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 7 (8 + i.val)) := by
  decide +kernel

private theorem corr_7_2_16 : ∀ i : Fin 8, part 7 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 7 (16 + i.val)) := by
  decide +kernel

private theorem corr_7_2_24 : ∀ i : Fin 8, part 7 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 7 (24 + i.val)) := by
  decide +kernel

private theorem corr_7_2_32 : ∀ i : Fin 6, part 7 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 7 (32 + i.val)) := by
  decide +kernel

private theorem corr_7_2 : ∀ i : ℕ, i < 38 → part 7 2 i = sumWindow (2 * width) (chunkLen n 2) (term 7 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_7_2_0) corr_7_2_8) corr_7_2_16) corr_7_2_24) corr_7_2_32

private theorem corr_7_3_0 : ∀ i : Fin 8, part 7 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 7 i.val) := by
  decide +kernel

private theorem corr_7_3_8 : ∀ i : Fin 8, part 7 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 7 (8 + i.val)) := by
  decide +kernel

private theorem corr_7_3_16 : ∀ i : Fin 8, part 7 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 7 (16 + i.val)) := by
  decide +kernel

private theorem corr_7_3_24 : ∀ i : Fin 8, part 7 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 7 (24 + i.val)) := by
  decide +kernel

private theorem corr_7_3_32 : ∀ i : Fin 6, part 7 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 7 (32 + i.val)) := by
  decide +kernel

private theorem corr_7_3 : ∀ i : ℕ, i < 38 → part 7 3 i = sumWindow (3 * width) (chunkLen n 3) (term 7 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_7_3_0) corr_7_3_8) corr_7_3_16) corr_7_3_24) corr_7_3_32

private theorem corr_7_4_0 : ∀ i : Fin 8, part 7 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 7 i.val) := by
  decide +kernel

private theorem corr_7_4_8 : ∀ i : Fin 8, part 7 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 7 (8 + i.val)) := by
  decide +kernel

private theorem corr_7_4_16 : ∀ i : Fin 8, part 7 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 7 (16 + i.val)) := by
  decide +kernel

private theorem corr_7_4_24 : ∀ i : Fin 8, part 7 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 7 (24 + i.val)) := by
  decide +kernel

private theorem corr_7_4_32 : ∀ i : Fin 6, part 7 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 7 (32 + i.val)) := by
  decide +kernel

private theorem corr_7_4 : ∀ i : ℕ, i < 38 → part 7 4 i = sumWindow (4 * width) (chunkLen n 4) (term 7 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_7_4_0) corr_7_4_8) corr_7_4_16) corr_7_4_24) corr_7_4_32

private theorem corr_7_5_0 : ∀ i : Fin 8, part 7 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 7 i.val) := by
  decide +kernel

private theorem corr_7_5_8 : ∀ i : Fin 8, part 7 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 7 (8 + i.val)) := by
  decide +kernel

private theorem corr_7_5_16 : ∀ i : Fin 8, part 7 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 7 (16 + i.val)) := by
  decide +kernel

private theorem corr_7_5_24 : ∀ i : Fin 8, part 7 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 7 (24 + i.val)) := by
  decide +kernel

private theorem corr_7_5_32 : ∀ i : Fin 6, part 7 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 7 (32 + i.val)) := by
  decide +kernel

private theorem corr_7_5 : ∀ i : ℕ, i < 38 → part 7 5 i = sumWindow (5 * width) (chunkLen n 5) (term 7 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_7_5_0) corr_7_5_8) corr_7_5_16) corr_7_5_24) corr_7_5_32

private theorem corr_7_6_0 : ∀ i : Fin 8, part 7 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 7 i.val) := by
  decide +kernel

private theorem corr_7_6_8 : ∀ i : Fin 8, part 7 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 7 (8 + i.val)) := by
  decide +kernel

private theorem corr_7_6_16 : ∀ i : Fin 8, part 7 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 7 (16 + i.val)) := by
  decide +kernel

private theorem corr_7_6_24 : ∀ i : Fin 8, part 7 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 7 (24 + i.val)) := by
  decide +kernel

private theorem corr_7_6_32 : ∀ i : Fin 6, part 7 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 7 (32 + i.val)) := by
  decide +kernel

private theorem corr_7_6 : ∀ i : ℕ, i < 38 → part 7 6 i = sumWindow (6 * width) (chunkLen n 6) (term 7 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_7_6_0) corr_7_6_8) corr_7_6_16) corr_7_6_24) corr_7_6_32

private theorem corr_7_7_0 : ∀ i : Fin 8, part 7 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 7 i.val) := by
  decide +kernel

private theorem corr_7_7_8 : ∀ i : Fin 8, part 7 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 7 (8 + i.val)) := by
  decide +kernel

private theorem corr_7_7_16 : ∀ i : Fin 8, part 7 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 7 (16 + i.val)) := by
  decide +kernel

private theorem corr_7_7_24 : ∀ i : Fin 8, part 7 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 7 (24 + i.val)) := by
  decide +kernel

private theorem corr_7_7_32 : ∀ i : Fin 6, part 7 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 7 (32 + i.val)) := by
  decide +kernel

private theorem corr_7_7 : ∀ i : ℕ, i < 38 → part 7 7 i = sumWindow (7 * width) (chunkLen n 7) (term 7 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_7_7_0) corr_7_7_8) corr_7_7_16) corr_7_7_24) corr_7_7_32

private theorem corr_7_8_0 : ∀ i : Fin 8, part 7 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 7 i.val) := by
  decide +kernel

private theorem corr_7_8_8 : ∀ i : Fin 8, part 7 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 7 (8 + i.val)) := by
  decide +kernel

private theorem corr_7_8_16 : ∀ i : Fin 8, part 7 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 7 (16 + i.val)) := by
  decide +kernel

private theorem corr_7_8_24 : ∀ i : Fin 8, part 7 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 7 (24 + i.val)) := by
  decide +kernel

private theorem corr_7_8_32 : ∀ i : Fin 6, part 7 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 7 (32 + i.val)) := by
  decide +kernel

private theorem corr_7_8 : ∀ i : ℕ, i < 38 → part 7 8 i = sumWindow (8 * width) (chunkLen n 8) (term 7 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_7_8_0) corr_7_8_8) corr_7_8_16) corr_7_8_24) corr_7_8_32

private theorem corr_7_9_0 : ∀ i : Fin 8, part 7 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 7 i.val) := by
  decide +kernel

private theorem corr_7_9_8 : ∀ i : Fin 8, part 7 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 7 (8 + i.val)) := by
  decide +kernel

private theorem corr_7_9_16 : ∀ i : Fin 8, part 7 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 7 (16 + i.val)) := by
  decide +kernel

private theorem corr_7_9_24 : ∀ i : Fin 8, part 7 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 7 (24 + i.val)) := by
  decide +kernel

private theorem corr_7_9_32 : ∀ i : Fin 6, part 7 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 7 (32 + i.val)) := by
  decide +kernel

private theorem corr_7_9 : ∀ i : ℕ, i < 38 → part 7 9 i = sumWindow (9 * width) (chunkLen n 9) (term 7 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_7_9_0) corr_7_9_8) corr_7_9_16) corr_7_9_24) corr_7_9_32

theorem corr_7 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 7 b slot = sumWindow (b * width) (chunkLen n b) (term 7 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_7_0) corr_7_1) corr_7_2) corr_7_3) corr_7_4) corr_7_5) corr_7_6) corr_7_7) corr_7_8) corr_7_9

private theorem total_7_0 : ∀ i : Fin 8, correlationAt 7 i.val = sumChunks n (fun b => part 7 b i.val) := by
  decide +kernel

private theorem total_7_8 : ∀ i : Fin 8, correlationAt 7 (8 + i.val) = sumChunks n (fun b => part 7 b (8 + i.val)) := by
  decide +kernel

private theorem total_7_16 : ∀ i : Fin 8, correlationAt 7 (16 + i.val) = sumChunks n (fun b => part 7 b (16 + i.val)) := by
  decide +kernel

private theorem total_7_24 : ∀ i : Fin 8, correlationAt 7 (24 + i.val) = sumChunks n (fun b => part 7 b (24 + i.val)) := by
  decide +kernel

private theorem total_7_32 : ∀ i : Fin 6, correlationAt 7 (32 + i.val) = sumChunks n (fun b => part 7 b (32 + i.val)) := by
  decide +kernel

theorem total_7 : ∀ i : ℕ, i < 38 → correlationAt 7 i = sumChunks n (fun b => part 7 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_7_0) total_7_8) total_7_16) total_7_24) total_7_32

private theorem corr_8_0_0 : ∀ i : Fin 8, part 8 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 8 i.val) := by
  decide +kernel

private theorem corr_8_0_8 : ∀ i : Fin 8, part 8 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 8 (8 + i.val)) := by
  decide +kernel

private theorem corr_8_0_16 : ∀ i : Fin 8, part 8 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 8 (16 + i.val)) := by
  decide +kernel

private theorem corr_8_0_24 : ∀ i : Fin 8, part 8 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 8 (24 + i.val)) := by
  decide +kernel

private theorem corr_8_0_32 : ∀ i : Fin 6, part 8 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 8 (32 + i.val)) := by
  decide +kernel

private theorem corr_8_0 : ∀ i : ℕ, i < 38 → part 8 0 i = sumWindow (0 * width) (chunkLen n 0) (term 8 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_8_0_0) corr_8_0_8) corr_8_0_16) corr_8_0_24) corr_8_0_32

private theorem corr_8_1_0 : ∀ i : Fin 8, part 8 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 8 i.val) := by
  decide +kernel

private theorem corr_8_1_8 : ∀ i : Fin 8, part 8 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 8 (8 + i.val)) := by
  decide +kernel

private theorem corr_8_1_16 : ∀ i : Fin 8, part 8 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 8 (16 + i.val)) := by
  decide +kernel

private theorem corr_8_1_24 : ∀ i : Fin 8, part 8 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 8 (24 + i.val)) := by
  decide +kernel

private theorem corr_8_1_32 : ∀ i : Fin 6, part 8 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 8 (32 + i.val)) := by
  decide +kernel

private theorem corr_8_1 : ∀ i : ℕ, i < 38 → part 8 1 i = sumWindow (1 * width) (chunkLen n 1) (term 8 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_8_1_0) corr_8_1_8) corr_8_1_16) corr_8_1_24) corr_8_1_32

private theorem corr_8_2_0 : ∀ i : Fin 8, part 8 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 8 i.val) := by
  decide +kernel

private theorem corr_8_2_8 : ∀ i : Fin 8, part 8 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 8 (8 + i.val)) := by
  decide +kernel

private theorem corr_8_2_16 : ∀ i : Fin 8, part 8 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 8 (16 + i.val)) := by
  decide +kernel

private theorem corr_8_2_24 : ∀ i : Fin 8, part 8 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 8 (24 + i.val)) := by
  decide +kernel

private theorem corr_8_2_32 : ∀ i : Fin 6, part 8 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 8 (32 + i.val)) := by
  decide +kernel

private theorem corr_8_2 : ∀ i : ℕ, i < 38 → part 8 2 i = sumWindow (2 * width) (chunkLen n 2) (term 8 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_8_2_0) corr_8_2_8) corr_8_2_16) corr_8_2_24) corr_8_2_32

private theorem corr_8_3_0 : ∀ i : Fin 8, part 8 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 8 i.val) := by
  decide +kernel

private theorem corr_8_3_8 : ∀ i : Fin 8, part 8 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 8 (8 + i.val)) := by
  decide +kernel

private theorem corr_8_3_16 : ∀ i : Fin 8, part 8 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 8 (16 + i.val)) := by
  decide +kernel

private theorem corr_8_3_24 : ∀ i : Fin 8, part 8 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 8 (24 + i.val)) := by
  decide +kernel

private theorem corr_8_3_32 : ∀ i : Fin 6, part 8 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 8 (32 + i.val)) := by
  decide +kernel

private theorem corr_8_3 : ∀ i : ℕ, i < 38 → part 8 3 i = sumWindow (3 * width) (chunkLen n 3) (term 8 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_8_3_0) corr_8_3_8) corr_8_3_16) corr_8_3_24) corr_8_3_32

private theorem corr_8_4_0 : ∀ i : Fin 8, part 8 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 8 i.val) := by
  decide +kernel

private theorem corr_8_4_8 : ∀ i : Fin 8, part 8 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 8 (8 + i.val)) := by
  decide +kernel

private theorem corr_8_4_16 : ∀ i : Fin 8, part 8 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 8 (16 + i.val)) := by
  decide +kernel

private theorem corr_8_4_24 : ∀ i : Fin 8, part 8 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 8 (24 + i.val)) := by
  decide +kernel

private theorem corr_8_4_32 : ∀ i : Fin 6, part 8 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 8 (32 + i.val)) := by
  decide +kernel

private theorem corr_8_4 : ∀ i : ℕ, i < 38 → part 8 4 i = sumWindow (4 * width) (chunkLen n 4) (term 8 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_8_4_0) corr_8_4_8) corr_8_4_16) corr_8_4_24) corr_8_4_32

private theorem corr_8_5_0 : ∀ i : Fin 8, part 8 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 8 i.val) := by
  decide +kernel

private theorem corr_8_5_8 : ∀ i : Fin 8, part 8 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 8 (8 + i.val)) := by
  decide +kernel

private theorem corr_8_5_16 : ∀ i : Fin 8, part 8 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 8 (16 + i.val)) := by
  decide +kernel

private theorem corr_8_5_24 : ∀ i : Fin 8, part 8 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 8 (24 + i.val)) := by
  decide +kernel

private theorem corr_8_5_32 : ∀ i : Fin 6, part 8 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 8 (32 + i.val)) := by
  decide +kernel

private theorem corr_8_5 : ∀ i : ℕ, i < 38 → part 8 5 i = sumWindow (5 * width) (chunkLen n 5) (term 8 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_8_5_0) corr_8_5_8) corr_8_5_16) corr_8_5_24) corr_8_5_32

private theorem corr_8_6_0 : ∀ i : Fin 8, part 8 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 8 i.val) := by
  decide +kernel

private theorem corr_8_6_8 : ∀ i : Fin 8, part 8 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 8 (8 + i.val)) := by
  decide +kernel

private theorem corr_8_6_16 : ∀ i : Fin 8, part 8 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 8 (16 + i.val)) := by
  decide +kernel

private theorem corr_8_6_24 : ∀ i : Fin 8, part 8 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 8 (24 + i.val)) := by
  decide +kernel

private theorem corr_8_6_32 : ∀ i : Fin 6, part 8 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 8 (32 + i.val)) := by
  decide +kernel

private theorem corr_8_6 : ∀ i : ℕ, i < 38 → part 8 6 i = sumWindow (6 * width) (chunkLen n 6) (term 8 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_8_6_0) corr_8_6_8) corr_8_6_16) corr_8_6_24) corr_8_6_32

private theorem corr_8_7_0 : ∀ i : Fin 8, part 8 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 8 i.val) := by
  decide +kernel

private theorem corr_8_7_8 : ∀ i : Fin 8, part 8 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 8 (8 + i.val)) := by
  decide +kernel

private theorem corr_8_7_16 : ∀ i : Fin 8, part 8 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 8 (16 + i.val)) := by
  decide +kernel

private theorem corr_8_7_24 : ∀ i : Fin 8, part 8 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 8 (24 + i.val)) := by
  decide +kernel

private theorem corr_8_7_32 : ∀ i : Fin 6, part 8 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 8 (32 + i.val)) := by
  decide +kernel

private theorem corr_8_7 : ∀ i : ℕ, i < 38 → part 8 7 i = sumWindow (7 * width) (chunkLen n 7) (term 8 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_8_7_0) corr_8_7_8) corr_8_7_16) corr_8_7_24) corr_8_7_32

private theorem corr_8_8_0 : ∀ i : Fin 8, part 8 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 8 i.val) := by
  decide +kernel

private theorem corr_8_8_8 : ∀ i : Fin 8, part 8 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 8 (8 + i.val)) := by
  decide +kernel

private theorem corr_8_8_16 : ∀ i : Fin 8, part 8 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 8 (16 + i.val)) := by
  decide +kernel

private theorem corr_8_8_24 : ∀ i : Fin 8, part 8 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 8 (24 + i.val)) := by
  decide +kernel

private theorem corr_8_8_32 : ∀ i : Fin 6, part 8 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 8 (32 + i.val)) := by
  decide +kernel

private theorem corr_8_8 : ∀ i : ℕ, i < 38 → part 8 8 i = sumWindow (8 * width) (chunkLen n 8) (term 8 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_8_8_0) corr_8_8_8) corr_8_8_16) corr_8_8_24) corr_8_8_32

private theorem corr_8_9_0 : ∀ i : Fin 8, part 8 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 8 i.val) := by
  decide +kernel

private theorem corr_8_9_8 : ∀ i : Fin 8, part 8 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 8 (8 + i.val)) := by
  decide +kernel

private theorem corr_8_9_16 : ∀ i : Fin 8, part 8 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 8 (16 + i.val)) := by
  decide +kernel

private theorem corr_8_9_24 : ∀ i : Fin 8, part 8 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 8 (24 + i.val)) := by
  decide +kernel

private theorem corr_8_9_32 : ∀ i : Fin 6, part 8 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 8 (32 + i.val)) := by
  decide +kernel

private theorem corr_8_9 : ∀ i : ℕ, i < 38 → part 8 9 i = sumWindow (9 * width) (chunkLen n 9) (term 8 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_8_9_0) corr_8_9_8) corr_8_9_16) corr_8_9_24) corr_8_9_32

theorem corr_8 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 8 b slot = sumWindow (b * width) (chunkLen n b) (term 8 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_8_0) corr_8_1) corr_8_2) corr_8_3) corr_8_4) corr_8_5) corr_8_6) corr_8_7) corr_8_8) corr_8_9

private theorem total_8_0 : ∀ i : Fin 8, correlationAt 8 i.val = sumChunks n (fun b => part 8 b i.val) := by
  decide +kernel

private theorem total_8_8 : ∀ i : Fin 8, correlationAt 8 (8 + i.val) = sumChunks n (fun b => part 8 b (8 + i.val)) := by
  decide +kernel

private theorem total_8_16 : ∀ i : Fin 8, correlationAt 8 (16 + i.val) = sumChunks n (fun b => part 8 b (16 + i.val)) := by
  decide +kernel

private theorem total_8_24 : ∀ i : Fin 8, correlationAt 8 (24 + i.val) = sumChunks n (fun b => part 8 b (24 + i.val)) := by
  decide +kernel

private theorem total_8_32 : ∀ i : Fin 6, correlationAt 8 (32 + i.val) = sumChunks n (fun b => part 8 b (32 + i.val)) := by
  decide +kernel

theorem total_8 : ∀ i : ℕ, i < 38 → correlationAt 8 i = sumChunks n (fun b => part 8 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_8_0) total_8_8) total_8_16) total_8_24) total_8_32

end Chirped73
