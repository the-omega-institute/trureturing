/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73CorrelationBlock0
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Correlations.correlation_spec; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73CorrelationData.correlationAt
   digest: Checked partial and total correlation sums for order-73 block 0. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73CorrelationData

/-! Exact data and kernel checks for the order-73 chirped construction. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Chirped73

open ChirpedFinite

private theorem corr_0_0_0 : ∀ i : Fin 8, part 0 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 0 i.val) := by
  decide +kernel

private theorem corr_0_0_8 : ∀ i : Fin 8, part 0 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 0 (8 + i.val)) := by
  decide +kernel

private theorem corr_0_0_16 : ∀ i : Fin 8, part 0 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 0 (16 + i.val)) := by
  decide +kernel

private theorem corr_0_0_24 : ∀ i : Fin 8, part 0 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 0 (24 + i.val)) := by
  decide +kernel

private theorem corr_0_0_32 : ∀ i : Fin 6, part 0 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 0 (32 + i.val)) := by
  decide +kernel

private theorem corr_0_0 : ∀ i : ℕ, i < 38 → part 0 0 i = sumWindow (0 * width) (chunkLen n 0) (term 0 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_0_0_0) corr_0_0_8) corr_0_0_16) corr_0_0_24) corr_0_0_32

private theorem corr_0_1_0 : ∀ i : Fin 8, part 0 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 0 i.val) := by
  decide +kernel

private theorem corr_0_1_8 : ∀ i : Fin 8, part 0 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 0 (8 + i.val)) := by
  decide +kernel

private theorem corr_0_1_16 : ∀ i : Fin 8, part 0 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 0 (16 + i.val)) := by
  decide +kernel

private theorem corr_0_1_24 : ∀ i : Fin 8, part 0 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 0 (24 + i.val)) := by
  decide +kernel

private theorem corr_0_1_32 : ∀ i : Fin 6, part 0 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 0 (32 + i.val)) := by
  decide +kernel

private theorem corr_0_1 : ∀ i : ℕ, i < 38 → part 0 1 i = sumWindow (1 * width) (chunkLen n 1) (term 0 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_0_1_0) corr_0_1_8) corr_0_1_16) corr_0_1_24) corr_0_1_32

private theorem corr_0_2_0 : ∀ i : Fin 8, part 0 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 0 i.val) := by
  decide +kernel

private theorem corr_0_2_8 : ∀ i : Fin 8, part 0 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 0 (8 + i.val)) := by
  decide +kernel

private theorem corr_0_2_16 : ∀ i : Fin 8, part 0 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 0 (16 + i.val)) := by
  decide +kernel

private theorem corr_0_2_24 : ∀ i : Fin 8, part 0 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 0 (24 + i.val)) := by
  decide +kernel

private theorem corr_0_2_32 : ∀ i : Fin 6, part 0 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 0 (32 + i.val)) := by
  decide +kernel

private theorem corr_0_2 : ∀ i : ℕ, i < 38 → part 0 2 i = sumWindow (2 * width) (chunkLen n 2) (term 0 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_0_2_0) corr_0_2_8) corr_0_2_16) corr_0_2_24) corr_0_2_32

private theorem corr_0_3_0 : ∀ i : Fin 8, part 0 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 0 i.val) := by
  decide +kernel

private theorem corr_0_3_8 : ∀ i : Fin 8, part 0 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 0 (8 + i.val)) := by
  decide +kernel

private theorem corr_0_3_16 : ∀ i : Fin 8, part 0 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 0 (16 + i.val)) := by
  decide +kernel

private theorem corr_0_3_24 : ∀ i : Fin 8, part 0 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 0 (24 + i.val)) := by
  decide +kernel

private theorem corr_0_3_32 : ∀ i : Fin 6, part 0 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 0 (32 + i.val)) := by
  decide +kernel

private theorem corr_0_3 : ∀ i : ℕ, i < 38 → part 0 3 i = sumWindow (3 * width) (chunkLen n 3) (term 0 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_0_3_0) corr_0_3_8) corr_0_3_16) corr_0_3_24) corr_0_3_32

private theorem corr_0_4_0 : ∀ i : Fin 8, part 0 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 0 i.val) := by
  decide +kernel

private theorem corr_0_4_8 : ∀ i : Fin 8, part 0 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 0 (8 + i.val)) := by
  decide +kernel

private theorem corr_0_4_16 : ∀ i : Fin 8, part 0 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 0 (16 + i.val)) := by
  decide +kernel

private theorem corr_0_4_24 : ∀ i : Fin 8, part 0 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 0 (24 + i.val)) := by
  decide +kernel

private theorem corr_0_4_32 : ∀ i : Fin 6, part 0 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 0 (32 + i.val)) := by
  decide +kernel

private theorem corr_0_4 : ∀ i : ℕ, i < 38 → part 0 4 i = sumWindow (4 * width) (chunkLen n 4) (term 0 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_0_4_0) corr_0_4_8) corr_0_4_16) corr_0_4_24) corr_0_4_32

private theorem corr_0_5_0 : ∀ i : Fin 8, part 0 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 0 i.val) := by
  decide +kernel

private theorem corr_0_5_8 : ∀ i : Fin 8, part 0 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 0 (8 + i.val)) := by
  decide +kernel

private theorem corr_0_5_16 : ∀ i : Fin 8, part 0 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 0 (16 + i.val)) := by
  decide +kernel

private theorem corr_0_5_24 : ∀ i : Fin 8, part 0 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 0 (24 + i.val)) := by
  decide +kernel

private theorem corr_0_5_32 : ∀ i : Fin 6, part 0 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 0 (32 + i.val)) := by
  decide +kernel

private theorem corr_0_5 : ∀ i : ℕ, i < 38 → part 0 5 i = sumWindow (5 * width) (chunkLen n 5) (term 0 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_0_5_0) corr_0_5_8) corr_0_5_16) corr_0_5_24) corr_0_5_32

private theorem corr_0_6_0 : ∀ i : Fin 8, part 0 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 0 i.val) := by
  decide +kernel

private theorem corr_0_6_8 : ∀ i : Fin 8, part 0 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 0 (8 + i.val)) := by
  decide +kernel

private theorem corr_0_6_16 : ∀ i : Fin 8, part 0 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 0 (16 + i.val)) := by
  decide +kernel

private theorem corr_0_6_24 : ∀ i : Fin 8, part 0 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 0 (24 + i.val)) := by
  decide +kernel

private theorem corr_0_6_32 : ∀ i : Fin 6, part 0 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 0 (32 + i.val)) := by
  decide +kernel

private theorem corr_0_6 : ∀ i : ℕ, i < 38 → part 0 6 i = sumWindow (6 * width) (chunkLen n 6) (term 0 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_0_6_0) corr_0_6_8) corr_0_6_16) corr_0_6_24) corr_0_6_32

private theorem corr_0_7_0 : ∀ i : Fin 8, part 0 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 0 i.val) := by
  decide +kernel

private theorem corr_0_7_8 : ∀ i : Fin 8, part 0 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 0 (8 + i.val)) := by
  decide +kernel

private theorem corr_0_7_16 : ∀ i : Fin 8, part 0 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 0 (16 + i.val)) := by
  decide +kernel

private theorem corr_0_7_24 : ∀ i : Fin 8, part 0 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 0 (24 + i.val)) := by
  decide +kernel

private theorem corr_0_7_32 : ∀ i : Fin 6, part 0 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 0 (32 + i.val)) := by
  decide +kernel

private theorem corr_0_7 : ∀ i : ℕ, i < 38 → part 0 7 i = sumWindow (7 * width) (chunkLen n 7) (term 0 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_0_7_0) corr_0_7_8) corr_0_7_16) corr_0_7_24) corr_0_7_32

private theorem corr_0_8_0 : ∀ i : Fin 8, part 0 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 0 i.val) := by
  decide +kernel

private theorem corr_0_8_8 : ∀ i : Fin 8, part 0 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 0 (8 + i.val)) := by
  decide +kernel

private theorem corr_0_8_16 : ∀ i : Fin 8, part 0 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 0 (16 + i.val)) := by
  decide +kernel

private theorem corr_0_8_24 : ∀ i : Fin 8, part 0 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 0 (24 + i.val)) := by
  decide +kernel

private theorem corr_0_8_32 : ∀ i : Fin 6, part 0 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 0 (32 + i.val)) := by
  decide +kernel

private theorem corr_0_8 : ∀ i : ℕ, i < 38 → part 0 8 i = sumWindow (8 * width) (chunkLen n 8) (term 0 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_0_8_0) corr_0_8_8) corr_0_8_16) corr_0_8_24) corr_0_8_32

private theorem corr_0_9_0 : ∀ i : Fin 8, part 0 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 0 i.val) := by
  decide +kernel

private theorem corr_0_9_8 : ∀ i : Fin 8, part 0 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 0 (8 + i.val)) := by
  decide +kernel

private theorem corr_0_9_16 : ∀ i : Fin 8, part 0 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 0 (16 + i.val)) := by
  decide +kernel

private theorem corr_0_9_24 : ∀ i : Fin 8, part 0 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 0 (24 + i.val)) := by
  decide +kernel

private theorem corr_0_9_32 : ∀ i : Fin 6, part 0 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 0 (32 + i.val)) := by
  decide +kernel

private theorem corr_0_9 : ∀ i : ℕ, i < 38 → part 0 9 i = sumWindow (9 * width) (chunkLen n 9) (term 0 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_0_9_0) corr_0_9_8) corr_0_9_16) corr_0_9_24) corr_0_9_32

theorem corr_0 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 0 b slot = sumWindow (b * width) (chunkLen n b) (term 0 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_0_0) corr_0_1) corr_0_2) corr_0_3) corr_0_4) corr_0_5) corr_0_6) corr_0_7) corr_0_8) corr_0_9

private theorem total_0_0 : ∀ i : Fin 8, correlationAt 0 i.val = sumChunks n (fun b => part 0 b i.val) := by
  decide +kernel

private theorem total_0_8 : ∀ i : Fin 8, correlationAt 0 (8 + i.val) = sumChunks n (fun b => part 0 b (8 + i.val)) := by
  decide +kernel

private theorem total_0_16 : ∀ i : Fin 8, correlationAt 0 (16 + i.val) = sumChunks n (fun b => part 0 b (16 + i.val)) := by
  decide +kernel

private theorem total_0_24 : ∀ i : Fin 8, correlationAt 0 (24 + i.val) = sumChunks n (fun b => part 0 b (24 + i.val)) := by
  decide +kernel

private theorem total_0_32 : ∀ i : Fin 6, correlationAt 0 (32 + i.val) = sumChunks n (fun b => part 0 b (32 + i.val)) := by
  decide +kernel

theorem total_0 : ∀ i : ℕ, i < 38 → correlationAt 0 i = sumChunks n (fun b => part 0 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_0_0) total_0_8) total_0_16) total_0_24) total_0_32

private theorem corr_1_0_0 : ∀ i : Fin 8, part 1 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 1 i.val) := by
  decide +kernel

private theorem corr_1_0_8 : ∀ i : Fin 8, part 1 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 1 (8 + i.val)) := by
  decide +kernel

private theorem corr_1_0_16 : ∀ i : Fin 8, part 1 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 1 (16 + i.val)) := by
  decide +kernel

private theorem corr_1_0_24 : ∀ i : Fin 8, part 1 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 1 (24 + i.val)) := by
  decide +kernel

private theorem corr_1_0_32 : ∀ i : Fin 6, part 1 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 1 (32 + i.val)) := by
  decide +kernel

private theorem corr_1_0 : ∀ i : ℕ, i < 38 → part 1 0 i = sumWindow (0 * width) (chunkLen n 0) (term 1 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_1_0_0) corr_1_0_8) corr_1_0_16) corr_1_0_24) corr_1_0_32

private theorem corr_1_1_0 : ∀ i : Fin 8, part 1 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 1 i.val) := by
  decide +kernel

private theorem corr_1_1_8 : ∀ i : Fin 8, part 1 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 1 (8 + i.val)) := by
  decide +kernel

private theorem corr_1_1_16 : ∀ i : Fin 8, part 1 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 1 (16 + i.val)) := by
  decide +kernel

private theorem corr_1_1_24 : ∀ i : Fin 8, part 1 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 1 (24 + i.val)) := by
  decide +kernel

private theorem corr_1_1_32 : ∀ i : Fin 6, part 1 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 1 (32 + i.val)) := by
  decide +kernel

private theorem corr_1_1 : ∀ i : ℕ, i < 38 → part 1 1 i = sumWindow (1 * width) (chunkLen n 1) (term 1 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_1_1_0) corr_1_1_8) corr_1_1_16) corr_1_1_24) corr_1_1_32

private theorem corr_1_2_0 : ∀ i : Fin 8, part 1 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 1 i.val) := by
  decide +kernel

private theorem corr_1_2_8 : ∀ i : Fin 8, part 1 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 1 (8 + i.val)) := by
  decide +kernel

private theorem corr_1_2_16 : ∀ i : Fin 8, part 1 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 1 (16 + i.val)) := by
  decide +kernel

private theorem corr_1_2_24 : ∀ i : Fin 8, part 1 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 1 (24 + i.val)) := by
  decide +kernel

private theorem corr_1_2_32 : ∀ i : Fin 6, part 1 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 1 (32 + i.val)) := by
  decide +kernel

private theorem corr_1_2 : ∀ i : ℕ, i < 38 → part 1 2 i = sumWindow (2 * width) (chunkLen n 2) (term 1 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_1_2_0) corr_1_2_8) corr_1_2_16) corr_1_2_24) corr_1_2_32

private theorem corr_1_3_0 : ∀ i : Fin 8, part 1 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 1 i.val) := by
  decide +kernel

private theorem corr_1_3_8 : ∀ i : Fin 8, part 1 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 1 (8 + i.val)) := by
  decide +kernel

private theorem corr_1_3_16 : ∀ i : Fin 8, part 1 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 1 (16 + i.val)) := by
  decide +kernel

private theorem corr_1_3_24 : ∀ i : Fin 8, part 1 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 1 (24 + i.val)) := by
  decide +kernel

private theorem corr_1_3_32 : ∀ i : Fin 6, part 1 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 1 (32 + i.val)) := by
  decide +kernel

private theorem corr_1_3 : ∀ i : ℕ, i < 38 → part 1 3 i = sumWindow (3 * width) (chunkLen n 3) (term 1 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_1_3_0) corr_1_3_8) corr_1_3_16) corr_1_3_24) corr_1_3_32

private theorem corr_1_4_0 : ∀ i : Fin 8, part 1 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 1 i.val) := by
  decide +kernel

private theorem corr_1_4_8 : ∀ i : Fin 8, part 1 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 1 (8 + i.val)) := by
  decide +kernel

private theorem corr_1_4_16 : ∀ i : Fin 8, part 1 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 1 (16 + i.val)) := by
  decide +kernel

private theorem corr_1_4_24 : ∀ i : Fin 8, part 1 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 1 (24 + i.val)) := by
  decide +kernel

private theorem corr_1_4_32 : ∀ i : Fin 6, part 1 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 1 (32 + i.val)) := by
  decide +kernel

private theorem corr_1_4 : ∀ i : ℕ, i < 38 → part 1 4 i = sumWindow (4 * width) (chunkLen n 4) (term 1 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_1_4_0) corr_1_4_8) corr_1_4_16) corr_1_4_24) corr_1_4_32

private theorem corr_1_5_0 : ∀ i : Fin 8, part 1 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 1 i.val) := by
  decide +kernel

private theorem corr_1_5_8 : ∀ i : Fin 8, part 1 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 1 (8 + i.val)) := by
  decide +kernel

private theorem corr_1_5_16 : ∀ i : Fin 8, part 1 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 1 (16 + i.val)) := by
  decide +kernel

private theorem corr_1_5_24 : ∀ i : Fin 8, part 1 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 1 (24 + i.val)) := by
  decide +kernel

private theorem corr_1_5_32 : ∀ i : Fin 6, part 1 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 1 (32 + i.val)) := by
  decide +kernel

private theorem corr_1_5 : ∀ i : ℕ, i < 38 → part 1 5 i = sumWindow (5 * width) (chunkLen n 5) (term 1 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_1_5_0) corr_1_5_8) corr_1_5_16) corr_1_5_24) corr_1_5_32

private theorem corr_1_6_0 : ∀ i : Fin 8, part 1 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 1 i.val) := by
  decide +kernel

private theorem corr_1_6_8 : ∀ i : Fin 8, part 1 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 1 (8 + i.val)) := by
  decide +kernel

private theorem corr_1_6_16 : ∀ i : Fin 8, part 1 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 1 (16 + i.val)) := by
  decide +kernel

private theorem corr_1_6_24 : ∀ i : Fin 8, part 1 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 1 (24 + i.val)) := by
  decide +kernel

private theorem corr_1_6_32 : ∀ i : Fin 6, part 1 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 1 (32 + i.val)) := by
  decide +kernel

private theorem corr_1_6 : ∀ i : ℕ, i < 38 → part 1 6 i = sumWindow (6 * width) (chunkLen n 6) (term 1 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_1_6_0) corr_1_6_8) corr_1_6_16) corr_1_6_24) corr_1_6_32

private theorem corr_1_7_0 : ∀ i : Fin 8, part 1 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 1 i.val) := by
  decide +kernel

private theorem corr_1_7_8 : ∀ i : Fin 8, part 1 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 1 (8 + i.val)) := by
  decide +kernel

private theorem corr_1_7_16 : ∀ i : Fin 8, part 1 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 1 (16 + i.val)) := by
  decide +kernel

private theorem corr_1_7_24 : ∀ i : Fin 8, part 1 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 1 (24 + i.val)) := by
  decide +kernel

private theorem corr_1_7_32 : ∀ i : Fin 6, part 1 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 1 (32 + i.val)) := by
  decide +kernel

private theorem corr_1_7 : ∀ i : ℕ, i < 38 → part 1 7 i = sumWindow (7 * width) (chunkLen n 7) (term 1 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_1_7_0) corr_1_7_8) corr_1_7_16) corr_1_7_24) corr_1_7_32

private theorem corr_1_8_0 : ∀ i : Fin 8, part 1 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 1 i.val) := by
  decide +kernel

private theorem corr_1_8_8 : ∀ i : Fin 8, part 1 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 1 (8 + i.val)) := by
  decide +kernel

private theorem corr_1_8_16 : ∀ i : Fin 8, part 1 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 1 (16 + i.val)) := by
  decide +kernel

private theorem corr_1_8_24 : ∀ i : Fin 8, part 1 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 1 (24 + i.val)) := by
  decide +kernel

private theorem corr_1_8_32 : ∀ i : Fin 6, part 1 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 1 (32 + i.val)) := by
  decide +kernel

private theorem corr_1_8 : ∀ i : ℕ, i < 38 → part 1 8 i = sumWindow (8 * width) (chunkLen n 8) (term 1 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_1_8_0) corr_1_8_8) corr_1_8_16) corr_1_8_24) corr_1_8_32

private theorem corr_1_9_0 : ∀ i : Fin 8, part 1 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 1 i.val) := by
  decide +kernel

private theorem corr_1_9_8 : ∀ i : Fin 8, part 1 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 1 (8 + i.val)) := by
  decide +kernel

private theorem corr_1_9_16 : ∀ i : Fin 8, part 1 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 1 (16 + i.val)) := by
  decide +kernel

private theorem corr_1_9_24 : ∀ i : Fin 8, part 1 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 1 (24 + i.val)) := by
  decide +kernel

private theorem corr_1_9_32 : ∀ i : Fin 6, part 1 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 1 (32 + i.val)) := by
  decide +kernel

private theorem corr_1_9 : ∀ i : ℕ, i < 38 → part 1 9 i = sumWindow (9 * width) (chunkLen n 9) (term 1 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_1_9_0) corr_1_9_8) corr_1_9_16) corr_1_9_24) corr_1_9_32

theorem corr_1 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 1 b slot = sumWindow (b * width) (chunkLen n b) (term 1 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_1_0) corr_1_1) corr_1_2) corr_1_3) corr_1_4) corr_1_5) corr_1_6) corr_1_7) corr_1_8) corr_1_9

private theorem total_1_0 : ∀ i : Fin 8, correlationAt 1 i.val = sumChunks n (fun b => part 1 b i.val) := by
  decide +kernel

private theorem total_1_8 : ∀ i : Fin 8, correlationAt 1 (8 + i.val) = sumChunks n (fun b => part 1 b (8 + i.val)) := by
  decide +kernel

private theorem total_1_16 : ∀ i : Fin 8, correlationAt 1 (16 + i.val) = sumChunks n (fun b => part 1 b (16 + i.val)) := by
  decide +kernel

private theorem total_1_24 : ∀ i : Fin 8, correlationAt 1 (24 + i.val) = sumChunks n (fun b => part 1 b (24 + i.val)) := by
  decide +kernel

private theorem total_1_32 : ∀ i : Fin 6, correlationAt 1 (32 + i.val) = sumChunks n (fun b => part 1 b (32 + i.val)) := by
  decide +kernel

theorem total_1 : ∀ i : ℕ, i < 38 → correlationAt 1 i = sumChunks n (fun b => part 1 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_1_0) total_1_8) total_1_16) total_1_24) total_1_32

private theorem corr_2_0_0 : ∀ i : Fin 8, part 2 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 2 i.val) := by
  decide +kernel

private theorem corr_2_0_8 : ∀ i : Fin 8, part 2 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 2 (8 + i.val)) := by
  decide +kernel

private theorem corr_2_0_16 : ∀ i : Fin 8, part 2 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 2 (16 + i.val)) := by
  decide +kernel

private theorem corr_2_0_24 : ∀ i : Fin 8, part 2 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 2 (24 + i.val)) := by
  decide +kernel

private theorem corr_2_0_32 : ∀ i : Fin 6, part 2 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 2 (32 + i.val)) := by
  decide +kernel

private theorem corr_2_0 : ∀ i : ℕ, i < 38 → part 2 0 i = sumWindow (0 * width) (chunkLen n 0) (term 2 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_2_0_0) corr_2_0_8) corr_2_0_16) corr_2_0_24) corr_2_0_32

private theorem corr_2_1_0 : ∀ i : Fin 8, part 2 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 2 i.val) := by
  decide +kernel

private theorem corr_2_1_8 : ∀ i : Fin 8, part 2 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 2 (8 + i.val)) := by
  decide +kernel

private theorem corr_2_1_16 : ∀ i : Fin 8, part 2 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 2 (16 + i.val)) := by
  decide +kernel

private theorem corr_2_1_24 : ∀ i : Fin 8, part 2 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 2 (24 + i.val)) := by
  decide +kernel

private theorem corr_2_1_32 : ∀ i : Fin 6, part 2 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 2 (32 + i.val)) := by
  decide +kernel

private theorem corr_2_1 : ∀ i : ℕ, i < 38 → part 2 1 i = sumWindow (1 * width) (chunkLen n 1) (term 2 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_2_1_0) corr_2_1_8) corr_2_1_16) corr_2_1_24) corr_2_1_32

private theorem corr_2_2_0 : ∀ i : Fin 8, part 2 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 2 i.val) := by
  decide +kernel

private theorem corr_2_2_8 : ∀ i : Fin 8, part 2 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 2 (8 + i.val)) := by
  decide +kernel

private theorem corr_2_2_16 : ∀ i : Fin 8, part 2 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 2 (16 + i.val)) := by
  decide +kernel

private theorem corr_2_2_24 : ∀ i : Fin 8, part 2 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 2 (24 + i.val)) := by
  decide +kernel

private theorem corr_2_2_32 : ∀ i : Fin 6, part 2 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 2 (32 + i.val)) := by
  decide +kernel

private theorem corr_2_2 : ∀ i : ℕ, i < 38 → part 2 2 i = sumWindow (2 * width) (chunkLen n 2) (term 2 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_2_2_0) corr_2_2_8) corr_2_2_16) corr_2_2_24) corr_2_2_32

private theorem corr_2_3_0 : ∀ i : Fin 8, part 2 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 2 i.val) := by
  decide +kernel

private theorem corr_2_3_8 : ∀ i : Fin 8, part 2 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 2 (8 + i.val)) := by
  decide +kernel

private theorem corr_2_3_16 : ∀ i : Fin 8, part 2 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 2 (16 + i.val)) := by
  decide +kernel

private theorem corr_2_3_24 : ∀ i : Fin 8, part 2 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 2 (24 + i.val)) := by
  decide +kernel

private theorem corr_2_3_32 : ∀ i : Fin 6, part 2 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 2 (32 + i.val)) := by
  decide +kernel

private theorem corr_2_3 : ∀ i : ℕ, i < 38 → part 2 3 i = sumWindow (3 * width) (chunkLen n 3) (term 2 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_2_3_0) corr_2_3_8) corr_2_3_16) corr_2_3_24) corr_2_3_32

private theorem corr_2_4_0 : ∀ i : Fin 8, part 2 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 2 i.val) := by
  decide +kernel

private theorem corr_2_4_8 : ∀ i : Fin 8, part 2 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 2 (8 + i.val)) := by
  decide +kernel

private theorem corr_2_4_16 : ∀ i : Fin 8, part 2 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 2 (16 + i.val)) := by
  decide +kernel

private theorem corr_2_4_24 : ∀ i : Fin 8, part 2 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 2 (24 + i.val)) := by
  decide +kernel

private theorem corr_2_4_32 : ∀ i : Fin 6, part 2 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 2 (32 + i.val)) := by
  decide +kernel

private theorem corr_2_4 : ∀ i : ℕ, i < 38 → part 2 4 i = sumWindow (4 * width) (chunkLen n 4) (term 2 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_2_4_0) corr_2_4_8) corr_2_4_16) corr_2_4_24) corr_2_4_32

private theorem corr_2_5_0 : ∀ i : Fin 8, part 2 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 2 i.val) := by
  decide +kernel

private theorem corr_2_5_8 : ∀ i : Fin 8, part 2 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 2 (8 + i.val)) := by
  decide +kernel

private theorem corr_2_5_16 : ∀ i : Fin 8, part 2 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 2 (16 + i.val)) := by
  decide +kernel

private theorem corr_2_5_24 : ∀ i : Fin 8, part 2 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 2 (24 + i.val)) := by
  decide +kernel

private theorem corr_2_5_32 : ∀ i : Fin 6, part 2 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 2 (32 + i.val)) := by
  decide +kernel

private theorem corr_2_5 : ∀ i : ℕ, i < 38 → part 2 5 i = sumWindow (5 * width) (chunkLen n 5) (term 2 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_2_5_0) corr_2_5_8) corr_2_5_16) corr_2_5_24) corr_2_5_32

private theorem corr_2_6_0 : ∀ i : Fin 8, part 2 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 2 i.val) := by
  decide +kernel

private theorem corr_2_6_8 : ∀ i : Fin 8, part 2 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 2 (8 + i.val)) := by
  decide +kernel

private theorem corr_2_6_16 : ∀ i : Fin 8, part 2 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 2 (16 + i.val)) := by
  decide +kernel

private theorem corr_2_6_24 : ∀ i : Fin 8, part 2 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 2 (24 + i.val)) := by
  decide +kernel

private theorem corr_2_6_32 : ∀ i : Fin 6, part 2 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 2 (32 + i.val)) := by
  decide +kernel

private theorem corr_2_6 : ∀ i : ℕ, i < 38 → part 2 6 i = sumWindow (6 * width) (chunkLen n 6) (term 2 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_2_6_0) corr_2_6_8) corr_2_6_16) corr_2_6_24) corr_2_6_32

private theorem corr_2_7_0 : ∀ i : Fin 8, part 2 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 2 i.val) := by
  decide +kernel

private theorem corr_2_7_8 : ∀ i : Fin 8, part 2 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 2 (8 + i.val)) := by
  decide +kernel

private theorem corr_2_7_16 : ∀ i : Fin 8, part 2 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 2 (16 + i.val)) := by
  decide +kernel

private theorem corr_2_7_24 : ∀ i : Fin 8, part 2 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 2 (24 + i.val)) := by
  decide +kernel

private theorem corr_2_7_32 : ∀ i : Fin 6, part 2 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 2 (32 + i.val)) := by
  decide +kernel

private theorem corr_2_7 : ∀ i : ℕ, i < 38 → part 2 7 i = sumWindow (7 * width) (chunkLen n 7) (term 2 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_2_7_0) corr_2_7_8) corr_2_7_16) corr_2_7_24) corr_2_7_32

private theorem corr_2_8_0 : ∀ i : Fin 8, part 2 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 2 i.val) := by
  decide +kernel

private theorem corr_2_8_8 : ∀ i : Fin 8, part 2 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 2 (8 + i.val)) := by
  decide +kernel

private theorem corr_2_8_16 : ∀ i : Fin 8, part 2 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 2 (16 + i.val)) := by
  decide +kernel

private theorem corr_2_8_24 : ∀ i : Fin 8, part 2 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 2 (24 + i.val)) := by
  decide +kernel

private theorem corr_2_8_32 : ∀ i : Fin 6, part 2 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 2 (32 + i.val)) := by
  decide +kernel

private theorem corr_2_8 : ∀ i : ℕ, i < 38 → part 2 8 i = sumWindow (8 * width) (chunkLen n 8) (term 2 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_2_8_0) corr_2_8_8) corr_2_8_16) corr_2_8_24) corr_2_8_32

private theorem corr_2_9_0 : ∀ i : Fin 8, part 2 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 2 i.val) := by
  decide +kernel

private theorem corr_2_9_8 : ∀ i : Fin 8, part 2 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 2 (8 + i.val)) := by
  decide +kernel

private theorem corr_2_9_16 : ∀ i : Fin 8, part 2 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 2 (16 + i.val)) := by
  decide +kernel

private theorem corr_2_9_24 : ∀ i : Fin 8, part 2 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 2 (24 + i.val)) := by
  decide +kernel

private theorem corr_2_9_32 : ∀ i : Fin 6, part 2 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 2 (32 + i.val)) := by
  decide +kernel

private theorem corr_2_9 : ∀ i : ℕ, i < 38 → part 2 9 i = sumWindow (9 * width) (chunkLen n 9) (term 2 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_2_9_0) corr_2_9_8) corr_2_9_16) corr_2_9_24) corr_2_9_32

theorem corr_2 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 2 b slot = sumWindow (b * width) (chunkLen n b) (term 2 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_2_0) corr_2_1) corr_2_2) corr_2_3) corr_2_4) corr_2_5) corr_2_6) corr_2_7) corr_2_8) corr_2_9

private theorem total_2_0 : ∀ i : Fin 8, correlationAt 2 i.val = sumChunks n (fun b => part 2 b i.val) := by
  decide +kernel

private theorem total_2_8 : ∀ i : Fin 8, correlationAt 2 (8 + i.val) = sumChunks n (fun b => part 2 b (8 + i.val)) := by
  decide +kernel

private theorem total_2_16 : ∀ i : Fin 8, correlationAt 2 (16 + i.val) = sumChunks n (fun b => part 2 b (16 + i.val)) := by
  decide +kernel

private theorem total_2_24 : ∀ i : Fin 8, correlationAt 2 (24 + i.val) = sumChunks n (fun b => part 2 b (24 + i.val)) := by
  decide +kernel

private theorem total_2_32 : ∀ i : Fin 6, correlationAt 2 (32 + i.val) = sumChunks n (fun b => part 2 b (32 + i.val)) := by
  decide +kernel

theorem total_2 : ∀ i : ℕ, i < 38 → correlationAt 2 i = sumChunks n (fun b => part 2 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_2_0) total_2_8) total_2_16) total_2_24) total_2_32

end Chirped73
