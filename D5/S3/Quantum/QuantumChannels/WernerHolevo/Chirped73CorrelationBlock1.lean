/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73CorrelationBlock1
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Correlations.correlation_spec; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73CorrelationData.correlationAt
   digest: Checked partial and total correlation sums for order-73 block 1. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73CorrelationData

/-! Exact data and kernel checks for the order-73 chirped construction. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Chirped73

open ChirpedFinite

private theorem corr_3_0_0 : ∀ i : Fin 8, part 3 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 3 i.val) := by
  decide +kernel

private theorem corr_3_0_8 : ∀ i : Fin 8, part 3 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 3 (8 + i.val)) := by
  decide +kernel

private theorem corr_3_0_16 : ∀ i : Fin 8, part 3 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 3 (16 + i.val)) := by
  decide +kernel

private theorem corr_3_0_24 : ∀ i : Fin 8, part 3 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 3 (24 + i.val)) := by
  decide +kernel

private theorem corr_3_0_32 : ∀ i : Fin 6, part 3 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 3 (32 + i.val)) := by
  decide +kernel

private theorem corr_3_0 : ∀ i : ℕ, i < 38 → part 3 0 i = sumWindow (0 * width) (chunkLen n 0) (term 3 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_3_0_0) corr_3_0_8) corr_3_0_16) corr_3_0_24) corr_3_0_32

private theorem corr_3_1_0 : ∀ i : Fin 8, part 3 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 3 i.val) := by
  decide +kernel

private theorem corr_3_1_8 : ∀ i : Fin 8, part 3 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 3 (8 + i.val)) := by
  decide +kernel

private theorem corr_3_1_16 : ∀ i : Fin 8, part 3 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 3 (16 + i.val)) := by
  decide +kernel

private theorem corr_3_1_24 : ∀ i : Fin 8, part 3 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 3 (24 + i.val)) := by
  decide +kernel

private theorem corr_3_1_32 : ∀ i : Fin 6, part 3 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 3 (32 + i.val)) := by
  decide +kernel

private theorem corr_3_1 : ∀ i : ℕ, i < 38 → part 3 1 i = sumWindow (1 * width) (chunkLen n 1) (term 3 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_3_1_0) corr_3_1_8) corr_3_1_16) corr_3_1_24) corr_3_1_32

private theorem corr_3_2_0 : ∀ i : Fin 8, part 3 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 3 i.val) := by
  decide +kernel

private theorem corr_3_2_8 : ∀ i : Fin 8, part 3 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 3 (8 + i.val)) := by
  decide +kernel

private theorem corr_3_2_16 : ∀ i : Fin 8, part 3 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 3 (16 + i.val)) := by
  decide +kernel

private theorem corr_3_2_24 : ∀ i : Fin 8, part 3 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 3 (24 + i.val)) := by
  decide +kernel

private theorem corr_3_2_32 : ∀ i : Fin 6, part 3 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 3 (32 + i.val)) := by
  decide +kernel

private theorem corr_3_2 : ∀ i : ℕ, i < 38 → part 3 2 i = sumWindow (2 * width) (chunkLen n 2) (term 3 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_3_2_0) corr_3_2_8) corr_3_2_16) corr_3_2_24) corr_3_2_32

private theorem corr_3_3_0 : ∀ i : Fin 8, part 3 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 3 i.val) := by
  decide +kernel

private theorem corr_3_3_8 : ∀ i : Fin 8, part 3 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 3 (8 + i.val)) := by
  decide +kernel

private theorem corr_3_3_16 : ∀ i : Fin 8, part 3 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 3 (16 + i.val)) := by
  decide +kernel

private theorem corr_3_3_24 : ∀ i : Fin 8, part 3 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 3 (24 + i.val)) := by
  decide +kernel

private theorem corr_3_3_32 : ∀ i : Fin 6, part 3 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 3 (32 + i.val)) := by
  decide +kernel

private theorem corr_3_3 : ∀ i : ℕ, i < 38 → part 3 3 i = sumWindow (3 * width) (chunkLen n 3) (term 3 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_3_3_0) corr_3_3_8) corr_3_3_16) corr_3_3_24) corr_3_3_32

private theorem corr_3_4_0 : ∀ i : Fin 8, part 3 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 3 i.val) := by
  decide +kernel

private theorem corr_3_4_8 : ∀ i : Fin 8, part 3 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 3 (8 + i.val)) := by
  decide +kernel

private theorem corr_3_4_16 : ∀ i : Fin 8, part 3 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 3 (16 + i.val)) := by
  decide +kernel

private theorem corr_3_4_24 : ∀ i : Fin 8, part 3 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 3 (24 + i.val)) := by
  decide +kernel

private theorem corr_3_4_32 : ∀ i : Fin 6, part 3 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 3 (32 + i.val)) := by
  decide +kernel

private theorem corr_3_4 : ∀ i : ℕ, i < 38 → part 3 4 i = sumWindow (4 * width) (chunkLen n 4) (term 3 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_3_4_0) corr_3_4_8) corr_3_4_16) corr_3_4_24) corr_3_4_32

private theorem corr_3_5_0 : ∀ i : Fin 8, part 3 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 3 i.val) := by
  decide +kernel

private theorem corr_3_5_8 : ∀ i : Fin 8, part 3 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 3 (8 + i.val)) := by
  decide +kernel

private theorem corr_3_5_16 : ∀ i : Fin 8, part 3 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 3 (16 + i.val)) := by
  decide +kernel

private theorem corr_3_5_24 : ∀ i : Fin 8, part 3 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 3 (24 + i.val)) := by
  decide +kernel

private theorem corr_3_5_32 : ∀ i : Fin 6, part 3 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 3 (32 + i.val)) := by
  decide +kernel

private theorem corr_3_5 : ∀ i : ℕ, i < 38 → part 3 5 i = sumWindow (5 * width) (chunkLen n 5) (term 3 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_3_5_0) corr_3_5_8) corr_3_5_16) corr_3_5_24) corr_3_5_32

private theorem corr_3_6_0 : ∀ i : Fin 8, part 3 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 3 i.val) := by
  decide +kernel

private theorem corr_3_6_8 : ∀ i : Fin 8, part 3 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 3 (8 + i.val)) := by
  decide +kernel

private theorem corr_3_6_16 : ∀ i : Fin 8, part 3 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 3 (16 + i.val)) := by
  decide +kernel

private theorem corr_3_6_24 : ∀ i : Fin 8, part 3 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 3 (24 + i.val)) := by
  decide +kernel

private theorem corr_3_6_32 : ∀ i : Fin 6, part 3 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 3 (32 + i.val)) := by
  decide +kernel

private theorem corr_3_6 : ∀ i : ℕ, i < 38 → part 3 6 i = sumWindow (6 * width) (chunkLen n 6) (term 3 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_3_6_0) corr_3_6_8) corr_3_6_16) corr_3_6_24) corr_3_6_32

private theorem corr_3_7_0 : ∀ i : Fin 8, part 3 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 3 i.val) := by
  decide +kernel

private theorem corr_3_7_8 : ∀ i : Fin 8, part 3 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 3 (8 + i.val)) := by
  decide +kernel

private theorem corr_3_7_16 : ∀ i : Fin 8, part 3 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 3 (16 + i.val)) := by
  decide +kernel

private theorem corr_3_7_24 : ∀ i : Fin 8, part 3 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 3 (24 + i.val)) := by
  decide +kernel

private theorem corr_3_7_32 : ∀ i : Fin 6, part 3 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 3 (32 + i.val)) := by
  decide +kernel

private theorem corr_3_7 : ∀ i : ℕ, i < 38 → part 3 7 i = sumWindow (7 * width) (chunkLen n 7) (term 3 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_3_7_0) corr_3_7_8) corr_3_7_16) corr_3_7_24) corr_3_7_32

private theorem corr_3_8_0 : ∀ i : Fin 8, part 3 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 3 i.val) := by
  decide +kernel

private theorem corr_3_8_8 : ∀ i : Fin 8, part 3 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 3 (8 + i.val)) := by
  decide +kernel

private theorem corr_3_8_16 : ∀ i : Fin 8, part 3 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 3 (16 + i.val)) := by
  decide +kernel

private theorem corr_3_8_24 : ∀ i : Fin 8, part 3 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 3 (24 + i.val)) := by
  decide +kernel

private theorem corr_3_8_32 : ∀ i : Fin 6, part 3 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 3 (32 + i.val)) := by
  decide +kernel

private theorem corr_3_8 : ∀ i : ℕ, i < 38 → part 3 8 i = sumWindow (8 * width) (chunkLen n 8) (term 3 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_3_8_0) corr_3_8_8) corr_3_8_16) corr_3_8_24) corr_3_8_32

private theorem corr_3_9_0 : ∀ i : Fin 8, part 3 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 3 i.val) := by
  decide +kernel

private theorem corr_3_9_8 : ∀ i : Fin 8, part 3 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 3 (8 + i.val)) := by
  decide +kernel

private theorem corr_3_9_16 : ∀ i : Fin 8, part 3 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 3 (16 + i.val)) := by
  decide +kernel

private theorem corr_3_9_24 : ∀ i : Fin 8, part 3 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 3 (24 + i.val)) := by
  decide +kernel

private theorem corr_3_9_32 : ∀ i : Fin 6, part 3 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 3 (32 + i.val)) := by
  decide +kernel

private theorem corr_3_9 : ∀ i : ℕ, i < 38 → part 3 9 i = sumWindow (9 * width) (chunkLen n 9) (term 3 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_3_9_0) corr_3_9_8) corr_3_9_16) corr_3_9_24) corr_3_9_32

theorem corr_3 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 3 b slot = sumWindow (b * width) (chunkLen n b) (term 3 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_3_0) corr_3_1) corr_3_2) corr_3_3) corr_3_4) corr_3_5) corr_3_6) corr_3_7) corr_3_8) corr_3_9

private theorem total_3_0 : ∀ i : Fin 8, correlationAt 3 i.val = sumChunks n (fun b => part 3 b i.val) := by
  decide +kernel

private theorem total_3_8 : ∀ i : Fin 8, correlationAt 3 (8 + i.val) = sumChunks n (fun b => part 3 b (8 + i.val)) := by
  decide +kernel

private theorem total_3_16 : ∀ i : Fin 8, correlationAt 3 (16 + i.val) = sumChunks n (fun b => part 3 b (16 + i.val)) := by
  decide +kernel

private theorem total_3_24 : ∀ i : Fin 8, correlationAt 3 (24 + i.val) = sumChunks n (fun b => part 3 b (24 + i.val)) := by
  decide +kernel

private theorem total_3_32 : ∀ i : Fin 6, correlationAt 3 (32 + i.val) = sumChunks n (fun b => part 3 b (32 + i.val)) := by
  decide +kernel

theorem total_3 : ∀ i : ℕ, i < 38 → correlationAt 3 i = sumChunks n (fun b => part 3 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_3_0) total_3_8) total_3_16) total_3_24) total_3_32

private theorem corr_4_0_0 : ∀ i : Fin 8, part 4 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 4 i.val) := by
  decide +kernel

private theorem corr_4_0_8 : ∀ i : Fin 8, part 4 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 4 (8 + i.val)) := by
  decide +kernel

private theorem corr_4_0_16 : ∀ i : Fin 8, part 4 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 4 (16 + i.val)) := by
  decide +kernel

private theorem corr_4_0_24 : ∀ i : Fin 8, part 4 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 4 (24 + i.val)) := by
  decide +kernel

private theorem corr_4_0_32 : ∀ i : Fin 6, part 4 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 4 (32 + i.val)) := by
  decide +kernel

private theorem corr_4_0 : ∀ i : ℕ, i < 38 → part 4 0 i = sumWindow (0 * width) (chunkLen n 0) (term 4 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_4_0_0) corr_4_0_8) corr_4_0_16) corr_4_0_24) corr_4_0_32

private theorem corr_4_1_0 : ∀ i : Fin 8, part 4 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 4 i.val) := by
  decide +kernel

private theorem corr_4_1_8 : ∀ i : Fin 8, part 4 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 4 (8 + i.val)) := by
  decide +kernel

private theorem corr_4_1_16 : ∀ i : Fin 8, part 4 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 4 (16 + i.val)) := by
  decide +kernel

private theorem corr_4_1_24 : ∀ i : Fin 8, part 4 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 4 (24 + i.val)) := by
  decide +kernel

private theorem corr_4_1_32 : ∀ i : Fin 6, part 4 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 4 (32 + i.val)) := by
  decide +kernel

private theorem corr_4_1 : ∀ i : ℕ, i < 38 → part 4 1 i = sumWindow (1 * width) (chunkLen n 1) (term 4 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_4_1_0) corr_4_1_8) corr_4_1_16) corr_4_1_24) corr_4_1_32

private theorem corr_4_2_0 : ∀ i : Fin 8, part 4 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 4 i.val) := by
  decide +kernel

private theorem corr_4_2_8 : ∀ i : Fin 8, part 4 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 4 (8 + i.val)) := by
  decide +kernel

private theorem corr_4_2_16 : ∀ i : Fin 8, part 4 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 4 (16 + i.val)) := by
  decide +kernel

private theorem corr_4_2_24 : ∀ i : Fin 8, part 4 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 4 (24 + i.val)) := by
  decide +kernel

private theorem corr_4_2_32 : ∀ i : Fin 6, part 4 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 4 (32 + i.val)) := by
  decide +kernel

private theorem corr_4_2 : ∀ i : ℕ, i < 38 → part 4 2 i = sumWindow (2 * width) (chunkLen n 2) (term 4 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_4_2_0) corr_4_2_8) corr_4_2_16) corr_4_2_24) corr_4_2_32

private theorem corr_4_3_0 : ∀ i : Fin 8, part 4 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 4 i.val) := by
  decide +kernel

private theorem corr_4_3_8 : ∀ i : Fin 8, part 4 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 4 (8 + i.val)) := by
  decide +kernel

private theorem corr_4_3_16 : ∀ i : Fin 8, part 4 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 4 (16 + i.val)) := by
  decide +kernel

private theorem corr_4_3_24 : ∀ i : Fin 8, part 4 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 4 (24 + i.val)) := by
  decide +kernel

private theorem corr_4_3_32 : ∀ i : Fin 6, part 4 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 4 (32 + i.val)) := by
  decide +kernel

private theorem corr_4_3 : ∀ i : ℕ, i < 38 → part 4 3 i = sumWindow (3 * width) (chunkLen n 3) (term 4 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_4_3_0) corr_4_3_8) corr_4_3_16) corr_4_3_24) corr_4_3_32

private theorem corr_4_4_0 : ∀ i : Fin 8, part 4 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 4 i.val) := by
  decide +kernel

private theorem corr_4_4_8 : ∀ i : Fin 8, part 4 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 4 (8 + i.val)) := by
  decide +kernel

private theorem corr_4_4_16 : ∀ i : Fin 8, part 4 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 4 (16 + i.val)) := by
  decide +kernel

private theorem corr_4_4_24 : ∀ i : Fin 8, part 4 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 4 (24 + i.val)) := by
  decide +kernel

private theorem corr_4_4_32 : ∀ i : Fin 6, part 4 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 4 (32 + i.val)) := by
  decide +kernel

private theorem corr_4_4 : ∀ i : ℕ, i < 38 → part 4 4 i = sumWindow (4 * width) (chunkLen n 4) (term 4 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_4_4_0) corr_4_4_8) corr_4_4_16) corr_4_4_24) corr_4_4_32

private theorem corr_4_5_0 : ∀ i : Fin 8, part 4 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 4 i.val) := by
  decide +kernel

private theorem corr_4_5_8 : ∀ i : Fin 8, part 4 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 4 (8 + i.val)) := by
  decide +kernel

private theorem corr_4_5_16 : ∀ i : Fin 8, part 4 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 4 (16 + i.val)) := by
  decide +kernel

private theorem corr_4_5_24 : ∀ i : Fin 8, part 4 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 4 (24 + i.val)) := by
  decide +kernel

private theorem corr_4_5_32 : ∀ i : Fin 6, part 4 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 4 (32 + i.val)) := by
  decide +kernel

private theorem corr_4_5 : ∀ i : ℕ, i < 38 → part 4 5 i = sumWindow (5 * width) (chunkLen n 5) (term 4 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_4_5_0) corr_4_5_8) corr_4_5_16) corr_4_5_24) corr_4_5_32

private theorem corr_4_6_0 : ∀ i : Fin 8, part 4 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 4 i.val) := by
  decide +kernel

private theorem corr_4_6_8 : ∀ i : Fin 8, part 4 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 4 (8 + i.val)) := by
  decide +kernel

private theorem corr_4_6_16 : ∀ i : Fin 8, part 4 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 4 (16 + i.val)) := by
  decide +kernel

private theorem corr_4_6_24 : ∀ i : Fin 8, part 4 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 4 (24 + i.val)) := by
  decide +kernel

private theorem corr_4_6_32 : ∀ i : Fin 6, part 4 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 4 (32 + i.val)) := by
  decide +kernel

private theorem corr_4_6 : ∀ i : ℕ, i < 38 → part 4 6 i = sumWindow (6 * width) (chunkLen n 6) (term 4 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_4_6_0) corr_4_6_8) corr_4_6_16) corr_4_6_24) corr_4_6_32

private theorem corr_4_7_0 : ∀ i : Fin 8, part 4 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 4 i.val) := by
  decide +kernel

private theorem corr_4_7_8 : ∀ i : Fin 8, part 4 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 4 (8 + i.val)) := by
  decide +kernel

private theorem corr_4_7_16 : ∀ i : Fin 8, part 4 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 4 (16 + i.val)) := by
  decide +kernel

private theorem corr_4_7_24 : ∀ i : Fin 8, part 4 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 4 (24 + i.val)) := by
  decide +kernel

private theorem corr_4_7_32 : ∀ i : Fin 6, part 4 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 4 (32 + i.val)) := by
  decide +kernel

private theorem corr_4_7 : ∀ i : ℕ, i < 38 → part 4 7 i = sumWindow (7 * width) (chunkLen n 7) (term 4 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_4_7_0) corr_4_7_8) corr_4_7_16) corr_4_7_24) corr_4_7_32

private theorem corr_4_8_0 : ∀ i : Fin 8, part 4 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 4 i.val) := by
  decide +kernel

private theorem corr_4_8_8 : ∀ i : Fin 8, part 4 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 4 (8 + i.val)) := by
  decide +kernel

private theorem corr_4_8_16 : ∀ i : Fin 8, part 4 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 4 (16 + i.val)) := by
  decide +kernel

private theorem corr_4_8_24 : ∀ i : Fin 8, part 4 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 4 (24 + i.val)) := by
  decide +kernel

private theorem corr_4_8_32 : ∀ i : Fin 6, part 4 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 4 (32 + i.val)) := by
  decide +kernel

private theorem corr_4_8 : ∀ i : ℕ, i < 38 → part 4 8 i = sumWindow (8 * width) (chunkLen n 8) (term 4 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_4_8_0) corr_4_8_8) corr_4_8_16) corr_4_8_24) corr_4_8_32

private theorem corr_4_9_0 : ∀ i : Fin 8, part 4 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 4 i.val) := by
  decide +kernel

private theorem corr_4_9_8 : ∀ i : Fin 8, part 4 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 4 (8 + i.val)) := by
  decide +kernel

private theorem corr_4_9_16 : ∀ i : Fin 8, part 4 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 4 (16 + i.val)) := by
  decide +kernel

private theorem corr_4_9_24 : ∀ i : Fin 8, part 4 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 4 (24 + i.val)) := by
  decide +kernel

private theorem corr_4_9_32 : ∀ i : Fin 6, part 4 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 4 (32 + i.val)) := by
  decide +kernel

private theorem corr_4_9 : ∀ i : ℕ, i < 38 → part 4 9 i = sumWindow (9 * width) (chunkLen n 9) (term 4 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_4_9_0) corr_4_9_8) corr_4_9_16) corr_4_9_24) corr_4_9_32

theorem corr_4 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 4 b slot = sumWindow (b * width) (chunkLen n b) (term 4 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_4_0) corr_4_1) corr_4_2) corr_4_3) corr_4_4) corr_4_5) corr_4_6) corr_4_7) corr_4_8) corr_4_9

private theorem total_4_0 : ∀ i : Fin 8, correlationAt 4 i.val = sumChunks n (fun b => part 4 b i.val) := by
  decide +kernel

private theorem total_4_8 : ∀ i : Fin 8, correlationAt 4 (8 + i.val) = sumChunks n (fun b => part 4 b (8 + i.val)) := by
  decide +kernel

private theorem total_4_16 : ∀ i : Fin 8, correlationAt 4 (16 + i.val) = sumChunks n (fun b => part 4 b (16 + i.val)) := by
  decide +kernel

private theorem total_4_24 : ∀ i : Fin 8, correlationAt 4 (24 + i.val) = sumChunks n (fun b => part 4 b (24 + i.val)) := by
  decide +kernel

private theorem total_4_32 : ∀ i : Fin 6, correlationAt 4 (32 + i.val) = sumChunks n (fun b => part 4 b (32 + i.val)) := by
  decide +kernel

theorem total_4 : ∀ i : ℕ, i < 38 → correlationAt 4 i = sumChunks n (fun b => part 4 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_4_0) total_4_8) total_4_16) total_4_24) total_4_32

private theorem corr_5_0_0 : ∀ i : Fin 8, part 5 0 i.val = sumWindow (0 * width) (chunkLen n 0) (term 5 i.val) := by
  decide +kernel

private theorem corr_5_0_8 : ∀ i : Fin 8, part 5 0 (8 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 5 (8 + i.val)) := by
  decide +kernel

private theorem corr_5_0_16 : ∀ i : Fin 8, part 5 0 (16 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 5 (16 + i.val)) := by
  decide +kernel

private theorem corr_5_0_24 : ∀ i : Fin 8, part 5 0 (24 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 5 (24 + i.val)) := by
  decide +kernel

private theorem corr_5_0_32 : ∀ i : Fin 6, part 5 0 (32 + i.val) = sumWindow (0 * width) (chunkLen n 0) (term 5 (32 + i.val)) := by
  decide +kernel

private theorem corr_5_0 : ∀ i : ℕ, i < 38 → part 5 0 i = sumWindow (0 * width) (chunkLen n 0) (term 5 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_5_0_0) corr_5_0_8) corr_5_0_16) corr_5_0_24) corr_5_0_32

private theorem corr_5_1_0 : ∀ i : Fin 8, part 5 1 i.val = sumWindow (1 * width) (chunkLen n 1) (term 5 i.val) := by
  decide +kernel

private theorem corr_5_1_8 : ∀ i : Fin 8, part 5 1 (8 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 5 (8 + i.val)) := by
  decide +kernel

private theorem corr_5_1_16 : ∀ i : Fin 8, part 5 1 (16 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 5 (16 + i.val)) := by
  decide +kernel

private theorem corr_5_1_24 : ∀ i : Fin 8, part 5 1 (24 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 5 (24 + i.val)) := by
  decide +kernel

private theorem corr_5_1_32 : ∀ i : Fin 6, part 5 1 (32 + i.val) = sumWindow (1 * width) (chunkLen n 1) (term 5 (32 + i.val)) := by
  decide +kernel

private theorem corr_5_1 : ∀ i : ℕ, i < 38 → part 5 1 i = sumWindow (1 * width) (chunkLen n 1) (term 5 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_5_1_0) corr_5_1_8) corr_5_1_16) corr_5_1_24) corr_5_1_32

private theorem corr_5_2_0 : ∀ i : Fin 8, part 5 2 i.val = sumWindow (2 * width) (chunkLen n 2) (term 5 i.val) := by
  decide +kernel

private theorem corr_5_2_8 : ∀ i : Fin 8, part 5 2 (8 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 5 (8 + i.val)) := by
  decide +kernel

private theorem corr_5_2_16 : ∀ i : Fin 8, part 5 2 (16 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 5 (16 + i.val)) := by
  decide +kernel

private theorem corr_5_2_24 : ∀ i : Fin 8, part 5 2 (24 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 5 (24 + i.val)) := by
  decide +kernel

private theorem corr_5_2_32 : ∀ i : Fin 6, part 5 2 (32 + i.val) = sumWindow (2 * width) (chunkLen n 2) (term 5 (32 + i.val)) := by
  decide +kernel

private theorem corr_5_2 : ∀ i : ℕ, i < 38 → part 5 2 i = sumWindow (2 * width) (chunkLen n 2) (term 5 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_5_2_0) corr_5_2_8) corr_5_2_16) corr_5_2_24) corr_5_2_32

private theorem corr_5_3_0 : ∀ i : Fin 8, part 5 3 i.val = sumWindow (3 * width) (chunkLen n 3) (term 5 i.val) := by
  decide +kernel

private theorem corr_5_3_8 : ∀ i : Fin 8, part 5 3 (8 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 5 (8 + i.val)) := by
  decide +kernel

private theorem corr_5_3_16 : ∀ i : Fin 8, part 5 3 (16 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 5 (16 + i.val)) := by
  decide +kernel

private theorem corr_5_3_24 : ∀ i : Fin 8, part 5 3 (24 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 5 (24 + i.val)) := by
  decide +kernel

private theorem corr_5_3_32 : ∀ i : Fin 6, part 5 3 (32 + i.val) = sumWindow (3 * width) (chunkLen n 3) (term 5 (32 + i.val)) := by
  decide +kernel

private theorem corr_5_3 : ∀ i : ℕ, i < 38 → part 5 3 i = sumWindow (3 * width) (chunkLen n 3) (term 5 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_5_3_0) corr_5_3_8) corr_5_3_16) corr_5_3_24) corr_5_3_32

private theorem corr_5_4_0 : ∀ i : Fin 8, part 5 4 i.val = sumWindow (4 * width) (chunkLen n 4) (term 5 i.val) := by
  decide +kernel

private theorem corr_5_4_8 : ∀ i : Fin 8, part 5 4 (8 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 5 (8 + i.val)) := by
  decide +kernel

private theorem corr_5_4_16 : ∀ i : Fin 8, part 5 4 (16 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 5 (16 + i.val)) := by
  decide +kernel

private theorem corr_5_4_24 : ∀ i : Fin 8, part 5 4 (24 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 5 (24 + i.val)) := by
  decide +kernel

private theorem corr_5_4_32 : ∀ i : Fin 6, part 5 4 (32 + i.val) = sumWindow (4 * width) (chunkLen n 4) (term 5 (32 + i.val)) := by
  decide +kernel

private theorem corr_5_4 : ∀ i : ℕ, i < 38 → part 5 4 i = sumWindow (4 * width) (chunkLen n 4) (term 5 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_5_4_0) corr_5_4_8) corr_5_4_16) corr_5_4_24) corr_5_4_32

private theorem corr_5_5_0 : ∀ i : Fin 8, part 5 5 i.val = sumWindow (5 * width) (chunkLen n 5) (term 5 i.val) := by
  decide +kernel

private theorem corr_5_5_8 : ∀ i : Fin 8, part 5 5 (8 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 5 (8 + i.val)) := by
  decide +kernel

private theorem corr_5_5_16 : ∀ i : Fin 8, part 5 5 (16 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 5 (16 + i.val)) := by
  decide +kernel

private theorem corr_5_5_24 : ∀ i : Fin 8, part 5 5 (24 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 5 (24 + i.val)) := by
  decide +kernel

private theorem corr_5_5_32 : ∀ i : Fin 6, part 5 5 (32 + i.val) = sumWindow (5 * width) (chunkLen n 5) (term 5 (32 + i.val)) := by
  decide +kernel

private theorem corr_5_5 : ∀ i : ℕ, i < 38 → part 5 5 i = sumWindow (5 * width) (chunkLen n 5) (term 5 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_5_5_0) corr_5_5_8) corr_5_5_16) corr_5_5_24) corr_5_5_32

private theorem corr_5_6_0 : ∀ i : Fin 8, part 5 6 i.val = sumWindow (6 * width) (chunkLen n 6) (term 5 i.val) := by
  decide +kernel

private theorem corr_5_6_8 : ∀ i : Fin 8, part 5 6 (8 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 5 (8 + i.val)) := by
  decide +kernel

private theorem corr_5_6_16 : ∀ i : Fin 8, part 5 6 (16 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 5 (16 + i.val)) := by
  decide +kernel

private theorem corr_5_6_24 : ∀ i : Fin 8, part 5 6 (24 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 5 (24 + i.val)) := by
  decide +kernel

private theorem corr_5_6_32 : ∀ i : Fin 6, part 5 6 (32 + i.val) = sumWindow (6 * width) (chunkLen n 6) (term 5 (32 + i.val)) := by
  decide +kernel

private theorem corr_5_6 : ∀ i : ℕ, i < 38 → part 5 6 i = sumWindow (6 * width) (chunkLen n 6) (term 5 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_5_6_0) corr_5_6_8) corr_5_6_16) corr_5_6_24) corr_5_6_32

private theorem corr_5_7_0 : ∀ i : Fin 8, part 5 7 i.val = sumWindow (7 * width) (chunkLen n 7) (term 5 i.val) := by
  decide +kernel

private theorem corr_5_7_8 : ∀ i : Fin 8, part 5 7 (8 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 5 (8 + i.val)) := by
  decide +kernel

private theorem corr_5_7_16 : ∀ i : Fin 8, part 5 7 (16 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 5 (16 + i.val)) := by
  decide +kernel

private theorem corr_5_7_24 : ∀ i : Fin 8, part 5 7 (24 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 5 (24 + i.val)) := by
  decide +kernel

private theorem corr_5_7_32 : ∀ i : Fin 6, part 5 7 (32 + i.val) = sumWindow (7 * width) (chunkLen n 7) (term 5 (32 + i.val)) := by
  decide +kernel

private theorem corr_5_7 : ∀ i : ℕ, i < 38 → part 5 7 i = sumWindow (7 * width) (chunkLen n 7) (term 5 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_5_7_0) corr_5_7_8) corr_5_7_16) corr_5_7_24) corr_5_7_32

private theorem corr_5_8_0 : ∀ i : Fin 8, part 5 8 i.val = sumWindow (8 * width) (chunkLen n 8) (term 5 i.val) := by
  decide +kernel

private theorem corr_5_8_8 : ∀ i : Fin 8, part 5 8 (8 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 5 (8 + i.val)) := by
  decide +kernel

private theorem corr_5_8_16 : ∀ i : Fin 8, part 5 8 (16 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 5 (16 + i.val)) := by
  decide +kernel

private theorem corr_5_8_24 : ∀ i : Fin 8, part 5 8 (24 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 5 (24 + i.val)) := by
  decide +kernel

private theorem corr_5_8_32 : ∀ i : Fin 6, part 5 8 (32 + i.val) = sumWindow (8 * width) (chunkLen n 8) (term 5 (32 + i.val)) := by
  decide +kernel

private theorem corr_5_8 : ∀ i : ℕ, i < 38 → part 5 8 i = sumWindow (8 * width) (chunkLen n 8) (term 5 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_5_8_0) corr_5_8_8) corr_5_8_16) corr_5_8_24) corr_5_8_32

private theorem corr_5_9_0 : ∀ i : Fin 8, part 5 9 i.val = sumWindow (9 * width) (chunkLen n 9) (term 5 i.val) := by
  decide +kernel

private theorem corr_5_9_8 : ∀ i : Fin 8, part 5 9 (8 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 5 (8 + i.val)) := by
  decide +kernel

private theorem corr_5_9_16 : ∀ i : Fin 8, part 5 9 (16 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 5 (16 + i.val)) := by
  decide +kernel

private theorem corr_5_9_24 : ∀ i : Fin 8, part 5 9 (24 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 5 (24 + i.val)) := by
  decide +kernel

private theorem corr_5_9_32 : ∀ i : Fin 6, part 5 9 (32 + i.val) = sumWindow (9 * width) (chunkLen n 9) (term 5 (32 + i.val)) := by
  decide +kernel

private theorem corr_5_9 : ∀ i : ℕ, i < 38 → part 5 9 i = sumWindow (9 * width) (chunkLen n 9) (term 5 i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart corr_5_9_0) corr_5_9_8) corr_5_9_16) corr_5_9_24) corr_5_9_32

theorem corr_5 : ∀ b : ℕ, b < 10 → ∀ slot : ℕ, slot < m + 1 →
    part 5 b slot = sumWindow (b * width) (chunkLen n b) (term 5 slot) := by
  exact coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst corr_5_0) corr_5_1) corr_5_2) corr_5_3) corr_5_4) corr_5_5) corr_5_6) corr_5_7) corr_5_8) corr_5_9

private theorem total_5_0 : ∀ i : Fin 8, correlationAt 5 i.val = sumChunks n (fun b => part 5 b i.val) := by
  decide +kernel

private theorem total_5_8 : ∀ i : Fin 8, correlationAt 5 (8 + i.val) = sumChunks n (fun b => part 5 b (8 + i.val)) := by
  decide +kernel

private theorem total_5_16 : ∀ i : Fin 8, correlationAt 5 (16 + i.val) = sumChunks n (fun b => part 5 b (16 + i.val)) := by
  decide +kernel

private theorem total_5_24 : ∀ i : Fin 8, correlationAt 5 (24 + i.val) = sumChunks n (fun b => part 5 b (24 + i.val)) := by
  decide +kernel

private theorem total_5_32 : ∀ i : Fin 6, correlationAt 5 (32 + i.val) = sumChunks n (fun b => part 5 b (32 + i.val)) := by
  decide +kernel

theorem total_5 : ∀ i : ℕ, i < 38 → correlationAt 5 i = sumChunks n (fun b => part 5 b i) := by
  exact coverNext 32 6 (
    coverNext 24 8 (
    coverNext 16 8 (
    coverNext 8 8 (
    coverStart total_5_0) total_5_8) total_5_16) total_5_24) total_5_32

end Chirped73
