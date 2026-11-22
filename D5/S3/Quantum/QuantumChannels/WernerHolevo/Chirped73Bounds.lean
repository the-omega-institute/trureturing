/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Bounds
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Replay.existsUnique_zero; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Bounds.strict_inclusion
   digest: Integer row bounds and strict contraction and inclusion checks for order 73. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73BoundBlocks

/-! Exact data and kernel checks for the order-73 chirped construction. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Chirped73

open ChirpedFinite

private theorem defect_19_0 : defectPart 19 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 19) := by
  decide +kernel

private theorem defect_19_1 : defectPart 19 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 19) := by
  decide +kernel

private theorem defect_19_2 : defectPart 19 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 19) := by
  decide +kernel

private theorem defect_19_3 : defectPart 19 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 19) := by
  decide +kernel

private theorem defect_19_4 : defectPart 19 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 19) := by
  decide +kernel

private theorem defect_19 : ∀ b : ℕ, b < m / width + 1 → defectPart 19 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 19) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_19_0) defect_19_1) defect_19_2) defect_19_3) defect_19_4

private theorem row_19 : stepRow n m a fAt 19 ≤ E ∧ rowWeight m a 19 ≤ M ∧ checkedDefect 19 ≤ delta := by
  decide +kernel

private theorem defect_20_0 : defectPart 20 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 20) := by
  decide +kernel

private theorem defect_20_1 : defectPart 20 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 20) := by
  decide +kernel

private theorem defect_20_2 : defectPart 20 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 20) := by
  decide +kernel

private theorem defect_20_3 : defectPart 20 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 20) := by
  decide +kernel

private theorem defect_20_4 : defectPart 20 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 20) := by
  decide +kernel

private theorem defect_20 : ∀ b : ℕ, b < m / width + 1 → defectPart 20 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 20) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_20_0) defect_20_1) defect_20_2) defect_20_3) defect_20_4

private theorem row_20 : stepRow n m a fAt 20 ≤ E ∧ rowWeight m a 20 ≤ M ∧ checkedDefect 20 ≤ delta := by
  decide +kernel

private theorem defect_21_0 : defectPart 21 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 21) := by
  decide +kernel

private theorem defect_21_1 : defectPart 21 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 21) := by
  decide +kernel

private theorem defect_21_2 : defectPart 21 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 21) := by
  decide +kernel

private theorem defect_21_3 : defectPart 21 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 21) := by
  decide +kernel

private theorem defect_21_4 : defectPart 21 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 21) := by
  decide +kernel

private theorem defect_21 : ∀ b : ℕ, b < m / width + 1 → defectPart 21 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 21) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_21_0) defect_21_1) defect_21_2) defect_21_3) defect_21_4

private theorem row_21 : stepRow n m a fAt 21 ≤ E ∧ rowWeight m a 21 ≤ M ∧ checkedDefect 21 ≤ delta := by
  decide +kernel

private theorem defect_22_0 : defectPart 22 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 22) := by
  decide +kernel

private theorem defect_22_1 : defectPart 22 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 22) := by
  decide +kernel

private theorem defect_22_2 : defectPart 22 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 22) := by
  decide +kernel

private theorem defect_22_3 : defectPart 22 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 22) := by
  decide +kernel

private theorem defect_22_4 : defectPart 22 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 22) := by
  decide +kernel

private theorem defect_22 : ∀ b : ℕ, b < m / width + 1 → defectPart 22 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 22) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_22_0) defect_22_1) defect_22_2) defect_22_3) defect_22_4

private theorem row_22 : stepRow n m a fAt 22 ≤ E ∧ rowWeight m a 22 ≤ M ∧ checkedDefect 22 ≤ delta := by
  decide +kernel

private theorem defect_23_0 : defectPart 23 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 23) := by
  decide +kernel

private theorem defect_23_1 : defectPart 23 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 23) := by
  decide +kernel

private theorem defect_23_2 : defectPart 23 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 23) := by
  decide +kernel

private theorem defect_23_3 : defectPart 23 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 23) := by
  decide +kernel

private theorem defect_23_4 : defectPart 23 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 23) := by
  decide +kernel

private theorem defect_23 : ∀ b : ℕ, b < m / width + 1 → defectPart 23 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 23) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_23_0) defect_23_1) defect_23_2) defect_23_3) defect_23_4

private theorem row_23 : stepRow n m a fAt 23 ≤ E ∧ rowWeight m a 23 ≤ M ∧ checkedDefect 23 ≤ delta := by
  decide +kernel

private theorem defect_24_0 : defectPart 24 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 24) := by
  decide +kernel

private theorem defect_24_1 : defectPart 24 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 24) := by
  decide +kernel

private theorem defect_24_2 : defectPart 24 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 24) := by
  decide +kernel

private theorem defect_24_3 : defectPart 24 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 24) := by
  decide +kernel

private theorem defect_24_4 : defectPart 24 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 24) := by
  decide +kernel

private theorem defect_24 : ∀ b : ℕ, b < m / width + 1 → defectPart 24 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 24) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_24_0) defect_24_1) defect_24_2) defect_24_3) defect_24_4

private theorem row_24 : stepRow n m a fAt 24 ≤ E ∧ rowWeight m a 24 ≤ M ∧ checkedDefect 24 ≤ delta := by
  decide +kernel

private theorem defect_25_0 : defectPart 25 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 25) := by
  decide +kernel

private theorem defect_25_1 : defectPart 25 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 25) := by
  decide +kernel

private theorem defect_25_2 : defectPart 25 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 25) := by
  decide +kernel

private theorem defect_25_3 : defectPart 25 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 25) := by
  decide +kernel

private theorem defect_25_4 : defectPart 25 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 25) := by
  decide +kernel

private theorem defect_25 : ∀ b : ℕ, b < m / width + 1 → defectPart 25 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 25) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_25_0) defect_25_1) defect_25_2) defect_25_3) defect_25_4

private theorem row_25 : stepRow n m a fAt 25 ≤ E ∧ rowWeight m a 25 ≤ M ∧ checkedDefect 25 ≤ delta := by
  decide +kernel

private theorem defect_26_0 : defectPart 26 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 26) := by
  decide +kernel

private theorem defect_26_1 : defectPart 26 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 26) := by
  decide +kernel

private theorem defect_26_2 : defectPart 26 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 26) := by
  decide +kernel

private theorem defect_26_3 : defectPart 26 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 26) := by
  decide +kernel

private theorem defect_26_4 : defectPart 26 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 26) := by
  decide +kernel

private theorem defect_26 : ∀ b : ℕ, b < m / width + 1 → defectPart 26 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 26) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_26_0) defect_26_1) defect_26_2) defect_26_3) defect_26_4

private theorem row_26 : stepRow n m a fAt 26 ≤ E ∧ rowWeight m a 26 ≤ M ∧ checkedDefect 26 ≤ delta := by
  decide +kernel

private theorem defect_27_0 : defectPart 27 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 27) := by
  decide +kernel

private theorem defect_27_1 : defectPart 27 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 27) := by
  decide +kernel

private theorem defect_27_2 : defectPart 27 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 27) := by
  decide +kernel

private theorem defect_27_3 : defectPart 27 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 27) := by
  decide +kernel

private theorem defect_27_4 : defectPart 27 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 27) := by
  decide +kernel

private theorem defect_27 : ∀ b : ℕ, b < m / width + 1 → defectPart 27 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 27) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_27_0) defect_27_1) defect_27_2) defect_27_3) defect_27_4

private theorem row_27 : stepRow n m a fAt 27 ≤ E ∧ rowWeight m a 27 ≤ M ∧ checkedDefect 27 ≤ delta := by
  decide +kernel

private theorem defect_28_0 : defectPart 28 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 28) := by
  decide +kernel

private theorem defect_28_1 : defectPart 28 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 28) := by
  decide +kernel

private theorem defect_28_2 : defectPart 28 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 28) := by
  decide +kernel

private theorem defect_28_3 : defectPart 28 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 28) := by
  decide +kernel

private theorem defect_28_4 : defectPart 28 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 28) := by
  decide +kernel

private theorem defect_28 : ∀ b : ℕ, b < m / width + 1 → defectPart 28 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 28) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_28_0) defect_28_1) defect_28_2) defect_28_3) defect_28_4

private theorem row_28 : stepRow n m a fAt 28 ≤ E ∧ rowWeight m a 28 ≤ M ∧ checkedDefect 28 ≤ delta := by
  decide +kernel

private theorem defect_29_0 : defectPart 29 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 29) := by
  decide +kernel

private theorem defect_29_1 : defectPart 29 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 29) := by
  decide +kernel

private theorem defect_29_2 : defectPart 29 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 29) := by
  decide +kernel

private theorem defect_29_3 : defectPart 29 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 29) := by
  decide +kernel

private theorem defect_29_4 : defectPart 29 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 29) := by
  decide +kernel

private theorem defect_29 : ∀ b : ℕ, b < m / width + 1 → defectPart 29 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 29) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_29_0) defect_29_1) defect_29_2) defect_29_3) defect_29_4

private theorem row_29 : stepRow n m a fAt 29 ≤ E ∧ rowWeight m a 29 ≤ M ∧ checkedDefect 29 ≤ delta := by
  decide +kernel

private theorem defect_30_0 : defectPart 30 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 30) := by
  decide +kernel

private theorem defect_30_1 : defectPart 30 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 30) := by
  decide +kernel

private theorem defect_30_2 : defectPart 30 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 30) := by
  decide +kernel

private theorem defect_30_3 : defectPart 30 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 30) := by
  decide +kernel

private theorem defect_30_4 : defectPart 30 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 30) := by
  decide +kernel

private theorem defect_30 : ∀ b : ℕ, b < m / width + 1 → defectPart 30 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 30) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_30_0) defect_30_1) defect_30_2) defect_30_3) defect_30_4

private theorem row_30 : stepRow n m a fAt 30 ≤ E ∧ rowWeight m a 30 ≤ M ∧ checkedDefect 30 ≤ delta := by
  decide +kernel

private theorem defect_31_0 : defectPart 31 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 31) := by
  decide +kernel

private theorem defect_31_1 : defectPart 31 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 31) := by
  decide +kernel

private theorem defect_31_2 : defectPart 31 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 31) := by
  decide +kernel

private theorem defect_31_3 : defectPart 31 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 31) := by
  decide +kernel

private theorem defect_31_4 : defectPart 31 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 31) := by
  decide +kernel

private theorem defect_31 : ∀ b : ℕ, b < m / width + 1 → defectPart 31 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 31) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_31_0) defect_31_1) defect_31_2) defect_31_3) defect_31_4

private theorem row_31 : stepRow n m a fAt 31 ≤ E ∧ rowWeight m a 31 ≤ M ∧ checkedDefect 31 ≤ delta := by
  decide +kernel

private theorem defect_32_0 : defectPart 32 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 32) := by
  decide +kernel

private theorem defect_32_1 : defectPart 32 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 32) := by
  decide +kernel

private theorem defect_32_2 : defectPart 32 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 32) := by
  decide +kernel

private theorem defect_32_3 : defectPart 32 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 32) := by
  decide +kernel

private theorem defect_32_4 : defectPart 32 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 32) := by
  decide +kernel

private theorem defect_32 : ∀ b : ℕ, b < m / width + 1 → defectPart 32 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 32) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_32_0) defect_32_1) defect_32_2) defect_32_3) defect_32_4

private theorem row_32 : stepRow n m a fAt 32 ≤ E ∧ rowWeight m a 32 ≤ M ∧ checkedDefect 32 ≤ delta := by
  decide +kernel

private theorem defect_33_0 : defectPart 33 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 33) := by
  decide +kernel

private theorem defect_33_1 : defectPart 33 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 33) := by
  decide +kernel

private theorem defect_33_2 : defectPart 33 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 33) := by
  decide +kernel

private theorem defect_33_3 : defectPart 33 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 33) := by
  decide +kernel

private theorem defect_33_4 : defectPart 33 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 33) := by
  decide +kernel

private theorem defect_33 : ∀ b : ℕ, b < m / width + 1 → defectPart 33 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 33) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_33_0) defect_33_1) defect_33_2) defect_33_3) defect_33_4

private theorem row_33 : stepRow n m a fAt 33 ≤ E ∧ rowWeight m a 33 ≤ M ∧ checkedDefect 33 ≤ delta := by
  decide +kernel

private theorem defect_34_0 : defectPart 34 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 34) := by
  decide +kernel

private theorem defect_34_1 : defectPart 34 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 34) := by
  decide +kernel

private theorem defect_34_2 : defectPart 34 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 34) := by
  decide +kernel

private theorem defect_34_3 : defectPart 34 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 34) := by
  decide +kernel

private theorem defect_34_4 : defectPart 34 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 34) := by
  decide +kernel

private theorem defect_34 : ∀ b : ℕ, b < m / width + 1 → defectPart 34 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 34) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_34_0) defect_34_1) defect_34_2) defect_34_3) defect_34_4

private theorem row_34 : stepRow n m a fAt 34 ≤ E ∧ rowWeight m a 34 ≤ M ∧ checkedDefect 34 ≤ delta := by
  decide +kernel

private theorem defect_35_0 : defectPart 35 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 35) := by
  decide +kernel

private theorem defect_35_1 : defectPart 35 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 35) := by
  decide +kernel

private theorem defect_35_2 : defectPart 35 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 35) := by
  decide +kernel

private theorem defect_35_3 : defectPart 35 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 35) := by
  decide +kernel

private theorem defect_35_4 : defectPart 35 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 35) := by
  decide +kernel

private theorem defect_35 : ∀ b : ℕ, b < m / width + 1 → defectPart 35 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 35) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_35_0) defect_35_1) defect_35_2) defect_35_3) defect_35_4

private theorem row_35 : stepRow n m a fAt 35 ≤ E ∧ rowWeight m a 35 ≤ M ∧ checkedDefect 35 ≤ delta := by
  decide +kernel

private theorem defect_36_0 : defectPart 36 0 = sumWindow (0 * width) (chunkLen m 0) (defectTerm H m a jAt 36) := by
  decide +kernel

private theorem defect_36_1 : defectPart 36 1 = sumWindow (1 * width) (chunkLen m 1) (defectTerm H m a jAt 36) := by
  decide +kernel

private theorem defect_36_2 : defectPart 36 2 = sumWindow (2 * width) (chunkLen m 2) (defectTerm H m a jAt 36) := by
  decide +kernel

private theorem defect_36_3 : defectPart 36 3 = sumWindow (3 * width) (chunkLen m 3) (defectTerm H m a jAt 36) := by
  decide +kernel

private theorem defect_36_4 : defectPart 36 4 = sumWindow (4 * width) (chunkLen m 4) (defectTerm H m a jAt 36) := by
  decide +kernel

private theorem defect_36 : ∀ b : ℕ, b < m / width + 1 → defectPart 36 b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt 36) := by
  exact coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_36_0) defect_36_1) defect_36_2) defect_36_3) defect_36_4

private theorem row_36 : stepRow n m a fAt 36 ≤ E ∧ rowWeight m a 36 ≤ M ∧ checkedDefect 36 ≤ delta := by
  decide +kernel

private theorem defectPartsChecked : ∀ i : ℕ, i < m → ∀ b : ℕ, b < m / width + 1 →
    defectPart i b = sumWindow (b * width) (chunkLen m b) (defectTerm H m a jAt i) := by
  exact coverOne 36 (
    coverOne 35 (
    coverOne 34 (
    coverOne 33 (
    coverOne 32 (
    coverOne 31 (
    coverOne 30 (
    coverOne 29 (
    coverOne 28 (
    coverOne 27 (
    coverOne 26 (
    coverOne 25 (
    coverOne 24 (
    coverOne 23 (
    coverOne 22 (
    coverOne 21 (
    coverOne 20 (
    coverOne 19 (
    coverOne 18 (
    coverOne 17 (
    coverOne 16 (
    coverOne 15 (
    coverOne 14 (
    coverOne 13 (
    coverOne 12 (
    coverOne 11 (
    coverOne 10 (
    coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst defect_0) defect_1) defect_2) defect_3) defect_4) defect_5) defect_6) defect_7) defect_8) defect_9) defect_10) defect_11) defect_12) defect_13) defect_14) defect_15) defect_16) defect_17) defect_18) defect_19) defect_20) defect_21) defect_22) defect_23) defect_24) defect_25) defect_26) defect_27) defect_28) defect_29) defect_30) defect_31) defect_32) defect_33) defect_34) defect_35) defect_36

private theorem rowsChecked : ∀ i : ℕ, i < m → stepRow n m a fAt i ≤ E ∧ rowWeight m a i ≤ M ∧ checkedDefect i ≤ delta := by
  exact coverOne 36 (
    coverOne 35 (
    coverOne 34 (
    coverOne 33 (
    coverOne 32 (
    coverOne 31 (
    coverOne 30 (
    coverOne 29 (
    coverOne 28 (
    coverOne 27 (
    coverOne 26 (
    coverOne 25 (
    coverOne 24 (
    coverOne 23 (
    coverOne 22 (
    coverOne 21 (
    coverOne 20 (
    coverOne 19 (
    coverOne 18 (
    coverOne 17 (
    coverOne 16 (
    coverOne 15 (
    coverOne 14 (
    coverOne 13 (
    coverOne 12 (
    coverOne 11 (
    coverOne 10 (
    coverOne 9 (
    coverOne 8 (
    coverOne 7 (
    coverOne 6 (
    coverOne 5 (
    coverOne 4 (
    coverOne 3 (
    coverOne 2 (
    coverOne 1 (
    coverFirst row_0) row_1) row_2) row_3) row_4) row_5) row_6) row_7) row_8) row_9) row_10) row_11) row_12) row_13) row_14) row_15) row_16) row_17) row_18) row_19) row_20) row_21) row_22) row_23) row_24) row_25) row_26) row_27) row_28) row_29) row_30) row_31) row_32) row_33) row_34) row_35) row_36

theorem row_bounds (i : Fin m) :
    stepRow n m a fAt i.val ≤ E ∧ rowWeight m a i.val ≤ M ∧ defectRow H n m a jAt i.val ≤ delta := by
  obtain ⟨he, hy, hd⟩ := rowsChecked i.val i.isLt
  have h := sumChunks_eq m (defectTerm H m a jAt i.val) (defectPart i.val)
    (defectPartsChecked i.val i.isLt)
  unfold checkedDefect at hd
  rw [h] at hd
  exact ⟨he, hy, hd⟩

theorem bounds_nonnegative : 0 ≤ E ∧ 0 ≤ delta ∧ 0 ≤ M := by
  decide +kernel

theorem denominator_exact : H = 546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763456 := by
  decide +kernel

theorem contraction_exact : contraction delta M = 4257627628358457031360384980446001631083818128041428005817080005257107381552286161958530739712 := by
  decide +kernel

theorem inclusion_exact : E * radiusDen + contraction delta M = 149951112120745156807606347878672081104331048443382347359885379562576013424781985856178701495808 := by
  decide +kernel

theorem strict_contraction : contraction delta M < H := by
  decide +kernel

theorem strict_inclusion : E * radiusDen + contraction delta M < H := by
  decide +kernel

theorem strong_contraction : 65536 * contraction delta M < H := by
  decide +kernel

theorem strong_inclusion : 2048 * (E * radiusDen + contraction delta M) < H := by
  decide +kernel

end Chirped73
