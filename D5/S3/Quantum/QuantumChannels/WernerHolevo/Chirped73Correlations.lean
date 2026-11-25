/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Correlations
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Replay.existsUnique_zero; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped73Correlations.f_spec
   digest: Exact correlation and slope checks for the order-73 residual and Jacobian tables. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73CorrelationBlock0
import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73CorrelationBlock1
import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73CorrelationBlock2
import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73CorrelationBlock3
import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73CorrelationBlock4
import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73CorrelationBlock5
import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped73CorrelationBlock6

/-! Exact data and kernel checks for the order-73 chirped construction. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

namespace Chirped73

open ChirpedFinite

private theorem partsChecked : ∀ c : ℕ, c < constraints.length → ∀ b : ℕ, b < n / width + 1 →
    ∀ slot : ℕ, slot < m + 1 →
    part c b slot = sumWindow (b * width) (chunkLen n b) (term c slot) := by
  exact coverOne 18 (
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
    coverFirst corr_0) corr_1) corr_2) corr_3) corr_4) corr_5) corr_6) corr_7) corr_8) corr_9) corr_10) corr_11) corr_12) corr_13) corr_14) corr_15) corr_16) corr_17) corr_18

private theorem totalsChecked : ∀ c : ℕ, c < constraints.length → ∀ slot : ℕ, slot < m + 1 →
    correlationAt c slot = sumChunks n (fun b => part c b slot) := by
  exact coverOne 18 (
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
    coverFirst total_0) total_1) total_2) total_3) total_4) total_5) total_6) total_7) total_8) total_9) total_10) total_11) total_12) total_13) total_14) total_15) total_16) total_17) total_18

theorem correlation_spec (c : ℕ) (hc : c < constraints.length) :
    correlationAt c 0 = sumRange n (corrTerm n inverseMultiplier (constraint c) seedAt) :=
  (totalsChecked c hc 0 (by decide +kernel)).trans
    (sumChunks_eq n (term c 0) (fun b => part c b 0)
      (fun b hb => partsChecked c hc b hb 0 (by decide +kernel)))

theorem derivative_spec (c : ℕ) (hc : c < constraints.length) (j : Fin m) :
    correlationAt c (j.val + 1) =
      sumRange n (jacTerm n inverseMultiplier (constraint c) seedAt seedSlopeAt j.val) :=
  (totalsChecked c hc (j.val + 1) (Nat.succ_lt_succ j.isLt)).trans
    (sumChunks_eq n (term c (j.val + 1)) (fun b => part c b (j.val + 1))
      (fun b hb => partsChecked c hc b hb (j.val + 1) (Nat.succ_lt_succ j.isLt)))

def fAt (i : ℕ) : ℤ :=
  let row := equation i
  component row.2 (correlationAt row.1 0)

def jAt (i j : ℕ) : ℤ :=
  let row := equation i
  component row.2 (correlationAt row.1 (j + 1))

theorem f_spec (i : Fin m) :
    fAt i.val = component (equation i.val).2
      (sumRange n (corrTerm n inverseMultiplier (constraint (equation i.val).1) seedAt)) :=
  congrArg (component (equation i.val).2)
    (correlation_spec _ (equation_domain i))

theorem j_spec (i j : Fin m) :
    jAt i.val j.val = component (equation i.val).2
      (sumRange n (jacTerm n inverseMultiplier (constraint (equation i.val).1)
        seedAt seedSlopeAt j.val)) :=
  congrArg (component (equation i.val).2)
    (derivative_spec _ (equation_domain i) j)

end Chirped73
