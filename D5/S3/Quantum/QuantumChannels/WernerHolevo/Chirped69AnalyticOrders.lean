/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69AnalyticOrders
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69ActualSeedBounds.existsUnique_zero_closedBall; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/Chirped69Replay.rawY
   digest: The exact order-69 residual has the replay Jacobian and derivative drift bound. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.ChirpedAnalyticReplayBridge
import D5.S3.Quantum.QuantumChannels.WernerHolevo.Chirped69Replay

open ChirpedAnalyticDrift

set_option maxRecDepth 100000
set_option maxHeartbeats 450000

namespace Chirped69

local instance : NeZero n := ⟨by decide⟩

private def inverseUnit : (ZMod n)ˣ := ⟨37, 28, by decide, by decide⟩

theorem valid_seed (k : ℕ) (hk : k < seeds.length) :
    ReplayBridge.ValidSeed n m (seed k) := by
  change k < 4 at hk
  have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨layout0_parameters, ReplayBridge.orbitTable_of_partition (n := n) (m := m) layout0
      (List.Perm.cons 0 layout0_partition)⟩
  · exact ⟨layout1_parameters, ReplayBridge.orbitTable_of_partition (n := n) (m := m) layout1
      (List.Perm.cons 0 layout1_partition)⟩
  · exact ⟨layout2_parameters, ReplayBridge.orbitTable_of_partition (n := n) (m := m) layout2
      (List.Perm.cons 0 layout2_partition)⟩
  · exact ⟨layout3_parameters, ReplayBridge.orbitTable_of_partition (n := n) (m := m) layout3
      (List.Perm.cons 0 layout3_partition)⟩

private theorem valid_row (i : Fin m) :
    ReplayBridge.ValidSeed n m (seed (pick i).left) ∧
      ReplayBridge.ValidSeed n m (seed (pick i).right) :=
  let h := constraints_domain ⟨(equation i.val).1, equation_domain i⟩
  ⟨valid_seed _ h.1, valid_seed _ h.2⟩

private abbrev signs (i : Fin m) : ℤ := signEntry i.val
private abbrev analyticRows := ReplayBridge.replayRows inverseUnit pick imag seed

private theorem F_eq (x : Fin m → ℝ) : residual signs analyticRows x = F x :=
  ReplayBridge.residual_eq signs inverseUnit inverseMultiplier rfl pick imag seed
    (fun i => (valid_row i).1) (fun i => (valid_row i).2) x

noncomputable def DF := derivative signs analyticRows

theorem hasFDerivAt_F (x : Fin m → ℝ) : HasFDerivAt F (DF x) x := by
  have hF : residual signs analyticRows = F := funext F_eq
  change HasFDerivAt F (derivative signs analyticRows x) x
  exact hF ▸ hasFDerivAt_residual signs analyticRows x

theorem DF_toMatrix (x : Fin m → ℝ) :
    LinearMap.toMatrix' (DF x).toLinearMap = (exactRows x).exactJacobian imag := by
  have hj := ReplayBridge.jacobian_eq signs inverseUnit inverseMultiplier rfl pick imag seed
    (fun i => (valid_row i).1) (fun i => (valid_row i).2) x
  have hphase : ReplayBridge.phaseAt signs x = exactPhase x := by
    funext j
    rfl
  have hslope : ReplayBridge.slopeAt signs x = exactSlope x := by
    funext j
    rfl
  rw [hphase, hslope] at hj
  simpa only [DF, analyticRows, exactRows] using hj

theorem DF_drift (x y : Fin m → ℝ) : ‖DF x - DF y‖ ≤ 16 * ‖x - y‖ :=
  derivative_drift signs (fun i => (signs_unit i).symm) analyticRows x y

theorem existsUnique_zero_of_seedBounds
    (hseed : ChirpedReplay.CorrelationRows.SeedBounds rows (exactRows center)) :
    ∃! x, x ∈ Metric.closedBall center ChirpedReplay.radius ∧ F x = 0 :=
  existsUnique_zero DF hseed (DF_toMatrix center) (fun x _ => hasFDerivAt_F x)
    (fun x _ => DF_drift x center)

end Chirped69
