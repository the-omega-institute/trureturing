/- GID: D5/S3/Zeros/CompletionLedger
   generality: I
   mirror-B: D5/B/S3/Zeros/CompletionLedger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify that the completion factors are address-independent explicit ledger entries. -/

import D5.S3.Analytic.CompletedZetaMellinReconstruction

namespace D5.S3.Zeros.CompletionLedger

open D5.S3.Weil.Convention
open D5.S3.Zeros.CompletedZeta

/--
This formalizes only the sufficient, address-independence direction of PZG Definition 23.2
used by Theorem 23.7. The intrinsic criteria for "unrecorded" and "explicit global ledger"
remain at the narrative layer.
-/
theorem completion_factors_are_explicit_ledger :
    let archFactor : ℂ → ℂ := fun s => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)
    let poleFactor : ℂ → ℂ := fun s => s * (s - 1)
    (∀ (Ledger Address : Type) (_ledger : Ledger) (s : ℂ) (a b : Address),
      (fun _ : Address => archFactor s) a = (fun _ : Address => archFactor s) b ∧
      (fun _ : Address => poleFactor s) a = (fun _ : Address => poleFactor s) b) ∧
    (∀ s : ℂ, 1 < s.re →
      completedZetaReading s = archFactor s * classicalZeta s) ∧
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      xiReading s = (1 / 2 : ℂ) * poleFactor s * completedZetaReading s) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro Ledger Address ledger s a b
    exact ⟨rfl, rfl⟩
  · intro s hs
    exact
      D5.S3.Analytic.CompletedZetaMellinReconstruction.completed_zeta_mellin_reconstruction.1
        s hs
  · intro s hs₀ hs₁
    simpa [mul_assoc] using xi_reading_eq_completed_zeta hs₀ hs₁

end D5.S3.Zeros.CompletionLedger
