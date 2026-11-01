/- GID: D5/S3/Quantum/Information/ClassicalADZhangYeung
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ClassicalADZhangYeung
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Zhang-Yeung for AD-classical density states with arbitrary conditional BC blocks. -/

import D5.S3.Quantum.Information.ClassicalADCopy
import D5.S3.Quantum.Information.FivePartySSA

set_option autoImplicit false

open scoped BigOperators
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Information.ClassicalADCopy

namespace D5.S3.Quantum.Information.ClassicalADZhangYeung

variable {A B C D : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B] [Nonempty B]
  [Fintype C] [DecidableEq C] [Nonempty C]
  [Fintype D] [DecidableEq D] [Nonempty D]

/-- Zhang-Yeung on the full AD-classical family. Conditional BC states may be entangled
and singular; probability weights may vanish. There is no SSA or copy-entropy premise. -/
theorem zhang_yeung_classical_ad
    (p : (A × D) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : (A × D) → DensityState (B × C)) :
    0 ≤ FourPartyMarginals.zhangYeungDefect (classicalADState p hp hs tau) := by
  have hA := FivePartySSA.entropyA_discard (copyState p hp hs tau)
  have hC := FivePartySSA.entropyC_discard (copyState p hp hs tau)
  have hD := FivePartySSA.entropyD_discard (copyState p hp hs tau)
  have hAB := FivePartySSA.entropyAB_discard (copyState p hp hs tau)
  have hAC := FivePartySSA.entropyAC_discard (copyState p hp hs tau)
  have hAD := FivePartySSA.entropyAD_discard (copyState p hp hs tau)
  have hBC := FivePartySSA.entropyBC_discard (copyState p hp hs tau)
  have hBD := FivePartySSA.entropyBD_discard (copyState p hp hs tau)
  have hCD := FivePartySSA.entropyCD_discard (copyState p hp hs tau)
  have hACD := FivePartySSA.entropyACD_discard (copyState p hp hs tau)
  have hBCD := FivePartySSA.entropyBCD_discard (copyState p hp hs tau)
  have hABCD := FivePartySSA.entropyABCD_discard (copyState p hp hs tau)
  rw [copyState_discard] at hA hC hD hAB hAC hAD hBC hBD hCD hACD hBCD hABCD
  have hz := copy_zero_cmi p hp hs tau
  rw [copy_entropy_ade, ← hAD, ← hABCD] at hz
  have hfull : FivePartySSA.entropyABCDE (copyState p hp hs tau) =
      FourPartyMarginals.entropyABCD (classicalADState p hp hs tau) +
      FourPartyMarginals.entropyACD (classicalADState p hp hs tau) -
      FourPartyMarginals.entropyAD (classicalADState p hp hs tau) := by
    linarith only [hz]
  have h := FivePartySSA.eleven_cmi_nonnegative (copyState p hp hs tau)
  rw [← hA, ← hC, ← hD, ← hAB, ← hAC, ← hBC, ← hBD, ← hCD, ← hACD, ← hBCD, ← hABCD,
    copy_entropy_e, copy_entropy_ae, copy_entropy_de, hfull] at h
  unfold FourPartyMarginals.zhangYeungDefect
  linarith only [h]

#print axioms zhang_yeung_classical_ad

end D5.S3.Quantum.Information.ClassicalADZhangYeung
