/- GID: D5/S3/Quantum/Information/FivePartySSA/Consistency
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/FivePartySSA/Consistency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual marginal consistency after discarding the fifth register. -/

import D5.S3.Quantum.Information.FivePartySSA.Marginals
import D5.S3.Quantum.Information.FourPartyMarginals

set_option autoImplicit false

open scoped BigOperators
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.StrongSubadditivity
open D5.S3.Quantum.Information.MarginalCalculus

namespace D5.S3.Quantum.Information.FivePartySSA

variable {A B C D : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D]
variable {E : Type*} [Fintype E] [DecidableEq E]

theorem entropyA_discard (rho : DensityState (A × (B × (C × (D × E))))) :
    FourPartyMarginals.entropyA (marginalABCD rho) = entropyA rho := by

  change vonNeumannEntropy (reduceState FourPartyMarginals.splitA
    (reduceState splitABCD rho)) = _
  rw [reduceState_compose]
  refine entropy_reduceState_congr _ splitA (Equiv.refl _)
    ({ toFun := fun q => (q.1.1, (q.1.2.1, (q.1.2.2, q.2)))
       invFun := fun q => ((q.1, (q.2.1, q.2.2.1)), q.2.2.2)
       left_inv := by rintro ⟨⟨b, ⟨c, d⟩⟩, e⟩; rfl
       right_inv := by rintro ⟨b, ⟨c, ⟨d, e⟩⟩⟩; rfl }) rho ?_
  intro q
  rfl

theorem entropyC_discard (rho : DensityState (A × (B × (C × (D × E))))) :
    FourPartyMarginals.entropyC (marginalABCD rho) = entropyC rho := by

  change vonNeumannEntropy (reduceState FourPartyMarginals.splitC
    (reduceState splitABCD rho)) = _
  rw [reduceState_compose]
  refine entropy_reduceState_congr _ splitC (Equiv.refl _)
    ({ toFun := fun q => (q.1.1, (q.1.2.1, (q.1.2.2, q.2)))
       invFun := fun q => ((q.1, (q.2.1, q.2.2.1)), q.2.2.2)
       left_inv := by rintro ⟨⟨a, ⟨b, d⟩⟩, e⟩; rfl
       right_inv := by rintro ⟨a, ⟨b, ⟨d, e⟩⟩⟩; rfl }) rho ?_
  intro q
  rfl

theorem entropyD_discard (rho : DensityState (A × (B × (C × (D × E))))) :
    FourPartyMarginals.entropyD (marginalABCD rho) = entropyD rho := by

  change vonNeumannEntropy (reduceState FourPartyMarginals.splitD
    (reduceState splitABCD rho)) = _
  rw [reduceState_compose]
  refine entropy_reduceState_congr _ splitD (Equiv.refl _)
    ({ toFun := fun q => (q.1.1, (q.1.2.1, (q.1.2.2, q.2)))
       invFun := fun q => ((q.1, (q.2.1, q.2.2.1)), q.2.2.2)
       left_inv := by rintro ⟨⟨a, ⟨b, c⟩⟩, e⟩; rfl
       right_inv := by rintro ⟨a, ⟨b, ⟨c, e⟩⟩⟩; rfl }) rho ?_
  intro q
  rfl

theorem entropyAB_discard (rho : DensityState (A × (B × (C × (D × E))))) :
    FourPartyMarginals.entropyAB (marginalABCD rho) = entropyAB rho := by

  change vonNeumannEntropy (reduceState FourPartyMarginals.splitAB
    (reduceState splitABCD rho)) = _
  rw [reduceState_compose]
  refine entropy_reduceState_congr _ splitAB (Equiv.refl _)
    ({ toFun := fun q => (q.1.1, (q.1.2, q.2))
       invFun := fun q => ((q.1, q.2.1), q.2.2)
       left_inv := by rintro ⟨⟨c, d⟩, e⟩; rfl
       right_inv := by rintro ⟨c, ⟨d, e⟩⟩; rfl }) rho ?_
  intro q
  rfl

theorem entropyAC_discard (rho : DensityState (A × (B × (C × (D × E))))) :
    FourPartyMarginals.entropyAC (marginalABCD rho) = entropyAC rho := by

  change vonNeumannEntropy (reduceState FourPartyMarginals.splitAC
    (reduceState splitABCD rho)) = _
  rw [reduceState_compose]
  refine entropy_reduceState_congr _ splitAC (Equiv.refl _)
    ({ toFun := fun q => (q.1.1, (q.1.2, q.2))
       invFun := fun q => ((q.1, q.2.1), q.2.2)
       left_inv := by rintro ⟨⟨b, d⟩, e⟩; rfl
       right_inv := by rintro ⟨b, ⟨d, e⟩⟩; rfl }) rho ?_
  intro q
  rfl

theorem entropyAD_discard (rho : DensityState (A × (B × (C × (D × E))))) :
    FourPartyMarginals.entropyAD (marginalABCD rho) = entropyAD rho := by

  change vonNeumannEntropy (reduceState FourPartyMarginals.splitAD
    (reduceState splitABCD rho)) = _
  rw [reduceState_compose]
  refine entropy_reduceState_congr _ splitAD (Equiv.refl _)
    ({ toFun := fun q => (q.1.1, (q.1.2, q.2))
       invFun := fun q => ((q.1, q.2.1), q.2.2)
       left_inv := by rintro ⟨⟨b, c⟩, e⟩; rfl
       right_inv := by rintro ⟨b, ⟨c, e⟩⟩; rfl }) rho ?_
  intro q
  rfl

theorem entropyBC_discard (rho : DensityState (A × (B × (C × (D × E))))) :
    FourPartyMarginals.entropyBC (marginalABCD rho) = entropyBC rho := by

  change vonNeumannEntropy (reduceState FourPartyMarginals.splitBC
    (reduceState splitABCD rho)) = _
  rw [reduceState_compose]
  refine entropy_reduceState_congr _ splitBC (Equiv.refl _)
    ({ toFun := fun q => (q.1.1, (q.1.2, q.2))
       invFun := fun q => ((q.1, q.2.1), q.2.2)
       left_inv := by rintro ⟨⟨a, d⟩, e⟩; rfl
       right_inv := by rintro ⟨a, ⟨d, e⟩⟩; rfl }) rho ?_
  intro q
  rfl

theorem entropyBD_discard (rho : DensityState (A × (B × (C × (D × E))))) :
    FourPartyMarginals.entropyBD (marginalABCD rho) = entropyBD rho := by

  change vonNeumannEntropy (reduceState FourPartyMarginals.splitBD
    (reduceState splitABCD rho)) = _
  rw [reduceState_compose]
  refine entropy_reduceState_congr _ splitBD (Equiv.refl _)
    ({ toFun := fun q => (q.1.1, (q.1.2, q.2))
       invFun := fun q => ((q.1, q.2.1), q.2.2)
       left_inv := by rintro ⟨⟨a, c⟩, e⟩; rfl
       right_inv := by rintro ⟨a, ⟨c, e⟩⟩; rfl }) rho ?_
  intro q
  rfl

theorem entropyCD_discard (rho : DensityState (A × (B × (C × (D × E))))) :
    FourPartyMarginals.entropyCD (marginalABCD rho) = entropyCD rho := by

  change vonNeumannEntropy (reduceState FourPartyMarginals.splitCD
    (reduceState splitABCD rho)) = _
  rw [reduceState_compose]
  refine entropy_reduceState_congr _ splitCD (Equiv.refl _)
    ({ toFun := fun q => (q.1.1, (q.1.2, q.2))
       invFun := fun q => ((q.1, q.2.1), q.2.2)
       left_inv := by rintro ⟨⟨a, b⟩, e⟩; rfl
       right_inv := by rintro ⟨a, ⟨b, e⟩⟩; rfl }) rho ?_
  intro q
  rfl

theorem entropyACD_discard (rho : DensityState (A × (B × (C × (D × E))))) :
    FourPartyMarginals.entropyACD (marginalABCD rho) = entropyACD rho := by

  change vonNeumannEntropy (reduceState FourPartyMarginals.splitACD
    (reduceState splitABCD rho)) = _
  rw [reduceState_compose]
  refine entropy_reduceState_congr _ splitACD (Equiv.refl _)
    ({ toFun := fun q => (q.1, q.2)
       invFun := fun q => (q.1, q.2)
       left_inv := by rintro ⟨b, e⟩; rfl
       right_inv := by rintro ⟨b, e⟩; rfl }) rho ?_
  intro q
  rfl

theorem entropyBCD_discard (rho : DensityState (A × (B × (C × (D × E))))) :
    FourPartyMarginals.entropyBCD (marginalABCD rho) = entropyBCD rho := by

  change vonNeumannEntropy (reduceState FourPartyMarginals.splitBCD
    (reduceState splitABCD rho)) = _
  rw [reduceState_compose]
  refine entropy_reduceState_congr _ splitBCD (Equiv.refl _)
    ({ toFun := fun q => (q.1, q.2)
       invFun := fun q => (q.1, q.2)
       left_inv := by rintro ⟨a, e⟩; rfl
       right_inv := by rintro ⟨a, e⟩; rfl }) rho ?_
  intro q
  rfl

theorem entropyABCD_discard (rho : DensityState (A × (B × (C × (D × E))))) :
    FourPartyMarginals.entropyABCD (marginalABCD rho) = entropyABCD rho := by

  rfl

end D5.S3.Quantum.Information.FivePartySSA
