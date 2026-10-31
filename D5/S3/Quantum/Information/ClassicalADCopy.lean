/- GID: D5/S3/Quantum/Information/ClassicalADCopy
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/ClassicalADCopy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical AD-classical conditional copies retain arbitrary quantum BC blocks. -/

import D5.S3.Quantum.Information.ClassicalConditionalCopy
import D5.S3.Quantum.Information.FivePartySSA.Consistency

set_option autoImplicit false

open scoped BigOperators
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.StrongSubadditivity
open D5.S3.Quantum.Information.MarginalCalculus

open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Information.ClassicalConditionalCopy
open D5.S3.Entropy.MaxEntropy

namespace D5.S3.Quantum.Information.ClassicalADCopy

variable {A B C D : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D]

def sourceEquiv : (A × (B × (C × D))) ≃ ((A × D) × (B × C)) :=
  { toFun := fun q => ((q.1, q.2.2.2), (q.2.1, q.2.2.1))
    invFun := fun q => (q.1.1, (q.2.1, (q.2.2, q.1.2)))
    left_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl
    right_inv := by rintro ⟨⟨a, d⟩, ⟨b, c⟩⟩; rfl }

def copyEquiv : (A × (B × (C × (D × C)))) ≃ ((A × D) × ((B × C) × C)) :=
  { toFun := fun q => ((q.1, q.2.2.2.1), ((q.2.1, q.2.2.1), q.2.2.2.2))
    invFun := fun q => (q.1.1, (q.2.1.1, (q.2.1.2, (q.1.2, q.2.2))))
    left_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl
    right_inv := by rintro ⟨⟨a, d⟩, ⟨⟨b, c⟩, e⟩⟩; rfl }

noncomputable def classicalADState (p : (A × D) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : (A × D) → DensityState (B × C)) : DensityState (A × (B × (C × D))) :=
  relabelState sourceEquiv (recordState p hp hs tau)

noncomputable def copyState (p : (A × D) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : (A × D) → DensityState (B × C)) : DensityState (A × (B × (C × (D × C)))) :=
  relabelState copyEquiv (conditionalCopy p hp hs tau)

theorem copyState_discard (p : (A × D) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : (A × D) → DensityState (B × C)) :
    FivePartySSA.marginalABCD (copyState p hp hs tau) = classicalADState p hp hs tau := by
  change reduceState (FivePartySSA.splitABCD.trans copyEquiv)
    (conditionalCopy p hp hs tau) = _
  calc
    _ = relabelState sourceEquiv (reduceState (Equiv.prodAssoc (A × D) (B × C) C)
        (conditionalCopy p hp hs tau)) := by
      refine reduceState_congr _ _ sourceEquiv (Equiv.refl C) _ ?_
      intro q
      rfl
    _ = _ := congrArg (relabelState sourceEquiv) (conditionalCopy_discard p hp hs tau)

def copyPointerEquiv : (A × (D × C)) ≃ ((A × D) × C) :=
  { toFun := fun q => ((q.1, q.2.1), q.2.2)
    invFun := fun q => (q.1.1, (q.1.2, q.2))
    left_inv := by rintro ⟨a, ⟨d, e⟩⟩; rfl
    right_inv := by rintro ⟨⟨a, d⟩, e⟩; rfl }

theorem copy_pointer_marginal (p : (A × D) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : (A × D) → DensityState (B × C)) :
    FivePartySSA.marginalADE (copyState p hp hs tau) =
      relabelState copyPointerEquiv
        (recordState p hp hs (fun x => marginalLeft (tau x))) := by
  change reduceState (FivePartySSA.splitADE.trans copyEquiv)
    (conditionalCopy p hp hs tau) = _
  calc
    _ = relabelState copyPointerEquiv (reduceState middleSwap (conditionalCopy p hp hs tau)) := by
      refine reduceState_congr _ _ copyPointerEquiv (Equiv.refl _) _ ?_
      intro q
      rfl
    _ = _ := congrArg (relabelState copyPointerEquiv) (conditionalCopy_pointer_copy p hp hs tau)

def sourcePointerEquiv : (A × (C × D)) ≃ ((A × D) × C) :=
  { toFun := fun q => ((q.1, q.2.2), q.2.1)
    invFun := fun q => (q.1.1, (q.2, q.1.2))
    left_inv := by rintro ⟨a, ⟨c, d⟩⟩; rfl
    right_inv := by rintro ⟨⟨a, d⟩, e⟩; rfl }

theorem source_pointer_marginal (p : (A × D) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : (A × D) → DensityState (B × C)) :
    FourPartyMarginals.marginalACD (classicalADState p hp hs tau) =
      relabelState sourcePointerEquiv
        (recordState p hp hs (fun x => marginalLeft (tau x))) := by
  change reduceState (FourPartyMarginals.splitACD.trans sourceEquiv)
    (recordState p hp hs tau) = _
  calc
    _ = relabelState sourcePointerEquiv (reduceState middleSwap (recordState p hp hs tau)) := by
      refine reduceState_congr _ _ sourcePointerEquiv (Equiv.refl _) _ ?_
      intro q
      rfl
    _ = _ := congrArg (relabelState sourcePointerEquiv) (recordState_traceMiddle p hp hs tau)

theorem copy_entropy_e (p : (A × D) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : (A × D) → DensityState (B × C)) :
    FivePartySSA.entropyE (copyState p hp hs tau) =
      FourPartyMarginals.entropyC (classicalADState p hp hs tau) := by
  let g : (C × (A × D)) ≃ ((A × D) × C) :=
    { toFun := fun q => ((q.2.1, q.2.2), q.1)
      invFun := fun q => (q.2, (q.1.1, q.1.2))
      left_inv := by rintro ⟨e, ⟨a, d⟩⟩; rfl
      right_inv := by rintro ⟨⟨a, d⟩, e⟩; rfl }

  have hcopy : FivePartySSA.entropyE (copyState p hp hs tau) =
      vonNeumannEntropy (reduceState g
        (recordState p hp hs (fun x => marginalLeft (tau x)))) := by
    calc
      _ = vonNeumannEntropy (reduceState g (reduceState middleSwap (conditionalCopy p hp hs tau))) := by
        change vonNeumannEntropy (reduceState (FivePartySSA.splitE.trans copyEquiv)
          (conditionalCopy p hp hs tau)) = _
        rw [reduceState_compose]
        refine entropy_reduceState_congr _ _
          ({ toFun := fun q => q
             invFun := fun q => q
             left_inv := by rintro e; rfl
             right_inv := by rintro e; rfl })
          ({ toFun := fun q => ((q.1, q.2.2.2), (q.2.1, q.2.2.1))
             invFun := fun q => (q.1.1, (q.2.1, (q.2.2, q.1.2)))
             left_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl
             right_inv := by rintro ⟨⟨a, d⟩, ⟨b, c⟩⟩; rfl }) _ ?_
        intro q
        rfl
      _ = _ := congrArg (fun r => vonNeumannEntropy (reduceState g r))
        (conditionalCopy_pointer_copy p hp hs tau)

  have hsource : FourPartyMarginals.entropyC (classicalADState p hp hs tau) =
      vonNeumannEntropy (reduceState g
        (recordState p hp hs (fun x => marginalLeft (tau x)))) := by
    calc
      _ = vonNeumannEntropy (reduceState g (reduceState middleSwap (recordState p hp hs tau))) := by
        change vonNeumannEntropy (reduceState (FourPartyMarginals.splitC.trans sourceEquiv)
          (recordState p hp hs tau)) = _
        rw [reduceState_compose]
        refine entropy_reduceState_congr _ _
          ({ toFun := fun q => q
             invFun := fun q => q
             left_inv := by rintro c; rfl
             right_inv := by rintro e; rfl })
          ({ toFun := fun q => ((q.1, q.2.2), q.2.1)
             invFun := fun q => (q.1.1, (q.2, q.1.2))
             left_inv := by rintro ⟨a, ⟨b, d⟩⟩; rfl
             right_inv := by rintro ⟨⟨a, d⟩, b⟩; rfl }) _ ?_
        intro q
        rfl
      _ = _ := congrArg (fun r => vonNeumannEntropy (reduceState g r))
        (recordState_traceMiddle p hp hs tau)

  exact hcopy.trans hsource.symm

theorem copy_entropy_ae (p : (A × D) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : (A × D) → DensityState (B × C)) :
    FivePartySSA.entropyAE (copyState p hp hs tau) =
      FourPartyMarginals.entropyAC (classicalADState p hp hs tau) := by
  let g : ((A × C) × D) ≃ ((A × D) × C) :=
    { toFun := fun q => ((q.1.1, q.2), q.1.2)
      invFun := fun q => ((q.1.1, q.2), q.1.2)
      left_inv := by rintro ⟨⟨a, e⟩, d⟩; rfl
      right_inv := by rintro ⟨⟨a, d⟩, e⟩; rfl }

  have hcopy : FivePartySSA.entropyAE (copyState p hp hs tau) =
      vonNeumannEntropy (reduceState g
        (recordState p hp hs (fun x => marginalLeft (tau x)))) := by
    calc
      _ = vonNeumannEntropy (reduceState g (reduceState middleSwap (conditionalCopy p hp hs tau))) := by
        change vonNeumannEntropy (reduceState (FivePartySSA.splitAE.trans copyEquiv)
          (conditionalCopy p hp hs tau)) = _
        rw [reduceState_compose]
        refine entropy_reduceState_congr _ _
          ({ toFun := fun q => (q.1, q.2)
             invFun := fun q => (q.1, q.2)
             left_inv := by rintro ⟨a, e⟩; rfl
             right_inv := by rintro ⟨a, e⟩; rfl })
          ({ toFun := fun q => (q.2.2, (q.1, q.2.1))
             invFun := fun q => (q.2.1, (q.2.2, q.1))
             left_inv := by rintro ⟨b, ⟨c, d⟩⟩; rfl
             right_inv := by rintro ⟨d, ⟨b, c⟩⟩; rfl }) _ ?_
        intro q
        rfl
      _ = _ := congrArg (fun r => vonNeumannEntropy (reduceState g r))
        (conditionalCopy_pointer_copy p hp hs tau)

  have hsource : FourPartyMarginals.entropyAC (classicalADState p hp hs tau) =
      vonNeumannEntropy (reduceState g
        (recordState p hp hs (fun x => marginalLeft (tau x)))) := by
    calc
      _ = vonNeumannEntropy (reduceState g (reduceState middleSwap (recordState p hp hs tau))) := by
        change vonNeumannEntropy (reduceState (FourPartyMarginals.splitAC.trans sourceEquiv)
          (recordState p hp hs tau)) = _
        rw [reduceState_compose]
        refine entropy_reduceState_congr _ _
          ({ toFun := fun q => (q.1, q.2)
             invFun := fun q => (q.1, q.2)
             left_inv := by rintro ⟨a, c⟩; rfl
             right_inv := by rintro ⟨a, e⟩; rfl })
          ({ toFun := fun q => (q.2, q.1)
             invFun := fun q => (q.2, q.1)
             left_inv := by rintro ⟨b, d⟩; rfl
             right_inv := by rintro ⟨d, b⟩; rfl }) _ ?_
        intro q
        rfl
      _ = _ := congrArg (fun r => vonNeumannEntropy (reduceState g r))
        (recordState_traceMiddle p hp hs tau)

  exact hcopy.trans hsource.symm

theorem copy_entropy_de (p : (A × D) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : (A × D) → DensityState (B × C)) :
    FivePartySSA.entropyDE (copyState p hp hs tau) =
      FourPartyMarginals.entropyCD (classicalADState p hp hs tau) := by
  let g : ((D × C) × A) ≃ ((A × D) × C) :=
    { toFun := fun q => ((q.2, q.1.1), q.1.2)
      invFun := fun q => ((q.1.2, q.2), q.1.1)
      left_inv := by rintro ⟨⟨d, e⟩, a⟩; rfl
      right_inv := by rintro ⟨⟨a, d⟩, e⟩; rfl }

  have hcopy : FivePartySSA.entropyDE (copyState p hp hs tau) =
      vonNeumannEntropy (reduceState g
        (recordState p hp hs (fun x => marginalLeft (tau x)))) := by
    calc
      _ = vonNeumannEntropy (reduceState g (reduceState middleSwap (conditionalCopy p hp hs tau))) := by
        change vonNeumannEntropy (reduceState (FivePartySSA.splitDE.trans copyEquiv)
          (conditionalCopy p hp hs tau)) = _
        rw [reduceState_compose]
        refine entropy_reduceState_congr _ _
          ({ toFun := fun q => (q.1, q.2)
             invFun := fun q => (q.1, q.2)
             left_inv := by rintro ⟨d, e⟩; rfl
             right_inv := by rintro ⟨d, e⟩; rfl })
          ({ toFun := fun q => (q.1, (q.2.1, q.2.2))
             invFun := fun q => (q.1, (q.2.1, q.2.2))
             left_inv := by rintro ⟨a, ⟨b, c⟩⟩; rfl
             right_inv := by rintro ⟨a, ⟨b, c⟩⟩; rfl }) _ ?_
        intro q
        rfl
      _ = _ := congrArg (fun r => vonNeumannEntropy (reduceState g r))
        (conditionalCopy_pointer_copy p hp hs tau)

  have hsource : FourPartyMarginals.entropyCD (classicalADState p hp hs tau) =
      vonNeumannEntropy (reduceState g
        (recordState p hp hs (fun x => marginalLeft (tau x)))) := by
    calc
      _ = vonNeumannEntropy (reduceState g (reduceState middleSwap (recordState p hp hs tau))) := by
        change vonNeumannEntropy (reduceState (FourPartyMarginals.splitCD.trans sourceEquiv)
          (recordState p hp hs tau)) = _
        rw [reduceState_compose]
        refine entropy_reduceState_congr _ _
          ({ toFun := fun q => (q.2, q.1)
             invFun := fun q => (q.2, q.1)
             left_inv := by rintro ⟨c, d⟩; rfl
             right_inv := by rintro ⟨d, e⟩; rfl })
          ({ toFun := fun q => (q.1, q.2)
             invFun := fun q => (q.1, q.2)
             left_inv := by rintro ⟨a, b⟩; rfl
             right_inv := by rintro ⟨a, b⟩; rfl }) _ ?_
        intro q
        rfl
      _ = _ := congrArg (fun r => vonNeumannEntropy (reduceState g r))
        (recordState_traceMiddle p hp hs tau)

  exact hcopy.trans hsource.symm

def copySourceEquiv : (A × (D × C)) ≃ (A × (C × D)) where
  toFun q := (q.1, (q.2.2, q.2.1))
  invFun q := (q.1, (q.2.2, q.2.1))
  left_inv := by rintro ⟨a, d, c⟩; rfl
  right_inv := by rintro ⟨a, c, d⟩; rfl

/-- The ADE density is precisely the ACD density with the copied index relabeled. -/
theorem copy_ade_eq_relabel
    (p : (A × D) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : (A × D) → DensityState (B × C)) :
    FivePartySSA.marginalADE (copyState p hp hs tau) =
      relabelState copySourceEquiv (FourPartyMarginals.marginalACD
        (classicalADState p hp hs tau)) := by
  rw [copy_pointer_marginal, source_pointer_marginal, relabelState_comp]
  rfl

theorem copy_entropy_ade (p : (A × D) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : (A × D) → DensityState (B × C)) :
    FivePartySSA.entropyADE (copyState p hp hs tau) =
      FourPartyMarginals.entropyACD (classicalADState p hp hs tau) := by
  change vonNeumannEntropy (FivePartySSA.marginalADE _) =
    vonNeumannEntropy (FourPartyMarginals.marginalACD _)
  rw [copy_ade_eq_relabel, entropy_relabelState]

theorem source_entropy_ad (p : (A × D) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : (A × D) → DensityState (B × C)) :
    FourPartyMarginals.entropyAD (classicalADState p hp hs tau) = shannonEntropy p := by
  have h : FourPartyMarginals.marginalAD (classicalADState p hp hs tau) =
      marginalRight (recordState p hp hs tau) := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    ext i j
    rfl
  change vonNeumannEntropy (FourPartyMarginals.marginalAD _) = _
  rw [h, entropy_record_pointer]

theorem copy_entropy_total (p : (A × D) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : (A × D) → DensityState (B × C)) :
    FivePartySSA.entropyABCDE (copyState p hp hs tau) =
      FourPartyMarginals.entropyABCD (classicalADState p hp hs tau) +
      FourPartyMarginals.entropyACD (classicalADState p hp hs tau) -
      FourPartyMarginals.entropyAD (classicalADState p hp hs tau) := by
  have hsource : FourPartyMarginals.entropyABCD (classicalADState p hp hs tau) =
      vonNeumannEntropy (recordState p hp hs tau) := entropy_relabelState _ _
  have hpointer : FourPartyMarginals.entropyACD (classicalADState p hp hs tau) =
      vonNeumannEntropy (recordState p hp hs (fun x => marginalLeft (tau x))) := by
    change vonNeumannEntropy (FourPartyMarginals.marginalACD _) = _
    rw [source_pointer_marginal, entropy_relabelState]
  change vonNeumannEntropy (relabelState copyEquiv (conditionalCopy p hp hs tau)) = _
  rw [entropy_relabelState, entropy_conditionalCopy, hsource, hpointer, source_entropy_ad]

theorem copy_zero_cmi
    (p : (A × D) → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (tau : (A × D) → DensityState (B × C)) :
    FivePartySSA.entropyADE (copyState p hp hs tau) +
      FivePartySSA.entropyABCD (copyState p hp hs tau) -
      FivePartySSA.entropyAD (copyState p hp hs tau) -
      FivePartySSA.entropyABCDE (copyState p hp hs tau) = 0 := by
  have hAD := FivePartySSA.entropyAD_discard (copyState p hp hs tau)
  have hABCD := FivePartySSA.entropyABCD_discard (copyState p hp hs tau)
  rw [copyState_discard] at hAD hABCD
  rw [copy_entropy_ade, copy_entropy_total, ← hAD, ← hABCD]
  ring

#print axioms copyState_discard
#print axioms copy_entropy_total

end D5.S3.Quantum.Information.ClassicalADCopy
