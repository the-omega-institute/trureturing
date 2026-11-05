/- GID: D5/S3/Quantum/Information/FourPartyMarginals
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/FourPartyMarginals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite density marginals and the Zhang-Yeung entropy defect. -/

import D5.S3.Quantum.Information.MarginalCalculus

set_option autoImplicit false

open scoped BigOperators
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.StrongSubadditivity
open D5.S3.Quantum.Information.MarginalCalculus

namespace D5.S3.Quantum.Information.FourPartyMarginals

variable {A B C D : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D]

def splitA : (A × (B × (C × D))) ≃ (A × (B × (C × D))) :=
  { toFun := fun q => (q.1, (q.2.1, (q.2.2.1, q.2.2.2)))
    invFun := fun q => (q.1, (q.2.1, (q.2.2.1, q.2.2.2)))
    left_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl }

noncomputable def marginalA (rho : DensityState (A × (B × (C × D)))) : DensityState A :=
  reduceState splitA rho

noncomputable abbrev entropyA (rho : DensityState (A × (B × (C × D)))) : ℝ :=
  vonNeumannEntropy (marginalA rho)

def splitB : (B × (A × (C × D))) ≃ (A × (B × (C × D))) :=
  { toFun := fun q => (q.2.1, (q.1, (q.2.2.1, q.2.2.2)))
    invFun := fun q => (q.2.1, (q.1, (q.2.2.1, q.2.2.2)))
    left_inv := by rintro ⟨b, ⟨a, ⟨c, d⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl }

noncomputable def marginalB (rho : DensityState (A × (B × (C × D)))) : DensityState B :=
  reduceState splitB rho

noncomputable abbrev entropyB (rho : DensityState (A × (B × (C × D)))) : ℝ :=
  vonNeumannEntropy (marginalB rho)

def splitC : (C × (A × (B × D))) ≃ (A × (B × (C × D))) :=
  { toFun := fun q => (q.2.1, (q.2.2.1, (q.1, q.2.2.2)))
    invFun := fun q => (q.2.2.1, (q.1, (q.2.1, q.2.2.2)))
    left_inv := by rintro ⟨c, ⟨a, ⟨b, d⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl }

noncomputable def marginalC (rho : DensityState (A × (B × (C × D)))) : DensityState C :=
  reduceState splitC rho

noncomputable abbrev entropyC (rho : DensityState (A × (B × (C × D)))) : ℝ :=
  vonNeumannEntropy (marginalC rho)

def splitD : (D × (A × (B × C))) ≃ (A × (B × (C × D))) :=
  { toFun := fun q => (q.2.1, (q.2.2.1, (q.2.2.2, q.1)))
    invFun := fun q => (q.2.2.2, (q.1, (q.2.1, q.2.2.1)))
    left_inv := by rintro ⟨d, ⟨a, ⟨b, c⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl }

noncomputable def marginalD (rho : DensityState (A × (B × (C × D)))) : DensityState D :=
  reduceState splitD rho

noncomputable abbrev entropyD (rho : DensityState (A × (B × (C × D)))) : ℝ :=
  vonNeumannEntropy (marginalD rho)

def splitAB : ((A × B) × (C × D)) ≃ (A × (B × (C × D))) :=
  { toFun := fun q => (q.1.1, (q.1.2, (q.2.1, q.2.2)))
    invFun := fun q => ((q.1, q.2.1), (q.2.2.1, q.2.2.2))
    left_inv := by rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl }

noncomputable def marginalAB (rho : DensityState (A × (B × (C × D)))) : DensityState (A × B) :=
  reduceState splitAB rho

noncomputable abbrev entropyAB (rho : DensityState (A × (B × (C × D)))) : ℝ :=
  vonNeumannEntropy (marginalAB rho)

def splitAC : ((A × C) × (B × D)) ≃ (A × (B × (C × D))) :=
  { toFun := fun q => (q.1.1, (q.2.1, (q.1.2, q.2.2)))
    invFun := fun q => ((q.1, q.2.2.1), (q.2.1, q.2.2.2))
    left_inv := by rintro ⟨⟨a, c⟩, ⟨b, d⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl }

noncomputable def marginalAC (rho : DensityState (A × (B × (C × D)))) : DensityState (A × C) :=
  reduceState splitAC rho

noncomputable abbrev entropyAC (rho : DensityState (A × (B × (C × D)))) : ℝ :=
  vonNeumannEntropy (marginalAC rho)

def splitAD : ((A × D) × (B × C)) ≃ (A × (B × (C × D))) :=
  { toFun := fun q => (q.1.1, (q.2.1, (q.2.2, q.1.2)))
    invFun := fun q => ((q.1, q.2.2.2), (q.2.1, q.2.2.1))
    left_inv := by rintro ⟨⟨a, d⟩, ⟨b, c⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl }

noncomputable def marginalAD (rho : DensityState (A × (B × (C × D)))) : DensityState (A × D) :=
  reduceState splitAD rho

noncomputable abbrev entropyAD (rho : DensityState (A × (B × (C × D)))) : ℝ :=
  vonNeumannEntropy (marginalAD rho)

def splitBC : ((B × C) × (A × D)) ≃ (A × (B × (C × D))) :=
  { toFun := fun q => (q.2.1, (q.1.1, (q.1.2, q.2.2)))
    invFun := fun q => ((q.2.1, q.2.2.1), (q.1, q.2.2.2))
    left_inv := by rintro ⟨⟨b, c⟩, ⟨a, d⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl }

noncomputable def marginalBC (rho : DensityState (A × (B × (C × D)))) : DensityState (B × C) :=
  reduceState splitBC rho

noncomputable abbrev entropyBC (rho : DensityState (A × (B × (C × D)))) : ℝ :=
  vonNeumannEntropy (marginalBC rho)

def splitBD : ((B × D) × (A × C)) ≃ (A × (B × (C × D))) :=
  { toFun := fun q => (q.2.1, (q.1.1, (q.2.2, q.1.2)))
    invFun := fun q => ((q.2.1, q.2.2.2), (q.1, q.2.2.1))
    left_inv := by rintro ⟨⟨b, d⟩, ⟨a, c⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl }

noncomputable def marginalBD (rho : DensityState (A × (B × (C × D)))) : DensityState (B × D) :=
  reduceState splitBD rho

noncomputable abbrev entropyBD (rho : DensityState (A × (B × (C × D)))) : ℝ :=
  vonNeumannEntropy (marginalBD rho)

def splitCD : ((C × D) × (A × B)) ≃ (A × (B × (C × D))) :=
  { toFun := fun q => (q.2.1, (q.2.2, (q.1.1, q.1.2)))
    invFun := fun q => ((q.2.2.1, q.2.2.2), (q.1, q.2.1))
    left_inv := by rintro ⟨⟨c, d⟩, ⟨a, b⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl }

noncomputable def marginalCD (rho : DensityState (A × (B × (C × D)))) : DensityState (C × D) :=
  reduceState splitCD rho

noncomputable abbrev entropyCD (rho : DensityState (A × (B × (C × D)))) : ℝ :=
  vonNeumannEntropy (marginalCD rho)

def splitACD : ((A × (C × D)) × B) ≃ (A × (B × (C × D))) :=
  { toFun := fun q => (q.1.1, (q.2, (q.1.2.1, q.1.2.2)))
    invFun := fun q => ((q.1, (q.2.2.1, q.2.2.2)), q.2.1)
    left_inv := by rintro ⟨⟨a, ⟨c, d⟩⟩, b⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl }

noncomputable def marginalACD (rho : DensityState (A × (B × (C × D)))) : DensityState (A × (C × D)) :=
  reduceState splitACD rho

noncomputable abbrev entropyACD (rho : DensityState (A × (B × (C × D)))) : ℝ :=
  vonNeumannEntropy (marginalACD rho)

def splitBCD : ((B × (C × D)) × A) ≃ (A × (B × (C × D))) :=
  { toFun := fun q => (q.2, (q.1.1, (q.1.2.1, q.1.2.2)))
    invFun := fun q => ((q.2.1, (q.2.2.1, q.2.2.2)), q.1)
    left_inv := by rintro ⟨⟨b, ⟨c, d⟩⟩, a⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, d⟩⟩⟩; rfl }

noncomputable def marginalBCD (rho : DensityState (A × (B × (C × D)))) : DensityState (B × (C × D)) :=
  reduceState splitBCD rho

noncomputable abbrev entropyBCD (rho : DensityState (A × (B × (C × D)))) : ℝ :=
  vonNeumannEntropy (marginalBCD rho)

noncomputable abbrev marginalABCD (rho : DensityState (A × (B × (C × D)))) := rho

noncomputable abbrev entropyABCD (rho : DensityState (A × (B × (C × D)))) : ℝ :=
  vonNeumannEntropy (marginalABCD rho)

/-- I(A:B) + I(A:CD) + 3 I(C:D|A) + I(C:D|B) - 2 I(C:D), on actual marginals. -/
noncomputable def zhangYeungDefect (rho : DensityState (A × (B × (C × D)))) : ℝ :=
  (entropyA rho + entropyB rho - entropyAB rho) +
    (entropyA rho + entropyCD rho - entropyACD rho) +
    3 * (entropyAC rho + entropyAD rho - entropyA rho - entropyACD rho) +
    (entropyBC rho + entropyBD rho - entropyB rho - entropyBCD rho) -
    2 * (entropyC rho + entropyD rho - entropyCD rho)

end D5.S3.Quantum.Information.FourPartyMarginals
