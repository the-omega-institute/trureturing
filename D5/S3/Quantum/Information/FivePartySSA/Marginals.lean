/- GID: D5/S3/Quantum/Information/FivePartySSA/Marginals
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/FivePartySSA/Marginals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Eleven actual conditional mutual informations give the quantum copy precursor. -/

import D5.S3.Quantum.Information.MarginalCalculus

set_option autoImplicit false

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.StrongSubadditivity
open D5.S3.Quantum.Information.MarginalCalculus

namespace D5.S3.Quantum.Information.FivePartySSA

variable {A B C D E : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

def splitA : (A × (B × (C × (D × E)))) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.1, (q.2.1, (q.2.2.1, (q.2.2.2.1, q.2.2.2.2))))
    invFun := fun q => (q.1, (q.2.1, (q.2.2.1, (q.2.2.2.1, q.2.2.2.2))))
    left_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalA (rho : DensityState (A × (B × (C × (D × E))))) : DensityState A :=
  reduceState splitA rho

noncomputable abbrev entropyA (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalA rho)

def splitC : (C × (A × (B × (D × E)))) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.2.1, (q.2.2.1, (q.1, (q.2.2.2.1, q.2.2.2.2))))
    invFun := fun q => (q.2.2.1, (q.1, (q.2.1, (q.2.2.2.1, q.2.2.2.2))))
    left_inv := by rintro ⟨c, ⟨a, ⟨b, ⟨d, e⟩⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalC (rho : DensityState (A × (B × (C × (D × E))))) : DensityState C :=
  reduceState splitC rho

noncomputable abbrev entropyC (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalC rho)

def splitD : (D × (A × (B × (C × E)))) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.2.1, (q.2.2.1, (q.2.2.2.1, (q.1, q.2.2.2.2))))
    invFun := fun q => (q.2.2.2.1, (q.1, (q.2.1, (q.2.2.1, q.2.2.2.2))))
    left_inv := by rintro ⟨d, ⟨a, ⟨b, ⟨c, e⟩⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalD (rho : DensityState (A × (B × (C × (D × E))))) : DensityState D :=
  reduceState splitD rho

noncomputable abbrev entropyD (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalD rho)

def splitE : (E × (A × (B × (C × D)))) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.2.1, (q.2.2.1, (q.2.2.2.1, (q.2.2.2.2, q.1))))
    invFun := fun q => (q.2.2.2.2, (q.1, (q.2.1, (q.2.2.1, q.2.2.2.1))))
    left_inv := by rintro ⟨e, ⟨a, ⟨b, ⟨c, d⟩⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalE (rho : DensityState (A × (B × (C × (D × E))))) : DensityState E :=
  reduceState splitE rho

noncomputable abbrev entropyE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalE rho)

def splitAB : ((A × B) × (C × (D × E))) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.1.1, (q.1.2, (q.2.1, (q.2.2.1, q.2.2.2))))
    invFun := fun q => ((q.1, q.2.1), (q.2.2.1, (q.2.2.2.1, q.2.2.2.2)))
    left_inv := by rintro ⟨⟨a, b⟩, ⟨c, ⟨d, e⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalAB (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (A × B) :=
  reduceState splitAB rho

noncomputable abbrev entropyAB (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalAB rho)

def splitAC : ((A × C) × (B × (D × E))) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.1.1, (q.2.1, (q.1.2, (q.2.2.1, q.2.2.2))))
    invFun := fun q => ((q.1, q.2.2.1), (q.2.1, (q.2.2.2.1, q.2.2.2.2)))
    left_inv := by rintro ⟨⟨a, c⟩, ⟨b, ⟨d, e⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalAC (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (A × C) :=
  reduceState splitAC rho

noncomputable abbrev entropyAC (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalAC rho)

def splitAE : ((A × E) × (B × (C × D))) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.1.1, (q.2.1, (q.2.2.1, (q.2.2.2, q.1.2))))
    invFun := fun q => ((q.1, q.2.2.2.2), (q.2.1, (q.2.2.1, q.2.2.2.1)))
    left_inv := by rintro ⟨⟨a, e⟩, ⟨b, ⟨c, d⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalAE (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (A × E) :=
  reduceState splitAE rho

noncomputable abbrev entropyAE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalAE rho)

def splitBC : ((B × C) × (A × (D × E))) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.2.1, (q.1.1, (q.1.2, (q.2.2.1, q.2.2.2))))
    invFun := fun q => ((q.2.1, q.2.2.1), (q.1, (q.2.2.2.1, q.2.2.2.2)))
    left_inv := by rintro ⟨⟨b, c⟩, ⟨a, ⟨d, e⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalBC (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (B × C) :=
  reduceState splitBC rho

noncomputable abbrev entropyBC (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalBC rho)

def splitBD : ((B × D) × (A × (C × E))) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.2.1, (q.1.1, (q.2.2.1, (q.1.2, q.2.2.2))))
    invFun := fun q => ((q.2.1, q.2.2.2.1), (q.1, (q.2.2.1, q.2.2.2.2)))
    left_inv := by rintro ⟨⟨b, d⟩, ⟨a, ⟨c, e⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalBD (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (B × D) :=
  reduceState splitBD rho

noncomputable abbrev entropyBD (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalBD rho)

def splitBE : ((B × E) × (A × (C × D))) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.2.1, (q.1.1, (q.2.2.1, (q.2.2.2, q.1.2))))
    invFun := fun q => ((q.2.1, q.2.2.2.2), (q.1, (q.2.2.1, q.2.2.2.1)))
    left_inv := by rintro ⟨⟨b, e⟩, ⟨a, ⟨c, d⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalBE (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (B × E) :=
  reduceState splitBE rho

noncomputable abbrev entropyBE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalBE rho)

def splitCD : ((C × D) × (A × (B × E))) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.2.1, (q.2.2.1, (q.1.1, (q.1.2, q.2.2.2))))
    invFun := fun q => ((q.2.2.1, q.2.2.2.1), (q.1, (q.2.1, q.2.2.2.2)))
    left_inv := by rintro ⟨⟨c, d⟩, ⟨a, ⟨b, e⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalCD (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (C × D) :=
  reduceState splitCD rho

noncomputable abbrev entropyCD (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalCD rho)

def splitCE : ((C × E) × (A × (B × D))) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.2.1, (q.2.2.1, (q.1.1, (q.2.2.2, q.1.2))))
    invFun := fun q => ((q.2.2.1, q.2.2.2.2), (q.1, (q.2.1, q.2.2.2.1)))
    left_inv := by rintro ⟨⟨c, e⟩, ⟨a, ⟨b, d⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalCE (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (C × E) :=
  reduceState splitCE rho

noncomputable abbrev entropyCE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalCE rho)

def splitDE : ((D × E) × (A × (B × C))) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.2.1, (q.2.2.1, (q.2.2.2, (q.1.1, q.1.2))))
    invFun := fun q => ((q.2.2.2.1, q.2.2.2.2), (q.1, (q.2.1, q.2.2.1)))
    left_inv := by rintro ⟨⟨d, e⟩, ⟨a, ⟨b, c⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalDE (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (D × E) :=
  reduceState splitDE rho

noncomputable abbrev entropyDE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalDE rho)

def splitABC : ((A × (B × C)) × (D × E)) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.1.1, (q.1.2.1, (q.1.2.2, (q.2.1, q.2.2))))
    invFun := fun q => ((q.1, (q.2.1, q.2.2.1)), (q.2.2.2.1, q.2.2.2.2))
    left_inv := by rintro ⟨⟨a, ⟨b, c⟩⟩, ⟨d, e⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalABC (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (A × (B × C)) :=
  reduceState splitABC rho

noncomputable abbrev entropyABC (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalABC rho)

def splitABE : ((A × (B × E)) × (C × D)) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.1.1, (q.1.2.1, (q.2.1, (q.2.2, q.1.2.2))))
    invFun := fun q => ((q.1, (q.2.1, q.2.2.2.2)), (q.2.2.1, q.2.2.2.1))
    left_inv := by rintro ⟨⟨a, ⟨b, e⟩⟩, ⟨c, d⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalABE (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (A × (B × E)) :=
  reduceState splitABE rho

noncomputable abbrev entropyABE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalABE rho)

def splitACD : ((A × (C × D)) × (B × E)) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.1.1, (q.2.1, (q.1.2.1, (q.1.2.2, q.2.2))))
    invFun := fun q => ((q.1, (q.2.2.1, q.2.2.2.1)), (q.2.1, q.2.2.2.2))
    left_inv := by rintro ⟨⟨a, ⟨c, d⟩⟩, ⟨b, e⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalACD (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (A × (C × D)) :=
  reduceState splitACD rho

noncomputable abbrev entropyACD (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalACD rho)

def splitACE : ((A × (C × E)) × (B × D)) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.1.1, (q.2.1, (q.1.2.1, (q.2.2, q.1.2.2))))
    invFun := fun q => ((q.1, (q.2.2.1, q.2.2.2.2)), (q.2.1, q.2.2.2.1))
    left_inv := by rintro ⟨⟨a, ⟨c, e⟩⟩, ⟨b, d⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalACE (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (A × (C × E)) :=
  reduceState splitACE rho

noncomputable abbrev entropyACE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalACE rho)

def splitBCD : ((B × (C × D)) × (A × E)) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.2.1, (q.1.1, (q.1.2.1, (q.1.2.2, q.2.2))))
    invFun := fun q => ((q.2.1, (q.2.2.1, q.2.2.2.1)), (q.1, q.2.2.2.2))
    left_inv := by rintro ⟨⟨b, ⟨c, d⟩⟩, ⟨a, e⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalBCD (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (B × (C × D)) :=
  reduceState splitBCD rho

noncomputable abbrev entropyBCD (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalBCD rho)

def splitBCE : ((B × (C × E)) × (A × D)) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.2.1, (q.1.1, (q.1.2.1, (q.2.2, q.1.2.2))))
    invFun := fun q => ((q.2.1, (q.2.2.1, q.2.2.2.2)), (q.1, q.2.2.2.1))
    left_inv := by rintro ⟨⟨b, ⟨c, e⟩⟩, ⟨a, d⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalBCE (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (B × (C × E)) :=
  reduceState splitBCE rho

noncomputable abbrev entropyBCE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalBCE rho)

def splitBDE : ((B × (D × E)) × (A × C)) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.2.1, (q.1.1, (q.2.2, (q.1.2.1, q.1.2.2))))
    invFun := fun q => ((q.2.1, (q.2.2.2.1, q.2.2.2.2)), (q.1, q.2.2.1))
    left_inv := by rintro ⟨⟨b, ⟨d, e⟩⟩, ⟨a, c⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalBDE (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (B × (D × E)) :=
  reduceState splitBDE rho

noncomputable abbrev entropyBDE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalBDE rho)

def splitCDE : ((C × (D × E)) × (A × B)) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.2.1, (q.2.2, (q.1.1, (q.1.2.1, q.1.2.2))))
    invFun := fun q => ((q.2.2.1, (q.2.2.2.1, q.2.2.2.2)), (q.1, q.2.1))
    left_inv := by rintro ⟨⟨c, ⟨d, e⟩⟩, ⟨a, b⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalCDE (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (C × (D × E)) :=
  reduceState splitCDE rho

noncomputable abbrev entropyCDE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalCDE rho)

def splitABCD : ((A × (B × (C × D))) × E) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.1.1, (q.1.2.1, (q.1.2.2.1, (q.1.2.2.2, q.2))))
    invFun := fun q => ((q.1, (q.2.1, (q.2.2.1, q.2.2.2.1))), q.2.2.2.2)
    left_inv := by rintro ⟨⟨a, ⟨b, ⟨c, d⟩⟩⟩, e⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalABCD (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (A × (B × (C × D))) :=
  reduceState splitABCD rho

noncomputable abbrev entropyABCD (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalABCD rho)

def splitABCE : ((A × (B × (C × E))) × D) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.1.1, (q.1.2.1, (q.1.2.2.1, (q.2, q.1.2.2.2))))
    invFun := fun q => ((q.1, (q.2.1, (q.2.2.1, q.2.2.2.2))), q.2.2.2.1)
    left_inv := by rintro ⟨⟨a, ⟨b, ⟨c, e⟩⟩⟩, d⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalABCE (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (A × (B × (C × E))) :=
  reduceState splitABCE rho

noncomputable abbrev entropyABCE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalABCE rho)

def splitACDE : ((A × (C × (D × E))) × B) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.1.1, (q.2, (q.1.2.1, (q.1.2.2.1, q.1.2.2.2))))
    invFun := fun q => ((q.1, (q.2.2.1, (q.2.2.2.1, q.2.2.2.2))), q.2.1)
    left_inv := by rintro ⟨⟨a, ⟨c, ⟨d, e⟩⟩⟩, b⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalACDE (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (A × (C × (D × E))) :=
  reduceState splitACDE rho

noncomputable abbrev entropyACDE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalACDE rho)

def splitBCDE : ((B × (C × (D × E))) × A) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.2, (q.1.1, (q.1.2.1, (q.1.2.2.1, q.1.2.2.2))))
    invFun := fun q => ((q.2.1, (q.2.2.1, (q.2.2.2.1, q.2.2.2.2))), q.1)
    left_inv := by rintro ⟨⟨b, ⟨c, ⟨d, e⟩⟩⟩, a⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalBCDE (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (B × (C × (D × E))) :=
  reduceState splitBCDE rho

noncomputable abbrev entropyBCDE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalBCDE rho)

noncomputable abbrev marginalABCDE (rho : DensityState (A × (B × (C × (D × E))))) := rho

noncomputable abbrev entropyABCDE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalABCDE rho)


def splitAD : ((A × D) × (B × (C × E))) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.1.1, (q.2.1, (q.2.2.1, (q.1.2, q.2.2.2))))
    invFun := fun q => ((q.1, q.2.2.2.1), (q.2.1, (q.2.2.1, q.2.2.2.2)))
    left_inv := by rintro ⟨⟨a, d⟩, ⟨b, ⟨c, e⟩⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalAD (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (A × D) :=
  reduceState splitAD rho

noncomputable abbrev entropyAD (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalAD rho)

def splitADE : ((A × (D × E)) × (B × C)) ≃ (A × (B × (C × (D × E)))) :=
  { toFun := fun q => (q.1.1, (q.2.1, (q.2.2, (q.1.2.1, q.1.2.2))))
    invFun := fun q => ((q.1, (q.2.2.2.1, q.2.2.2.2)), (q.2.1, q.2.2.1))
    left_inv := by rintro ⟨⟨a, ⟨d, e⟩⟩, ⟨b, c⟩⟩; rfl
    right_inv := by rintro ⟨a, ⟨b, ⟨c, ⟨d, e⟩⟩⟩⟩; rfl }

noncomputable def marginalADE (rho : DensityState (A × (B × (C × (D × E))))) : DensityState (A × (D × E)) :=
  reduceState splitADE rho

noncomputable abbrev entropyADE (rho : DensityState (A × (B × (C × (D × E))))) : ℝ :=
  vonNeumannEntropy (marginalADE rho)

end D5.S3.Quantum.Information.FivePartySSA
