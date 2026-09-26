/- GID: D5/S3/ConceptDynamics/InformationEscape/ParityKernelRegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/ParityKernelRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Observation families for parity-kernel laws on the sign hypercube of every dimension. -/

import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Basic

namespace D5.S3.ConceptDynamics.InformationEscape.ParityKernelRegistrationTemplates

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-- A finite role observes one real law value of a coordinate record. Parameters are the
dimension, the kernel profile, the observed coordinate set and the horizon; the state is the
sequence of observed sign vectors at times `0, …, T`. -/
def subcoordinateRecordSignature : Signature where
  Params := Σ d : ℕ, Σ _ : (Fin d → ℤˣ) → ℝ, Σ _ : Finset (Fin d), ℕ
  State := fun p => Fin (p.2.2.2 + 1) → Fin p.1 → ℤˣ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- A finite role observes one real two-step transition value. Parameters are the dimension, two
kernel profiles and the start vertex; the state is the end vertex. -/
def twoStepKernelSignature : Signature where
  Params := Σ d : ℕ, Σ _ : (Fin d → ℤˣ) → ℝ, Σ _ : (Fin d → ℤˣ) → ℝ, Fin d → ℤˣ
  State := fun p => Fin p.1 → ℤˣ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- A finite role observes one real path-functional value as a function of the number of steps.
Parameters are the dimension and two kernel profiles; the state is the path length. -/
def profilePairStepSignature : Signature where
  Params := Σ d : ℕ, Σ _ : (Fin d → ℤˣ) → ℝ, (Fin d → ℤˣ) → ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- A finite role observes the characteristic polynomial of a kernel built from a profile.
The parameter is the dimension; the state is the profile on the sign hypercube. -/
@[reducible] def profileCharpolySignature : Signature where
  Params := ℕ
  State := fun d => (Fin d → ℤˣ) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Polynomial ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

end D5.S3.ConceptDynamics.InformationEscape.ParityKernelRegistrationTemplates
