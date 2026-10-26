import D5.S3.VertexAlgebra.LatticeHalfFockPositiveCurrentResidue
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockPositiveCurrentResidue

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

noncomputable section

/-- The complete original source telescope, including both actual carriers. -/
abbrev sourceScope_correctedField_positive_current_residue :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.correctedField_positive_current_residue)

theorem source_actual_correctedField_positive_current_residue :
    sourceScope_correctedField_positive_current_residue :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.correctedField_positive_current_residue

/-- The complete unweighted tail telescope, with the original source cutoff. -/
abbrev sourceScope_correctedField_positive_current_residue_tail :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.correctedField_positive_current_residue_tail)

theorem source_actual_correctedField_positive_current_residue_tail :
    sourceScope_correctedField_positive_current_residue_tail :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.correctedField_positive_current_residue_tail

namespace EqualityAttempt

structure Parameters where
  D : LatticeData
  hu : IsUnit D.G.det
  i : Fin D.rank

abbrev signature : Signature where
  Params := Parameters
  State p := Carrier p.D × ℤ × ℤ × ℕ × ActualTensor p.D p.hu
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ActualTensor p.D p.hu
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun role p input =>
    let (b, gamma, t, s, x) := input
    if role then
      ∑ n ∈ Finset.range (vectorFrequencyBound p.D b + 1),
        if s ≤ n then Ring.choose (1 / 2 : ℂ) (n - s) •
          (correctedField p.D p.hu (neutralMode p.D p.i (n : ℤ) b)).coeff
            (-2 * (t + (s : ℤ) - (n : ℤ)) - gamma - 3) x
        else 0
    else currentResidue p.D p.hu p.i (correctedField p.D p.hu b) gamma (s : ℤ) t x)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ p input, R.readout false p input = R.readout true p input

/-- Reconstructs the full equality telescope without narrowing either carrier. -/
theorem source_bridge : sourceScope_correctedField_positive_current_residue ↔
    arena.Law actual := by
  constructor
  · intro h p ⟨b, gamma, t, s, x⟩
    exact h p.D p.hu p.i b gamma t s x
  · intro h D hu i b gamma t s x
    exact h ⟨D, hu, i⟩ ⟨b, gamma, t, s, x⟩

end EqualityAttempt

namespace TailAttempt

structure Parameters where
  D : LatticeData
  hu : IsUnit D.G.det
  i : Fin D.rank
  b : Carrier D
  gamma : ℤ
  t : ℤ
  s : ℕ
  hs : vectorFrequencyBound D b + 1 ≤ s

abbrev signature : Signature where
  Params := Parameters
  State p := ActualTensor p.D p.hu
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ActualTensor p.D p.hu
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p x => currentResidue p.D p.hu p.i (correctedField p.D p.hu p.b)
    p.gamma (p.s : ℤ) p.t x) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ p x, R.readout () p x = 0

/-- Reconstructs every tail premise, including the source-bound inequality. -/
theorem source_bridge : sourceScope_correctedField_positive_current_residue_tail ↔
    arena.Law actual := by
  constructor
  · intro h p x
    exact h p.D p.hu p.i p.b p.gamma p.t p.s x p.hs
  · intro h D hu i b gamma t s x hs
    exact h ⟨D, hu, i, b, gamma, t, s, hs⟩ x

theorem actual_zero (p : Parameters) (x : signature.State p) : actual.readout () p x = 0 :=
  source_actual_correctedField_positive_current_residue_tail
    p.D p.hu p.i p.b p.gamma p.t p.s x p.hs

/-- A complete-residue readout on admitted tail fibers cannot supply dependence. -/
theorem whole_residue_dependence_impossible : ¬ ObservationalDependence signature actual := by
  intro dependence
  obtain ⟨p, x, y, different⟩ := dependence ()
  exact different (by rw [actual_zero, actual_zero])

end TailAttempt

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockPositiveCurrentResidue
