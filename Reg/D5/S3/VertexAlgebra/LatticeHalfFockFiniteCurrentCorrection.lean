import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCurrentCorrection
import Reg.Support.SingleDependentReadout

/-! Faithful dependent-family observations on the complete original source telescope. -/

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCurrentCorrection

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open LatticeHalfFockCorrectedField LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

noncomputable section

structure TriangleParameter where
  lattice : LatticeData
  unit : IsUnit lattice.G.det
  index : Index lattice
  source : Carrier lattice
  gamma : ℤ
  mode : ℤ
  length : ℕ
  cutoff : vectorFrequencyBound lattice source + 1 ≤ length

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  TriangleParameter
  (fun p => ActualTensor p.lattice p.unit)
  (fun p => ActualTensor p.lattice p.unit)

def actual : Realization signature := realize signature
  (fun _ p x =>
    (correctedField p.lattice p.unit
      (neutralMode p.lattice p.index.1 (-(sourceWeight p.lattice p.index : ℤ)) p.source)).coeff
        (-2 * p.mode - p.gamma - 3) x)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (index : Index D) (b : Carrier D) (gamma k : ℤ) (x : ActualTensor D hu) (L : ℕ)
    (cutoff : vectorFrequencyBound D b + 1 ≤ L),
    let m : ℕ := sourceWeight D index
    readout.readout () ⟨D, hu, index, b, gamma, k, L, cutoff⟩ x =
      (∑ j ∈ Finset.range m, halfBinomial j •
        currentResidue D hu index.1 (correctedField D hu b) gamma
          (-(m : ℤ) + (j : ℤ)) (k - (j : ℤ)) x) +
      ∑ s ∈ Finset.range L, halfBinomial (m + s) •
        (∑ n ∈ Finset.range L, if s ≤ n then
          Ring.choose (1 / 2 : ℂ) (n - s) •
            (correctedField D hu (neutralMode D index.1 (n : ℤ) b)).coeff
              (-2 * (k - (m : ℤ) - (n : ℤ)) - gamma - 3) x else 0)

/-- Complete original telescope for the dependent-family registration attempt. -/
abbrev sourceScope_correctedField_negative_current_insertion_finite_triangle :=
  type_of% (@correctedField_negative_current_insertion_finite_triangle)

theorem source_actual_correctedField_negative_current_insertion_finite_triangle :
    sourceScope_correctedField_negative_current_insertion_finite_triangle :=
  @correctedField_negative_current_insertion_finite_triangle

theorem source_bridge :
    sourceScope_correctedField_negative_current_insertion_finite_triangle ↔ arena.Law actual :=
  Iff.rfl

theorem actual_law : arena.Law actual :=
  source_bridge.mp source_actual_correctedField_negative_current_insertion_finite_triangle

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCurrentCorrection
