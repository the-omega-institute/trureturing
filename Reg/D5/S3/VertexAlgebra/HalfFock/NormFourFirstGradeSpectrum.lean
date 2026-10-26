import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.HalfFock.NormFourFirstGradeSpectrum

set_option autoImplicit false

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.HalfFock.NormFourFirstGradeSpectrum

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockGradedTrace HalfFock.NormFourLowestGrades
open HalfFock.NormFourFirstGradeSpectrum HalfFock.LatticeHalfFockParityField
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped VertexOperator

/- Exact dependent source mirrors preserve the actual operators, submodules and
dimensions. They are not Contract.Registration values. Whole-family intervention,
sensitivity, observational dependence and typed source-selection evidence are absent.
Open audit: https://github.com/the-omega-institute/trureturing/issues/22350.
No validated audit is asserted. -/

structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  a : Charge D
  ha : bilinear D a a = 4
  s : ℂ

structure SignParams extends Params where
  hs : s ^ 2 = 1

namespace Transport
abbrev signature : Signature where
  Params := Params
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Module.End ℂ (actualGrade p.D p.hu 1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => actualGradeOneZeroMode p.D p.hu p.a p.ha p.s) (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ),
    r.readout () ⟨D, hu, a, ha, s⟩ () = actualTransport D hu (nativeL D hu a s)

theorem source_bridge : (type_of% (@actualZeroMode_transport)) ↔ law actual := Iff.rfl
theorem actual_positive : law actual := source_bridge.mp (@actualZeroMode_transport)
end Transport

namespace Projectors
abbrev signature : Signature where
  Params := SignParams
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Module.End ℂ (actualGrade p.D p.hu 1) ×
    Module.End ℂ (actualGrade p.D p.hu 1) × Module.End ℂ (actualGrade p.D p.hu 1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => (actualProjectorZero p.D p.hu p.a p.s,
    actualProjectorSixteen p.D p.hu p.a p.s, actualProjectorHalf p.D p.hu p.a p.s))
  (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1),
    ((r.readout () ⟨⟨D, hu, a, ha, s⟩, hs⟩ ()).1 +
      (r.readout () ⟨⟨D, hu, a, ha, s⟩, hs⟩ ()).2.1 +
      (r.readout () ⟨⟨D, hu, a, ha, s⟩, hs⟩ ()).2.2 = 1) ∧
    (LinearMap.IsProj ((actualGradeOneZeroMode D hu a ha s).eigenspace 0)
      (r.readout () ⟨⟨D, hu, a, ha, s⟩, hs⟩ ()).1 ∧
    LinearMap.IsProj ((actualGradeOneZeroMode D hu a ha s).eigenspace (1 / 16))
      (r.readout () ⟨⟨D, hu, a, ha, s⟩, hs⟩ ()).2.1 ∧
    LinearMap.IsProj ((actualGradeOneZeroMode D hu a ha s).eigenspace (1 / 2))
      (r.readout () ⟨⟨D, hu, a, ha, s⟩, hs⟩ ()).2.2) ∧
    (LinearMap.range (r.readout () ⟨⟨D, hu, a, ha, s⟩, hs⟩ ()).1 =
      (actualGradeOneZeroMode D hu a ha s).eigenspace 0 ∧
    LinearMap.range (r.readout () ⟨⟨D, hu, a, ha, s⟩, hs⟩ ()).2.1 =
      (actualGradeOneZeroMode D hu a ha s).eigenspace (1 / 16) ∧
    LinearMap.range (r.readout () ⟨⟨D, hu, a, ha, s⟩, hs⟩ ()).2.2 =
      (actualGradeOneZeroMode D hu a ha s).eigenspace (1 / 2))

theorem source_bridge : (type_of% (@actual_projectors_complete)) ↔ law actual := Iff.rfl
theorem actual_positive : law actual := source_bridge.mp (@actual_projectors_complete)
end Projectors

namespace Traces
abbrev signature : Signature where
  Params := Params
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ × ℂ × ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => (LinearMap.trace ℂ (actualGrade p.D p.hu 1)
      (actualProjectorZero p.D p.hu p.a p.s),
    LinearMap.trace ℂ (actualGrade p.D p.hu 1) (actualProjectorSixteen p.D p.hu p.a p.s),
    LinearMap.trace ℂ (actualGrade p.D p.hu 1) (actualProjectorHalf p.D p.hu p.a p.s)))
  (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ),
    (r.readout () ⟨D, hu, a, ha, s⟩ ()).1 =
      ((D.rank : ℂ) - 1) * ((2 ^ (D.rank / 2) : ℕ) : ℂ) / 2 ∧
    (r.readout () ⟨D, hu, a, ha, s⟩ ()).2.1 =
      (D.rank : ℂ) * ((2 ^ (D.rank / 2) : ℕ) : ℂ) / 2 ∧
    (r.readout () ⟨D, hu, a, ha, s⟩ ()).2.2 = ((2 ^ (D.rank / 2) : ℕ) : ℂ) / 2

theorem source_bridge : (type_of% (@actual_projectors_traces)) ↔ law actual := Iff.rfl
theorem actual_positive : law actual := source_bridge.mp (@actual_projectors_traces)
end Traces

namespace Multiplicities
abbrev signature : Signature where
  Params := SignParams
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ × ℕ × ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => (Module.finrank ℂ ((actualGradeOneZeroMode p.D p.hu p.a p.ha p.s).eigenspace 0),
    Module.finrank ℂ ((actualGradeOneZeroMode p.D p.hu p.a p.ha p.s).eigenspace (1 / 16)),
    Module.finrank ℂ ((actualGradeOneZeroMode p.D p.hu p.a p.ha p.s).eigenspace (1 / 2))))
  (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1),
    2 * (r.readout () ⟨⟨D, hu, a, ha, s⟩, hs⟩ ()).1 =
      (D.rank - 1) * 2 ^ (D.rank / 2) ∧
    2 * (r.readout () ⟨⟨D, hu, a, ha, s⟩, hs⟩ ()).2.1 =
      D.rank * 2 ^ (D.rank / 2) ∧
    2 * (r.readout () ⟨⟨D, hu, a, ha, s⟩, hs⟩ ()).2.2 = 2 ^ (D.rank / 2)

theorem source_bridge :
    (type_of% (@actual_first_grade_eigenspace_multiplicities)) ↔ law actual := Iff.rfl
theorem actual_positive : law actual := source_bridge.mp (@actual_first_grade_eigenspace_multiplicities)
end Multiplicities

namespace WholeSpace
structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  h24 : D.rank = 24
abbrev signature : Signature where
  Params := Params
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Submodule ℂ (ActualTensor p.D p.hu)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => actualGrade p.D p.hu 1) (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (h24 : D.rank = 24),
    r.readout () ⟨D, hu, h24⟩ () = parityMinusEnergyTwo D hu

theorem source_bridge :
    (type_of% (@actual_grade_one_eq_parity_minus_energy_two)) ↔ law actual := Iff.rfl
theorem actual_positive : law actual := source_bridge.mp (@actual_grade_one_eq_parity_minus_energy_two)
end WholeSpace

namespace PhysicalSpectrum
structure Params extends SignParams where
  h24 : D.rank = 24
abbrev signature : Signature where
  Params := Params
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Module.End ℂ (parityMinusEnergyTwo p.D p.hu) × ℕ × ℕ × ℕ × ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p _ => (parityMinusEnergyTwoZeroMode p.D p.hu p.h24 p.a p.ha p.s,
    Module.finrank ℂ (parityMinusEnergyTwo p.D p.hu),
    Module.finrank ℂ ((parityMinusEnergyTwoZeroMode p.D p.hu p.h24 p.a p.ha p.s).eigenspace 0),
    Module.finrank ℂ ((parityMinusEnergyTwoZeroMode p.D p.hu p.h24 p.a p.ha p.s).eigenspace (1 / 16)),
    Module.finrank ℂ ((parityMinusEnergyTwoZeroMode p.D p.hu p.h24 p.a p.ha p.s).eigenspace (1 / 2))))
  (fun e => nomatch e)

def law (r : Realization signature) : Prop :=
  ∀ (D : LatticeData) (hu : IsUnit D.G.det) (h24 : D.rank = 24)
    (a : Charge D) (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1),
    (∀ v : parityMinusEnergyTwo D hu,
      ((r.readout () ⟨⟨⟨D, hu, a, ha, s⟩, hs⟩, h24⟩ ()).1 v : ActualTensor D hu) =
        (((fixedParitySlice D hu (-1) (normFourFixedSource D a s))[[1]])
          ⟨v, v.property.1⟩ : ActualTensor D hu)) ∧
    (r.readout () ⟨⟨⟨D, hu, a, ha, s⟩, hs⟩, h24⟩ ()).2.1 = 98304 ∧
    (r.readout () ⟨⟨⟨D, hu, a, ha, s⟩, hs⟩, h24⟩ ()).2.2.1 = 47104 ∧
    (r.readout () ⟨⟨⟨D, hu, a, ha, s⟩, hs⟩, h24⟩ ()).2.2.2.1 = 49152 ∧
    (r.readout () ⟨⟨⟨D, hu, a, ha, s⟩, hs⟩, h24⟩ ()).2.2.2.2 = 2048

theorem source_bridge :
    (type_of% (@actual_parity_minus_energy_two_multiplicities)) ↔ law actual := Iff.rfl
theorem actual_positive : law actual := source_bridge.mp (@actual_parity_minus_energy_two_multiplicities)
end PhysicalSpectrum

end Reg.D5.S3.VertexAlgebra.HalfFock.NormFourFirstGradeSpectrum
