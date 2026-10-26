import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.HalfFock.ActualParityIrreducible

/-! Exact dependent-family source reconstruction for the fixed-source action on
entire actual parity spaces. A four-slot registration is not supplied: the
whole-family intervention, observational sensitivity and escape carrier binding
remain unproved. This partial source bridge is not declared_validated. Missing audit evidence is
tracked at https://github.com/the-omega-institute/trureturing/issues/22484. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.HalfFock.ActualParityIrreducible
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients LatticeInvolution
open HalfFock.LatticeHalfFockParityField HalfFock.ActualParityIrreducible
open scoped VertexOperator

structure Params where
  D : LatticeData
  hu : IsUnit D.G.det
  s : ℂ
  source : FixedCarrier D
  n : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Params (fun p => paritySpace p.D p.hu p.s) (fun p => paritySpace p.D p.hu p.s)

def actual : Realization signature := realize signature
  (fun _ p x => ((fixedParitySlice p.D p.hu p.s p.source)[[p.n]]) x)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (s : ℂ), (s = 1 ∨ s = -1) → ∀ (S : Submodule ℂ (paritySpace D hu s)),
    (∀ (a : FixedCarrier D) (n : ℤ) (v : paritySpace D hu s),
      v ∈ S → r.readout () ⟨D, hu, s, a, n⟩ v ∈ S) → S = ⊥ ∨ S = ⊤

theorem source_bridge :
    (type_of% (@fixedParitySlice_irreducible)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := fixedParitySlice_irreducible

end Reg.D5.S3.VertexAlgebra.HalfFock.ActualParityIrreducible
