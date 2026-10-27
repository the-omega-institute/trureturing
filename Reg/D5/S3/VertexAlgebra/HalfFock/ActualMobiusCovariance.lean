import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance

/- Faithful partial source-family audit. No Contract.Registration,
TemplateEnrollment selection, intervention proof or validated binding is
claimed. The operator-valued whole-family sensitivity remains open. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- Full-source faithful family attempt. This does not supply an enrolled
readout, intervention, sensitivity, or a Contract.Registration. -/
namespace FullSource
structure Parameter where
  D : LatticeData
  hu : IsUnit D.G.det

abbrev signature := Reg.Support.SingleDependentReadout.signature Parameter
  (fun p => Carrier p.D × ℤ) (fun p => Module.End ℂ (ActualTensor p.D p.hu))

def actual : Realization signature :=
  realize signature
    (fun _ p ae => (LatticeHalfFockCorrectedField.correctedField p.D p.hu ae.1).coeff ae.2)
    (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (p : Parameter) (a : Carrier p.D) (e : ℤ),
    tensorL p.D (ActualGround p.D p.hu) (HalfFockSpectralFiberSource.actualInverse p.D) 1 *
        readout.readout () p (a,e) -
      readout.readout () p (a,e) *
        tensorL p.D (ActualGround p.D p.hu) (HalfFockSpectralFiberSource.actualInverse p.D) 1 =
      readout.readout () p
        (LatticeSugawaraCurrents.sugawaraMode p.D (LatticeSugawaraCurrents.gramComplex p.D)⁻¹ 1 a,e) +
      ((e:ℂ)/2-1) • readout.readout () p (a,e-2) +
      (2:ℂ) • readout.readout () p
        (LatticeSugawaraCurrents.sugawaraMode p.D (LatticeSugawaraCurrents.gramComplex p.D)⁻¹ 0 a,e-2)

theorem source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance.corrected_field_l1_coefficient)) ↔
      arena.Law actual := by
  constructor
  · intro h p a e
    exact h p.D p.hu a e
  · intro h D hu a e
    exact h ⟨D, hu⟩ a e

theorem actual_positive : arena.Law actual := source_bridge.mp
  _root_.D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance.corrected_field_l1_coefficient
end FullSource

end Reg.D5.S3.VertexAlgebra.HalfFock.ActualMobiusCovariance
