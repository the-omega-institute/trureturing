import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.HalfFock.ActualMobiusCharged

/- Faithful partial source-family audit. No Contract.Registration,
TemplateEnrollment selection, intervention proof or validated binding is
claimed. The operator-valued whole-family sensitivity remains open. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.HalfFock.ActualMobiusCharged
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Parameter where
  D : LatticeData
  hu : IsUnit D.G.det
  a : Charge D

abbrev signature := Reg.Support.SingleDependentReadout.signature Parameter
  (fun _ => ℤ) (fun p => Module.End ℂ (ActualTensor p.D p.hu))

def actual : Realization signature :=
  realize signature
    (fun _ p e => chargedCoefficient p.D p.hu p.a e) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law readout := ∀ (p : Parameter) (e : ℤ),
    tensorL p.D (ActualGround p.D p.hu) (HalfFockSpectralFiberSource.actualInverse p.D) 1 *
        readout.readout () p e -
      readout.readout () p e *
        tensorL p.D (ActualGround p.D p.hu) (HalfFockSpectralFiberSource.actualInverse p.D) 1 =
      (((e : ℂ) - 2) / 2 + (bilinear p.D p.a p.a : ℂ)) • readout.readout () p (e - 2)

theorem source_bridge :
    (type_of% (@_root_.D5.S3.VertexAlgebra.HalfFock.ActualMobiusCharged.charged_l1_coefficient)) ↔
      arena.Law actual := by
  constructor
  · intro h p e
    exact h p.D p.hu p.a e
  · intro h D hu a e
    exact h ⟨D, hu, a⟩ e

theorem actual_positive : arena.Law actual := source_bridge.mp
  _root_.D5.S3.VertexAlgebra.HalfFock.ActualMobiusCharged.charged_l1_coefficient

end Reg.D5.S3.VertexAlgebra.HalfFock.ActualMobiusCharged
