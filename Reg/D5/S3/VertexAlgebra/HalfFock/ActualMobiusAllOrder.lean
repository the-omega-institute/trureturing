import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder

/-! Exact dependent-family reconstruction. Enrolled occurrence selection,
whole-family variation/sensitivity and observational dependence are not
supplied here; no Contract.Registration or validated binding is asserted. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeSugawaraCurrents
open LatticeHalfFockChargedTensorCoefficients LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

structure Parameter where
  D : LatticeData
  hu : IsUnit D.G.det

namespace Coefficient
abbrev signature := Reg.Support.SingleDependentReadout.signature Parameter
  (fun p => Carrier p.D × ℤ) (fun p => Module.End ℂ (ActualTensor p.D p.hu))

def actual : Realization signature := realize signature
  (fun _ p ae => (LatticeHalfFockCorrectedField.correctedField p.D p.hu ae.1).coeff ae.2)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (p : Parameter) (n : ℕ) (e : ℤ) (a : Carrier p.D),
    (∑ i ∈ Finset.range (n+1),
      ((-1:ℂ)^(n-i) / ((i.factorial:ℂ)*((n-i).factorial:ℂ))) •
        (tensorL p.D (ActualGround p.D p.hu) (HalfFockSpectralFiberSource.actualInverse p.D) 1 ^ i *
          R.readout () p (a,e) *
          tensorL p.D (ActualGround p.D p.hu) (HalfFockSpectralFiberSource.actualInverse p.D) 1 ^ (n-i))) =
    ∑ h ∈ stateEnergies p.D a, ∑ k ∈ Finset.range (n+1),
      (Ring.choose (2*(h:ℂ)+(e:ℂ)/2-(k:ℂ)-1) (n-k) / (k.factorial:ℂ)) •
        R.readout () p
          ((sugawaraMode p.D (LatticeSugawaraCurrents.gramComplex p.D)⁻¹ 1 ^ k)
            (gradeProjection p.D h a), e-2*(n:ℤ)+2*(k:ℤ))

theorem source_bridge : (type_of% (@corrected_field_mobius_coefficient)) ↔ arena.Law actual := by
  constructor
  · intro H p n e a
    exact H p.D p.hu n e a
  · intro H D hu n e a
    exact H ⟨D,hu⟩ n e a

theorem actual_positive : arena.Law actual := source_bridge.mp corrected_field_mobius_coefficient
end Coefficient

namespace RawCoordinate
abbrev signature := Reg.Support.SingleDependentReadout.signature Parameter
  (fun p => ℕ × ℤ × Carrier p.D)
  (fun p => Module.End ℂ (ActualTensor p.D p.hu) × Module.End ℂ (ActualTensor p.D p.hu))

def actual : Realization signature := realize signature
  (fun _ p nea => ((formalMobiusOrder p.D p.hu nea.1 nea.2.2).coeff nea.2.1,
    rawHalfCoordinateReadout p.D p.hu nea.1 nea.2.1 nea.2.2))
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (p : Parameter) (n : ℕ) (e : ℤ) (a : Carrier p.D),
    (R.readout () p (n,e,a)).1 = (R.readout () p (n,e,a)).2

theorem source_bridge : (type_of% (@formal_mobius_raw_coordinate)) ↔ arena.Law actual := by
  constructor
  · intro H p n e a
    exact H p.D p.hu n e a
  · intro H D hu n e a
    exact H ⟨D,hu⟩ n e a

theorem actual_positive : arena.Law actual := source_bridge.mp formal_mobius_raw_coordinate
end RawCoordinate

end Reg.D5.S3.VertexAlgebra.HalfFock.ActualMobiusAllOrder
