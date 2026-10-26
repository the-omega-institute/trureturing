import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.ChargedResidue.TwoChamber

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.ChargedResidue.TwoChamber
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open PowerSeries

abbrev Parameters := ℤ × ℤ × ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun _ => Unit) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p _ => chamberDifference p.1 p.2.1 p.2.2) (fun empty => nomatch empty)

abbrev coefficientScope := type_of% (@two_chamber_coefficient)
theorem coefficient_source : coefficientScope := @two_chamber_coefficient

def coefficientArena : Arena where
  signature := signature
  Law observation := ∀ (a b v : ℤ),
    observation.readout () ⟨a,b,v⟩ () = localPoleTotal a b v

theorem coefficient_bridge : coefficientScope ↔ coefficientArena.Law actual := Iff.rfl
theorem coefficient_positive : coefficientArena.Law actual := coefficient_bridge.mp coefficient_source

def scalarActual : Realization signature := realize signature
  (fun _ p _ => chamberDifference (p.1+p.2.1) (p.1-p.2.1) p.2.2)
  (fun empty => nomatch empty)

abbrev scalarScope := type_of% (@signed_two_chamber_scalar)
theorem scalar_source : scalarScope := @signed_two_chamber_scalar

def scalarArena : Arena where
  signature := signature
  Law observation := ∀ (q B v : ℤ), observation.readout () ⟨q,B,v⟩ () =
      (1/2 : ℂ) * (2 : ℂ)^(-2*B) *
        (if -q-1-B < 0 then 0 else collisionScalar (v-2*q-2) B (-q-1-B).toNat) +
      (-1 : ℂ)^v * (1/2 : ℂ) * (2 : ℂ)^(2*B) *
        (if -q-1+B < 0 then 0 else collisionScalar (v-2*q-2) (-B) (-q-1+B).toNat)

theorem scalar_bridge : scalarScope ↔ scalarArena.Law scalarActual := Iff.rfl
theorem scalar_positive : scalarArena.Law scalarActual := scalar_bridge.mp scalar_source

/- These exact source scopes and positive realizations retain the original
   infinite parameter and series families. Registration still needs a lawful
   enrolled-template readout, whole-family variation, sensitivity, observational
   dependence and structural sourceSelection; none is inferred from positivity. -/
end Reg.D5.S3.VertexAlgebra.ChargedResidue.TwoChamber
