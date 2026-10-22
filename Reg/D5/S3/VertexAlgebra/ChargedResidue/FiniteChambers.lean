import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.ChargedResidue.FiniteChambers

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.ChargedResidue.FiniteChambers
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedResidue LatticeHalfFockChargedCollision
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev Parameters := Σ D : LatticeData, Charge D × Charge D × ℤ × ℤ × ℕ × ℕ
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun _ => Unit) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p _ => nativeChamberScalar p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1
    p.2.2.2.2.2.1 p.2.2.2.2.2.2) (fun empty => nomatch empty)

abbrev sourceScope := type_of% (@native_chamber_scalar_full)
theorem source_actual : sourceScope := @native_chamber_scalar_full

def arena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (left right : Charge D) (q v : ℤ)
    (F R : ℕ), v < F → 2*q-v < R →
    observation.readout () ⟨D,left,right,q,v,F,R⟩ () =
      (1/2 : ℂ) * (2 : ℂ)^(-2*bilinear D left right) *
        (if -q-1-bilinear D left right < 0 then 0 else
          collisionScalar (v-2*q-2) (bilinear D left right)
            (-q-1-bilinear D left right).toNat) +
      (-1 : ℂ)^v * (1/2 : ℂ) * (2 : ℂ)^(2*bilinear D left right) *
        (if -q-1+bilinear D left right < 0 then 0 else
          collisionScalar (v-2*q-2) (-bilinear D left right)
            (-q-1+bilinear D left right).toNat)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl
theorem actual_positive : arena.Law actual := source_bridge.mp source_actual

/- The complete original dependent family is retained. Lawful template
   readout, variation, sensitivity, observational dependence and structural
   sourceSelection remain unproved Registration obligations. -/
end Reg.D5.S3.VertexAlgebra.ChargedResidue.FiniteChambers
