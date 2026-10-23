import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Lift
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
set_option autoImplicit false
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Lift
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Finset
open scoped BigOperators ComplexOrder
namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Lift
noncomputable section
universe u v
/- SOURCE ATTEMPT ONLY. No current binding evidence or declared_validated
claim. Original telescopes and comparisons below are retained exactly.
Raw sourceSelection paths are manual candidate paths, pending authoritative
source reconstruction and template-binding validation. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def orderActual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def equalityActual : Realization signature :=
  realize signature (fun _ _ x y => x=y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem order_dependence : ObservationalDependence signature orderActual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro he
  have hz : (0:ℝ) ≤ 0 := le_rfl
  have hf : (1:ℝ) ≤ 0 := Eq.mp (congrFun he 0) hz
  norm_num at hf
private theorem equality_dependence : ObservationalDependence signature equalityActual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro he
  have hf : (1:ℝ)=0 := Eq.mp (congrFun he 0) rfl
  norm_num at hf
private theorem sensitivity (law : Realization signature → Prop)
    (actual : Realization signature) (hbad : ¬ law rejected) :
    Sensitivity ⟨signature,law⟩ actual := by
  constructor
  · intro i
    refine ⟨rejected,?_,?_,hbad⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

/-- Exact unpaid owner-registration type for this original theorem.
No evidence constructor is supplied and no registration status is asserted. -/
def concentrated_nonnegative_registration_gap : Prop :=
  Nonempty (Contract.Registration.{_,_,_,0,0,0,0,0,0,1,0,0} (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Lift.concentrated_nonnegative) (Realization signature) Unit Unit)

/-- Exact unpaid owner-registration type for this original theorem.
No evidence constructor is supplied and no registration status is asserted. -/
def middle_mass_actual_registration_gap : Prop :=
  Nonempty (Contract.Registration.{_,_,_,0,0,0,0,0,0,1,0,0} (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Lift.middle_mass_actual) (Realization signature) Unit Unit)

/-- Exact unpaid owner-registration type for this original theorem.
No evidence constructor is supplied and no registration status is asserted. -/
def concentrated_boundary_registration_gap : Prop :=
  Nonempty (Contract.Registration.{_,_,_,0,0,0,0,0,0,1,0,0} (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Lift.concentrated_boundary) (Realization signature) Unit Unit)

/-- Exact unpaid owner-registration type for this original theorem.
No evidence constructor is supplied and no registration status is asserted. -/
def concentration_transfer_registration_gap : Prop :=
  Nonempty (Contract.Registration.{_,_,_,0,0,0,0,0,0,1,0,0} (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Lift.concentration_transfer) (Realization signature) Unit Unit)

/-- Exact unpaid owner-registration type for this original theorem.
No evidence constructor is supplied and no registration status is asserted. -/
def augmented_norm_lift_registration_gap : Prop :=
  Nonempty (Contract.Registration.{_,_,_,0,0,0,0,0,0,1,0,0} (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Lift.augmented_norm_lift.{u,v}) (Realization signature) Unit Unit)

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Lift
