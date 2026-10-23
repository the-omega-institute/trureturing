import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
set_option autoImplicit false
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Finset
open scoped BigOperators ComplexOrder
namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star
noncomputable section
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

namespace star_polynomial
abbrev arena : Arena where
  signature := signature
  Law realization := ∀ (delta B C : ℝ), realization.readout () () ((6*delta^2+3*delta*B+C)^2-9*delta^2*(4*delta^2+2*delta*B+B^2-2*C)) (18*delta^3*B+30*delta^2*C+6*delta*B*C+C^2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 0
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_polynomial)) where
  actual := equalityActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_polynomial,rejected,rejected_law⟩
  sensitivity := sensitivity arena.Law equalityActual rejected_law
  dependence := equality_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_polynomial) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_polynomial.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_polynomial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x=y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]
end star_polynomial

namespace star_product_bound
abbrev arena : Arena where
  signature := signature
  Law realization := ∀ (delta B C P t : ℝ) (hd : 0 ≤ delta) (hB : 0 ≤ B) (hC : 0 ≤ C) (hP : 0 ≤ P) (ht : 0 ≤ t) (hPe : P=6*delta^2+3*delta*B+C) (hte : t^2=4*delta^2+2*delta*B+B^2-2*C), realization.readout () () (3*delta*t) (P)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_product_bound)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_product_bound,rejected,rejected_law⟩
  sensitivity := sensitivity arena.Law orderActual rejected_law
  dependence := order_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_product_bound) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_product_bound.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_product_bound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]
end star_product_bound

namespace star_gain
abbrev arena : Arena where
  signature := signature
  Law realization := ∀ (t R Q delta P : ℝ) (ht : 0 < t) (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hd : 0 ≤ delta) (hQP : Q ≤ delta*R) (hP : 3*delta*t ≤ P), realization.readout () () (Real.sqrt (t^2+Q)) (t+R*P/(6*t^2))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_gain)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_gain,rejected,rejected_law⟩
  sensitivity := sensitivity arena.Law orderActual rejected_law
  dependence := order_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_gain) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_gain.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.star_gain.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]
end star_gain

namespace capped_tail_squares
abbrev arena : Arena where
  signature := signature
  Law realization := ∀ (u : ℝ) (d : Fin 15 → ℝ) (hu : 0 ≤ u) (hd : ∀ i,0 ≤ d i) (hdu : ∀ i,d i ≤ u) (ho : Antitone d) (hm : ∑ i,d i ≤ 5*u), realization.readout () () (∑ i,(d i)^2) (u*(∑ i,if i.val < 5 then d i else 0))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 (fun _ => 0) (by norm_num) (by simp) (by simp) (by intro i j hij; rfl) (by simp)
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.capped_tail_squares)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.capped_tail_squares,rejected,rejected_law⟩
  sensitivity := sensitivity arena.Law orderActual rejected_law
  dependence := order_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.capped_tail_squares) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.capped_tail_squares.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.capped_tail_squares.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]
end capped_tail_squares

/-- Exact unpaid owner-registration type for this original theorem.
No evidence constructor is supplied and no registration status is asserted. -/
def family_mass_budget_registration_gap : Prop :=
  Nonempty (Contract.Registration.{_,_,_,0,0,0,0,0,0,1,0,0} (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.family_mass_budget) (Realization signature) Unit Unit)

/-- Exact unpaid owner-registration type for this original theorem.
No evidence constructor is supplied and no registration status is asserted. -/
def five_coefficient_mass_registration_gap : Prop :=
  Nonempty (Contract.Registration.{_,_,_,0,0,0,0,0,0,1,0,0} (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.five_coefficient_mass) (Realization signature) Unit Unit)

/-- Exact unpaid owner-registration type for this original theorem.
No evidence constructor is supplied and no registration status is asserted. -/
def same_vector_coupling_registration_gap : Prop :=
  Nonempty (Contract.Registration.{_,_,_,0,0,0,0,0,0,1,0,0} (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.same_vector_coupling) (Realization signature) Unit Unit)

/-- Exact unmet registration evidence for the new full-domain existence theorem.
The source theorem now has a construction, but this file supplies no faithful
existential/witness readout, intervention proof, or compiled binding receipt.
This obligation is not a premise of balancedStarExistence. -/
def balancedStarExistence_registration_gap : Prop :=
  Nonempty (Contract.Registration.{_,_,_,0,0,0,0,0,0,1,0,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.balancedStarExistence)
    (Realization signature) Unit Unit)

/-- The complete source theorem requires a realization bridge, enrolled readout, source reconstruction and variation/sensitivity evidence. -/
def family_star_charges_registration_gap : Prop :=
  Nonempty (Contract.Registration.{_,_,_,0,0,0,0,0,0,1,0,0} (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star.family_star_charges) (Realization signature) Unit Unit)

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star
