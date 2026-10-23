import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
set_option autoImplicit false
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Finset
open scoped BigOperators ComplexOrder
namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
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

namespace pointwise_energy_cap
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r H D a q s : ℝ} (h : Hyp r H D a q s), R.readout () () (W r H D a q) (B0 r)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Hyp 0 0 0 0 0 5 := by constructor <;> norm_num
  exact h hz
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.pointwise_energy_cap)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.pointwise_energy_cap,rejected,rejected_law⟩
  sensitivity := sensitivity arena.Law orderActual rejected_law
  dependence := order_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.pointwise_energy_cap) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.pointwise_energy_cap.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.pointwise_energy_cap.family
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
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
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
end pointwise_energy_cap

namespace quadratic_upper
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A b c lo hi x K : ℝ) (hA : 0 ≤ A) (hx : lo ≤ x) (hx' : x ≤ hi) (hlo : A*lo^2+b*lo+c ≤ K) (hhi : A*hi^2+b*hi+c ≤ K), R.readout () () (A*x^2+b*x+c) (K)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 0 0 0 0 0 (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.quadratic_upper)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.quadratic_upper,rejected,rejected_law⟩
  sensitivity := sensitivity arena.Law orderActual rejected_law
  dependence := order_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.quadratic_upper) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.quadratic_upper.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.quadratic_upper.family
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
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
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
end quadratic_upper

namespace quadratic_lower
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A b c lo hi x K : ℝ) (hA : A ≤ 0) (hx : lo ≤ x) (hx' : x ≤ hi) (hlo : K ≤ A*lo^2+b*lo+c) (hhi : K ≤ A*hi^2+b*hi+c), R.readout () () (K) (A*x^2+b*x+c)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 0 0 0 0 0 (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.quadratic_lower)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.quadratic_lower,rejected,rejected_law⟩
  sensitivity := sensitivity arena.Law orderActual rejected_law
  dependence := order_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.quadratic_lower) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.quadratic_lower.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.quadratic_lower.family
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
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
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
end quadratic_lower

namespace concentrated_ge100
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N j r H D a q s : ℝ) (hN : 100 ≤ N) (h : Hyp r H D a q s), R.readout () () (energy N j r H D a q + (N-100)*(1+3*r)*(5-10*r)/125) ((25/(24*N))*(mass N j r H D)^2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : Hyp 0 0 0 0 0 5 := by constructor <;> norm_num
  exact h 100 10 0 0 0 0 0 5 (by norm_num) hz
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.concentrated_ge100)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.concentrated_ge100,rejected,rejected_law⟩
  sensitivity := sensitivity arena.Law orderActual rejected_law
  dependence := order_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.concentrated_ge100) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.concentrated_ge100.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.concentrated_ge100.family
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
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]
end concentrated_ge100

namespace common_loss_nonnegative
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N r : ℝ) (hN : 100 ≤ N) (hr : 0 ≤ r) (hr' : r ≤ 1/2), R.readout () () (0) ((N-100)*(1+3*r)*(5-10*r)/125)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 100 0 (by norm_num) (by norm_num) (by norm_num)
def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.common_loss_nonnegative)) where
  actual := orderActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.common_loss_nonnegative,rejected,rejected_law⟩
  sensitivity := sensitivity arena.Law orderActual rejected_law
  dependence := order_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.common_loss_nonnegative) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.common_loss_nonnegative.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.common_loss_nonnegative.family
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
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]
end common_loss_nonnegative

/-- Exact unpaid owner-registration type for this original theorem.
No evidence constructor is supplied and no registration status is asserted. -/
def energy_envelopes_registration_gap : Prop :=
  Nonempty (Contract.Registration.{_,_,_,0,0,0,0,0,0,1,0,0} (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.energy_envelopes) (Realization signature) Unit Unit)

/-- Exact unpaid owner-registration type for this original theorem.
No evidence constructor is supplied and no registration status is asserted. -/
def homogeneous_energy_cap_registration_gap : Prop :=
  Nonempty (Contract.Registration.{_,_,_,0,0,0,0,0,0,1,0,0} (@_root_.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar.homogeneous_energy_cap) (Realization signature) Unit Unit)

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
