import Reg.D5.S3.Quantum.Algebra.PauliFixedProductFamily
import D5.S3.Quantum.Algebra.PauliFixedProductLinear

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.PauliFixedProductFamily
open _root_.D5.S3.Quantum.Algebra.PauliLinearCertificate

noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.PauliFixedProductLinear
abbrev signature := Reg.D5.S3.Quantum.Algebra.PauliFixedProductFamily.signature

namespace Interval

def actual : Realization signature := realize signature
  (fun _ _ t => |t|) (fun a => nomatch a)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun a => nomatch a)
abbrev arena : Arena where
  signature := signature
  Law A := ∃ t : ℝ, 0<A.readout () () t ∧ A.readout () () t<smallEndpoint

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨t,ht,_⟩
  norm_num [rejected,realize] at ht

def family : Registration arena (type_of% (@small_interval_nonempty)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨small_interval_nonempty,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    norm_num [actual,realize]

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@small_interval_nonempty) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.PauliFixedProductFamily.small_interval_nonempty.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.PauliFixedProductLinear.Interval.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ t => |t|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.PauliFixedProductLinear
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg","body","fn","arg","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Interval

def actual : Realization signature := realize signature
  (fun _ _ t => epsilon t) (fun a => nomatch a)
def rejected : Realization signature := realize signature
  (fun _ _ _ => 1) (fun a => nomatch a)

private theorem dependence : ∀ i : Unit, ∃ (p : Unit) (x y : ℝ),
    actual.readout i p x≠actual.readout i p y := by
  intro i
  refine ⟨(),0,1,?_⟩
  change epsilon 0≠epsilon 1
  have hz : epsilon 0=0 := by simp [epsilon,full_report]
  have hp : 0<epsilon 1 := by
    unfold epsilon
    rw [full_report]
    positivity
  rw [hz]
  exact ne_of_lt hp

namespace Strict
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (t : ℝ) (_ht : 0 < |t|) (_hsmall : |t|<smallEndpoint),
    0<Real.sqrt 2-2*constant*(A.readout () () t) ∧
    (∃ a : J, D t a a≠0) ∧ D t (e 0)≠0 ∧
    (∀ a : J, ‖a‖=1 → ‖D t a a‖ ≤ linear ((A.readout () () t)) (localBound t)) ∧
    |t|/2 ≤ linear ((A.readout () () t)) (localBound t) ∧
    linear ((A.readout () () t)) (localBound t) < old ((A.readout () () t)) (localBound t)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨t,ht,hs⟩ := small_interval_nonempty
  have hh := (h t ht hs).1
  simp [rejected,realize,constant] at hh
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

def family : Registration arena (type_of% (@actual_strict_improvement)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_strict_improvement,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro a
      exact nomatch a
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@actual_strict_improvement) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.PauliFixedProductFamily.actual_strict_improvement.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.PauliFixedProductLinear.Strict.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ t => epsilon t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.PauliFixedProductLinear
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","fn","arg","arg","arg","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Strict

namespace Nonempty
abbrev arena : Arena where
  signature := signature
  Law A := ∃ t : ℝ,
    (type_of% (family_contract t)) ∧
    (type_of% (exact_defects t)) ∧
    (type_of% (exact_constants t)) ∧
    (type_of% (exact_action_data t)) ∧
    (type_of% (exact_label_data t)) ∧
    (type_of% (exact_support_gap t)) ∧
    0 < |t| ∧ |t|<smallEndpoint ∧
    (∃ a : J, D t a a≠0) ∧ D t (e 0)≠0 ∧
    |t|/2≤linear ((A.readout () () t)) (localBound t) ∧
    linear ((A.readout () () t)) (localBound t)<old ((A.readout () () t)) (localBound t)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨t,_,_,_,_,_,_,_,_,_,_,hdom,_⟩
  have hc : 0<constant := by unfold constant; positivity
  have hd : 0<localBound t := by unfold localBound; positivity
  have hden : Real.sqrt 2-2*constant*1<0 := by
    unfold constant
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hn : linear 1 (localBound t)<0 := by
    unfold linear
    exact div_neg_of_pos_of_neg (by positivity) hden
  have hh : |t|/2≤linear 1 (localBound t) := by
    simpa [rejected,realize] using hdom
  nlinarith [abs_nonneg t]

def family : Registration arena (type_of% (@nonempty_improvement)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nonempty_improvement,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro a
      exact nomatch a
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@nonempty_improvement) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Algebra.PauliFixedProductFamily.nonempty_improvement.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.PauliFixedProductLinear.Nonempty.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ t => epsilon t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.PauliFixedProductLinear
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg","body","arg","arg","arg","arg","arg","arg","arg","arg","arg","arg","fn","arg","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Nonempty
end Reg.D5.S3.Quantum.Algebra.PauliFixedProductLinear
