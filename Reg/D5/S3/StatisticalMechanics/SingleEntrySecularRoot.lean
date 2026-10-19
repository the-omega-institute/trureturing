import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import D5.S3.StatisticalMechanics.SingleEntrySecularRoot
import Reg.Support.DependentFamily

/-! # Source-bound audit of the finite secular equation -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u_1

namespace Reg.D5.S3.StatisticalMechanics.SingleEntrySecularRoot
open _root_.D5.S3.StatisticalMechanics.SingleEntrySecularRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- The original site type and two actual rate functions. Dictionaries and
positivity premises remain in the full law without becoming coordinates. -/
abbrev Parameters := Σ Sites : Type u_1, Σ _ : Sites → ℝ, Sites → ℝ

abbrev signature : Signature where
  Params := Parameters.{u_1}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u_1}).State p → (signature.{u_1}).Output role p :=
  fun _ p x => siteRate p.2.1 p.2.2 x

def actualAnchor : ∀ (_ : (signature.{u_1}).Anchor) p, (signature.{u_1}).State p :=
  fun e => nomatch e

def actual : Realization signature.{u_1} :=
  realize signature actualReadout actualAnchor

def rejected : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The selected observation is the actual free-site rate in the upper bound.
The secular function and every original dictionary and premise stay in scope. -/
abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {ι : Type u_1} [fi : Fintype ι] [de : DecidableEq ι] [ne : Nonempty ι]
    (a b : ι → ℝ) (η θ : ℝ),
    (∀ i, 0 < a i) → (∀ i, 0 < b i) → 0 < η → 0 < θ →
    (∃! x : ℝ, 0 < x ∧ (∀ i, x < R.readout () ⟨ι, a, b⟩ i) ∧
      secular a b η θ x = 0) ∧
    ∀ x : ℝ, 0 ≤ x → (∀ i, x < siteRate a b i) →
      HasDerivAt (secular a b η θ) (secularSlope a b η x) x ∧
      secularSlope a b η x < 0

private theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  obtain ⟨x, hx, _⟩ := (h (ι := ULift.{u_1} Unit) (fun _ => 1) (fun _ => 1) 1 1
    (by intro i; norm_num) (by intro i; norm_num) (by norm_num) (by norm_num)).1
  have hh := hx.2.1 (ULift.up ())
  norm_num [rejected, realize] at hh
  linarith [hx.1]

private theorem dependence : ObservationalDependence signature.{u_1} actual := by
  intro role
  let a : ULift.{u_1} (Fin 2) → ℝ := fun i => if i.down = 0 then 1 else 2
  refine ⟨⟨ULift.{u_1} (Fin 2), a, fun _ => 1⟩, ULift.up 0, ULift.up 1, ?_⟩
  norm_num [actual, actualReadout, realize, siteRate, a]

def family : Registration arena.{u_1} (arena.Law actual) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨@secular_unique_root.{u_1}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntrySecularRoot
  definition := none
  coordinates := #[0, 4, 5]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body",
      "body", "body", "body", "body", "body", "body",
      "fn", "arg", "arg", "body", "arg", "fn", "arg", "body", "arg"]
    stateBinder := 13
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@secular_unique_root.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySecularRoot.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySecularRoot.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- The complete original telescope is reconstructed definitionally. -/
def analysisSource : Analysis.Source (@secular_unique_root.{u_1}) :=
  Analysis.Source.ofRegistration _ family .exact selection

/-- The scalar equation supplies no trajectory law or five-mode pushforward. -/
def analysis : AuricFib.Contract.Application (@secular_unique_root.{u_1}) where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable
      "Real scalar equation: finite presentation and generator-to-five-mode law bridge unacquired" }

#print axioms family
#print axioms registration
#print axioms analysisSource
#print axioms analysis

namespace Weight
abbrev Parameters := Σ I : Type u_1, Σ _ : Fintype I, Σ _ : DecidableEq I, (I → ℝ) × (I → ℝ)
abbrev signature : Signature where
  Params := Parameters.{u_1}
  State p := Finset p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u_1}).State p → (signature.{u_1}).Output role p :=
  fun _ p S => @modeWeight p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 S

def actualAnchor : ∀ (_ : (signature.{u_1}).Anchor) p, (signature.{u_1}).State p :=
  fun e => nomatch e

def actual : Realization signature.{u_1} := realize signature actualReadout actualAnchor
def rejected : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {I : Type u_1} [fi : Fintype I] [de : DecidableEq I]
    (a b : I → ℝ), (∀ i, 0 < a i) → (∀ i, 0 < b i) →
    ∀ S : Finset I, 0 < R.readout () ⟨I, fi, de, a, b⟩ S

private theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  have hh := h (I := ULift.{u_1} Unit) (fun _ => 1) (fun _ => 2)
    (by intro i; norm_num) (by intro i; norm_num) ∅
  simpa [rejected, realize] using hh

private theorem dependence : ObservationalDependence signature.{u_1} actual := by
  intro role
  refine ⟨⟨ULift.{u_1} Unit, inferInstance, inferInstance, fun _ => 1, fun _ => 2⟩,
    ∅, {ULift.up ()}, ?_⟩
  have hd : (default : ULift.{u_1} Unit) = ULift.up () := Subsingleton.elim _ _
  norm_num [actual, actualReadout, realize, modeWeight, occupancy, siteRate,
    Fintype.prod_unique, hd]
  simp only [Finset.notMem_empty, Finset.mem_singleton_self, ite_false, ite_true]
  norm_num

def family : Registration arena.{u_1} (arena.Law actual) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨@weight_pos.{u_1}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntrySecularRoot
  definition := none
  coordinates := #[0, 1, 2, 3, 4]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
    stateBinder := 7
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

run_cmd do
  let mut e := (← Lean.getConstInfo ``weight_pos).type
  let mut binders := 0
  for step in #["body", "body", "body", "body", "body", "body", "body", "body", "arg"] do
    e ← match e, step with
      | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
        binders := binders + 1
        pure b
      | .app _ a, "arg" => pure a
      | _, _ => throwError "The original positive weight occurrence is absent"
  unless e.isAppOfArity ``modeWeight 6 && binders == 8 && e.getAppArgs[5]! == .bvar 0 do
    throwError "The weight source occurrence is not bound to its original subset"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weight_pos.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySecularRoot.Weight.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySecularRoot.Weight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms registration
end Weight

end Reg.D5.S3.StatisticalMechanics.SingleEntrySecularRoot
