import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import D5.S3.StatisticalMechanics.SingleEntrySecularRoot
import Reg.Support.DependentFamily

/-! # Source-bound audit of the finite secular equation -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Reg.D5.S3.StatisticalMechanics.SingleEntrySecularRoot
open _root_.D5.S3.StatisticalMechanics.SingleEntrySecularRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- The original site type and two actual rate functions. Dictionaries and
positivity premises remain in the full law without becoming coordinates. -/
abbrev Parameters := Σ Sites : Type u, Σ _ : Sites → ℝ, Sites → ℝ

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u}).State p → (signature.{u}).Output role p :=
  fun _ p x => siteRate p.2.1 p.2.2 x

def actualAnchor : ∀ (_ : (signature.{u}).Anchor) p, (signature.{u}).State p :=
  fun e => nomatch e

def actual : Realization signature.{u} :=
  realize signature actualReadout actualAnchor

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The selected observation is the actual free-site rate in the upper bound.
The secular function and every original dictionary and premise stay in scope. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [fi : Fintype ι] [de : DecidableEq ι] [ne : Nonempty ι]
    (a b : ι → ℝ) (η θ : ℝ),
    (∀ i, 0 < a i) → (∀ i, 0 < b i) → 0 < η → 0 < θ →
    (∃! x : ℝ, 0 < x ∧ (∀ i, x < R.readout () ⟨ι, a, b⟩ i) ∧
      secular a b η θ x = 0) ∧
    ∀ x : ℝ, 0 ≤ x → (∀ i, x < siteRate a b i) →
      HasDerivAt (secular a b η θ) (secularSlope a b η x) x ∧
      secularSlope a b η x < 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨x, hx, _⟩ := (h (ι := ULift.{u} Unit) (fun _ => 1) (fun _ => 1) 1 1
    (by intro i; norm_num) (by intro i; norm_num) (by norm_num) (by norm_num)).1
  have hh := hx.2.1 (ULift.up ())
  norm_num [rejected, realize] at hh
  linarith [hx.1]

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let a : ULift.{u} (Fin 2) → ℝ := fun i => if i.down = 0 then 1 else 2
  refine ⟨⟨ULift.{u} (Fin 2), a, fun _ => 1⟩, ULift.up 0, ULift.up 1, ?_⟩
  norm_num [actual, actualReadout, realize, siteRate, a]

def family : Registration arena.{u} (arena.Law actual) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨@secular_unique_root.{u}, rejected, rejected_law⟩
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
    (@secular_unique_root.{u}) (Realization signature.{u}) Unit Unit where
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
def analysisSource : Analysis.Source (@secular_unique_root.{u}) :=
  Analysis.Source.ofRegistration _ family .exact selection

/-- The scalar equation supplies no trajectory law or five-mode pushforward. -/
def analysis : AuricFib.Contract.Application (@secular_unique_root.{u}) where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable
      "Real scalar equation: finite presentation and generator-to-five-mode law bridge unacquired" }

#print axioms family
#print axioms registration
#print axioms analysisSource
#print axioms analysis

end Reg.D5.S3.StatisticalMechanics.SingleEntrySecularRoot
