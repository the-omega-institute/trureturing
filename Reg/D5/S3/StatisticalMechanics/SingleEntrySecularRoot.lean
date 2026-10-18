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

/-- The complete parameter family of the original secular equation. -/
structure Parameters where
  Sites : Type u
  finiteSites : Fintype Sites
  decidableSites : DecidableEq Sites
  nonemptySites : Nonempty Sites
  a : Sites → ℝ
  b : Sites → ℝ
  eta : ℝ
  theta : ℝ

abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x =>
    @secular p.Sites p.finiteSites p.decidableSites p.a p.b p.eta p.theta x)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [fi : Fintype ι] [de : DecidableEq ι] [ne : Nonempty ι]
    (a b : ι → ℝ) (η θ : ℝ),
    (∀ i, 0 < a i) → (∀ i, 0 < b i) → 0 < η → 0 < θ →
    ∃! x : ℝ, 0 < x ∧ (∀ i, x < siteRate a b i) ∧
      R.readout () ⟨ι, fi, de, ne, a, b, η, θ⟩ x = 0

private def unitParameters : Parameters.{u} where
  Sites := ULift.{u} Unit
  finiteSites := inferInstance
  decidableSites := inferInstance
  nonemptySites := inferInstance
  a _ := 1
  b _ := 1
  eta := 1
  theta := 1

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨x, hx, _⟩ := h (ι := ULift.{u} Unit) (fun _ => 1) (fun _ => 1) 1 1
    (by intro i; norm_num) (by intro i; norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hx

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  obtain ⟨x, hx, _⟩ := secular_unique_root (ι := ULift.{u} Unit)
    (fun _ => 1) (fun _ => 1) 1 1
    (by intro i; norm_num) (by intro i; norm_num) (by norm_num) (by norm_num)
  refine ⟨unitParameters, 0, x, ?_⟩
  change secular (fun _ : ULift.{u} Unit => 1) (fun _ => 1) 1 1 0 ≠
    secular (fun _ : ULift.{u} Unit => 1) (fun _ => 1) 1 1 x
  rw [hx.2.2]
  have hw : 0 < modeWeight (fun _ : ULift.{u} Unit => 1) (fun _ => 1) ∅ := by
    unfold modeWeight
    apply Finset.prod_pos
    intro i _
    norm_num [occupancy, siteRate]
  simp only [secular, one_mul, sub_zero, mul_zero, zero_mul]
  linarith

def family : Registration arena.{u} (arena.Law actual) where
  actual := actual
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
  coordinates := #[0, 1, 2, 3, 4, 5, 6, 7]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body",
      "body", "body", "body", "body", "body", "body",
      "arg", "body", "arg", "arg", "fn", "arg"]
    stateBinder := 12
    functionOperand := false
    stateOperand := some #["arg"]
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
  readout := some (realize signature (fun _ p x =>
    @secular p.Sites p.finiteSites p.decidableSites p.a p.b p.eta p.theta x)
    (fun e => nomatch e))
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
