import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Probability.CdsoRareHubProfile

/-! Typed whole-family evidence for the actual rare-hub subset law. -/

open _root_.D5.S3.Combinatorics.Probability.CdsoRareHubProfile
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Probability.CdsoRareHubProfile

abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ a := Finset (Fin (a+2)) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a ε => rareLaw a ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := TheoremClaims (fun a ε => R.readout () a ε)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := (h.1 4 (by norm_num) (1/4) (by norm_num) (by norm_num)).total
  norm_num [rejected, realize] at hz

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      have hji' : j = i := by cases j; cases i; rfl
      exact (hji hji').elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    change ∃ (a : ℕ) (s t : ℝ), rareLaw a s ≠ rareLaw a t
    refine ⟨4, 1/4, 1/8, ?_⟩
    intro h
    have hv := congrFun h {extra 4}
    change rareLaw 4 (1/4) {extra 4} = rareLaw 4 (1/8) {extra 4} at hv
    have h1 := (result.1 4 (by norm_num) (1/4) (by norm_num) (by norm_num)).masses.1
    have h2 := (result.1 4 (by norm_num) (1/8) (by norm_num) (by norm_num)).masses.1
    rw [h1, h2] at hv
    norm_num at hv

/-- The exact bridge and family obligations are typed evidence. SourceSelection
is absent: the source assertion is an applied proposition definition, rather
than a supported nullary proposition entry. -/
def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Probability.CdsoRareHubProfile.result)
    (type_of% (realize signature (fun _ a ε => rareLaw a ε) (fun e => nomatch e)))
    (Type) (Unit) := {
  unitName := `D5.S3.Combinatorics.Probability.CdsoRareHubProfile.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Probability.CdsoRareHubProfile.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a ε => rareLaw a ε) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }] }

end Reg.D5.S3.Combinatorics.Probability.CdsoRareHubProfile
