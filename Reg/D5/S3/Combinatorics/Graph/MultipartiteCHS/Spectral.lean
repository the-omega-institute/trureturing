import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.MultipartiteCHS.Spectral
import Reg.Support.DependentFamily

/-! Source-family registration for the spectral recurrence identity. -/

namespace Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Spectral
open _root_.D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs
open _root_.D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence
open _root_.D5.S3.Combinatorics.Graph.MultipartiteCHS.Spectral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := Σ r : ℕ, Fin r → ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p d => recH p.2 d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℕ} (a : Fin r → ℕ) (d : ℕ), chs a d = R.readout () ⟨r, a⟩ d

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have he := h (r := 0) Fin.elim0 0
  norm_num [rejected, realize, chs, MvPolynomial.hsymm_zero] at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, Fin.elim0⟩, 0, 1, ?_⟩
  change recH (r := 0) Fin.elim0 0 ≠ recH (r := 0) Fin.elim0 1
  rw [recH_zero, recH_eq _ (show 1 ≤ (1 : ℕ) from le_rfl)]
  norm_num

def source : Registration arena (type_of% @chs_eq_recH) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chs_eq_recH, rejected, rejected_not_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_not_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chs_eq_recH) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Spectral.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Spectral.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p d => recH p.2 d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.MultipartiteCHS.Spectral
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.MultipartiteCHS.Spectral
