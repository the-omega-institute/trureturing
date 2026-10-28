import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.RegularCHS.CycleBound
import Reg.Support.DependentFamily

/-! Audit of the cycle coefficient comparison. -/

noncomputable section

namespace Reg.D5.S3.Combinatorics.Graph.RegularCHS.CycleBound
open _root_.D5.S3.Combinatorics.Graph.RegularCHS.Defs
open _root_.D5.S3.Combinatorics.Graph.RegularCHS.Interface
open _root_.D5.S3.Combinatorics.Graph.RegularCHS.CycleBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Classical

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n m => bseq n 4 m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 3 ≤ n → ∀ m : ℕ, chs (SimpleGraph.cycleGraph n) (2 * m) ≤ R.readout () n m

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 3 (by omega) 0
  norm_num [rejected, realize, chs, MvPolynomial.hsymm_zero] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, 0, 1, ?_⟩
  change bseq 3 4 0 ≠ bseq 3 4 1
  norm_num [bseq]

def source : Registration arena (type_of% @chs_cycle_le_bseq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨chs_cycle_le_bseq, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chs_cycle_le_bseq) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.CycleBound.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.CycleBound.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n m => bseq n 4 m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.RegularCHS.CycleBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Reg.D5.S3.Combinatorics.Graph.RegularCHS.CycleBound
