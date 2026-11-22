import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnParity
import Reg.Support.SingleDependentReadout
import Mathlib.Data.Fintype.Powerset

/-! Observe the binary support weight as the selected column indices vary. -/

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnParity

open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnParity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped symmDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private abbrev Parameters :=
  Σ n : ℕ, Σ _ : Finset (Finset (Fin n)), Fin 3 ↪ Finset (Fin n)

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters (fun _ => Finset (Fin 3)) (fun _ => ℕ)

private abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} (rows : Finset (Finset (Fin n)))
    (center : Fin 3 ↪ Finset (Fin n))
    (_hsize : ∀ j, (rows.filter fun x => (center j ∆ x).card = 1).card = 4)
    (selected : Finset (Fin 3)) (_hselected : selected.Nonempty),
    r.readout () ⟨n, rows, center⟩ selected ∈ ({4, 6, 8, 10, 12} : Finset ℕ)

private def actual : Realization signature :=
  realize signature (fun _ p selected => cubeColumnParityWeight p.2.1 p.2.2 selected)
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private def sampleCenter : Fin 3 ↪ Finset (Fin 4) where
  toFun j := if j = 0 then ∅ else if j = 1 then Finset.univ else {0}
  inj' := by decide

private abbrev sampleRows : Finset (Finset (Fin 4)) := Finset.univ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have hsize : ∀ j, (sampleRows.filter fun x => (sampleCenter j ∆ x).card = 1).card = 4 := by
    decide
  have h := law sampleRows sampleCenter hsize {0} (Finset.singleton_nonempty _)
  change (0 : ℕ) ∈ ({4, 6, 8, 10, 12} : Finset ℕ) at h
  exact (by decide : (0 : ℕ) ∉ ({4, 6, 8, 10, 12} : Finset ℕ)) h

def source_registration : Registration arena (type_of% @cube_column_parity_weight) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cube_column_parity_weight, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    refine ⟨⟨4, sampleRows, sampleCenter⟩, {0}, {0, 1}, ?_⟩
    change cubeColumnParityWeight sampleRows sampleCenter {0} ≠
      cubeColumnParityWeight sampleRows sampleCenter {0, 1}
    decide

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cube_column_parity_weight) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnParity.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnParity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p selected => cubeColumnParityWeight p.2.1 p.2.2 selected) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnParity
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnParity
