import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnEnergy
import Reg.Support.SingleDependentReadout

/-! Observe the integer energy as the coefficient triple varies. -/

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnEnergy

open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private abbrev Parameters := Σ n : ℕ, Σ _ : Finset (Fin n), Fin n → Fin 3 → ℤ

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters (fun _ => Fin 3 → ℤ) (fun _ => ℤ)

private abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} (rows : Finset (Fin n)) (B : Fin n → Fin 3 → ℤ)
    (_hdiag : ∀ j, (∑ x ∈ rows, B x j ^ 2) = 4)
    (_hoff : ∀ i j : Fin 3, i < j → |∑ x ∈ rows, B x i * B x j| ≤ 1)
    (a : Fin 3 → ℤ) (_ha : a ≠ 0),
    let energy := r.readout () ⟨n, rows, B⟩ a
    4 ≤ energy ∧
      (energy = 4 ↔ ∃ i, (a i = 1 ∨ a i = -1) ∧ ∀ j, j ≠ i → a j = 0) ∧
      ((∃ i j, i ≠ j ∧ a i ≠ 0 ∧ a j ≠ 0) → 6 ≤ energy)

private def actual : Realization signature :=
  realize signature (fun _ p a => columnEnergy p.2.1 p.2.2 a) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private def sampleColumns (r : Fin 12) (j : Fin 3) : ℤ :=
  if r.val / 4 = j.val then 1 else 0

private def sampleAxis (x : ℤ) (j : Fin 3) : ℤ := if j = 0 then x else 0

private theorem sample_diag (j : Fin 3) : (∑ x : Fin 12, sampleColumns x j ^ 2) = 4 := by
  decide +revert

private theorem sample_off (i j : Fin 3) :
    i < j → |∑ x : Fin 12, sampleColumns x i * sampleColumns x j| ≤ 1 := by
  decide +revert

private theorem sample_nonzero : sampleAxis 1 ≠ 0 := by
  intro h
  have hz := congrFun h 0
  simp [sampleAxis] at hz

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law Finset.univ sampleColumns sample_diag sample_off (sampleAxis 1) sample_nonzero).1
  exact (by decide : ¬ (4 : ℤ) ≤ 0) h

def source_registration : Registration arena (type_of% @three_column_energy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@three_column_energy, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    refine ⟨⟨12, Finset.univ, sampleColumns⟩, sampleAxis 1, sampleAxis 2, ?_⟩
    change columnEnergy Finset.univ sampleColumns (sampleAxis 1) ≠
      columnEnergy Finset.univ sampleColumns (sampleAxis 2)
    decide

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@three_column_energy) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnEnergy.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnEnergy.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => columnEnergy p.2.1 p.2.2 a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnEnergy
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnEnergy
