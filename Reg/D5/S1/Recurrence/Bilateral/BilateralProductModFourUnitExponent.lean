import D5.S1.Recurrence.Bilateral.BilateralProductModFourUnitExponent
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Coefficient observations for the normalized bilateral product equation. -/

open PowerSeries
open _root_.D5.S1.Recurrence.Bilateral.BilateralProductModFourUnitExponent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.Bilateral.BilateralProductModFourUnitExponent
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := PowerSeries ℤ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ _ state => coeff state.2 state.1) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    (∃ A, HannaA380066.IsGF A) ∧
      ∀ A, HannaA380066.IsGF A → ∀ n : ℕ, 0 < n →
        r.readout () () (A, n) % 4 = 2

private theorem actual_law : arena.Law actual := result

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, hA⟩ := h.1
  have hc := h.2 A hA 1 (by decide)
  norm_num [rejected, realize] at hc

def evidence : Registration arena HannaA380066.claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), ((1 : PowerSeries ℤ), 0), ((1 : PowerSeries ℤ), 1), ?_⟩
    simp [actual, realize]

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Recurrence.Bilateral.BilateralProductModFourUnitExponent.result)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.Bilateral.BilateralProductModFourUnitExponent.informationUnit
  realizationName := `Reg.D5.S1.Recurrence.Bilateral.BilateralProductModFourUnitExponent.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ state => coeff state.2 state.1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S1.Recurrence.Bilateral.BilateralProductModFourUnitExponent
