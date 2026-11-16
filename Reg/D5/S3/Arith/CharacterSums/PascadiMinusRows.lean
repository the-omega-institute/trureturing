import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.CharacterSums.PascadiMinusRows
import Reg.Support.DependentFamily

/-! Source-bound registration attempt for the literal original count reduction. -/

open _root_.D5.S3.Arith.CharacterSums
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.CharacterSums.PascadiMinusRows
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ Y n => 3*n + 8*(2*Y+1)^2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {p X Y : ℕ} (_hp : p.Prime) (_hXY : X ≤ Y) (_hY : 6*Y < p^2)
    (a₁ a₂ : ZMod (p^3)) (_h₁ : IsUnit a₁) (_h₂ : IsUnit a₂),
    Nminus p X Y a₁ a₂ ≤ r.readout () Y (Uminus p X Y a₁ a₂)

private theorem zero_box : Nminus 2 0 0 1 1 = 1 := by decide
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (p := 2) (X := 0) (Y := 0) (by decide) le_rfl (by decide)
    1 1 isUnit_one isUnit_one
  change Nminus 2 0 0 1 1 ≤ 0 at hh
  rw [zero_box] at hh
  omega

def family : Registration arena (type_of% @Nminus_le_three_Uminus) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Nminus_le_three_Uminus, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨0,0,1,by decide⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@Nminus_le_three_Uminus) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.CharacterSums.PascadiMinusRows.unit
  realizationName := `Reg.D5.S3.Arith.CharacterSums.PascadiMinusRows.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ Y n => 3*n + 8*(2*Y+1)^2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.CharacterSums.PascadiMinusRows
