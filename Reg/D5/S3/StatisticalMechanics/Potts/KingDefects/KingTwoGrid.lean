import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace labelled_eq_twentyFour

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 24 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (24 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) (hne : n ≠ 2 ∨ k ≠ 2),
    L n k = R.readout () () (T n k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 4 4 (by norm_num) (by norm_num) (by omega)
  have ha := labelled_eq_twentyFour 4 4 (by norm_num) (by norm_num) (by omega)
  omega

def family : Registration arena (type_of% @labelled_eq_twentyFour) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@labelled_eq_twentyFour, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (24 * (0 : ℕ)) ≠ (24 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@labelled_eq_twentyFour) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid.labelled_eq_twentyFour.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid.labelled_eq_twentyFour.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 24 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end labelled_eq_twentyFour
end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid
