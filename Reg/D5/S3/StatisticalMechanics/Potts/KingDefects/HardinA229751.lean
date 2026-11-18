import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229751
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-equivalent readout laws for king-graph defect counts. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229751

open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects

open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229751
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open KingTwoGrid

noncomputable section

namespace result

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ x => (x : ℤ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => ((x : ℤ)) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 12 ≤ n →
    R.readout () () (T n 4) =
      9 * T (n - 1) 4 - 33 * T (n - 2) 4 +
      63 * T (n - 3) 4 - 66 * T (n - 4) 4 +
      36 * T (n - 5) 4 - 8 * T (n - 6) 4

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 12 (by norm_num)
  have ha := result 12 (by norm_num)
  linarith only [hb, ha]

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (((0 : ℕ) : ℤ)) ≠ (((1 : ℕ) : ℤ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229751.result.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229751.result.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => (x : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229751
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "fn", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end result

end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.HardinA229751
