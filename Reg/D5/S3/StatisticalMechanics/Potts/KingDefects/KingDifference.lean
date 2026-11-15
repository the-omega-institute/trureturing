import D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference

open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open KingGrid KingDifference
open scoped IsAddKleinFour

noncomputable section

namespace count_by_kind

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M),
    N_H N M + N_H M N + 2 * N_D N M = R.readout () () (T (N + 1) (M + 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1 1 (by norm_num) (by norm_num)
  have ha := count_by_kind 1 1 (by norm_num) (by norm_num)
  omega

def family : Registration arena (type_of% @count_by_kind) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@count_by_kind, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@count_by_kind) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference.count_by_kind.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference.count_by_kind.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 6 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "arg"]
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end count_by_kind

end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference
