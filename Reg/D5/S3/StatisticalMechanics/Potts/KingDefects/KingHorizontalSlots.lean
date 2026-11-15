import D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots

open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open KingGrid KingDifference
open scoped IsAddKleinFour

noncomputable section

namespace word_support_card

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => Type) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Nat.card x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (Nat.card x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (S : Finset Bool),
    R.readout () () ({u : Fin n → Bool // word_support u) = S} = support_weight n S

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1 (by norm_num)
  have ha := word_support_card 1 (by norm_num)
  omega

def family : Registration arena (type_of% @word_support_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@word_support_card, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), PEmpty, PUnit, ?_⟩
    change Nat.card PEmpty ≠ Nat.card PUnit
    simp [Nat.card_eq_fintype_card]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 1, 0, 0, 0, 0}
    (@word_support_card) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots.word_support_card.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots.word_support_card.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Nat.card x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "fn", "arg"]
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end word_support_card

end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots
