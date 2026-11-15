import D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary

open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open KingGrid KingDifference
open scoped IsAddKleinFour

noncomputable section

namespace boundary_words_zero_card

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 2 ^ x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (2 ^ x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c d : ℕ),
    Nat.card (BoundaryWords 0 c d) = R.readout () () ((c + d))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1 1
  have ha := boundary_words_zero_card 1 1
  omega

def family : Registration arena (type_of% @boundary_words_zero_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@boundary_words_zero_card, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (2 ^ (0 : ℕ)) ≠ (2 ^ (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@boundary_words_zero_card) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary.boundary_words_zero_card.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary.boundary_words_zero_card.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 2 ^ x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg"]
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end boundary_words_zero_card

namespace nz_pair_card

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => Type) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Nat.card x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (Nat.card x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (NZPair) = 6

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h
  have ha := nz_pair_card
  omega

def family : Registration arena (type_of% @nz_pair_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nz_pair_card, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), PEmpty, PUnit, ?_⟩
    change Nat.card PEmpty ≠ Nat.card PUnit
    simp [Nat.card_eq_fintype_card]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 1, 0, 0, 0, 0}
    (@nz_pair_card) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary.nz_pair_card.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary.nz_pair_card.family
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
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary
    coordinates := #[]
    readouts := #[{ path := #["fn", "arg"]
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end nz_pair_card

namespace boundary_count_zero

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c d : ℕ),
    N_e (.H 0 (pivot c d) : Edge 2 (c + (d + 1) + 1)) = R.readout () () (2 ^ (c + d))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1 1
  have ha := boundary_count_zero 1 1
  omega

def family : Registration arena (type_of% @boundary_count_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@boundary_count_zero, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@boundary_count_zero) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary.boundary_count_zero.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary.boundary_count_zero.family
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
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg"]
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end boundary_count_zero

namespace boundary_count_pos

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m c d : ℕ) (hm : 0 < m),
    N_e (.H 0 (pivot c d) : Edge (m + 1 + 1) (c + (d + 1) + 1)) + 12 = R.readout () () ((2 ^ m + 2 ^ c + 2 ^ d))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1 1 1 (by norm_num)
  have ha := boundary_count_pos 1 1 1 (by norm_num)
  omega

def family : Registration arena (type_of% @boundary_count_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@boundary_count_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@boundary_count_pos) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary.boundary_count_pos.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary.boundary_count_pos.family
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
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "arg"]
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end boundary_count_pos

namespace boundary_count

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m c d : ℕ),
    N_e (.H 0 (pivot c d) : Edge (m + 1 + 1) (c + (d + 1) + 1)) = R.readout () () (E m c d)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1 1 1
  have ha := boundary_count 1 1 1
  omega

def family : Registration arena (type_of% @boundary_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@boundary_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@boundary_count) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary.boundary_count.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary.boundary_count.family
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
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "arg"]
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end boundary_count

end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalBoundary
