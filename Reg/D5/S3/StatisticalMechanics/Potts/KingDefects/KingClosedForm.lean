import D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-equivalent readout laws for king-graph defect counts. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm

open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open KingGrid KingDifference

noncomputable section

namespace closed_form

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ x => (x : ℤ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => ((x : ℤ)) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ) (hn : 4 ≤ n) (hk : 4 ≤ k),
    4 * (R.readout () () (T n k)) =
      ((n : ℤ)*k-n+6*k+12)*2^n + ((n : ℤ)*k-k+6*n+12)*2^k +
        16*(n : ℤ)*k-64*n-64*k-32

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 4 4 (by norm_num) (by norm_num)
  have ha := closed_form 4 4 (by norm_num) (by norm_num)
  linarith only [hb, ha]

def family : Registration arena (type_of% @closed_form) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@closed_form, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (((0 : ℕ) : ℤ)) ≠ (((1 : ℕ) : ℤ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@closed_form) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm.closed_form.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm.closed_form.family
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
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end closed_form

namespace width_two

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ x => (x : ℤ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => ((x : ℤ)) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 2 ≤ n),
    (R.readout () () (T n 2)) = (7*(n : ℤ)-8)*2^(n-2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 4 (by norm_num)
  have ha := width_two 4 (by norm_num)
  linarith only [hb, ha]

def family : Registration arena (type_of% @width_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@width_two, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (((0 : ℕ) : ℤ)) ≠ (((1 : ℕ) : ℤ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@width_two) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm.width_two.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm.width_two.family
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
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm
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

end width_two

namespace width_three

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ x => (x : ℤ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => ((x : ℤ)) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 2 ≤ n),
    4*(R.readout () () (T n 3)) = (3*(n : ℤ)+27)*2^n+44*n-116

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 4 (by norm_num)
  have ha := width_three 4 (by norm_num)
  linarith only [hb, ha]

def family : Registration arena (type_of% @width_three) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@width_three, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (((0 : ℕ) : ℤ)) ≠ (((1 : ℕ) : ℤ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@width_three) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm.width_three.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm.width_three.family
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
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "fn", "arg", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end width_three

namespace diagonal_closed

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ x => (x : ℤ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => ((x : ℤ)) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 3 ≤ n),
    2*(R.readout () () (T n n)) = ((n : ℤ)^2+5*n+12)*2^n+8*(n : ℤ)^2-64*n-16

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 4 (by norm_num)
  have ha := diagonal_closed 4 (by norm_num)
  linarith only [hb, ha]

def family : Registration arena (type_of% @diagonal_closed) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagonal_closed, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (((0 : ℕ) : ℤ)) ≠ (((1 : ℕ) : ℤ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@diagonal_closed) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm.diagonal_closed.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm.diagonal_closed.family
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
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "fn", "arg", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end diagonal_closed

end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingClosedForm
