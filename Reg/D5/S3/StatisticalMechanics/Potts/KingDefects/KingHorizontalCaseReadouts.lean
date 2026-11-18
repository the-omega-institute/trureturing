import D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-equivalent readout laws for king-graph defect counts. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts

open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open KingGrid KingDifference

noncomputable section

namespace interior_endpoint_value

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 2 ^ x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (2 ^ x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b d : ℕ) (hm : 0 < a + b) (hd : 0 < d),
    E (a+b) 0 d + 2^(a+b) + P a b 0 d + P a b d 0 + Q a b 0 d + Q a b d 0 + 2 =
      R.readout () () (a+b+1) + 2^(d+1) + 2^(a+1) + 2^(b+1)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := @h 1 1 1 (by norm_num) (by norm_num)
  have ha := @interior_endpoint_value 1 1 1 (by norm_num) (by norm_num)
  omega

def family : Registration arena (type_of% @interior_endpoint_value) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@interior_endpoint_value, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (2 ^ (0 : ℕ)) ≠ (2 ^ (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@interior_endpoint_value) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.interior_endpoint_value.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.interior_endpoint_value.family
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
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end interior_endpoint_value

namespace interior_middle_value

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 2 ^ x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (2 ^ x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d : ℕ) (hm : 0 < a + b)
    (hc : 0 < c) (hd : 0 < d),
    E (a+b) c d + 2^(a+b) + P a b c d + P a b d c + Q a b c d + Q a b d c =
      R.readout () () (a+b+1) + 2^c + 2^d + 2*((if a=0 then 1 else 0)+(if b=0 then 1 else 0))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := @h 1 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  have ha := @interior_middle_value 1 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  omega

def family : Registration arena (type_of% @interior_middle_value) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@interior_middle_value, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (2 ^ (0 : ℕ)) ≠ (2 ^ (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@interior_middle_value) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.interior_middle_value.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.interior_middle_value.family
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
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end interior_middle_value

namespace lower_pair_valid

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature NZPair
    (fun _ => Fin 6) (fun _ => K × K)

def actual : Realization signature :=
  realize signature (fun _ p x => lower_pair_values p x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : NZPair) (i : Fin 6),
    (R.readout () x i).1 ≠ 0 ∧ (lower_pair_values x i).2 ≠ 0 ∧
      (lower_pair_values x i).1 ≠ (lower_pair_values x i).2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ⟨((1, 0), (0, 1)), by decide +kernel⟩ 0
  exact hb.1 rfl

def family : Registration arena (type_of% @lower_pair_valid) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@lower_pair_valid, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨⟨((1, 0), (0, 1)), by decide +kernel⟩, 0, 1, ?_⟩
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@lower_pair_valid) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.lower_pair_valid.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.lower_pair_valid.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => lower_pair_values p x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg", "arg"]
                    stateBinder := 1
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end lower_pair_valid

namespace support_case_eval

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ)
    (fun _ => Fin 6) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ p x => six_case_value p.1 p.2.1 p.2.2.1 p.2.2.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p x => six_case_value p.1 p.2.1 p.2.2.1 p.2.2.2 x + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d : ℕ) (i : Fin 6),
    support_case_count a b c d i = R.readout () ⟨a, b, c, d⟩ i

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 1 1 1 0
  have ha := support_case_eval 1 1 1 1 0
  change _ = six_case_value 1 1 1 1 0 + 1 at hb
  omega

def family : Registration arena (type_of% @support_case_eval) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@support_case_eval, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨⟨1, 1, 1, 1⟩, 0, 1, ?_⟩
    change six_case_value 1 1 1 1 0 ≠ six_case_value 1 1 1 1 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@support_case_eval) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.support_case_eval.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.support_case_eval.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => six_case_value p.1 p.2.1 p.2.2.1 p.2.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end support_case_eval

namespace pair_support_cases

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ)
    (fun _ => Fin 6) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ p x => support_case_count p.1 p.2.1 p.2.2.1 p.2.2.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p x => support_case_count p.1 p.2.1 p.2.2.1 p.2.2.2 x + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d : ℕ) (x : NZPair) (i : Fin 6),
    pair_support_count a b c d x (lower_pair x i) = R.readout () ⟨a, b, c, d⟩ i

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 1 1 1 ⟨((1, 0), (0, 1)), by decide +kernel⟩ 0
  have ha := pair_support_cases 1 1 1 1 ⟨((1, 0), (0, 1)), by decide +kernel⟩ 0
  change _ = support_case_count 1 1 1 1 0 + 1 at hb
  omega

def family : Registration arena (type_of% @pair_support_cases) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pair_support_cases, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨⟨1, 1, 1, 1⟩, 0, 1, ?_⟩
    change support_case_count 1 1 1 1 0 ≠ support_case_count 1 1 1 1 1
    rw [support_case_eval, support_case_eval]
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@pair_support_cases) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.pair_support_cases.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.pair_support_cases.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => support_case_count p.1 p.2.1 p.2.2.1 p.2.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end pair_support_cases


namespace interior_count_support

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature
    (Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, NZPair)
    (fun _ => NZPair) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ p x => pair_support_count p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p x => pair_support_count p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 x + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d : ℕ),
    N_e (.H (cut_row (a + 1) (b + 1)) (pivot c d) :
      Edge ((a + 1) + (b + 1) + 1) (c + (d + 1) + 1)) =
      ∑ x : NZPair, ∑ y : NZPair, R.readout () ⟨a, b, c, d, x⟩ y

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 1 1 1
  have ha := interior_count_support 1 1 1 1
  dsimp only [rejected, realize] at hb
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one, ← Nat.card_eq_fintype_card, nz_pair_card] at hb
  omega

def family : Registration arena (type_of% @interior_count_support) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@interior_count_support, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    let x : NZPair := ⟨((1, 0), (0, 1)), by decide +kernel⟩
    refine ⟨⟨1, 1, 1, 1, x⟩, lower_pair x 0, lower_pair x 1, ?_⟩
    change pair_support_count 1 1 1 1 x (lower_pair x 0) ≠
      pair_support_count 1 1 1 1 x (lower_pair x 1)
    rw [pair_support_cases, pair_support_cases, support_case_eval, support_case_eval]
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@interior_count_support) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.interior_count_support.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.interior_count_support.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => pair_support_count p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{ path := #["body", "body", "body", "body", "arg", "arg", "body", "arg", "body"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end interior_count_support

end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
