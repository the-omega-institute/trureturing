import D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-equivalent readout laws for king-graph defect counts. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots

open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open KingGrid KingDifference

noncomputable section




namespace word_support_empty

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature ℕ
    (fun n => Fin n → Bool) (fun _ => Finset Bool)

def actual : Realization signature :=
  realize signature (fun _ n u => word_support u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Finset.univ) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (u : Fin n → Bool),
    R.readout () n u = ∅ ↔ n = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (@h 0 (fun e => nomatch e)).mpr rfl
  have hmem : false ∈ (Finset.univ : Finset Bool) := Finset.mem_univ _
  rw [show (Finset.univ : Finset Bool) = ∅ from hb] at hmem
  exact Finset.notMem_empty false hmem

def family : Registration arena (type_of% @word_support_empty) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@word_support_empty, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨1, (fun _ => false), (fun _ => true), ?_⟩
    change word_support (fun _ : Fin 1 => false) ≠ word_support (fun _ : Fin 1 => true)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@word_support_empty) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots.word_support_empty.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots.word_support_empty.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n x => word_support x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg"]
                    stateBinder := 1
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end word_support_empty

namespace word_support_singleton

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature ℕ
    (fun n => Fin n → Bool) (fun _ => Finset Bool)

def actual : Realization signature :=
  realize signature (fun _ n u => word_support u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (hn : 0 < n) (u : Fin n → Bool) (b : Bool),
    R.readout () n u = {b} ↔ u = (fun _ => b)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (@h 1 (by decide) (fun _ => false) false).mpr rfl
  have hmem : false ∈ ({false} : Finset Bool) := Finset.mem_singleton_self _
  rw [← show (∅ : Finset Bool) = {false} from hb] at hmem
  exact Finset.notMem_empty false hmem

def family : Registration arena (type_of% @word_support_singleton) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@word_support_singleton, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨1, (fun _ => false), (fun _ => true), ?_⟩
    change word_support (fun _ : Fin 1 => false) ≠ word_support (fun _ : Fin 1 => true)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@word_support_singleton) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots.word_support_singleton.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots.word_support_singleton.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n x => word_support x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
                    stateBinder := 2
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end word_support_singleton

namespace word_support_full

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature ℕ
    (fun n => Fin n → Bool) (fun _ => Finset Bool)

def actual : Realization signature :=
  realize signature (fun _ n u => word_support u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Finset.univ) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (hn : 0 < n) (u : Fin n → Bool),
    R.readout () n u = Finset.univ ↔
      u ≠ (fun _ => false) ∧ u ≠ (fun _ => true)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (@h 1 (by decide) (fun _ => false)).mp rfl
  exact hb.1 rfl

def family : Registration arena (type_of% @word_support_full) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@word_support_full, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨1, (fun _ => false), (fun _ => true), ?_⟩
    change word_support (fun _ : Fin 1 => false) ≠ word_support (fun _ : Fin 1 => true)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@word_support_full) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots.word_support_full.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots.word_support_full.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n x => word_support x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
                    stateBinder := 2
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end word_support_full

namespace sum_by_support

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Finset Bool → ℕ)
    (fun _ => Finset Bool) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ f S => f S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ f S => f S + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (f : Finset Bool → ℕ),
    (∑ u : Fin n → Bool, R.readout () f (word_support u)) =
      ∑ S : Finset Bool, support_weight n S * f S

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 (fun _ => 0)
  simpa [arena, rejected, realize] using hb

def family : Registration arena (type_of% @sum_by_support) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_by_support, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨Finset.card, ∅, {false}, ?_⟩
    change (∅ : Finset Bool).card ≠ ({false} : Finset Bool).card
    simp

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@sum_by_support) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots.sum_by_support.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots.sum_by_support.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f x => f x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots
    definition := none
    coordinates := #[1]
    readouts := #[{ path := #["body", "body", "fn", "arg", "arg", "body"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end sum_by_support

namespace word_support_card

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Finset Bool)
    (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ S n => support_weight n S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ S n => support_weight n S + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (S : Finset Bool),
    Nat.card {u : Fin n → Bool // word_support u = S} = R.readout () S n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 ∅
  have ha := word_support_card 0 ∅
  change Nat.card {u : Fin 0 → Bool // word_support u = ∅} = support_weight 0 ∅ + 1 at hb
  omega

def family : Registration arena (type_of% @word_support_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@word_support_card, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨Finset.univ, 2, 3, ?_⟩
    change support_weight 2 Finset.univ ≠ support_weight 3 Finset.univ
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
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
  readout := some (realize signature (fun _ S x => support_weight x S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots
    definition := none
    coordinates := #[1]
    readouts := #[{ path := #["body", "body", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["fn", "arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end word_support_card

namespace ordinary_value_valid

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature NZPair
    (fun _ => Bool) (fun _ => K)

def actual : Realization signature :=
  realize signature (fun _ p x => ordinary_value p x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : NZPair) (b : Bool),
    R.readout () x b ≠ 0 ∧ ordinary_value x b ≠ x.val.1 + x.val.2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ⟨((1, 0), (0, 1)), by decide +kernel⟩ false
  exact hb.1 rfl

def family : Registration arena (type_of% @ordinary_value_valid) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ordinary_value_valid, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨⟨((1, 0), (0, 1)), by decide +kernel⟩, false, true, ?_⟩
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@ordinary_value_valid) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots.ordinary_value_valid.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots.ordinary_value_valid.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => ordinary_value p x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg"]
                    stateBinder := 1
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ordinary_value_valid

namespace pair_count_support

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
  Law R := ∀ (a b c d : ℕ) (x y : NZPair),
    (∑ u : Fin a → OrdinaryAlphabet x, ∑ v : Fin b → OrdinaryAlphabet y,
      Nat.card (InteriorAlphabet x y u v x.val.1 y.val.1) ^ c *
      Nat.card (InteriorAlphabet x y u v x.val.2 y.val.2) ^ d) =
        R.readout () ⟨a, b, c, d, x⟩ y

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 1 1 1 ⟨((1, 0), (0, 1)), by decide +kernel⟩ ⟨((1, 0), (0, 1)), by decide +kernel⟩
  have ha := pair_count_support 1 1 1 1 ⟨((1, 0), (0, 1)), by decide +kernel⟩ ⟨((1, 0), (0, 1)), by decide +kernel⟩
  dsimp only [arena, rejected, realize] at hb
  exact (Nat.ne_of_lt (Nat.lt_succ_self _)) (ha.symm.trans hb)

def family : Registration arena (type_of% @pair_count_support) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pair_count_support, rejected, rejected_law⟩
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
    (@pair_count_support) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots.pair_count_support.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots.pair_count_support.family
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
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end pair_count_support

end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalSlots
