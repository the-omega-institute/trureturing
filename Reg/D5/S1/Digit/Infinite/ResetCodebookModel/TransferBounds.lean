import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Infinite.ResetCodebookWeighted
import Reg.Support.DependentFamily

open D5.S1.Digit.Infinite
open D5.S1.Digit.Infinite.ResetCodebook
open D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Topology
open D5.S1.Digit.Infinite.ResetCodebook.Transfer
open D5.S1.Digit.Infinite.ResetCodebook.Spectral
open scoped Matrix.Norms.Operator
universe u
noncomputable section

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.positive_pow
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), (∀ i j, 0 ≤ A i j) → ∀ (k : ℕ) (i j : ι), 0 ≤ (A^k) i j
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), (∀ i j, 0 ≤ A i j) → ∀ (k : ℕ) (i j : ι), R.readout () () ((A^k) i j)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact hh (ι := ULift.{u} Unit) 0 (by simp) 0 ⟨()⟩ ⟨()⟩
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Spectral.positive_pow,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0 : ℝ),(-1 : ℝ),?_⟩
    change (0 ≤ (0 : ℝ)) ≠ (0 ≤ (-1 : ℝ))
    simp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Spectral.positive_pow)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Spectral.positive_pow.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.positive_pow.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookModel, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.positive_pow

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.mass_nonneg
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ {ι : Type u}  (next : ι → Bool → ι) (allow : ι → Bool → Prop) (z : ℝ), 0 ≤ z → ∀ (v : ι) (w : List Bool), 0 ≤ mass next allow z v w
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u}  (next : ι → Bool → ι) (allow : ι → Bool → Prop) (z : ℝ), 0 ≤ z → ∀ (v : ι) (w : List Bool), R.readout () () (mass next allow z v w)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact hh (ι := ULift.{u} Unit) (fun v _ => v) (fun _ _ => True) 0 le_rfl ⟨()⟩ []
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Transfer.mass_nonneg,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0 : ℝ),(-1 : ℝ),?_⟩
    change (0 ≤ (0 : ℝ)) ≠ (0 ≤ (-1 : ℝ))
    simp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Transfer.mass_nonneg)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Transfer.mass_nonneg.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.mass_nonneg.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookModel, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.mass_nonneg

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.transfer_nonneg
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ {ι : Type u}  (next : ι → Bool → ι) (allow : ι → Bool → Prop) (z : ℝ), 0 ≤ z → ∀ (v v' : ι), 0 ≤ transfer next allow z v v'
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u}  (next : ι → Bool → ι) (allow : ι → Bool → Prop) (z : ℝ), 0 ≤ z → ∀ (v v' : ι), R.readout () () (transfer next allow z v v')
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact hh (ι := ULift.{u} Unit) (fun v _ => v) (fun _ _ => True) 0 le_rfl ⟨()⟩ ⟨()⟩
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Transfer.transfer_nonneg,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0 : ℝ),(-1 : ℝ),?_⟩
    change (0 ≤ (0 : ℝ)) ≠ (0 ≤ (-1 : ℝ))
    simp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Transfer.transfer_nonneg)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Transfer.transfer_nonneg.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.transfer_nonneg.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookModel, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.transfer_nonneg

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.transfer_pow_nonneg
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (next : ι → Bool → ι) (allow : ι → Bool → Prop) (z : ℝ), 0 ≤ z → ∀ (k : ℕ) (v v' : ι), 0 ≤ (transfer next allow z ^ k) v v'
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (next : ι → Bool → ι) (allow : ι → Bool → Prop) (z : ℝ), 0 ≤ z → ∀ (k : ℕ) (v v' : ι), R.readout () () ((transfer next allow z ^ k) v v')
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact hh (ι := ULift.{u} Unit) (fun v _ => v) (fun _ _ => True) 0 le_rfl 0 ⟨()⟩ ⟨()⟩
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Transfer.transfer_pow_nonneg,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0 : ℝ),(-1 : ℝ),?_⟩
    change (0 ≤ (0 : ℝ)) ≠ (0 ≤ (-1 : ℝ))
    simp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Transfer.transfer_pow_nonneg)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Transfer.transfer_pow_nonneg.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.transfer_pow_nonneg.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookModel, definition := none, coordinates := #[],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.transfer_pow_nonneg

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.mem_wordSet
abbrev signature : Signature where
  Params := List Bool
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ w k => w.length = k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ (w : List Bool) (k : ℕ), w ∈ wordSet k ↔ w.length = k
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (w : List Bool) (k : ℕ), w ∈ wordSet k ↔ R.readout () w k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact (hh [] 0).mp (by simp [wordSet])
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Transfer.mem_wordSet,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨[],0,1,?_⟩
    change (([] : List Bool).length = 0) ≠ (([] : List Bool).length = 1)
    simp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Transfer.mem_wordSet)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ w k => w.length = k) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Transfer.mem_wordSet.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.mem_wordSet.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ w k => w.length = k) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookModel, definition := none, coordinates := #[0],
    readouts := #[{ path := #["body", "body", "arg"], stateBinder := 1,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.mem_wordSet

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.mass_of_accepts
abbrev signature : Signature where
  Params := List Bool
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ w z => z^Statement.letterWeight w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ {ι : Type u} (next : ι → Bool → ι) (allow : ι → Bool → Prop) (z : ℝ) (v : ι) (w : List Bool), accepts next allow v w → mass next allow z v w = z^Statement.letterWeight w
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} (next : ι → Bool → ι) (allow : ι → Bool → Prop) (z : ℝ) (v : ι) (w : List Bool), accepts next allow v w → mass next allow z v w = R.readout () w z
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh (ι := ULift.{u} Unit) (fun v _ => v) (fun _ _ => True) 0 ⟨()⟩ [] trivial
  norm_num [mass,rejected,realize] at he
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Transfer.mass_of_accepts,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨[false],(0 : ℝ),(1 : ℝ),?_⟩
    norm_num [actual,realize,Statement.letterWeight]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Transfer.mass_of_accepts)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ w z => z^Statement.letterWeight w) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Transfer.mass_of_accepts.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.mass_of_accepts.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ w z => z^Statement.letterWeight w) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookModel, definition := none, coordinates := #[5],
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookModel.TransferBounds.mass_of_accepts

