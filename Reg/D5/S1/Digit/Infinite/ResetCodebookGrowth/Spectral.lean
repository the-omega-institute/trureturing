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

local notation "complexify" => Complex.ofRealHom.mapMatrix
local notation "radius" => fun A => ENNReal.toReal (spectralRadius ℂ (Complex.ofRealHom.mapMatrix A))

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.Spectral.radius_smul
abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ c x => c*x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ) (c : ℝ), 0 ≤ c → radius (c • A) = c * radius A
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ) (c : ℝ), 0 ≤ c → radius (c • A) = R.readout () c (radius A)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  have hh' := hh (ι := ULift.{u} Unit) 0 0 le_rfl
  change ENNReal.toReal _ = -1 at hh'
  have hn : (0 : ℝ) ≤ -1 := hh' ▸ ENNReal.toReal_nonneg
  norm_num at hn
def registration : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Spectral.radius_smul.{u},rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨1,(0 : ℝ),(1 : ℝ),?_⟩
    norm_num [actual,realize]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Spectral.radius_smul.{u})
    (type_of% (realize.{0,0,0,0,0} signature (fun _ c x => c*x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Spectral.radius_smul.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.Spectral.radius_smul.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨registration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ c x => c*x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookGrowth, definition := none, coordinates := #[5],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.Spectral.radius_smul

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.Spectral.radius_sq
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => x^2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ), radius (A^2) = radius A ^ 2
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ), radius (A^2) = R.readout () () (radius A)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  have hh' := hh (ι := ULift.{u} Unit) 0
  change ENNReal.toReal _ = -1 at hh'
  linarith [ENNReal.toReal_nonneg (a := spectralRadius ℂ (complexify ((0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℝ)^2)))]
def registration : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Spectral.radius_sq.{u},rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0 : ℝ),(1 : ℝ),?_⟩
    norm_num [actual,realize]
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Spectral.radius_sq.{u})
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => x^2) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Spectral.radius_sq.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.Spectral.radius_sq.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨registration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => x^2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookGrowth, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.Spectral.radius_sq


namespace Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.Spectral.row_lower_radius
abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ r x => r ≤ x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ), (∀ i j, 0 ≤ A i j) → ∀ r : ℝ, 0 ≤ r → (∀ i, r ≤ ∑ j, A i j) → r ≤ radius A
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ), (∀ i j, 0 ≤ A i j) → ∀ r : ℝ, 0 ≤ r → (∀ i, r ≤ ∑ j, A i j) → R.readout () r (radius A)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  exact hh (ι := ULift.{u} Unit) 0 (by simp) 0 le_rfl (by simp)
def registration : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Spectral.row_lower_radius.{u},rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨0,(0 : ℝ),(-1 : ℝ),?_⟩
    change (0 ≤ (0 : ℝ)) ≠ (0 ≤ (-1 : ℝ))
    simp
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Spectral.row_lower_radius.{u})
    (type_of% (realize.{0,0,0,0,0} signature (fun _ r x => r ≤ x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Spectral.row_lower_radius.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.Spectral.row_lower_radius.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨registration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ r x => r ≤ x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookGrowth, definition := none, coordinates := #[6],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.Spectral.row_lower_radius

