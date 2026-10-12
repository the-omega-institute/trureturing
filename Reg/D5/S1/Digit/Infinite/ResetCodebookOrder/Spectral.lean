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

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.Spectral.gelfand
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Filter ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ z => nhds z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)
def sourceStatement : Prop := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ), Filter.Tendsto (fun k : ℕ => ‖complexify A ^ k‖ ^ (1 / (k : ℝ))) Filter.atTop (nhds (radius A))
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ), Filter.Tendsto (fun k : ℕ => ‖complexify A ^ k‖ ^ (1 / (k : ℝ))) Filter.atTop (R.readout () () (radius A))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  have hh' := hh (ι := ULift.{u} Unit) 0
  exact Filter.atTop_neBot.ne (Filter.tendsto_bot_right_iff.mp hh')
def registration : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Spectral.gelfand.{u},rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0 : ℝ),(1 : ℝ),?_⟩
    exact nhds_injective.ne (by norm_num)
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Spectral.gelfand.{u})
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ z => nhds z) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Spectral.gelfand.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.Spectral.gelfand.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨registration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ z => nhds z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.Spectral.gelfand


namespace Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.Spectral.radius_mono
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A B : Matrix ι ι ℝ), (∀ i j, 0 ≤ A i j) → (∀ i j, A i j ≤ B i j) → radius A ≤ radius B
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A B : Matrix ι ι ℝ), (∀ i j, 0 ≤ A i j) → (∀ i j, A i j ≤ B i j) → R.readout () () (radius A) (radius B)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro hh
  exact hh (ι := ULift.{u} Unit) 0 0 (by simp) (by simp)
def registration : Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.Spectral.radius_mono.{u},rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0 : ℝ),(1 : ℝ),?_⟩
    intro he
    have bad : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at bad
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.Spectral.radius_mono.{u})
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.Spectral.radius_mono.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.Spectral.radius_mono.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena.{u}⟩, objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena.{u} ⟨registration.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookOrder, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookOrder.Spectral.radius_mono
