import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.Analytic.ExceptionCount.CountingTransfer
import Reg.Support.SingleDependentReadout

/-! Source families for distinct-prime counting transfers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Real Finset LeanInformationAudit
open scoped Topology BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open _root_.D5.S3.Arith.Robin.Analytic.OmegaTail
open _root_.D5.S3.Arith.Robin.Analytic.ExceptionCount.Counting
open _root_.D5.S3.Arith.Robin.Analytic.ExceptionCount.CountingTransfer

namespace Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.CountingTransfer

namespace GlobalTransfer

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (E : ℕ → Prop) [DecidablePred E],
    (∀ eta : ℝ, 0 < eta → ∀ᶠ t : ℝ in atTop,
      ∀ n : ℕ, t / 2 < n → (n : ℝ) ≤ t → E n →
        threshold (-eta) t < (ArithmeticFunction.cardDistinctFactors n : ℝ)) →
    ∀ {epsilon : ℝ}, 0 < epsilon → ∀ᶠ x : ℝ in atTop,
      R.readout () () (((Icc 1 ⌊x⌋₊).filter E).card : ℝ)
        (exp ((C0 + epsilon) * scale x))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfalse := h (fun _ => False)
    (by
      intro eta heta
      filter_upwards [] with t
      intro n hnlo hnhi hE
      exact hE.elim)
    (epsilon := 1) (by norm_num)
  obtain ⟨x, hx⟩ := hfalse.exists
  exact hx

def family : Registration arena (type_of% @count_from_local_exclusion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@count_from_local_exclusion, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), 1, ?_⟩
    intro he
    have hh : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@count_from_local_exclusion) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.Analytic.ExceptionCount.CountingTransfer.count_from_local_exclusion.audit
  realizationName := `Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.CountingTransfer.GlobalTransfer.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.Analytic.ExceptionCount.CountingTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GlobalTransfer

end Reg.D5.S3.Arith.Robin.Analytic.ExceptionCount.CountingTransfer
