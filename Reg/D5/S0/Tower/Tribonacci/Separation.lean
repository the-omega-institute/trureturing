import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S0.Tower.Tribonacci.Separation
import D5.S3.Constants.Irrationality.TribonacciTraceLattice

/-! Coordinate observations on finite Tribonacci name layers. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S0.Tower.Tribonacci.Separation

open _root_.D5.S0.Tower.Tribonacci.Names
open _root_.D5.S0.Tower.Tribonacci.Values
open _root_.D5.S0.Tower.Tribonacci.ModelSet
open _root_.D5.S0.Tower.Tribonacci.Binet
open _root_.D5.S0.Tower.Tribonacci.Separation
open _root_.D5.S3.Constants.Irrationality.TribonacciTraceLattice
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : ℂ, ℕ
  State p := TribonacciName p.2
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p u => conjugateCoordinate p.1 u) (fun e => nomatch e)

def erasedAt (i : Fin 2) : Realization signature :=
  realize signature
    (fun j p u => if j = i then 0 else conjugateCoordinate p.1 u)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z : ℂ}, z ∈ tribonacciCharacteristicPolynomial.roots →
    z ≠ (tribonacciConstant : ℂ) → ∀ (Q : ℕ) (u v : TribonacciName Q), u ≠ v →
    Real.sqrt (tribonacciConstant - 1) * ‖z‖ ^ Q ≤
      dist (R.readout 0 ⟨z, Q⟩ u) (R.readout 1 ⟨z, Q⟩ v)

abbrev sourceScope := type_of% (@conjugateCoordinate_separation)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

private def zeroName : TribonacciName 1 := ⟨fun _ => false, trivial⟩
private def oneName : TribonacciName 1 := ⟨fun _ => true, trivial⟩

private theorem root_mem :
    tribonacciSecondaryRoot.1 ∈ tribonacciCharacteristicPolynomial.roots := by
  have hp : tribonacciCharacteristicPolynomial ≠ 0 := by
    intro h
    have he := congrArg (Polynomial.eval (2 : ℂ)) h
    norm_num [tribonacciCharacteristicPolynomial] at he
  apply (Polynomial.mem_roots hp).mpr
  simpa [Polynomial.IsRoot, tribonacciCharacteristicPolynomial] using
    tribonacciSecondaryRoot.2.1

private theorem positive_scale :
    0 < Real.sqrt (tribonacciConstant - 1) * ‖tribonacciSecondaryRoot.1‖ ^ 1 := by
  have hz : tribonacciSecondaryRoot.1 ≠ 0 := by
    intro h
    have hi := tribonacciSecondaryRoot.2.2.2
    rw [h] at hi
    simpa using hi
  exact mul_pos (Real.sqrt_pos.mpr (sub_pos.mpr one_lt_tribonacciConstant))
    (pow_pos (norm_pos_iff.mpr hz) 1)

theorem erased_fails (i : Fin 2) : ¬ arena.Law (erasedAt i) := by
  have hne : oneName ≠ zeroName := by
    intro h
    have he : (true : Bool) = false := congrArg (fun u : TribonacciName 1 => u.1 0) h
    cases he
  intro h
  fin_cases i
  · have hb := h root_mem tribonacciSecondaryRoot.2.2.1 1 oneName zeroName hne
    have hn : ¬ Real.sqrt (tribonacciConstant - 1) * ‖tribonacciSecondaryRoot.1‖ ^ 1 ≤ 0 :=
      not_le.mpr positive_scale
    apply hn
    simpa [erasedAt, realize, conjugateCoordinate, oneName, zeroName] using hb
  · have hb := h root_mem tribonacciSecondaryRoot.2.2.1 1 zeroName oneName (Ne.symm hne)
    have hn : ¬ Real.sqrt (tribonacciConstant - 1) * ‖tribonacciSecondaryRoot.1‖ ^ 1 ≤ 0 :=
      not_le.mpr positive_scale
    apply hn
    simpa [erasedAt, realize, conjugateCoordinate, oneName, zeroName] using hb

def family : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨@conjugateCoordinate_separation, erasedAt 0, erased_fails 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erasedAt i, ?_, rfl, erased_fails i⟩
      intro j hj
      funext p u
      change conjugateCoordinate p.1 u = if j = i then 0 else conjugateCoordinate p.1 u
      rw [if_neg hj]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨tribonacciSecondaryRoot.1, 1⟩, zeroName, oneName, ?_⟩
    norm_num [actual, realize, conjugateCoordinate, zeroName, oneName]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@conjugateCoordinate_separation) (Realization signature) Unit Unit where
  unitName := `D5.S0.Tower.Tribonacci.Separation.conjugateCoordinate_separation.__information_unit
  realizationName := `Reg.D5.S0.Tower.Tribonacci.Separation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p u => conjugateCoordinate p.1 u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Tower.Tribonacci.Separation
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S0.Tower.Tribonacci.Separation
