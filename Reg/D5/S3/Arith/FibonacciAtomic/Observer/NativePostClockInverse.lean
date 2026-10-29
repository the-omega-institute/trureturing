import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativePostClockInverse
import Mathlib.Data.ZMod.Basic
import Reg.Support.DependentFamily

/-! Source-faithful family registration of the complete native post-clock inverse. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePostClockInverse

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address readout)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeMaterialRootRecognition
  (D material neighbors children)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair (Call run)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePostClockInverse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

local instance finiteCoordinates (t : Source) : Fintype (Coordinate t) := coordinates t

noncomputable section

theorem example_invertible (t : Source) : (clock 1 2 t).det ≠ 0 := by
  let M : Matrix (Coordinate t) (Coordinate t) ℤ := fun i j =>
    (if i = j then 1 else 0) + (if j.val ∈ neighbors t i.val then 2 else 0)
  have hrat : M.map (fun n => (n : ℚ)) = clock 1 2 t := by
    ext i j
    change ((M i j : ℤ) : ℚ) = _
    by_cases hi : i = j <;> by_cases hn : j.val ∈ neighbors t i.val <;>
      norm_num [M, clock, hi, hn]
  have htwo : M.map (fun n => (n : ZMod 2)) = 1 := by
    have htwo0 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    ext i j
    change ((M i j : ℤ) : ZMod 2) = _
    simp only [M, Int.cast_add, apply_ite, Int.cast_one, Int.cast_zero,
      Int.cast_ofNat, htwo0, ite_self, add_zero, Matrix.one_apply]
  intro h
  have hz : (M.det : ℚ) = 0 := by rw [Int.cast_det, hrat, h]
  have hz' : M.det = 0 := by exact_mod_cast hz
  have hmod := congrArg (fun n : ℤ => (n : ZMod 2)) hz'
  rw [Int.cast_det, htwo, Matrix.det_one] at hmod
  norm_num at hmod

@[reducible] def signature : Signature where
  Params := ℚ
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Call → Option Endpoint
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a c => encode a c) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ _ => none) (fun e => nomatch e)

def inverseLaw (E : ℚ → ℚ → List Call → Option Endpoint) : Prop :=
  ∀ (a c : ℚ) (_ha : 0 < a) (_hc : 0 < c)
    (_hinv : ∀ (v : List Call) (t : Source), run (.of true) v = some t →
      (clock a c t).det ≠ 0),
    (∀ (w : List Call) (t : Source), run (.of true) w = some t →
      ∃ x : Field t, E a c w = some ⟨t, x⟩ ∧
        decode a c ⟨t, x⟩ = some w ∧ ∀ q, 0 < x q) ∧
    (∀ (w : List Call) (e : Endpoint), E a c w = some e →
      decode a c e = some w) ∧
    (∀ e : Endpoint, (∃ w, E a c w = some e) →
      (decode a c e).bind (E a c) = some e) ∧
    (∀ (w v : List Call) (e : Endpoint), E a c w = some e →
      E a c v = some e → w = v) ∧
    (∀ (w : List Call) (e : Endpoint) (g : Call), E a c w = some e →
      subtree (address g) e.1 = some (.of (kind g)) →
      predecessor a c (appendEndpoint a c e g) = some (e, g) ∧
        (material e.1).length < (material (edited e.1 g)).length)

@[reducible] def arena : Arena where
  signature := signature
  Law R := inverseLaw (fun a c => R.readout () a c)

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hh := h 1 2 (by norm_num) (by norm_num) (fun _ t _ => example_invertible t)
  obtain ⟨x, hx, _⟩ := hh.1 [] (.of true) rfl
  change none = some _ at hx
  contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨1, 2, 4, ?_⟩
  intro he
  have hh := congrArg (fun f => (f [.promote []]).map
    (fun e => zeroInclude e.1 (.of false) e.2 ⟨[false], by simp [material]⟩)) he
  have hn : (encode 1 2 [.promote []]).map
      (fun e => zeroInclude e.1 (.of false) e.2 ⟨[false], by simp [material]⟩) ≠
      (encode 1 4 [.promote []]).map
      (fun e => zeroInclude e.1 (.of false) e.2 ⟨[false], by simp [material]⟩) := by
    decide +kernel
  exact hn hh

def familyRegistration : Registration arena (type_of% (@postclock_inverse)) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨postclock_inverse, bad, bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,
    fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl, bad_law⟩,
    fun e => nomatch e⟩
  dependence := dependence }

noncomputable def postclockInverseRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@postclock_inverse) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str
    `D5.S3.Arith.FibonacciAtomic.Observer.NativePostClockInverse.postclock_inverse
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePostClockInverse.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePostClockInverse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg",
        "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 1, functionOperand := false, stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePostClockInverse
