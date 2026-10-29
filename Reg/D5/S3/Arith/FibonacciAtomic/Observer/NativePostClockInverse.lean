import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativePostClockInverse
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePostClockInverse

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address readout)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeMaterialRootRecognition (D material neighbors children)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair (Call run)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePostClockInverse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

local instance finiteCoordinates (t : Source) : Fintype (Coordinate t) := coordinates t

noncomputable section

private theorem example_invertible (t : Source) : (clock 4 1 t).det ≠ 0 := by
  apply Matrix.det_ne_zero_of_sum_row_lt_diag
  intro k
  let S : Finset (Coordinate t) := Finset.univ.filter (fun j => j.val ∈ neighbors t k.val)
  have hdeg : (neighbors t k.val).length ≤ 3 := by
    unfold neighbors children
    split <;> split <;> simp_all
  have hcard : S.card ≤ 3 := by
    calc
      S.card = (S.image Subtype.val).card :=
        (Finset.card_image_of_injective S Subtype.val_injective).symm
      _ ≤ ((neighbors t k.val).toFinset).card := Finset.card_le_card (by
        intro q hq
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
        exact List.mem_toFinset.mpr (Finset.mem_filter.mp hj).2)
      _ ≤ (neighbors t k.val).length := List.toFinset_card_le _
      _ ≤ 3 := hdeg
  have hrow : ∑ j ∈ Finset.univ.erase k, ‖clock 4 1 t k j‖ ≤ (3 : ℝ) := by
    calc
      _ = ∑ j ∈ Finset.univ.erase k,
          (if j.val ∈ neighbors t k.val then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hne : k ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
        simp [clock, hne]
      _ ≤ ∑ j : Coordinate t, (if j.val ∈ neighbors t k.val then (1 : ℝ) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (by intros; positivity)
      _ = (S.card : ℝ) := by simp [S, Finset.card_filter]
      _ ≤ 3 := by exact_mod_cast hcard
  have hdiag : (4 : ℝ) ≤ ‖clock 4 1 t k k‖ := by
    simp only [clock, ↓reduceIte]
    split <;> norm_num
  linarith

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
  ∀ (a c : ℚ) (ha : 0 < a) (hc : 0 < c)
    (hinv : ∀ t, D t → (clock a c t).det ≠ 0),
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
  have hh := h 4 1 (by norm_num) (by norm_num) (fun t _ => example_invertible t)
  obtain ⟨x, hx, _⟩ := hh.1 [] (.of true) rfl
  change none = some _ at hx
  contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨0, 0, 1, ?_⟩
  intro he
  have hh := congrArg (fun f => (f [.promote []]).map
    (fun e => zeroInclude e.1 (.of false) e.2 ⟨[false], by simp [material]⟩)) he
  change some (0 : ℚ) = some 1 at hh
  contradiction

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
    `D5.S3.Arith.FibonacciAtomic.Observer.NativePostClockInverse.postclock_inverse "__information_unit"
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
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 1, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePostClockInverse
