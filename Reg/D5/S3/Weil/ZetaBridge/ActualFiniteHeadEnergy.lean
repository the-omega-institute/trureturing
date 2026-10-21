import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure
open _root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy
open LeanInformationAudit

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := Unit
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => ∑' j, f j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun j => if j = 0 then 1 else 0), ?_⟩
  simp [actual, realize]

namespace Summability

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := Unit
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => Summable f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (hS : S.Nonempty)
    (N : ℕ) (v : ℤ → ℂ), r.readout () () (pairedColumnTerm c N S v)

private theorem actual_law : arena.Law actual :=
  @_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.actual_tail_summable_all

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (c := 3) (by decide) {0} (by simp) 0 (fun _ => 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  change Summable (fun _ : ℕ => (0 : ℝ)) ≠ Summable (fun _ : ℕ => (1 : ℝ))
  intro h
  have hs : Summable (fun _ : ℕ => (1 : ℝ)) := h ▸ summable_zero
  exact one_ne_zero ((summable_const_iff (1 : ℝ)).mp hs)

def family : Registration arena
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.actual_tail_summable_all)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.actual_tail_summable_all)
    (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.Summability.unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.Summability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => Summable f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Summability

namespace Positive

def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (N : ℕ)
    (v : ℤ → ℂ) (hv : ∃ k ∈ S, v k ≠ 0),
    0 < r.readout () () (pairedColumnTerm c N S v)

private theorem actual_law : arena.Law actual :=
  @_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.actual_finite_head_tail_pos

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := h (c := 3) (by decide) {0} 0 (fun _ => 1) ⟨0, by simp, one_ne_zero⟩
  exact (lt_irrefl (0 : ℝ)) hp

def family : Registration arena
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.actual_finite_head_tail_pos)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.actual_finite_head_tail_pos)
    (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.Positive.unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.Positive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => ∑' j, f j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Positive

namespace ZeroKernel

def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 3 ≤ c) (S : Finset ℤ) (N : ℕ) (v : ℤ → ℂ),
    r.readout () () (pairedColumnTerm c N S v) = 0 ↔ ∀ k ∈ S, v k = 0

private theorem actual_law : arena.Law actual :=
  @_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.actual_finite_head_tail_zero_iff

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := (h (c := 3) (by decide) {0} 0 (fun _ => 1)).mp rfl
  exact one_ne_zero (hp 0 (by simp))

def family : Registration arena
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.actual_finite_head_tail_zero_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.actual_finite_head_tail_zero_iff)
    (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.ZeroKernel.unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy.ZeroKernel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => ∑' j, f j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ZeroKernel
end Reg.D5.S3.Weil.ZetaBridge.ActualFiniteHeadEnergy
