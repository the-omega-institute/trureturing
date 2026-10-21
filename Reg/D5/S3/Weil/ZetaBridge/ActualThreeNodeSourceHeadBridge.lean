import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder Matrix

namespace Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
open _root_.D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure
open LeanInformationAudit

namespace LinearCombination

private def pulse : tailSpace := lp.single 2 0 (!₂[1, 0] : pairSpace)

private lemma pulse_ne_zero : pulse ≠ 0 := by
  intro h
  have hv := congrArg (fun f : tailSpace => f 0 0) h
  simpa [pulse, lp.single_apply] using hv

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := Unit
  State _ := Fin 3 → tailSpace
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := tailSpace
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => ∑ i, f i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (pulse : tailSpace)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ)
    (x : Fin 3 → ℂ),
    r.readout () () (fun i => x i • sourceTailFamily hc N n i) =
      sourceColumnMap hc n N (sourceHead n x)

private theorem actual_law : arena.Law actual :=
  @_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.source_linear_combination

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (c := 3) (by decide) 1 0 (0 : Fin 3 → ℂ)
  apply pulse_ne_zero
  simpa [rejected, realize, sourceHead] using hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun j => if j = 0 then pulse else 0), ?_⟩
  change (∑ j : Fin 3, (0 : tailSpace)) ≠
    ∑ j : Fin 3, if j = 0 then pulse else 0
  simpa using pulse_ne_zero.symm

def family : Registration arena
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.source_linear_combination)) where
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
    (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.source_linear_combination) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.LinearCombination.unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.LinearCombination.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => ∑ i, f i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end LinearCombination

namespace CompleteGram

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
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ)
    (x : Fin 3 → ℂ),
    let G : Matrix (Fin 3) (Fin 3) ℂ := Matrix.gram ℂ (sourceTailFamily hc N n)
    star x ⬝ᵥ (G *ᵥ x) =
      (r.readout () () (pairedColumnTerm c N (threeNodes n) (sourceHead n x)) : ℂ)

private theorem actual_law : arena.Law actual :=
  @_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_source_gram_tsum

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (c := 3) (by decide) 1 0 (0 : Fin 3 → ℂ)
  have hz : (0 : ℂ) = 1 := by simpa [rejected, realize] using hh
  exact zero_ne_one hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun j => if j = 0 then 1 else 0), ?_⟩
  simp [actual, realize]

def family : Registration arena
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_source_gram_tsum)) where
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
    (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_source_gram_tsum) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.CompleteGram.unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.CompleteGram.family
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
    owner := `D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end CompleteGram

namespace CoefficientGram

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := ℤ
  State _ := Fin 3 → (ℤ → ℂ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 3) (Fin 3) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n b => coefficientGram n b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : Matrix (Fin 3) (Fin 3) ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {n : ℤ} (hn : n ≠ 0),
    r.readout () n (normalizedHead n) = 1

private theorem actual_law : arena.Law actual :=
  @_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.normalizedHead_coefficient_gram

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh : (0 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := h (n := 1) (by decide)
  exact zero_ne_one hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, normalizedHead 1, (fun _ => 0), ?_⟩
  change coefficientGram 1 (normalizedHead 1) ≠ coefficientGram 1 (fun _ => 0)
  rw [normalizedHead_coefficient_gram (by decide : (1 : ℤ) ≠ 0)]
  have hv : nodeVector (1 : ℤ) (0 : ℤ → ℂ) = 0 := by
    ext k
    fin_cases k <;> rfl
  have hz : coefficientGram 1 (fun _ => 0) = 0 := by
    ext j k
    simp [coefficientGram, coefficientInner, hv]
  rw [hz]
  exact one_ne_zero

def family : Registration arena
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.normalizedHead_coefficient_gram)) where
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
    (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.normalizedHead_coefficient_gram) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.CoefficientGram.unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.CoefficientGram.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n b => coefficientGram n b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end CoefficientGram

namespace OriginalMass

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {n : ℤ} (hn : n ≠ 0) (x : Fin 3 → ℂ),
    (∑ k ∈ threeNodes n, (r.readout () () (sourceHead n x k)) ^ 2) =
      ∑ i : Fin 3, ‖x i‖ ^ 2

private theorem actual_law : arena.Law actual :=
  @_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.sourceHead_original_norm

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 1) (by decide) (0 : Fin 3 → ℂ)
  norm_num [rejected, realize, threeNodes] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
  change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
  norm_num

def family : Registration arena
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.sourceHead_original_norm)) where
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
    (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.sourceHead_original_norm) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.OriginalMass.unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.OriginalMass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end OriginalMass

namespace PositiveDefinite

abbrev signature : Signature.{0, 0, 0, 0, 0} where
  Params := Unit
  State _ := Matrix (Fin 3) (Fin 3) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ M => M.PosDef) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (False : Prop)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0) (N : ℕ),
    r.readout () () (Matrix.gram ℂ (sourceTailFamily hc N n))

private theorem actual_law : arena.Law actual :=
  @_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_gram_posDef

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (c := 3) (by decide) (n := 1) (by decide) 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (1 : Matrix (Fin 3) (Fin 3) ℂ), 0, ?_⟩
  change (1 : Matrix (Fin 3) (Fin 3) ℂ).PosDef ≠
    (0 : Matrix (Fin 3) (Fin 3) ℂ).PosDef
  intro h
  have hz : (0 : Matrix (Fin 3) (Fin 3) ℂ).PosDef := h ▸ Matrix.PosDef.one
  have hp : (0 : ℂ) < 0 := hz.diag_pos (i := (0 : Fin 3))
  exact (lt_irrefl (0 : ℂ)) hp

def family : Registration arena
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_gram_posDef)) where
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
    (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_gram_posDef) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.PositiveDefinite.unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.PositiveDefinite.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ M => M.PosDef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end PositiveDefinite

end Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge

namespace Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.FiniteHeadEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.ActualNodalTailEnclosure
open _root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
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
  @_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_tail_summable_all

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
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_tail_summable_all)) where
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
    (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_tail_summable_all)
    (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.FiniteHeadEnergy.Summability.unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.FiniteHeadEnergy.Summability.family
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
    owner := `D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
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
  @_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_finite_head_tail_pos

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := h (c := 3) (by decide) {0} 0 (fun _ => 1) ⟨0, by simp, one_ne_zero⟩
  exact (lt_irrefl (0 : ℝ)) hp

def family : Registration arena
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_finite_head_tail_pos)) where
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
    (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_finite_head_tail_pos)
    (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.FiniteHeadEnergy.Positive.unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.FiniteHeadEnergy.Positive.family
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
    owner := `D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
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
  @_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_finite_head_tail_zero_iff

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := (h (c := 3) (by decide) {0} 0 (fun _ => 1)).mp rfl
  exact one_ne_zero (hp 0 (by simp))

def family : Registration arena
    (type_of% (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_finite_head_tail_zero_iff)) where
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
    (@_root_.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.actual_finite_head_tail_zero_iff)
    (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.FiniteHeadEnergy.ZeroKernel.unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.FiniteHeadEnergy.ZeroKernel.family
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
    owner := `D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge
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
end Reg.D5.S3.Weil.ZetaBridge.ActualThreeNodeSourceHeadBridge.FiniteHeadEnergy
