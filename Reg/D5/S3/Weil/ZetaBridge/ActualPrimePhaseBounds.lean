import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Analysis.Source
import D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open _root_.D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
open _root_.D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
open _root_.D5.S3.Weil.ZetaBridge.ActualFullSymbolTail
open _root_.D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds
open LeanInformationAudit
open scoped BigOperators ComplexConjugate

namespace Reg.D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds
noncomputable section

/-- The whole natural cutoff is the source state. All labels and ordered
channels remain in the native observations, including higher prime powers. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private theorem indices_two : primeIndices 2 = ∅ := by simp [primeIndices]

private theorem indices_three : primeIndices 3 = {2} := by
  ext q
  simp only [primeIndices, Finset.mem_Ico, Finset.mem_singleton]
  omega

private theorem weight_two_pos : 0 < primeWeight 2 := by
  unfold primeWeight
  rw [ArithmeticFunction.vonMangoldt_apply_prime (by decide : Nat.Prime 2)]
  exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))

private theorem two_mem_three : 2 ∈ primeIndices 3 := by
  rw [indices_three]
  exact Finset.mem_singleton_self _

/-- The existing exact ordered sum-resonance theorem rejects this genuine
nonresonant self-pair (2,2) at c=3. The full offset keeps resonant self-pairs. -/
private theorem self_phase_ne_one : primePhase 3 2 * primePhase 3 2 ≠ 1 := by
  intro h
  have heq : (2 : ℕ) * 2 = 3 :=
    (sum_resonance (c := 3) (by decide) two_mem_three two_mem_three).mp h
  norm_num at heq

private theorem first_phase_ne_one : primePhase 3 2 ≠ 1 := by
  intro h
  apply self_phase_ne_one
  rw [h, one_mul]

private theorem first_chord_pos : 0 < ‖1 - primePhase 3 2‖ := by
  apply norm_pos_iff.mpr
  exact sub_ne_zero.mpr (Ne.symm first_phase_ne_one)

private theorem sum_chord_pos : 0 < ‖1 - primePhase 3 2 * primePhase 3 2‖ := by
  apply norm_pos_iff.mpr
  exact sub_ne_zero.mpr (Ne.symm self_phase_ne_one)

private theorem amplitude_two : (∑ q ∈ primeIndices 2, primeWeight q) = 0 := by
  simp only [indices_two, Finset.sum_empty]

private theorem amplitude_three_pos : 0 < ∑ q ∈ primeIndices 3, primeWeight q := by
  simpa only [indices_three, Finset.sum_singleton] using weight_two_pos

private theorem firstMoment_two : primeFirstMoment 2 = 0 := by
  simp only [primeFirstMoment, indices_two, Finset.sum_empty]

private theorem firstMoment_three_pos : 0 < primeFirstMoment 3 := by
  simp only [primeFirstMoment, indices_three, Finset.sum_singleton]
  exact div_pos (mul_pos (by norm_num) (abs_pos.mpr weight_two_pos.ne')) first_chord_pos

private theorem offset_two : offset 2 = 0 := by
  simp [offset, primeCross, orderedCross, sumCross, indices_two]

private theorem offset_three_pos : 0 < offset 3 := by
  have heq : offset 3 =
      (2 * |primeWeight 2 * primeWeight 2| /
        ‖1 - primePhase 3 2 * primePhase 3 2‖) / 2 := by
    norm_num [offset, primeCross, orderedCross, sumCross, indices_three]
  rw [heq]
  exact div_pos
    (div_pos (mul_pos (by norm_num)
      (abs_pos.mpr (mul_ne_zero weight_two_pos.ne' weight_two_pos.ne'))) sum_chord_pos)
    (by norm_num)

namespace Amplitude

def actual : Realization signature :=
  realize signature (fun _ _ c => ∑ q ∈ primeIndices c, primeWeight q)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ c => 2 * Real.sqrt (c : ℝ) * logLength c + 1)
    (fun e => nomatch e)

/-- Every original c, implicit binder, hypothesis and prime-power term survives. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 3 ≤ c),
    r.readout () () c ≤ 2 * Real.sqrt (c : ℝ) * logLength c

private theorem source_reconstruction :
    (type_of% (@amplitude_le)) ↔ arena.Law actual := Iff.rfl

private def source_type_reconstruction : Analysis.Reconstruction
    (type_of% (@amplitude_le)) (arena.Law actual) := .exact

private theorem actual_law : arena.Law actual := @amplitude_le

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall (c := 3) (by decide)
  change 2 * Real.sqrt (3 : ℝ) * logLength 3 + 1 ≤
    2 * Real.sqrt (3 : ℝ) * logLength 3 at h
  linarith

private theorem changed_observation :
    actual.readout () () 3 ≠ rejected.readout () () 3 := by
  intro heq
  have h := amplitude_le (c := 3) (by decide)
  change (∑ q ∈ primeIndices 3, primeWeight q) =
    2 * Real.sqrt (3 : ℝ) * logLength 3 + 1 at heq
  rw [heq] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  change (∑ q ∈ primeIndices 2, primeWeight q) ≠
    (∑ q ∈ primeIndices 3, primeWeight q)
  rw [amplitude_two]
  exact ne_of_lt amplitude_three_pos

def familyRegistration : Registration arena (type_of% (@amplitude_le)) where
  actual := actual
  bridge := source_reconstruction
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
  dependence := actual_dependence

/-- Raw source selection, bound to the accepted owner bytes identified above.
The native producer must independently check this path and full reconstruction. -/
def selection : Contract.SourceSelection where
  owner := `D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds
  definition := none
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "fn", "arg"]
    stateBinder := 0
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

/-- An exact source model, separate from the ordinary logical equivalence. -/
def source : Analysis.Source (@amplitude_le) :=
  Analysis.Source.ofRegistration (@amplitude_le) familyRegistration
    source_type_reconstruction selection

/-- The outer absent fields use the source implementation's proved family slots;
unknown is used only for the residual continuation. No audit verdict is asserted. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@amplitude_le) (type_of% (realize signature (fun _ _ c => ∑ q ∈ primeIndices c, primeWeight q) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds.amplitude_le.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds.Amplitude.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => ∑ q ∈ primeIndices c, primeWeight q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms source
#print axioms registration

end Amplitude

namespace FirstMoment

def actual : Realization signature :=
  realize signature (fun _ _ c => primeFirstMoment c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ c => (c : ℝ) * Real.sqrt (c : ℝ) * logLength c^2 + 1) (fun e => nomatch e)

/-- The complete original family law. The selected native observation retains
all original phase denominators, ordered channels and resonance conventions. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 3 ≤ c),
    r.readout () () c ≤ (c : ℝ) * Real.sqrt (c : ℝ) * logLength c^2

private theorem source_reconstruction :
    (type_of% (@firstMoment_le)) ↔ arena.Law actual := Iff.rfl

private def source_type_reconstruction : Analysis.Reconstruction
    (type_of% (@firstMoment_le)) (arena.Law actual) := .exact

private theorem actual_law : arena.Law actual := @firstMoment_le

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall (c := 3) (by decide)
  change (3 : ℝ) * Real.sqrt (3 : ℝ) * logLength 3^2 + 1 ≤ (3 : ℝ) * Real.sqrt (3 : ℝ) * logLength 3^2 at h
  linarith

private theorem changed_observation :
    actual.readout () () 3 ≠ rejected.readout () () 3 := by
  intro heq
  have h := firstMoment_le (c := 3) (by decide)
  change primeFirstMoment 3 = (3 : ℝ) * Real.sqrt (3 : ℝ) * logLength 3^2 + 1 at heq
  rw [heq] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  change primeFirstMoment 2 ≠ primeFirstMoment 3
  rw [firstMoment_two]
  exact ne_of_lt firstMoment_three_pos

def familyRegistration : Registration arena (type_of% (@firstMoment_le)) where
  actual := actual
  bridge := source_reconstruction
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
  dependence := actual_dependence

/-- Raw source selection, bound to the accepted owner bytes identified above.
The native producer must independently check this path and full reconstruction. -/
def selection : Contract.SourceSelection where
  owner := `D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds
  definition := none
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "fn", "arg"]
    stateBinder := 0
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

/-- An exact source model, separate from the ordinary logical equivalence. -/
def source : Analysis.Source (@firstMoment_le) :=
  Analysis.Source.ofRegistration (@firstMoment_le) familyRegistration
    source_type_reconstruction selection

/-- The outer absent fields use the source implementation's proved family slots;
unknown is used only for the residual continuation. No audit verdict is asserted. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@firstMoment_le) (type_of% (realize signature (fun _ _ c => primeFirstMoment c) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds.firstMoment_le.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds.FirstMoment.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => primeFirstMoment c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms source
#print axioms registration

end FirstMoment

namespace Offset

def actual : Realization signature :=
  realize signature (fun _ _ c => offset c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ c => (c : ℝ) * (2 * (c : ℝ) + 1) * logLength c^3 + 1) (fun e => nomatch e)

/-- The complete original family law. The selected native observation retains
all original phase denominators, ordered channels and resonance conventions. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 3 ≤ c),
    r.readout () () c ≤ (c : ℝ) * (2 * (c : ℝ) + 1) * logLength c^3

private theorem source_reconstruction :
    (type_of% (@offset_le)) ↔ arena.Law actual := Iff.rfl

private def source_type_reconstruction : Analysis.Reconstruction
    (type_of% (@offset_le)) (arena.Law actual) := .exact

private theorem actual_law : arena.Law actual := @offset_le

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall (c := 3) (by decide)
  change (3 : ℝ) * (2 * (3 : ℝ) + 1) * logLength 3^3 + 1 ≤ (3 : ℝ) * (2 * (3 : ℝ) + 1) * logLength 3^3 at h
  linarith

private theorem changed_observation :
    actual.readout () () 3 ≠ rejected.readout () () 3 := by
  intro heq
  have h := offset_le (c := 3) (by decide)
  change offset 3 = (3 : ℝ) * (2 * (3 : ℝ) + 1) * logLength 3^3 + 1 at heq
  rw [heq] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  change offset 2 ≠ offset 3
  rw [offset_two]
  exact ne_of_lt offset_three_pos

def familyRegistration : Registration arena (type_of% (@offset_le)) where
  actual := actual
  bridge := source_reconstruction
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
  dependence := actual_dependence

/-- Raw source selection, bound to the accepted owner bytes identified above.
The native producer must independently check this path and full reconstruction. -/
def selection : Contract.SourceSelection where
  owner := `D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds
  definition := none
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "fn", "arg"]
    stateBinder := 0
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

/-- An exact source model, separate from the ordinary logical equivalence. -/
def source : Analysis.Source (@offset_le) :=
  Analysis.Source.ofRegistration (@offset_le) familyRegistration
    source_type_reconstruction selection

/-- The outer absent fields use the source implementation's proved family slots;
unknown is used only for the residual continuation. No audit verdict is asserted. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@offset_le) (type_of% (realize signature (fun _ _ c => offset c) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds.offset_le.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds.Offset.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => offset c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms source
#print axioms registration

end Offset

end
end Reg.D5.S3.Weil.ZetaBridge.ActualPrimePhaseBounds
