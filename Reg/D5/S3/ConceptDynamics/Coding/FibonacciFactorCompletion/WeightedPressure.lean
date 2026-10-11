import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
noncomputable section

abbrev partitionSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℝ)
    (fun _ => Set (ℤ → CuLetter)) (fun _ => ℝ)

def partitionActual : Realization partitionSignature :=
  realize partitionSignature (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e)

def partitionRejected : Realization partitionSignature :=
  realize partitionSignature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

/-- These are two inhabited points in the original infinite language carrier. -/
def oneLanguage : Set (ℤ → CuLetter) := {fun _ => CuLetter.c}
def twoLanguage : Set (ℤ → CuLetter) := {fun _ => CuLetter.c, fun _ => CuLetter.u}

theorem one_occupied : oneLanguage.Nonempty := ⟨fun _ => .c, rfl⟩

theorem constant_singleton_occurs (a : CuLetter) : Occurs (fun _ => a) [a] := by
  refine ⟨0, ?_⟩
  intro i
  simp

def oneWord : LengthDictionary oneLanguage 1 :=
  ⟨[.c], ⟨fun _ => .c, rfl, constant_singleton_occurs .c⟩, rfl⟩

def twoWord (a : CuLetter) : LengthDictionary twoLanguage 1 :=
  ⟨[a], ⟨fun _ => a, by cases a <;> simp [twoLanguage], constant_singleton_occurs a⟩, rfl⟩

theorem one_word_unique (w : LengthDictionary oneLanguage 1) : w = oneWord := by
  apply Subtype.ext
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp w.property.2
  rcases w.property.1 with ⟨ω, hω, i, hi⟩
  have hc : ω = fun _ => CuLetter.c := hω
  have h := hi ⟨0, by simp [ha]⟩
  simp only [hc, ha, List.getElem_cons_zero] at h
  simpa [oneWord, h] using ha

theorem partition_one : partitionSum oneLanguage 1 0 = 1 := by
  classical
  letI : Unique (LengthDictionary oneLanguage 1) := ⟨⟨oneWord⟩, one_word_unique⟩
  simp [partitionSum, wordTerm]

theorem partition_two : partitionSum twoLanguage 1 0 = 2 := by
  classical
  have bij : Function.Bijective twoWord := by
    constructor
    · intro a b h
      have hh := congrArg Subtype.val h
      simpa [twoWord] using hh
    · intro w
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp w.property.2
      exact ⟨a, Subtype.ext ha.symm⟩
  have card := Fintype.card_congr (Equiv.ofBijective twoWord bij)
  have letters : Fintype.card CuLetter = 2 := by decide
  simp [partitionSum, wordTerm, ← card, letters]

theorem partition_actual_dependence : ObservationalDependence partitionSignature partitionActual := by
  intro i
  refine ⟨⟨1, 0⟩, oneLanguage, twoLanguage, ?_⟩
  change partitionSum oneLanguage 1 0 ≠ partitionSum twoLanguage 1 0
  rw [partition_one, partition_two]
  norm_num

abbrev positiveArena : Arena.{0,0,0,0,0} where
  signature := partitionSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) (k : ℕ) (θ : ℝ),
    0 < r.readout () ⟨k, θ⟩ X

abbrev submultiplicativeArena : Arena.{0,0,0,0,0} where
  signature := partitionSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (k j : ℕ) (θ : ℝ),
    partitionSum X (k + j) θ ≤ r.readout () ⟨k, θ⟩ X * partitionSum X j θ

abbrev lowerArena : Arena.{0,0,0,0,0} where
  signature := partitionSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) (k : ℕ) (θ : ℝ),
    (2 : ℝ) ^ (-20 * |θ| * (k : ℝ)) ≤ r.readout () ⟨k, θ⟩ X

abbrev shiftArena : Arena.{0,0,0,0,0} where
  signature := partitionSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (k : ℕ) (θ a : ℝ) (nonnegative : 0 ≤ a),
    (2 : ℝ) ^ (-20 * a * (k : ℝ)) * partitionSum X k θ ≤ partitionSum X k (θ+a) ∧
    partitionSum X k (θ+a) ≤ (2 : ℝ) ^ (-6 * a * (k : ℝ)) * r.readout () ⟨k, θ⟩ X

theorem positive_rejected : ¬ positiveArena.Law partitionRejected := by
  intro h
  have hh := h oneLanguage one_occupied 1 0
  norm_num [partitionRejected, realize] at hh

theorem submultiplicative_rejected : ¬ submultiplicativeArena.Law partitionRejected := by
  intro h
  have hh := h oneLanguage 1 0 0
  norm_num [partitionRejected, realize, partition_one] at hh

theorem lower_rejected : ¬ lowerArena.Law partitionRejected := by
  intro h
  have hh := h oneLanguage one_occupied 1 0
  norm_num [partitionRejected, realize] at hh

theorem shift_rejected : ¬ shiftArena.Law partitionRejected := by
  intro h
  have hh := (h oneLanguage 1 0 0 (by norm_num)).2
  norm_num [partitionRejected, realize, partition_one] at hh

def positiveRegistration : Registration positiveArena (type_of% @partition_positive) where
  actual := partitionActual
  bridge := Iff.rfl
  variation := ⟨@partition_positive, partitionRejected, positive_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    positiveArena.Law partitionActual partitionRejected positive_rejected
  dependence := partition_actual_dependence

def partition_positive_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_positive)
      (type_of% (realize.{0,0,0,0,0} partitionSignature
        (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_positive_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.positiveRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨positiveArena⟩
  objectArena := .source ⟨positiveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source positiveArena ⟨positiveRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} partitionSignature
    (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms positiveRegistration
#print axioms partition_positive_registration

def submultiplicativeRegistration : Registration submultiplicativeArena (type_of% @partition_submultiplicative) where
  actual := partitionActual
  bridge := Iff.rfl
  variation := ⟨@partition_submultiplicative, partitionRejected, submultiplicative_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    submultiplicativeArena.Law partitionActual partitionRejected submultiplicative_rejected
  dependence := partition_actual_dependence

def partition_submultiplicative_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_submultiplicative)
      (type_of% (realize.{0,0,0,0,0} partitionSignature
        (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_submultiplicative_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.submultiplicativeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨submultiplicativeArena⟩
  objectArena := .source ⟨submultiplicativeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source submultiplicativeArena ⟨submultiplicativeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} partitionSignature
    (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms submultiplicativeRegistration
#print axioms partition_submultiplicative_registration

def lowerRegistration : Registration lowerArena (type_of% @partition_lower_bound) where
  actual := partitionActual
  bridge := Iff.rfl
  variation := ⟨@partition_lower_bound, partitionRejected, lower_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    lowerArena.Law partitionActual partitionRejected lower_rejected
  dependence := partition_actual_dependence

def partition_lower_bound_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_lower_bound)
      (type_of% (realize.{0,0,0,0,0} partitionSignature
        (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_lower_bound_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.lowerRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨lowerArena⟩
  objectArena := .source ⟨lowerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lowerArena ⟨lowerRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} partitionSignature
    (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms lowerRegistration
#print axioms partition_lower_bound_registration

def shiftRegistration : Registration shiftArena (type_of% @partition_shift_bounds) where
  actual := partitionActual
  bridge := Iff.rfl
  variation := ⟨@partition_shift_bounds, partitionRejected, shift_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    shiftArena.Law partitionActual partitionRejected shift_rejected
  dependence := partition_actual_dependence

def partition_shift_bounds_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_shift_bounds)
      (type_of% (realize.{0,0,0,0,0} partitionSignature
        (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.partition_shift_bounds_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.shiftRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨shiftArena⟩
  objectArena := .source ⟨shiftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source shiftArena ⟨shiftRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} partitionSignature
    (fun _ p X => partitionSum X p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms shiftRegistration
#print axioms partition_shift_bounds_registration

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
