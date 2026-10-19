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

def submultiplicativeRegistration : Registration submultiplicativeArena (type_of% @partition_submultiplicative) where
  actual := partitionActual
  bridge := Iff.rfl
  variation := ⟨@partition_submultiplicative, partitionRejected, submultiplicative_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    submultiplicativeArena.Law partitionActual partitionRejected submultiplicative_rejected
  dependence := partition_actual_dependence

def lowerRegistration : Registration lowerArena (type_of% @partition_lower_bound) where
  actual := partitionActual
  bridge := Iff.rfl
  variation := ⟨@partition_lower_bound, partitionRejected, lower_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    lowerArena.Law partitionActual partitionRejected lower_rejected
  dependence := partition_actual_dependence

def shiftRegistration : Registration shiftArena (type_of% @partition_shift_bounds) where
  actual := partitionActual
  bridge := Iff.rfl
  variation := ⟨@partition_shift_bounds, partitionRejected, shift_rejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    shiftArena.Law partitionActual partitionRejected shift_rejected
  dependence := partition_actual_dependence

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal173
noncomputable section


abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => Set (ℤ → CuLetter)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => Set (ℤ → CuLetter)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) (k : ℕ), Nonempty (LengthDictionary (r.readout () () X) k)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨w⟩ := h {fun _ => .u} ⟨(fun _ => .u), Set.mem_singleton _⟩ 0
  obtain ⟨ω, hω, _⟩ := w.property.1
  exact hω

def evidence : Registration sourceArena (type_of% @length_dictionary_nonempty) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@length_dictionary_nonempty, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), {fun _ => .u}, {fun _ => .c}, ?_⟩
    intro eq
    change ({fun _ : ℤ => CuLetter.u} : Set (ℤ → CuLetter)) = {fun _ => .c} at eq
    have member : (fun _ : ℤ => CuLetter.u) ∈ ({fun _ => CuLetter.c} : Set (ℤ → CuLetter)) := by
      rw [← eq]
      exact Set.mem_singleton _
    have same := Set.mem_singleton_iff.mp member
    have impossible := congrFun same 0
    cases impossible

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal173

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal182
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Set (ℤ → CuLetter)
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ X s => pressure X s) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ X s => pressure X s + 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) (θ a : ℝ) (nonnegative : 0 ≤ a), (r.readout () X θ - 20*a ≤ pressure X (θ+a)) ∧ (pressure X (θ+a) ≤ pressure X θ - 6*a)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h Set.univ ⟨(fun _ => .c), Set.mem_univ _⟩ 0 0 le_rfl).1
  change pressure Set.univ 0 + 1 - 20*0 ≤ pressure Set.univ (0+0) at impossible
  norm_num at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_shift_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_shift_bounds, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨Set.univ, 0, 1, ?_⟩
    exact ne_of_gt (pressure_strictAnti Set.univ ⟨(fun _ => .c), Set.mem_univ _⟩ (by norm_num : (0 : ℝ) < 1))

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal182

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal185
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Set (ℤ → CuLetter)
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ X s => pressure X s) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty), 0 ≤ r.readout () X 0

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h Set.univ ⟨(fun _ => .c), Set.mem_univ _⟩
  change (0 : ℝ) ≤ -1 at impossible
  norm_num at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_zero_nonneg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_zero_nonneg, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨Set.univ, 0, 1, ?_⟩
    exact ne_of_gt (pressure_strictAnti Set.univ ⟨(fun _ => .c), Set.mem_univ _⟩ (by norm_num : (0 : ℝ) < 1))

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal185

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal191
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Set (ℤ → CuLetter)
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ X s => pressure X s) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) (θ : ℝ), r.readout () X θ = 0 ↔ θ = weightedFactorRate X

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h Set.univ ⟨(fun _ => .c), Set.mem_univ _⟩ (weightedFactorRate Set.univ)).mpr rfl
  change (1 : ℝ) = 0 at impossible
  norm_num at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_zero_iff_rate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_zero_iff_rate, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨Set.univ, 0, 1, ?_⟩
    exact ne_of_gt (pressure_strictAnti Set.univ ⟨(fun _ => .c), Set.mem_univ _⟩ (by norm_num : (0 : ℝ) < 1))

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal191

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.AnalyticWitnesses
noncomputable section
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral

def language : Set (ℤ → CuLetter) := {fun _ => .u}
theorem occupied : language.Nonempty := ⟨fun _ => .u, rfl⟩
def emptyWord : OccurringWord language := ⟨[], fun _ => .u, rfl, 0, by intro i; exact Fin.elim0 i⟩
def unitWord : OccurringWord language := ⟨[.u], fun _ => .u, rfl, 0, by intro i; simp⟩
theorem terms_differ : wordTerm 1 emptyWord.val ≠ wordTerm 1 unitWord.val := by
  norm_num [wordTerm, emptyWord, unitWord, wordWeight, Real.rpow_neg_one]

theorem negative : pressure language (pressure language 0 + 1) < 0 := by
  have nonnegative := pressure_zero_nonneg language occupied
  have h := (pressure_shift_bounds language occupied 0 (pressure language 0 + 1)
    (by linarith)).2
  simp only [zero_add] at h
  linarith

theorem partitions_differ : ∃ k : ℕ,
    partitionSum language 0 (pressure language 0 + 1) ≠
      partitionSum language k (pressure language 0 + 1) := by
  by_contra h
  push_neg at h
  have hs := negative_pressure_summable language occupied _ negative
  have same : (fun k : ℕ => partitionSum language k (pressure language 0 + 1)) =
      (fun _ : ℕ => partitionSum language 0 (pressure language 0 + 1)) := by
    funext k
    exact (h k).symm
  rw [same, summable_const_iff] at hs
  exact (ne_of_gt (partition_positive language occupied 0 _)) hs
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.AnalyticWitnesses

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal186
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Set (ℤ → CuLetter)
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
        (fun _ X η => pressure X η) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty),
  ∃! η : ℝ, 0 ≤ η ∧ r.readout () X η = (0 : ℝ)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨η, hη, _⟩ := h Set.univ ⟨(fun _ => .u), Set.mem_univ _⟩
  have impossible := hη.2
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_unique_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.pressure_unique_zero, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨Set.univ, 0, 1, ?_⟩
    exact ne_of_gt (pressure_strictAnti Set.univ ⟨(fun _ => .u), Set.mem_univ _⟩
      (by norm_num : (0 : ℝ) < 1))

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal186

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal187
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ X : Set (ℤ → CuLetter), ℝ
  State := fun p => OccurringWord p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
        (fun _ p w => wordTerm p.2 w.val) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (θ : ℝ), ((∑' w : OccurringWord X, ENNReal.ofReal (r.readout () ⟨X, θ⟩ w)) = ∑' k : ℕ, ENNReal.ofReal (partitionSum X k θ)) ∧ ((∑' w : OccurringWord X, ENNReal.ofReal (wordTerm θ w.val)) = ∑' T : ℕ, ENNReal.ofReal ((factorCount X T : ℝ) * ((2 : ℝ) ^ (-θ)) ^ T))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h AnalyticWitnesses.language 0).1
  have eqn := (whole_series_regrouping AnalyticWitnesses.language 0).1
  rw [whole_series_nonpositive AnalyticWitnesses.language AnalyticWitnesses.occupied 0 le_rfl] at eqn
  simp only [rejected, realize, ENNReal.ofReal_zero, tsum_zero] at impossible
  exact ENNReal.zero_ne_top (impossible.trans eqn.symm)

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.whole_series_regrouping) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.whole_series_regrouping, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨AnalyticWitnesses.language, 1⟩, AnalyticWitnesses.emptyWord, AnalyticWitnesses.unitWord, ?_⟩
    exact AnalyticWitnesses.terms_differ

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal187

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal188
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ X : Set (ℤ → CuLetter), ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
        (fun _ p k => partitionSum p.1 k p.2) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (θ : ℝ), (Summable (fun k : ℕ => r.readout () ⟨X, θ⟩ k) ↔ (∑' w : OccurringWord X, ENNReal.ofReal (wordTerm θ w.val)) < ∞) ∧ (Summable (fun T : ℕ => (factorCount X T : ℝ) * ((2 : ℝ) ^ (-θ)) ^ T) ↔ (∑' w : OccurringWord X, ENNReal.ofReal (wordTerm θ w.val)) < ∞)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h AnalyticWitnesses.language 0).1.mp (by
    change Summable (fun _ : ℕ => (0 : ℝ))
    exact summable_zero)
  rw [whole_series_nonpositive AnalyticWitnesses.language AnalyticWitnesses.occupied 0 le_rfl] at impossible
  exact (lt_irrefl _) impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.whole_series_finiteness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.whole_series_finiteness, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨k, hk⟩ := AnalyticWitnesses.partitions_differ
    exact ⟨⟨AnalyticWitnesses.language, pressure AnalyticWitnesses.language 0 + 1⟩, 0, k, hk⟩

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal188

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal189
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ X : Set (ℤ → CuLetter), ℝ
  State := fun p => OccurringWord p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
        (fun _ p w => wordTerm p.2 w.val) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) (θ : ℝ) (nonpositive : θ ≤ 0), (∑' w : OccurringWord X, ENNReal.ofReal (r.readout () ⟨X, θ⟩ w)) = ∞

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h AnalyticWitnesses.language AnalyticWitnesses.occupied 0 le_rfl
  simpa [rejected, realize] using impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.whole_series_nonpositive) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.whole_series_nonpositive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨AnalyticWitnesses.language, 1⟩, AnalyticWitnesses.emptyWord, AnalyticWitnesses.unitWord, ?_⟩
    exact AnalyticWitnesses.terms_differ

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal189

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal190
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ X : Set (ℤ → CuLetter), ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
        (fun _ p k => partitionSum p.1 k p.2) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) (θ : ℝ) (negative : pressure X θ < 0), Summable (fun k : ℕ => r.readout () ⟨X, θ⟩ k)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h AnalyticWitnesses.language AnalyticWitnesses.occupied
    (pressure AnalyticWitnesses.language 0 + 1) AnalyticWitnesses.negative
  change Summable (fun _ : ℕ => (1 : ℝ)) at impossible
  simpa only [summable_const_iff, one_ne_zero] using impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.negative_pressure_summable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.negative_pressure_summable, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    obtain ⟨k, hk⟩ := AnalyticWitnesses.partitions_differ
    exact ⟨⟨AnalyticWitnesses.language, pressure AnalyticWitnesses.language 0 + 1⟩, 0, k, hk⟩

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal190

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal179
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := ℕ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ k x => x / (k : ℝ)) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty)
    (θ : ℝ) (k : ℕ), -20 * |θ| ≤ r.readout () k (logPartition X θ k)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h Set.univ ⟨(fun _ => .u), Set.mem_univ _⟩ 0 0
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.log_quotient_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.log_quotient_lower_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    norm_num [actual, realize]

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal179

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.AnalyticWitnesses
noncomputable section

theorem pressures_differ : pressure language 0 ≠ pressure language 1 := by
  have bound := (pressure_shift_bounds language occupied 0 1 (by norm_num)).2
  norm_num only [zero_add, mul_one] at bound
  linarith

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.AnalyticWitnesses

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal183
noncomputable section

abbrev observationSignature := ExactOriginal182.observationSignature

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ X θ => pressure X θ) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ θ => 21 * θ) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty),
    LipschitzWith 20 (r.readout () X)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h AnalyticWitnesses.language AnalyticWitnesses.occupied).dist_le_mul 0 1
  norm_num [rejected, realize, Real.dist_eq] at impossible

def evidence : Registration sourceArena (type_of% @pressure_lipschitz) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pressure_lipschitz, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨AnalyticWitnesses.language, 0, 1, AnalyticWitnesses.pressures_differ⟩

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal183

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal184
noncomputable section

abbrev observationSignature := ExactOriginal183.observationSignature

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ X θ => pressure X θ) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty),
    StrictAnti (r.readout () X)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h AnalyticWitnesses.language AnalyticWitnesses.occupied
    (by norm_num : (0 : ℝ) < 1)
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @pressure_strictAnti) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pressure_strictAnti, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨AnalyticWitnesses.language, 0, 1, AnalyticWitnesses.pressures_differ⟩

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal184

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.AnalyticWitnesses
noncomputable section

theorem log_partitions_differ : ∃ k : ℕ,
    logPartition language (pressure language 0 + 1) 0 ≠
      logPartition language (pressure language 0 + 1) k := by
  obtain ⟨k, hk⟩ := partitions_differ
  refine ⟨k, ?_⟩
  intro h
  exact hk (Real.logb_injOn_pos (by norm_num : (1 : ℝ) < 2)
    (partition_positive language occupied 0 _) (partition_positive language occupied k _) h)

theorem log_quotients_differ : ∃ k : ℕ,
    logPartition language (pressure language 0 + 1) 0 / (0 : ℝ) ≠
      logPartition language (pressure language 0 + 1) k / (k : ℝ) := by
  by_contra h
  push_neg at h
  have same : (fun k : ℕ => logPartition language (pressure language 0 + 1) k / (k : ℝ)) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext k
    simpa only [div_zero] using (h k).symm
  have convergence := pressure_tendsto language occupied (pressure language 0 + 1)
  rw [same] at convergence
  have zero_pressure : pressure language (pressure language 0 + 1) = 0 :=
    tendsto_nhds_unique convergence tendsto_const_nhds
  exact (ne_of_lt negative) zero_pressure

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.AnalyticWitnesses

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal177
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : Set (ℤ → CuLetter), ℝ)
    (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature
    (fun _ p k => logPartition p.1 p.2 k) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) (θ : ℝ),
    Subadditive (r.readout () ⟨X, θ⟩)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h AnalyticWitnesses.language AnalyticWitnesses.occupied 0 0 0
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @log_partition_subadditive) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@log_partition_subadditive, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := by
    intro i
    obtain ⟨k, hk⟩ := AnalyticWitnesses.log_partitions_differ
    exact ⟨⟨AnalyticWitnesses.language, pressure AnalyticWitnesses.language 0 + 1⟩, 0, k, hk⟩

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal177

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal180
noncomputable section
open Filter Topology

abbrev observationSignature := ExactOriginal177.observationSignature

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature
    (fun _ p k => logPartition p.1 p.2 k / (k : ℝ)) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ p _ => pressure p.1 p.2 + 1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (occupied : X.Nonempty) (θ : ℝ),
    Tendsto (r.readout () ⟨X, θ⟩) atTop (𝓝 (pressure X θ))

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have convergence := h AnalyticWitnesses.language AnalyticWitnesses.occupied 0
  change Tendsto (fun _ : ℕ => pressure AnalyticWitnesses.language 0 + 1) atTop
    (𝓝 (pressure AnalyticWitnesses.language 0)) at convergence
  have impossible : pressure AnalyticWitnesses.language 0 =
      pressure AnalyticWitnesses.language 0 + 1 :=
    tendsto_nhds_unique convergence tendsto_const_nhds
  linarith

def evidence : Registration sourceArena (type_of% @pressure_tendsto) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pressure_tendsto, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law actual rejected rejected_law
  dependence := by
    intro i
    obtain ⟨k, hk⟩ := AnalyticWitnesses.log_quotients_differ
    refine ⟨⟨AnalyticWitnesses.language, pressure AnalyticWitnesses.language 0 + 1⟩, 0, k, ?_⟩
    simpa only [actual, realize, Nat.cast_zero] using hk

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WeightedPressure.ExactOriginal180
