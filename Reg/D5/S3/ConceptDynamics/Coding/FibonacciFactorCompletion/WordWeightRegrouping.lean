import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
import Reg.Support.FibonacciFactorWitnesses
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal192
noncomputable section

open Reg.Support.FibonacciFactorWitnesses

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ T => T) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ) (T : ℕ), Nonempty (CorePathWitnessDictionary side n K d (r.readout () () T) ≃ RetainedPathDictionary side n K d T)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  letI : IsEmpty (CorePathWitnessDictionary .lower 1 1 0 1) := ⟨by
    intro x
    exact word_weight_ne_one _ x.property.2⟩
  obtain ⟨e⟩ := h .lower 1 1 0 0
  change CorePathWitnessDictionary .lower 1 1 0 1 ≃ RetainedPathDictionary .lower 1 1 0 0 at e
  exact isEmptyElim (e.symm empty_retained)

def evidence : Registration sourceArena (type_of% @core_path_witness_dictionary_equiv) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@core_path_witness_dictionary_equiv, rejected, rejected_law⟩
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
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def core_path_witness_dictionary_equiv_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.core_path_witness_dictionary_equiv)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ T => T) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal192.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal192.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ T => T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms core_path_witness_dictionary_equiv_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal192

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal193
noncomputable section

open Reg.Support.FibonacciFactorWitnesses

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ T => T) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ) (T : ℕ), Nat.card (CorePathWitnessDictionary side n K d (r.readout () () T)) = Nat.card (RetainedPathDictionary side n K d T)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  letI : IsEmpty (CorePathWitnessDictionary .lower 1 1 0 1) := ⟨by
    intro x
    exact word_weight_ne_one _ x.property.2⟩
  letI : Finite (RetainedPathDictionary .lower 1 1 0 0) :=
    (original_weighted_path_count .lower 1 1 0 (by decide) (by decide) 0).1
  letI : Nonempty (RetainedPathDictionary .lower 1 1 0 0) := ⟨empty_retained⟩
  have positive := Nat.card_pos (α := RetainedPathDictionary .lower 1 1 0 0)
  have eq := h .lower 1 1 0 0
  change Nat.card (CorePathWitnessDictionary .lower 1 1 0 1) = _ at eq
  have zero : Nat.card (CorePathWitnessDictionary .lower 1 1 0 1) = 0 := by simp
  omega

def evidence : Registration sourceArena (type_of% @core_path_witness_dictionary_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@core_path_witness_dictionary_card, rejected, rejected_law⟩
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
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def core_path_witness_dictionary_card_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.core_path_witness_dictionary_card)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ T => T) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal193.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal193.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ T => T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms core_path_witness_dictionary_card_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal193


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal199
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => Set (ℤ → CuLetter)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)), 0 ≤ r.readout () () X

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h ∅
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.factor_rate_nonneg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.factor_rate_nonneg, rejected, rejected_law⟩
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
    refine ⟨(), MemoryLanguage .lower 1 1 (oneStepCeiling + 1),
      MemoryLanguage .lower 0 2 0, ?_⟩
    exact Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.RateWitness.actual_rate_separation

def factor_rate_nonneg_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.factor_rate_nonneg)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal199.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal199.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms factor_rate_nonneg_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal199


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal201
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => Set (ℤ → CuLetter)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ) (positive : 0 < K) (memory : K ≤ n), r.readout () () (MemoryLanguage side n K d) = sInf {s : ℝ | 0 < s ∧ SpectralBoundary.weightedRadius side n K d ((2 : ℝ) ^ (-s)) < 1}

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h .lower 1 1 0 (by norm_num) le_rfl
  have same := original_weighted_rate_abscissa .lower 1 1 0 (by norm_num) le_rfl
  have nonneg := factor_rate_nonneg (MemoryLanguage .lower 1 1 0)
  change (-1 : ℝ) = _ at impossible
  rw [← same] at impossible
  linarith

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.original_weighted_rate_abscissa) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.original_weighted_rate_abscissa, rejected, rejected_law⟩
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
    refine ⟨(), MemoryLanguage .lower 1 1 (oneStepCeiling + 1),
      MemoryLanguage .lower 0 2 0, ?_⟩
    exact Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.RateWitness.actual_rate_separation

def original_weighted_rate_abscissa_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.original_weighted_rate_abscissa)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal201.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal201.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_weighted_rate_abscissa_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal201

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.SeriesWitness
noncomputable section
open Reg.Support.FibonacciFactorWitnesses

theorem retained_zero_positive :
    0 < Nat.card (RetainedPathDictionary .lower 1 1 0 0) := by
  letI : Finite (RetainedPathDictionary .lower 1 1 0 0) :=
    (original_weighted_path_count .lower 1 1 0 (by decide) (by decide) 0).1
  letI : Nonempty (RetainedPathDictionary .lower 1 1 0 0) := ⟨empty_retained⟩
  exact Nat.card_pos

theorem factor_zero_positive :
    0 < factorCount (MemoryLanguage .lower 1 1 0) 0 := by
  have upper := (original_weighted_path_count .lower 1 1 0
    (by decide) (by decide) 0).2.2
  have positive := retained_zero_positive
  norm_num at upper
  omega

theorem factor_one_zero (X : Set (ℤ → CuLetter)) : factorCount X 1 = 0 := by
  letI : IsEmpty (FactorDictionary X 1) := ⟨fun w => word_weight_ne_one w.val w.property.2⟩
  simp [factorCount]

theorem summable_zero_base (c : ℕ → ℝ) :
    Summable (fun T : ℕ => c T * (0 : ℝ) ^ T) := by
  apply summable_of_ne_finset_zero (s := {0})
  intro T hT
  have nonzero : T ≠ 0 := by simpa using hT
  simp [zero_pow nonzero]

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.SeriesWitness

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal194
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
  realize observationSignature (fun _ T z => z ^ T) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d z : ℝ) (T : ℕ) (positive : 0 < K) (memory : K ≤ n),
    (∑' x : CorePathWitnessDictionary side n K d T, z ^ T) =
      (Nat.card (RetainedPathDictionary side n K d T) : ℝ) * r.readout () T z

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h .lower 1 1 0 1 0 (by decide) (by decide)
  have original := actual_weight_regrouping .lower 1 1 0 1 0 (by decide) (by decide)
  have positive : (0 : ℝ) < (Nat.card (RetainedPathDictionary .lower 1 1 0 0) : ℝ) := by
    exact_mod_cast SeriesWitness.retained_zero_positive
  simp only [rejected, realize, mul_zero] at impossible
  rw [impossible] at original
  norm_num at original
  linarith

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.actual_weight_regrouping) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.actual_weight_regrouping, rejected, rejected_law⟩
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

def actual_weight_regrouping_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.actual_weight_regrouping)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ T z => z ^ T) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal194.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal194.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ T z => z ^ T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_weight_regrouping_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal194

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal195
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ side : MemorySide, Σ n : ℕ, Σ K : ℕ, Σ d : ℝ, ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ p k => ∑ v : CoreVertex p.1 p.2.1 p.2.2.1 p.2.2.2.1,
      ∑ choices : Fin k → CuLetter × CoreVertex p.1 p.2.1 p.2.2.1 p.2.2.2.1,
        coreMonomial p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 k v choices) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d z : ℝ) (positive : 0 < K) (memory : K ≤ n) (nonnegative : 0 ≤ z),
    (Summable (r.readout () ⟨side, n, K, d, z⟩) ↔
      Summable (fun T : ℕ => (Nat.card (RetainedPathDictionary side n K d T) : ℝ) * z ^ T)) ∧
    ((∑' k : ℕ, ∑ v : CoreVertex side n K d,
      ∑ choices : Fin k → CuLetter × CoreVertex side n K d,
        coreMonomial side K d z k v choices) =
      ∑' T : ℕ, (Nat.card (RetainedPathDictionary side n K d T) : ℝ) * z ^ T)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h .lower 1 1 0 0 (by decide) (by decide) (by norm_num)).1.mpr
    (SeriesWitness.summable_zero_base (fun T =>
      (Nat.card (RetainedPathDictionary .lower 1 1 0 T) : ℝ)))
  simpa [rejected, realize, summable_const_iff] using impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.actual_monomial_series_regrouping) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.actual_monomial_series_regrouping, rejected, rejected_law⟩
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
    refine ⟨⟨.lower, 1, 1, 0, 0⟩, 0, 1, ?_⟩
    exact Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.SeriesWitness.core_zero_one_separation

def actual_monomial_series_regrouping_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.actual_monomial_series_regrouping)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p k => ∑ v : CoreVertex p.1 p.2.1 p.2.2.1 p.2.2.2.1,
      ∑ choices : Fin k → CuLetter × CoreVertex p.1 p.2.1 p.2.2.1 p.2.2.2.1,
        coreMonomial p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 k v choices) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal195.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal195.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ p k => ∑ v : CoreVertex p.1 p.2.1 p.2.2.1 p.2.2.2.1,
      ∑ choices : Fin k → CuLetter × CoreVertex p.1 p.2.1 p.2.2.1 p.2.2.2.1,
        coreMonomial p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 k v choices) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_monomial_series_regrouping_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal195

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal196
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ side : MemorySide, Σ n : ℕ, Σ K : ℕ, Σ d : ℝ, ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ p T => (Nat.card (RetainedPathDictionary p.1 p.2.1 p.2.2.1 p.2.2.2.1 T) : ℝ) * p.2.2.2.2 ^ T) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d z : ℝ) (positive : 0 < K) (memory : K ≤ n) (nonnegative : 0 ≤ z),
    Summable (r.readout () ⟨side, n, K, d, z⟩) ↔
      Summable (fun T : ℕ => (factorCount (MemoryLanguage side n K d) T : ℝ) * z ^ T)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h .lower 1 1 0 0 (by decide) (by decide) (by norm_num)).mpr
    (SeriesWitness.summable_zero_base (fun T =>
      (factorCount (MemoryLanguage .lower 1 1 0) T : ℝ)))
  simpa [rejected, realize, summable_const_iff] using impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.actual_factor_path_summability) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.actual_factor_path_summability, rejected, rejected_law⟩
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
    refine ⟨⟨.lower, 1, 1, 0, 0⟩, 0, 1, ?_⟩
    have positive := SeriesWitness.retained_zero_positive
    simpa [actual, realize] using (Nat.cast_ne_zero.mpr positive.ne' :
      (Nat.card (RetainedPathDictionary .lower 1 1 0 0) : ℝ) ≠ 0)

def actual_factor_path_summability_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.actual_factor_path_summability)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p T => (Nat.card (RetainedPathDictionary p.1 p.2.1 p.2.2.1 p.2.2.2.1 T) : ℝ) * p.2.2.2.2 ^ T) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal196.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal196.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ p T => (Nat.card (RetainedPathDictionary p.1 p.2.1 p.2.2.1 p.2.2.2.1 T) : ℝ) * p.2.2.2.2 ^ T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms actual_factor_path_summability_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal196

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal197
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ side : MemorySide, Σ n : ℕ, Σ K : ℕ, Σ d : ℝ, ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ p T => (factorCount (MemoryLanguage p.1 p.2.1 p.2.2.1 p.2.2.2.1) T : ℝ) * p.2.2.2.2 ^ T) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d z : ℝ) (positive : 0 < K) (memory : K ≤ n) (nonnegative : 0 ≤ z),
    Summable (r.readout () ⟨side, n, K, d, z⟩) ↔
      SpectralBoundary.weightedRadius side n K d z < 1

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have small := (original_factor_series_boundary .lower 1 1 0 0
    (by decide) (by decide) (by norm_num)).mp
      (SeriesWitness.summable_zero_base (fun T =>
        (factorCount (MemoryLanguage .lower 1 1 0) T : ℝ)))
  have impossible := (h .lower 1 1 0 0 (by decide) (by decide) (by norm_num)).mpr small
  simpa [rejected, realize, summable_const_iff] using impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.original_factor_series_boundary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.original_factor_series_boundary, rejected, rejected_law⟩
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
    refine ⟨⟨.lower, 1, 1, 0, 0⟩, 0, 1, ?_⟩
    have positive := SeriesWitness.factor_zero_positive
    simpa [actual, realize] using (Nat.cast_ne_zero.mpr positive.ne' :
      (factorCount (MemoryLanguage .lower 1 1 0) 0 : ℝ) ≠ 0)

def original_factor_series_boundary_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.original_factor_series_boundary)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p T => (factorCount (MemoryLanguage p.1 p.2.1 p.2.2.1 p.2.2.2.1) T : ℝ) * p.2.2.2.2 ^ T) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal197.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal197.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ p T => (factorCount (MemoryLanguage p.1 p.2.1 p.2.2.1 p.2.2.2.1) T : ℝ) * p.2.2.2.2 ^ T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_factor_series_boundary_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal197

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal198
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Set (ℤ → CuLetter)
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ X T => factorLogRate X T) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)), (∀ T, 0 ≤ r.readout () X T) ∧
    IsBoundedUnder (· ≤ ·) atTop (factorLogRate X)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h ∅).1 0
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.factor_log_rate_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.factor_log_rate_bounds, rejected, rejected_law⟩
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
    let X := MemoryLanguage .lower 0 2 0
    have positive : 0 < weightedFactorRate X := by
      have lower := original_positive_weighted_rate .lower 0 2 0 (by norm_num)
      dsimp [X]
      linarith
    have nonzero : ∃ T, factorLogRate X T ≠ 0 := by
      by_contra h
      push Not at h
      have same : factorLogRate X = fun _ => 0 := funext h
      have zero : weightedFactorRate X = 0 := by
        change limsup (factorLogRate X) atTop = 0
        rw [same, limsup_const]
      rw [zero] at positive
      exact lt_irrefl _ positive
    obtain ⟨T, hT⟩ := nonzero
    refine ⟨X, 0, T, ?_⟩
    change factorLogRate X 0 ≠ factorLogRate X T
    have zero : factorLogRate X 0 = 0 := by simp [factorLogRate]
    rw [zero]
    exact hT.symm

def factor_log_rate_bounds_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.factor_log_rate_bounds)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ X T => factorLogRate X T) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal198.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal198.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ X T => factorLogRate X T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms factor_log_rate_bounds_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal198

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal200
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ X : Set (ℤ → CuLetter), ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ p T => (factorCount p.1 T : ℝ) * ((2 : ℝ) ^ (-p.2)) ^ T) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (X : Set (ℤ → CuLetter)) (s : ℝ) (positive : 0 < s),
    (weightedFactorRate X < s → Summable (r.readout () ⟨X, s⟩)) ∧
    (Summable (fun T : ℕ => (factorCount X T : ℝ) * ((2 : ℝ) ^ (-s)) ^ T) →
      weightedFactorRate X ≤ s)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have zero := (original_closed_root_boundary .lower (oneStepCeiling + 1)
    (lt_add_one _)).2.2.2
  have gap : weightedFactorRate (MemoryLanguage .lower 1 1 (oneStepCeiling + 1)) < 1 := by
    rw [zero]
    norm_num
  have impossible := (h (MemoryLanguage .lower 1 1 (oneStepCeiling + 1))
    1 (by norm_num)).1 gap
  simpa [rejected, realize, summable_const_iff] using impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.factor_rate_convergence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.factor_rate_convergence, rejected, rejected_law⟩
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
    refine ⟨⟨MemoryLanguage .lower 1 1 0, 1⟩, 0, 1, ?_⟩
    have positive := SeriesWitness.factor_zero_positive
    simpa [actual, realize, SeriesWitness.factor_one_zero] using
      (Nat.cast_ne_zero.mpr positive.ne' :
        (factorCount (MemoryLanguage .lower 1 1 0) 0 : ℝ) ≠ 0)

def factor_rate_convergence_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.factor_rate_convergence)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p T => (factorCount p.1 T : ℝ) * ((2 : ℝ) ^ (-p.2)) ^ T) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal200.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal200.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ p T => (factorCount p.1 T : ℝ) * ((2 : ℝ) ^ (-p.2)) ^ T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms factor_rate_convergence_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.WordWeightRegrouping.ExactOriginal200
