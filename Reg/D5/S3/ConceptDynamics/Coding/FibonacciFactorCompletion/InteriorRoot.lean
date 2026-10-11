import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.MemoryGraph
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal94
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ side : MemorySide, Σ n : ℕ, Σ K : ℕ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ), ∀ (z : ℝ) (hz : 0 < z), ENNReal.ofReal (z^6) ≤ r.readout () ⟨side, n, K, d⟩ z

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h .lower 2 2 0 1 (by norm_num)
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_spectral_positive) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_spectral_positive, rejected, rejected_law⟩
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
    refine ⟨⟨MemorySide.lower, 2, 2, 0⟩, 1, 2, ?_⟩
    intro eq
    have grow := original_radius_strict_increase .lower 2 2 0
      (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
      (by norm_num : (2 : ℝ) ∈ Set.Ioi 0) (by norm_num : (1 : ℝ) < 2)
    have same := congrArg ENNReal.toReal eq
    exact (ne_of_lt grow) same

def original_spectral_positive_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_spectral_positive)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal94.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal94.evidence
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
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_spectral_positive_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal94

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal96
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ side : MemorySide, Σ n : ℕ, Σ K : ℕ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ), ∀ (x y : ℝ) (xp : 0 < x) (xy : x ≤ y),
    (y/x)^6 * radiusValue side n K d x ≤ r.readout () ⟨side, n, K, d⟩ y ∧
    radiusValue side n K d y ≤ (y/x)^20 * radiusValue side n K d x

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h .lower 2 2 0 1 1 (by norm_num) le_rfl).1
  have nonnegative := ENNReal.toReal_nonneg (a := weightedRadius .lower 2 2 0 1)
  norm_num [rejected, realize] at impossible
  change 0 ≤ radiusValue .lower 2 2 0 1 at nonnegative
  linarith

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_radius_scaling) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_radius_scaling, rejected, rejected_law⟩
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
    refine ⟨⟨MemorySide.lower, 2, 2, 0⟩, 1, 2, ?_⟩
    exact ne_of_lt (original_radius_strict_increase .lower 2 2 0
      (by norm_num) (by norm_num) (by norm_num))

def original_radius_scaling_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_radius_scaling)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal96.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal96.evidence
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
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_radius_scaling_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal96

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal97
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ side : MemorySide, Σ n : ℕ, Σ K : ℕ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ), StrictMonoOn (r.readout () ⟨side, n, K, d⟩) (Set.Ioi 0)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h .lower 2 2 0 (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
    (by norm_num : (2 : ℝ) ∈ Set.Ioi 0) (by norm_num : (1 : ℝ) < 2)
  exact (lt_irrefl (0 : ℝ)) impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_radius_strict_increase) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_radius_strict_increase, rejected, rejected_law⟩
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
    refine ⟨⟨MemorySide.lower, 2, 2, 0⟩, 1, 2, ?_⟩
    exact ne_of_lt (original_radius_strict_increase .lower 2 2 0
      (by norm_num) (by norm_num) (by norm_num))

def original_radius_strict_increase_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_radius_strict_increase)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal97.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal97.evidence
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
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_radius_strict_increase_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal97

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal98
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ side : MemorySide, Σ n : ℕ, Σ K : ℕ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => Matrix (CoreVertex p.1 p.2.1 p.2.2.1 p.2.2.2) (CoreVertex p.1 p.2.1 p.2.2.1 p.2.2.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
        (fun _ p z => complexAdjacency p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ p _ => complexAdjacency p.1 p.2.1 p.2.2.1 p.2.2.2 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ), r.readout () ⟨side, n, K, d⟩ 0 = 0 ∧ Continuous (r.readout () ⟨side, n, K, d⟩)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have zero := (h .lower 2 2 0).1
  have lower := original_spectral_positive .lower 2 2 0 1 (by norm_num)
  change complexAdjacency .lower 2 2 0 1 = 0 at zero
  simp only [weightedRadius, zero, spectrum.spectralRadius_zero] at lower
  norm_num at lower

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_adjacency_zero_continuous) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_adjacency_zero_continuous, rejected, rejected_law⟩
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
    refine ⟨⟨MemorySide.lower, 2, 2, 0⟩, 0, 1, ?_⟩
    intro eq
    change complexAdjacency .lower 2 2 0 0 = complexAdjacency .lower 2 2 0 1 at eq
    have zero := (original_adjacency_zero_continuous .lower 2 2 0).1
    have onezero := eq.symm.trans zero
    have lower := original_spectral_positive .lower 2 2 0 1 (by norm_num)
    simp only [weightedRadius, onezero, spectrum.spectralRadius_zero] at lower
    norm_num at lower

def original_adjacency_zero_continuous_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_adjacency_zero_continuous)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => complexAdjacency p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal98.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal98.evidence
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
        (fun _ p z => complexAdjacency p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_adjacency_zero_continuous_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal98

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal99
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ side : MemorySide, Σ n : ℕ, Σ K : ℕ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ z => if z = 0 then 0 else 1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ), ContinuousOn (r.readout () ⟨side, n, K, d⟩) (Set.Ici 0)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have hc := h .lower 2 2 0 (0 : ℝ) (by simp)
  change ContinuousWithinAt (fun z : ℝ => if z = 0 then (0 : ℝ) else 1) (Set.Ici 0) 0 at hc
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp hc (1/2) (by norm_num)
  have hp : 0 < δ / 2 := by linarith
  have close : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hp]
    linarith
  have impossible := hd hp.le close
  norm_num [ne_of_gt hp] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_radius_continuous) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_radius_continuous, rejected, rejected_law⟩
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
    refine ⟨⟨MemorySide.lower, 2, 2, 0⟩, 1, 2, ?_⟩
    exact ne_of_lt (original_radius_strict_increase .lower 2 2 0
      (by norm_num) (by norm_num) (by norm_num))

def original_radius_continuous_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_radius_continuous)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal99.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal99.evidence
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
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_radius_continuous_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal99

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal100
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ side : MemorySide, Σ n : ℕ, Σ K : ℕ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ), ∀ (hK : 2 ≤ K) (memory : K ≤ n), 1 < r.readout () ⟨side, n, K, d⟩ 1

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h .lower 2 2 0 le_rfl le_rfl
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_spectral_at_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_spectral_at_one, rejected, rejected_law⟩
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
    refine ⟨⟨MemorySide.lower, 2, 2, 0⟩, 1, 2, ?_⟩
    exact ne_of_lt (original_radius_strict_increase .lower 2 2 0
      (by norm_num) (by norm_num) (by norm_num))

def original_spectral_at_one_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_spectral_at_one)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal100.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal100.evidence
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
        (fun _ p z => radiusValue p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_spectral_at_one_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal100

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal101
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ side : MemorySide, Σ n : ℕ, Σ K : ℕ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ), ∀ (hK : 2 ≤ K) (memory : K ≤ n),
    ∃! z : ℝ, 0 < z ∧ z < 1 ∧ r.readout () ⟨side, n, K, d⟩ z = 1

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨z, hz, _⟩ := h .lower 2 2 0 le_rfl le_rfl
  have impossible := hz.2.2
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_interior_root) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_interior_root, rejected, rejected_law⟩
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
    refine ⟨⟨MemorySide.lower, 2, 2, 0⟩, 1, 2, ?_⟩
    intro eq
    have grow := original_radius_strict_increase .lower 2 2 0
      (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
      (by norm_num : (2 : ℝ) ∈ Set.Ioi 0) (by norm_num : (1 : ℝ) < 2)
    have same := congrArg ENNReal.toReal eq
    exact (ne_of_lt grow) same

def original_interior_root_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_interior_root)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal101.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal101.evidence
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
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_interior_root_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal101

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal102
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ side : MemorySide, Σ n : ℕ, Σ K : ℕ, ℝ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ), ∀ (hK : 2 ≤ K) (memory : K ≤ n),
    ∃! z : ℝ, 0 < z ∧ z < 1 ∧ r.readout () ⟨side, n, K, d⟩ z = 1 ∧
      weightedFactorRate (MemoryLanguage side n K d) = -Real.logb 2 z

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨z, hz, _⟩ := h .lower 2 2 0 le_rfl le_rfl
  have impossible := hz.2.2.1
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_weighted_interior_root) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_weighted_interior_root, rejected, rejected_law⟩
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
    refine ⟨⟨MemorySide.lower, 2, 2, 0⟩, 1, 2, ?_⟩
    intro eq
    have grow := original_radius_strict_increase .lower 2 2 0
      (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
      (by norm_num : (2 : ℝ) ∈ Set.Ioi 0) (by norm_num : (1 : ℝ) < 2)
    have same := congrArg ENNReal.toReal eq
    exact (ne_of_lt grow) same

def original_weighted_interior_root_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_weighted_interior_root)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal102.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal102.evidence
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
        (fun _ p z => weightedRadius p.1 p.2.1 p.2.2.1 p.2.2.2 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_weighted_interior_root_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal102

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal103
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ K : ℕ, Σ d : ℝ, Σ side : MemorySide, ℕ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun p => ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.2.2.1 p.2.2.2 p.1 p.2.1 z) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (K : ℕ) (d : ℝ) (hK : 2 ≤ K),
  ∃ roots : MemorySide → ℕ → ℝ,
    (∀ side n, K ≤ n → 0 < roots side n ∧ roots side n < 1 ∧
      r.readout () ⟨K, d, side, n⟩ (roots side n) = (1 : ℝ≥0∞) ∧
      weightedFactorRate (MemoryLanguage side n K d) = -Real.logb 2 (roots side n)) ∧
    (∀ n, K ≤ n → -Real.logb 2 (roots .lower n) ≤ weightedFactorRate (AuxiliaryLanguage K d) ∧
      weightedFactorRate (AuxiliaryLanguage K d) ≤ -Real.logb 2 (roots .upper n)) ∧
    MonotoneOn (fun n => -Real.logb 2 (roots .lower n)) (Set.Ici K) ∧
    AntitoneOn (fun n => -Real.logb 2 (roots .upper n)) (Set.Ici K)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  obtain ⟨roots, properties, _⟩ := h 2 0 le_rfl
  have impossible := (properties .lower 2 le_rfl).2.2.1
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_root_rate_families) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_root_rate_families, rejected, rejected_law⟩
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
    refine ⟨⟨2, 0, MemorySide.lower, 2⟩, 1, 2, ?_⟩
    intro eq
    have grow := original_radius_strict_increase .lower 2 2 0
      (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
      (by norm_num : (2 : ℝ) ∈ Set.Ioi 0) (by norm_num : (1 : ℝ) < 2)
    have same := congrArg ENNReal.toReal eq
    exact (ne_of_lt grow) same

def original_root_rate_families_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_root_rate_families)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p z => weightedRadius p.2.2.1 p.2.2.2 p.1 p.2.1 z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal103.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal103.evidence
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
        (fun _ p z => weightedRadius p.2.2.1 p.2.2.2 p.1 p.2.1 z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 1, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "fn", "arg", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_root_rate_families_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal103


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal91
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
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ) (hK : 2 ≤ K), (1 : ℝ)/58 ≤ r.readout () () (MemoryLanguage side n K d)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := h .lower 0 2 0 (by norm_num)
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_positive_weighted_rate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_positive_weighted_rate, rejected, rejected_law⟩
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

def original_positive_weighted_rate_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_positive_weighted_rate)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal91.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal91.evidence
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_positive_weighted_rate_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal91


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal92
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
  Law r := ∀ (n K : ℕ) (d : ℝ), weightedFactorRate (MemoryLanguage .lower n K d) ≤ r.readout () () (MemoryLanguage .lower (n+1) K d) ∧ weightedFactorRate (MemoryLanguage .lower (n+1) K d) ≤ weightedFactorRate (AuxiliaryLanguage K d) ∧ weightedFactorRate (AuxiliaryLanguage K d) ≤ weightedFactorRate (MemoryLanguage .upper (n+1) K d) ∧ weightedFactorRate (MemoryLanguage .upper (n+1) K d) ≤ weightedFactorRate (MemoryLanguage .upper n K d)

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h 0 2 0).1
  change weightedFactorRate (MemoryLanguage .lower 0 2 0) ≤ -1 at impossible
  have nonneg := factor_rate_nonneg (MemoryLanguage .lower 0 2 0)
  linarith

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_memory_rate_nesting) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_memory_rate_nesting, rejected, rejected_law⟩
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

def original_memory_rate_nesting_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_memory_rate_nesting)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal92.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal92.evidence
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_memory_rate_nesting_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal92

open Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetCodebook.SetWitness


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal85
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => Set (ℤ → CuLetter)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ _ K => LowCapLanguage K) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => Set.univ) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d : ℝ) (positive : 0 < K), r.readout () () K ⊆ MemoryLanguage side n K d

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have bad := h .lower 0 1 0 (by norm_num) (show (fun _ : ℤ => CuLetter.c) ∈ Set.univ from trivial)
  exact bad.1 0 (fun _ => rfl)

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_low_cap_inclusion) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_low_cap_inclusion, rejected, rejected_law⟩
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
    refine ⟨(), 1, 2, ?_⟩
    change LowCapLanguage 1 ≠ LowCapLanguage 2
    intro h
    exact spike_not_low_one (h ▸ spike_low_two)

def original_low_cap_inclusion_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_low_cap_inclusion)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ _ K => LowCapLanguage K) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal85.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal85.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ _ K => LowCapLanguage K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_low_cap_inclusion_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal85


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal88
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : ℕ, ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => Set (ℤ → CuLetter)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ p K => MemoryLanguage .upper p.1 K p.2) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => ∅) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (n K : ℕ) (d : ℝ),
    MemoryLanguage .lower n K d ⊆ MemoryLanguage .lower (n+1) K d ∧
    MemoryLanguage .lower (n+1) K d ⊆ AuxiliaryLanguage K d ∧
    AuxiliaryLanguage K d ⊆ MemoryLanguage .upper (n+1) K d ∧
    MemoryLanguage .upper (n+1) K d ⊆ r.readout () ⟨n, d⟩ K

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  exact (h 0 1 0).2.2.2 (all_u_memory .upper 1 1 0 (by norm_num))

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_memory_language_nesting) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_memory_language_nesting, rejected, rejected_law⟩
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
    exact ⟨⟨0, hSide .high + 1⟩, 1, 2, upper_separation⟩

def original_memory_language_nesting_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.original_memory_language_nesting)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ p K => MemoryLanguage .upper p.1 K p.2) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal88.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal88.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ p K => MemoryLanguage .upper p.1 K p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_memory_language_nesting_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.InteriorRoot.ExactOriginal88
