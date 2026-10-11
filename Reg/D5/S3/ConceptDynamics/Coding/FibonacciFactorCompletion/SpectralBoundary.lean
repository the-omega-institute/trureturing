import Reg.Support.FibonacciFactorWitnesses
import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
import Reg.Support.SingleDependentReadout


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal148
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
  Law r := ∀ (side : MemorySide) (d : ℝ) (high : oneStepCeiling < d), (MemoryLanguage side 1 1 d = {fun _ : ℤ => CuLetter.u}) ∧ (∀ z : ℝ, 0 ≤ z → weightedRadius side 1 1 d z = ENNReal.ofReal (z^6)) ∧ (∀ z : ℝ, 0 ≤ z → (weightedRadius side 1 1 d z = 1 ↔ z = 1)) ∧ r.readout () () (MemoryLanguage side 1 1 d) = 0

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h .lower (oneStepCeiling + 1) (lt_add_one _)).2.2.2
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.original_closed_root_boundary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.original_closed_root_boundary, rejected, rejected_law⟩
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

def original_closed_root_boundary_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.original_closed_root_boundary)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal148.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal148.evidence
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_closed_root_boundary_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal148

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal145
noncomputable section
universe u_1

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize observationSignature (fun _ _ C => C) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ {A : Type u_1} [NormedRing A] [CompleteSpace A] [NormedAlgebra ℂ A]
    (a : A) (rate : ℝ≥0) (ha : spectralRadius ℂ a < (rate : ℝ≥0∞)),
    ∃ C : ℝ, 0 < r.readout () () C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C * (rate : ℝ) ^ n

theorem rejected_law : ¬ sourceArena.{u_1}.Law rejected := by
  intro h
  have premise : spectralRadius ℂ (0 : ULift.{u_1} ℂ) < ((1 : ℝ≥0) : ℝ≥0∞) := by
    simp [spectrum.spectralRadius_zero]
  obtain ⟨C, impossible, _⟩ := h (0 : ULift.{u_1} ℂ) 1 premise
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena.{u_1} (type_of% @geometric_bound_supplier.{u_1}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@geometric_bound_supplier.{u_1}, rejected, rejected_law⟩
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

def geometric_bound_supplier_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.geometric_bound_supplier.{u_1})
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ C => C) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal145.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal145.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena.{u_1}⟩
  objectArena := .source ⟨sourceArena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena.{u_1} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ C => C) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms geometric_bound_supplier_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal145

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.SeriesWitness
noncomputable section
open Reg.Support.FibonacciFactorWitnesses

theorem core_zero_one_separation :
    (∑ v : CoreVertex .lower 1 1 0,
      ∑ choices : Fin 0 → CuLetter × CoreVertex .lower 1 1 0,
        coreMonomial .lower 1 0 0 0 v choices) ≠
    (∑ v : CoreVertex .lower 1 1 0,
      ∑ choices : Fin 1 → CuLetter × CoreVertex .lower 1 1 0,
        coreMonomial .lower 1 0 0 1 v choices) := by
  classical
  letI : Nonempty (CoreVertex .lower 1 1 0) :=
    ⟨⟨(fun _ => .u), all_u_live 1 .lower 1 0⟩⟩
  have first : (∑ v : CoreVertex .lower 1 1 0,
      ∑ choices : Fin 0 → CuLetter × CoreVertex .lower 1 1 0,
        coreMonomial .lower 1 0 0 0 v choices) =
      (Fintype.card (CoreVertex .lower 1 1 0) : ℝ) := by
    simp [coreMonomial, CorePath, wordWeight]
  have second : (∑ v : CoreVertex .lower 1 1 0,
      ∑ choices : Fin 1 → CuLetter × CoreVertex .lower 1 1 0,
        coreMonomial .lower 1 0 0 1 v choices) = (0 : ℝ) := by
    apply Finset.sum_eq_zero
    intro v _
    apply Finset.sum_eq_zero
    intro choices _
    cases h : (choices 0).1 <;>
      simp [coreMonomial, List.ofFn_succ, h, wordWeight]
  rw [first, second]
  exact_mod_cast (Fintype.card_pos (α := CoreVertex .lower 1 1 0)).ne'

end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.SeriesWitness

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal147
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
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d z : ℝ) (nonnegative : 0 ≤ z),
    Summable (r.readout () ⟨side, n, K, d, z⟩) ↔ weightedRadius side n K d z < 1

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have radius := (original_closed_root_boundary .lower (oneStepCeiling + 1)
    (lt_add_one _)).2.1 0 (by norm_num)
  have small : weightedRadius .lower 1 1 (oneStepCeiling + 1) 0 < 1 := by
    rw [radius]
    norm_num
  have impossible := (h .lower 1 1 (oneStepCeiling + 1) 0 (by norm_num)).mpr small
  simpa [rejected, realize, summable_const_iff] using impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.original_weighted_series_boundary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.original_weighted_series_boundary, rejected, rejected_law⟩
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
    exact SeriesWitness.core_zero_one_separation

def original_weighted_series_boundary_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.original_weighted_series_boundary)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p k => ∑ v : CoreVertex p.1 p.2.1 p.2.2.1 p.2.2.2.1,
      ∑ choices : Fin k → CuLetter × CoreVertex p.1 p.2.1 p.2.2.1 p.2.2.2.1,
        coreMonomial p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 k v choices) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal147.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal147.evidence
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
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_weighted_series_boundary_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal147

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal146
noncomputable section
open scoped Matrix.Norms.Operator

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Σ _ : MemorySide, Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℝ, ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ p k => pathMass p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 k) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (n K : ℕ) (d z : ℝ)
    (nonnegative : 0 ≤ z) (k : ℕ) ,
    0 ≤ r.readout () ⟨side, n, K, d, z⟩ k ∧
    ‖complexAdjacency side n K d z ^ k‖ ≤ pathMass side n K d z k ∧
    pathMass side n K d z k ≤
      Fintype.card (CoreVertex side n K d) * ‖complexAdjacency side n K d z ^ k‖


theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h .lower 1 1 0 0 (by norm_num) 0).1
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.path_mass_norm_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.path_mass_norm_bounds, rejected, rejected_law⟩
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
    change pathMass .lower 1 1 0 0 0 ≠ pathMass .lower 1 1 0 0 1
    have transport (k : ℕ) : pathMass .lower 1 1 0 0 k =
        ∑ v : CoreVertex .lower 1 1 0,
          ∑ choices : Fin k → CuLetter × CoreVertex .lower 1 1 0,
            coreMonomial .lower 1 0 0 k v choices := by
      unfold pathMass
      apply Finset.sum_congr rfl
      intro v _
      exact (original_weighted_adjacency_paths .lower 1 1 0 0).2 k v
    rw [transport, transport]
    exact SeriesWitness.core_zero_one_separation

def path_mass_norm_bounds_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.path_mass_norm_bounds)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ p k => pathMass p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 k) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal146.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal146.evidence
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
    (fun _ p k => pathMass p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms path_mass_norm_bounds_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal146
