import D5.S3.TotalVariation.RandomKernelLowerBound
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.TotalVariation.RandomKernelExtremum
open _root_.D5.S3.TotalVariation.RandomKernelLowerBound
open _root_.D5.S3.TotalVariation.Pinsker
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reg.D5.S3.TotalVariation.RandomKernelLowerBound

namespace Minimax

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => rho d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {d : ℕ} (_hd : 2 ≤ d),
    IsLeast {e : ℝ | ∃ K : Option (Fin d × Fin d) → Option (Fin d × Fin d) → ℝ,
      ((∀ x y, 0 ≤ K x y) ∧ ∀ y, ∑ x, K x y = 1) ∧ e = worstError K}
      (r.readout () () d)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (d := 2) (by decide)
  have ht := _root_.D5.S3.TotalVariation.RandomKernelLowerBound.stochastic_kernel_minimax
    (d := 2) (by decide)
  have heq := hh.unique ht
  norm_num [rejected, realize, rho, beta, coefficient, Finset.range_add_one, Finset.sup'_insert, Finset.sup'_singleton] at heq

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 4, ?_⟩
  norm_num [actual, realize, rho, beta, coefficient, Finset.range_add_one, Finset.sup'_insert, Finset.sup'_singleton]

def registration : Registration arena (type_of% (@_root_.D5.S3.TotalVariation.RandomKernelLowerBound.stochastic_kernel_minimax)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.TotalVariation.RandomKernelLowerBound.stochastic_kernel_minimax, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.TotalVariation.RandomKernelLowerBound
  definition := none
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "arg", "fn"]
    stateBinder := 0
    functionOperand := true
    stateOperand := none
    booleanPredicate := false }]

noncomputable def contract : Contract.Registration
    (@_root_.D5.S3.TotalVariation.RandomKernelLowerBound.stochastic_kernel_minimax) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.RandomKernelLowerBound.Minimax.unit
  realizationName := `Reg.D5.S3.TotalVariation.RandomKernelLowerBound.Minimax.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Minimax

namespace Matching

abbrev signature : Signature where
  Params := ℕ
  State d := Finset (Fin d)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Option (Fin d × Fin d) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ S => matchingLaw S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {d : ℕ} (_hd : 2 ≤ d) (S : Finset (Fin d)) (_hk : 2 ≤ S.card)
    (_hmax : beta d = coefficient d S.card),
    totalVariation (kernelOutput (optimalKernel d) (r.readout () d S))
      (completion (matchingLaw S)) = rho d

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hm : beta 2 = coefficient 2 2 := by
    norm_num [beta, coefficient, Finset.range_add_one,
      Finset.sup'_insert, Finset.sup'_singleton]
  have hh := h (d := 2) (by decide) Finset.univ (by decide) (by simpa using hm)
  norm_num [rejected, realize, kernelOutput, completion, matchingLaw, totalVariation,
    Fintype.sum_option, Fintype.sum_prod_type, Fin.sum_univ_two, rho, beta, coefficient, Finset.range_add_one, Finset.sup'_insert, Finset.sup'_singleton] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨3, ({0,1} : Finset (Fin 3)), ({0,2} : Finset (Fin 3)), ?_⟩
  intro h
  have hh := congrFun h (some ((1,1) : Fin 3 × Fin 3))
  change matchingLaw ({0,1} : Finset (Fin 3)) (some (1,1)) =
    matchingLaw ({0,2} : Finset (Fin 3)) (some (1,1)) at hh
  norm_num [matchingLaw] at hh

def registration : Registration arena (type_of% (@_root_.D5.S3.TotalVariation.RandomKernelLowerBound.maximizing_matching_attains)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.TotalVariation.RandomKernelLowerBound.maximizing_matching_attains, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.TotalVariation.RandomKernelLowerBound
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
    stateBinder := 2
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

noncomputable def contract : Contract.Registration
    (@_root_.D5.S3.TotalVariation.RandomKernelLowerBound.maximizing_matching_attains) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.RandomKernelLowerBound.Matching.unit
  realizationName := `Reg.D5.S3.TotalVariation.RandomKernelLowerBound.Matching.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Matching

end Reg.D5.S3.TotalVariation.RandomKernelLowerBound
