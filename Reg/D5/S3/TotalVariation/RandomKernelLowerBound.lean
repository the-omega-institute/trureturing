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
  norm_num [rejected, realize, rho_values.1] at heq

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  have hz : rho 0 = 0 := by norm_num [rho, beta, coefficient]
  simpa [actual, realize, hz, rho_values.1] using (by norm_num : (0 : ℝ) ≠ 1/4)

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

end Reg.D5.S3.TotalVariation.RandomKernelLowerBound
