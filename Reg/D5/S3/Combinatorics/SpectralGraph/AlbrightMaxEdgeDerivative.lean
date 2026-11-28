import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.SpectralGraph.AlbrightMaxEdgeDerivative

/-! Observe adjacency at the second endpoint of the attaining path pair. -/

namespace Reg.D5.S3.Combinatorics.SpectralGraph.AlbrightMaxEdgeDerivative

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.SpectralGraph.AlbrightMaxEdgeDerivative
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.SingleDependentReadout (signature sensitivity)

noncomputable section

private abbrev path := SimpleGraph.pathGraph 3

abbrev endpointSignature : Signature := signature Unit (fun _ => Fin 3) (fun _ => Bool)

def actual : Realization endpointSignature :=
  realize endpointSignature
    (fun _ _ j => decide ((SimpleGraph.pathGraph 3).Adj 0 j)) (fun e => nomatch e)

def rejected : Realization endpointSignature :=
  realize endpointSignature (fun _ _ _ => true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := endpointSignature
  Law R :=
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      2 ≤ n → G.Connected → ∀ (x y : Fin n), x ≠ y → ∀ (lam : ℝ) (k : ℕ), 0 < k →
      ∀ b : OrthonormalBasis (Fin k) ℝ (eigenspace G x y lam),
        HasDerivAt (rayleighAverage G x y lam b) (edgeDerivative G x y lam b) 0 ∧
        edgeDerivative G x y lam b ≤ 1 ∧
        ∀ c : OrthonormalBasis (Fin k) ℝ (eigenspace G x y lam),
          edgeDerivative G x y lam b = edgeDerivative G x y lam c) ∧
    path.Connected ∧ (0 : Fin 3) ≠ 2 ∧ ¬ (R.readout () () 2 = true) ∧
    Module.finrank ℝ (eigenspace path 0 2 1) = 1 ∧
    ∃ b : OrthonormalBasis (Fin 1) ℝ (eigenspace path 0 2 1),
      HasDerivAt (rayleighAverage path 0 2 1 b) 1 0 ∧ edgeDerivative path 0 2 1 b = 1

private theorem bridge : claim ↔ arena.Law actual := by
  simp only [claim, actual, realize, path, decide_eq_true_eq]

private theorem rejected_law : ¬ arena.Law rejected := fun h => h.2.2.2.1 rfl

private theorem dependence : ObservationalDependence endpointSignature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  have h₁ : path.Adj 0 1 := by decide
  have h₂ : ¬ path.Adj 0 2 := by decide
  simp only [actual, realize, decide_eq_true h₁, decide_eq_false h₂]
  decide

def pathSource : Registration arena claim where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp result, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def pathRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization endpointSignature) Unit Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.AlbrightMaxEdgeDerivative.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.AlbrightMaxEdgeDerivative.pathSource
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨pathSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize endpointSignature
    (fun _ _ j => decide ((SimpleGraph.pathGraph 3).Adj 0 j)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.AlbrightMaxEdgeDerivative
    definition := some {
      owner := `D5.S3.Combinatorics.SpectralGraph.AlbrightMaxEdgeDerivative
      name := `D5.S3.Combinatorics.SpectralGraph.AlbrightMaxEdgeDerivative.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.SpectralGraph.AlbrightMaxEdgeDerivative
