import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.TripleDeletionCountComparison
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.TripleDeletionCountComparison

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.BinaryDeletionDimension
open _root_.D5.S3.Quantum.Entanglement.Marginals.TripleDeletionCountComparison
open _root_.D5.S0.Tower.Tribonacci.Names

noncomputable section

private abbrev comparisonSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def comparisonActual : Realization comparisonSignature :=
  realize comparisonSignature (fun _ _ x y => x = y) (fun anchor => nomatch anchor)

private def comparisonRejected : Realization comparisonSignature :=
  realize comparisonSignature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private abbrev comparisonArena : Arena where
  signature := comparisonSignature
  Law F := ∀ k : ℕ,
    let dim := Module.finrank ℂ (SupportedKernel (NoTriple (k + 1)))
    let count := Nat.card {w // NoTriple (k + 1) w}
    F.readout () k dim (4 * (tribonacci (k + 3) + tribonacci (k + 2))) ∧
      count = tribonacci (k + 5) ∧ dim < 2 * count

private theorem comparisonRejected_law : ¬ comparisonArena.Law comparisonRejected :=
  fun h => (h 0).1

def comparisonFamily : Registration comparisonArena (type_of% @triple_kernel_exact) where
  actual := comparisonActual
  bridge := Iff.rfl
  variation := ⟨@triple_kernel_exact, comparisonRejected, comparisonRejected_law⟩
  sensitivity := ⟨fun i => ⟨comparisonRejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, comparisonRejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    intro h
    exact Nat.one_ne_zero (Eq.mp (congrFun h 0) rfl)

def comparisonAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@triple_kernel_exact) (Realization comparisonSignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.Marginals.TripleDeletionCountComparison.triple_kernel_exact.audit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.Marginals.TripleDeletionCountComparison.comparisonFamily
  realizationSource := none
  generated := false
  arena := .source ⟨comparisonArena⟩
  objectArena := .source ⟨comparisonArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source comparisonArena ⟨comparisonFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize comparisonSignature (fun _ _ x y => x = y) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.TripleDeletionCountComparison
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.TripleDeletionCountComparison
