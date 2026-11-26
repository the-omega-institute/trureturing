import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Marginals.RationalQubitMixedEndpoint
import Reg.Support.DependentFamily

/-! Registration of the joint rank for a maximally mixed qubit marginal. -/

set_option autoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.Marginals.RationalQubitMixedEndpoint

open LeanInformationAudit Matrix
open scoped ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open _root_.D5.S3.Quantum.Entanglement.Marginals.RationalQubitMixedEndpoint
open _root_.D5.S3.Quantum.Entanglement.Marginals.RationalQubitProjector
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation

noncomputable section

private abbrev Joint := Matrix (Bool × Bool) (Bool × Bool) ℂ

private abbrev signature : Signature where
  Params := Unit
  State _ := Joint
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ T => T.rank) (fun anchor => nomatch anchor)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun anchor => nomatch anchor)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c : Fin 3 → ℚ), 0 < c ⬝ᵥ c → c ⬝ᵥ c < 1 →
    ∃ T : Joint, T.PosSemidef ∧ R.readout () () T = 2 ∧
      (∀ i j, RationalEntry (T i j)) ∧
      partialTraceRight T = (1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ) ∧
      partialTraceLeft T = (1 / 2 : ℂ) • (1 + rationalBlochMatrix c)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, hrank, _⟩ := h ![1 / 4, 1 / 4, 0]
    (by norm_num [dotProduct, Fin.sum_univ_three])
    (by norm_num [dotProduct, Fin.sum_univ_three])
  exact (by decide : (3 : ℕ) ≠ 2) hrank

def family : Registration arena (type_of% @rational_rank_two_of_maximally_mixed_endpoint) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rational_rank_two_of_maximally_mixed_endpoint, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change (0 : Joint).rank ≠ (1 : Joint).rank
    simp

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rational_rank_two_of_maximally_mixed_endpoint) (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S3.Quantum.Entanglement.Marginals.RationalQubitMixedEndpoint.rational_rank_two_of_maximally_mixed_endpoint
    "audit"
  realizationName := `Reg.D5.S3.Quantum.Entanglement.Marginals.RationalQubitMixedEndpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ T => T.rank) (fun anchor => nomatch anchor))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Marginals.RationalQubitMixedEndpoint
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body",
        "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Entanglement.Marginals.RationalQubitMixedEndpoint
