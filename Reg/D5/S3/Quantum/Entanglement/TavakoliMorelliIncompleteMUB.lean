import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB
open _root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option linter.checkUnivs false
noncomputable section
open _root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance

private def oneKet : Ket (Fin 1 × Fin 1) := ⟨fun _ => 1, by simp⟩

private theorem schmidt_one : SchmidtNumberLE (proj oneKet) 1 := by
  refine ⟨1, fun _ => 1, fun _ => oneKet, by simp, by simp, ?_, by simp⟩
  intro k
  exact le_trans (Matrix.rank_le_card_width _) (by simp)

private def oneMUB : MUBFamily 1 1 :=
  ⟨fun _ => 1, by intro l k hlk; exact (hlk (Subsingleton.elim _ _)).elim⟩

namespace Bound

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State p := Matrix (Fin p.2 × Fin p.1) (Fin p.2 × Fin p.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X => D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d m r : ℕ), 1 ≤ d → 1 ≤ m → m ≤ d → 1 ≤ r → r ≤ d →
    ∀ (A B : MUBFamily d m) (ρ : BipartiteOp d), SchmidtNumberLE ρ r →
      R.readout () ⟨d, m⟩ (Qm ρ A B) ≤ 1 + ((m : ℝ) - 1) * (r : ℝ) / (d : ℝ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1 1 1 le_rfl le_rfl le_rfl le_rfl le_rfl oneMUB oneMUB
    (proj oneKet) schmidt_one
  norm_num [rejected, realize] at he

def source_registration : Registration arena (type_of% @_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB.result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨show arena.Law actual from (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB.result), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
    simp [actual, realize, D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB.result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB.Bound.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB.Bound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB
    definition := some { owner := `D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB, name := `D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB.claim, path := #[] }
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Bound

end
end Reg.D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB
