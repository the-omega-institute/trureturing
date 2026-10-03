import D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum
open _root_.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State N := (Fin N → Fin 2) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ψ => ∑ w, ‖ψ w‖ ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete original claim; only the norm `∑ w, ‖ψ w‖ ^ 2` in the hypothesis of the lower
bound is replaced by the readout. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N : ℕ) (A : Finset (Fin N)), 1 ≤ A.card → A.card < N →
    (∀ ψ : (Fin N → Fin 2) → ℂ, O.readout () N ψ = 1 →
      conjecturedMin N A.card ≤ purityPlusOverlap A ψ) ∧
    ∃ ψ : (Fin N → Fin 2) → ℂ, ∑ w, ‖ψ w‖ ^ 2 = 1 ∧
      purityPlusOverlap A ψ = conjecturedMin N A.card

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := (h 2 {0} (by decide) (by decide)).1 0 rfl
  have hz : purityPlusOverlap ({0} : Finset (Fin 2)) 0 = 0 := by
    have h0' : reducedState ({0} : Finset (Fin 2)) 0 = 0 := by
      ext x y
      simp [reducedState, partialTraceRight]
    simp [purityPlusOverlap, h0', timeReversed]
  rw [hz] at h0
  have hpos : (0 : ℝ) < conjecturedMin 2 ({0} : Finset (Fin 2)).card := by
    unfold conjecturedMin; split_ifs <;> positivity
  linarith

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, fun _ => 0, fun _ => 1, fun h => ?_⟩
  change (∑ w : Fin 0 → Fin 2, ‖(0 : ℂ)‖ ^ 2) = ∑ w : Fin 0 → Fin 2, ‖(1 : ℂ)‖ ^ 2 at h
  simp at h

def registration :
    Registration arena
      _root_.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.result in arena
  readout via (realize signature (fun _ _ ψ => ∑ w, ‖ψ w‖ ^ 2) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum
    «definition» := some {
      owner := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum
      name := `D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "domain", "fn", "arg"]
      stateBinder := 4 }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.PurityTimeReversalOverlapMinimum
