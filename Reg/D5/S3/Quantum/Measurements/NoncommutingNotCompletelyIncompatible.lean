import D5.S3.Quantum.Measurements.NoncommutingNotCompletelyIncompatible
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Measurements.NoncommutingNotCompletelyIncompatible
open _root_.D5.S3.Quantum.Measurements.NoncommutingNotCompletelyIncompatible
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State d := (OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := (OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a => NonCommutingProjectors a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The original telescope, with only condition (ii) read through the selected basis. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ d : ℕ, 4 ≤ d → ∃ a b : (OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d))),
    O.readout () d a b ∧ ¬ CompletelyIncompatible a b

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, b, hab, _⟩ := h 4 (by decide)
  exact hab

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  obtain ⟨a, b, hab, _⟩ :=
    _root_.D5.S3.Quantum.Measurements.NoncommutingNotCompletelyIncompatible.result 4 (by decide)
  refine ⟨4, a, b, ?_⟩
  intro h
  have he := congrFun h b
  change NonCommutingProjectors a b = NonCommutingProjectors b b at he
  have hbb : NonCommutingProjectors b b := he ▸ hab
  have hs : ({0} : Finset (Fin 4)) ≠ Finset.univ := by decide
  exact hbb {0} {0} (by simp) hs (by simp) hs rfl

def registration : Registration arena
    _root_.D5.S3.Quantum.Measurements.NoncommutingNotCompletelyIncompatible.claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨
    _root_.D5.S3.Quantum.Measurements.NoncommutingNotCompletelyIncompatible.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := dependence_proof

register_information_theorem
  _root_.D5.S3.Quantum.Measurements.NoncommutingNotCompletelyIncompatible.result in arena
  readout via (realize signature (fun _ _ a => NonCommutingProjectors a) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurements.NoncommutingNotCompletelyIncompatible
    «definition» := some {
      owner := `D5.S3.Quantum.Measurements.NoncommutingNotCompletelyIncompatible
      name := `D5.S3.Quantum.Measurements.NoncommutingNotCompletelyIncompatible.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 2 }] })
  escape continues (open)

end
end Reg.D5.S3.Quantum.Measurements.NoncommutingNotCompletelyIncompatible
