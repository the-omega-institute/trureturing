import D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation
open _root_.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := Fin 2 → Fin 2 → Fin 2 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 2 → Fin 2 → Fin 2 → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ψ => ψ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete negated claim; only the state in the hypothesis `GenuinelyEntangled ψ` is
replaced. -/
abbrev arena : Arena where
  signature := signature
  Law O := ¬ ∀ (ψ : Fin 2 → Fin 2 → Fin 2 → ℂ) (up um dp dm : Fin 3 → Fin 2 → ℂ),
    ∑ i, ∑ j, ∑ k, Complex.normSq (ψ i j k) = 1 → GenuinelyEntangled (O.readout () () ψ) →
    (∀ k, IsONB (up k) (um k)) → (∀ k, IsONB (dp k) (dm k)) →
    prob (dp 0) (up 1) (up 2) ψ = 0 → prob (up 0) (dp 1) (up 2) ψ = 0 →
    prob (up 0) (up 1) (dp 2) ψ = 0 → 0 < prob (dm 0) (dm 1) (dm 2) ψ →
    prob (up 0) (up 1) (up 2) ψ - prob (dm 0) (dm 1) (dm 2) ψ ≤ 9 / 64

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro ψ up um dp dm _ hent
  exact absurd ⟨fun _ => 0, fun _ _ => 0, fun _ _ _ => by change (0 : ℂ) = 0 * 0; simp⟩ hent.1

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), fun _ _ _ => 0, fun _ _ _ => 1, fun h => ?_⟩
  have := congrFun (congrFun (congrFun h 0) 0) 0
  change (0 : ℂ) = 1 at this
  exact zero_ne_one this

def registration : Registration arena (¬ claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
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
  _root_.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.result in arena
  readout via (realize signature (fun _ _ ψ => ψ) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation
    «definition» := some {
      owner := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation
      name := `D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation.claim
      path := #["arg"] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.ThreeQubitCabelloRefutation
