import D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm
open _root_.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial
noncomputable section

abbrev signature : Signature where
  Params := (_ : ℕ) × ℕ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p r => stirlingHat p.1 p.2 r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete original claim; only the selected source operand is replaced. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ n k : ℕ, k ≤ n → ∀ r : ℤ,
    O.readout () ⟨n, k⟩ r = conjectureSum n k r

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0 0 (by omega) 0
  rw [← result 0 0 (by omega) 0] at h0
  norm_num [rejected, realize, stirlingHat] at h0

def registration : Registration arena (claim) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
    norm_num [actual, realize, stirlingHat]

register_information_theorem result in arena
  readout via (realize signature (fun _ p r => stirlingHat p.1 p.2 r) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm
    «definition» := some {
      owner := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm
      name := `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.claim }
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3 }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm
