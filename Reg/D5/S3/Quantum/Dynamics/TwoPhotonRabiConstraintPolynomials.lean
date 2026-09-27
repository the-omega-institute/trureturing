import D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials
open _root_.D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial
noncomputable section

abbrev signature : Signature where
  Params := (_ : ℕ) × (_ : ℝ) × ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ[X]
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p n => constraintPoly p.1 p.2.1 p.2.2 1 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The complete original claim; only the selected source operand is replaced. -/
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (N : ℕ) (ρ : ℝ), (ρ = 0 ∨ ρ = 1) →
    (∀ ε : ℝ, O.readout () ⟨N, ρ, ε⟩ N =
      ∏ n ∈ Finset.Icc 1 N, (X + C (2 * (n : ℝ) * (2 * n + 2 * ρ - 1)))) ∧
    (∀ ε : ℝ, 0 ≤ ε → ∀ x : ℝ, 1 < x →
      (∀ i ≤ N, 0 < (constraintPoly N ρ ε x N).coeff i) ∧
        ∀ y : ℝ, 0 < y → (constraintPoly N ρ ε x N).eval y ≠ 0)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := (h 0 0 (Or.inl rfl)).1 0
  norm_num [rejected, realize] at h0

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
    refine ⟨⟨1, 0, 0⟩, 0, 1, ?_⟩
    intro h
    have hc := congrArg (fun p : ℝ[X] => p.coeff 1) h
    norm_num [actual, realize, constraintPoly, Polynomial.coeff_one] at hc

register_information_theorem result in arena
  readout via (realize signature (fun _ p n => constraintPoly p.1 p.2.1 p.2.2 1 n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials
    «definition» := some {
      owner := `D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials
      name := `D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials.claim }
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "fn", "arg"]
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials
