import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumBounds.EnergyConstrainedDeterministicViolation
import Reg.Support.DependentFamily

/-! Source-bound audit of the deterministic-input Born probability. -/

namespace Reg.D5.S3.QuantumBounds.EnergyConstrainedDeterministicViolation
open _root_.D5.S3.QuantumBounds.EnergyConstrainedDeterministicViolation
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev signature : Signature where
  Params := Σ dp : ℕ, Σ ds : ℕ, Σ dm : ℕ,
    Σ _lam : Fin 2 → MatrixMap (Fin dp) (Fin ds) ℂ,
      Fin 2 → Matrix (Fin ds × Fin dm) (Fin ds × Fin dm) ℂ
  State p := Matrix (Fin p.1 × Fin p.2.2.1) (Fin p.1 × Fin p.2.2.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p σ => probability σ p.2.2.2.1 p.2.2.2.2 0 0)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ ω : ℝ, 0 < ω → ω < 1 / 2 →
    ∃ (dp ds dm : ℕ) (sigma : Matrix (Fin dp × Fin dm) (Fin dp × Fin dm) ℂ)
      (lam : Fin 2 → MatrixMap (Fin dp) (Fin ds) ℂ)
      (ham : Matrix (Fin ds) (Fin ds) ℂ) (g : Fin ds → ℂ)
      (povm : Fin 2 → Matrix (Fin ds × Fin dm) (Fin ds × Fin dm) ℂ),
      sigma.PosSemidef ∧ sigma.trace = 1 ∧
      (∀ x, (lam x).IsCompletelyPositive ∧ ∀ rho, (lam x rho).trace = rho.trace) ∧
      ham.IsHermitian ∧ star g ⬝ᵥ g = 1 ∧ ham *ᵥ g = 0 ∧
      (ham - (1 - Matrix.vecMulVec g (star g))).PosSemidef ∧
      (∀ b, (povm b).PosSemidef) ∧ povm 0 + povm 1 = 1 ∧
      (∀ x, (Matrix.trace (ham * lam x (partialTraceRight sigma))).re ≤ ω) ∧
      R.readout () ⟨dp, ds, dm, lam, povm⟩ sigma = 1 ∧
      probability sigma lam povm 0 1 - probability sigma lam povm 1 1 <
        2 * (1 - 2 * ω) ^ 2 - 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨dp, ds, dm, σ, lam, ham, g, povm, _, _, _, _, _, _, _, _, _, _, hp, _⟩ :=
    h (1 / 4) (by norm_num) (by norm_num)
  change (0 : ℝ) = 1 at hp
  exact zero_ne_one hp

theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨dp, ds, dm, σ, lam, ham, g, povm, _, _, _, _, _, _, _, _, _, _, hp, _⟩ :=
    result (1 / 4) (by norm_num) (by norm_num)
  refine ⟨⟨dp, ds, dm, lam, povm⟩, 0, σ, ?_⟩
  change probability 0 lam povm 0 0 ≠ probability σ lam povm 0 0
  rw [hp]
  simp [probability, _root_.D5.S3.Quantum.FiniteDimensional.bornProbability]

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `EnergyConstrainedDeterministicViolation.unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p σ => probability σ p.2.2.2.1 p.2.2.2.2 0 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumBounds.EnergyConstrainedDeterministicViolation
    definition := some {
      owner := `D5.S3.QuantumBounds.EnergyConstrainedDeterministicViolation
      name := `D5.S3.QuantumBounds.EnergyConstrainedDeterministicViolation.claim
      path := #[] }
    coordinates := #[3, 4, 5, 7, 10]
    readouts := #[{
      path := #[
        "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg",
        "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.QuantumBounds.EnergyConstrainedDeterministicViolation
