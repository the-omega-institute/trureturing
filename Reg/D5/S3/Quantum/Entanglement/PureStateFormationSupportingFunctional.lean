import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PureStateFormationSupportingFunctional
import Reg.Support.DependentFamily

/-! Source-bound audit of the supporting functional at a bipartite pure state. -/

namespace Reg.D5.S3.Quantum.Entanglement.PureStateFormationSupportingFunctional

open _root_.D5.S3.Quantum.Entanglement.PureStateFormationSupportingFunctional
open _root_.D5.S3.Quantum.Entanglement.MoreauYosidaFormationSelectiveLoccRefutation (E_F)
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open _root_.D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity (pureDensityState)
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (marginalRight)
open _root_.D5.S3.Quantum.Divergence.VonNeumannEntropyPinching (vonNeumannEntropy)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The dimensions and pure-state vector parameterize the functional's scalar value. -/
abbrev signature : Signature where
  Params := Σ a : ℕ, Σ b : ℕ, Fin a × Fin b → ℂ
  State p := Matrix (Fin p.1 × Fin p.2.1) (Fin p.1 × Fin p.2.1) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p W => (W * rankOneDensity p.2.2).trace.re)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- Retain every hypothesis, the real contact value, the formation equality and the global bound. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b →
    ∀ (ψ : Fin a × Fin b → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1),
    ∃ W : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
      W.IsHermitian ∧
      r.readout () ⟨a, b, ψ⟩ W =
        vonNeumannEntropy (marginalRight (pureDensityState ψ hψ)) ∧
      E_F (pureDensityState ψ hψ) = ENNReal.ofReal (W * rankOneDensity ψ).trace.re ∧
      ∀ σ : DensityState (Fin a × Fin b),
        ENNReal.ofReal (W * CStarMatrix.ofMatrix.symm σ.val).trace.re ≤ E_F σ

private theorem entropy_dim_one (ρ : DensityState (Fin 1)) : vonNeumannEntropy ρ = 0 := by
  have hρ : ρ.val = 1 := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_one] using ρ.property.2
  unfold vonNeumannEntropy
  rw [hρ, CFC.log_one, mul_zero]
  change -(Matrix.trace (0 : Matrix (Fin 1) (Fin 1) ℂ)).re = 0
  simp

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hψ : star (fun _ : Fin 1 × Fin 1 => (1 : ℂ)) ⬝ᵥ
      (fun _ : Fin 1 × Fin 1 => (1 : ℂ)) = 1 := by
    simp [dotProduct]
  obtain ⟨W, _, heq, _⟩ := h 1 1 (by norm_num) (by norm_num) (fun _ => 1) hψ
  change (1 : ℝ) = _ at heq
  have he := entropy_dim_one
    (marginalRight (pureDensityState (fun _ : Fin 1 × Fin 1 => 1) hψ))
  exact one_ne_zero (heq.trans he)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1, fun _ => 1⟩, 0, 1, ?_⟩
  change (0 * rankOneDensity (fun _ : Fin 1 × Fin 1 => (1 : ℂ))).trace.re ≠
    (1 * rankOneDensity (fun _ : Fin 1 × Fin 1 => (1 : ℂ))).trace.re
  norm_num [rankOneDensity, Matrix.trace, Fintype.sum_prod_type, Matrix.vecMulVec_apply]

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
      (@_root_.D5.S3.Quantum.Entanglement.PureStateFormationSupportingFunctional.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PureStateFormationSupportingFunctional.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.PureStateFormationSupportingFunctional.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p W => (W * rankOneDensity p.2.2).trace.re)
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PureStateFormationSupportingFunctional
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.PureStateFormationSupportingFunctional
      name := `D5.S3.Quantum.Entanglement.PureStateFormationSupportingFunctional.claim
      path := #[] }
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.PureStateFormationSupportingFunctional
