import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.CompleteHockeyStickBasisSupport

/-! Source-bound readout of the calibrated simplex payoff. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit Matrix
open scoped CStarAlgebra ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act E amp ptr)
open private E_contract from D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation
open _root_.D5.S3.Quantum.Divergence.CompleteHockeyStickBasisSupport (exists_budget_witness)

namespace Reg.D5.S3.Quantum.Divergence.CompleteHockeyStickBasisSupport

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ D => D = -1) (fun e => nomatch e)

private def identity : QuantumChannel (Option Unit) (Option Unit) where
  toCompletelyPositiveMap :=
    { toLinearMap := LinearMap.id
      map_cstarMatrix_nonneg' := fun _ _ h => h }
  trace_preserving _ := rfl

private theorem identity_support :
    (⨅ i, (act identity (Matrix.single i i 1)).mulVecLin.range) = ⊥ := by
  apply bot_unique
  intro v hv
  rw [Submodule.mem_bot]
  have h := (Submodule.mem_iInf _).mp hv
  ext j
  obtain ⟨i, hij⟩ : ∃ i : Option Unit, j ≠ i := by
    cases j with
    | none => exact ⟨some (), by simp⟩
    | some j => exact ⟨none, Option.some_ne_none j⟩
  obtain ⟨w, hw⟩ := h i
  have he : (Matrix.single i i (1 : ℂ)) *ᵥ w = v := hw
  rw [← he, Matrix.single_mulVec]
  simp [hij]

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {B : Type} [Fintype B] [DecidableEq B]
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty B]
    (N : QuantumChannel (Option I) B) (_pivot : I) (γ : ℝ) (_hγ : 1 < γ)
    (_hS : (⨅ i, (act N (Matrix.single i i 1)).mulVecLin.range) = ⊥),
    ∃ δ D : ℝ, 0 < δ ∧ R.readout () () 0 D ∧ ∀ a : ℝ, 0 < a → a ≤ δ →
      ∃ P Q : Matrix (Option I × Option I) (Option I × Option I) ℂ,
        P.PosSemidef ∧ P.trace = 1 ∧ Q.PosSemidef ∧ Q.trace = 1 ∧
        ptr P = ptr Q ∧ E γ P Q = a ∧ a / (1 + D * a) ≤ E γ (amp N P) (amp N Q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let N := identity
  obtain ⟨δ, D, hδ, hD, hbudget⟩ := h N () 2 (by norm_num) identity_support
  let a : ℝ := min δ (1 / 2)
  have ha : 0 < a := lt_min hδ (by norm_num)
  obtain ⟨ρ, σ, hρ, _, hσ, _, _, hin, hpay⟩ := hbudget a ha (min_le_left _ _)
  have hi : E 2 ρ σ ≤ a := hin.le
  have hhalf : a ≤ 1 / 2 := min_le_right _ _
  have hd : 0 < 1 + D * a := by rw [hD]; linarith
  have hg : a < a / (1 + D * a) := by
    apply (lt_div_iff₀ hd).mpr
    rw [hD]
    nlinarith only [sq_pos_of_pos ha]
  exact (not_lt_of_ge hi) (hg.trans_le (hpay.trans (E_contract N 2 hρ hσ)))

private theorem sensitivity : Sensitivity arena actual :=
  _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  exact (not_le.mpr zero_lt_one) he

def family : Registration arena (type_of% @exists_budget_witness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_budget_witness, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_budget_witness) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.CompleteHockeyStickBasisSupport.exists_budget_witness.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.CompleteHockeyStickBasisSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.CompleteHockeyStickBasisSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "arg", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Quantum.Divergence.CompleteHockeyStickBasisSupport
