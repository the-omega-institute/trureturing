import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.NonselectiveNegativityGainOptimum
import Reg.Support.DependentFamily

/-! Source-bound audit of the attained non-selective negativity bound. -/

namespace Reg.D5.S3.Quantum.Entanglement.NonselectiveNegativityGainOptimum
open _root_.D5.S3.Quantum.Entanglement.NonselectiveNegativityGainOptimum
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.QuantumBounds.NegativityReductionInclusionRefutation (negativity)
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_nonneg)
open _root_.D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the negativity after measurement as the measurement matrix varies. -/
abbrev signature : Signature where
  Params := Fin 2 × Fin 2 → ℂ
  State _ := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ ψ U => negativity (measured U (rankOneDensity ψ))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ ψ U => negativity (measured U (rankOneDensity ψ)) + 1)
    (fun e => nomatch e)

/-- Keep the normalization, universal bound, and attained equality. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ ψ : Fin 2 × Fin 2 → ℂ, (∑ i, Complex.normSq (ψ i)) = 1 →
    (∀ U ∈ unitaryGroup (Fin 2 × Fin 2) ℂ,
      r.readout () ψ U ≤ negativity (rankOneDensity ψ) / 2 + 1 / 4) ∧
    (∃ U ∈ unitaryGroup (Fin 2 × Fin 2) ℂ,
      negativity (measured U (rankOneDensity ψ)) = negativity (rankOneDensity ψ) / 2 + 1 / 4)

private def basisVector : Fin 2 × Fin 2 → ℂ :=
  fun p => if p = (0, 0) then 1 else 0

private theorem basisVector_normalized :
    (∑ i, Complex.normSq (basisVector i)) = 1 := by
  norm_num [basisVector, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨U, hU, hopt⟩ := (result basisVector basisVector_normalized).2
  have hbad := (h basisVector basisVector_normalized).1 U hU
  change negativity (measured U (rankOneDensity basisVector)) + 1 ≤ _ at hbad
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨U, _, hopt⟩ := (result basisVector basisVector_normalized).2
  refine ⟨basisVector, 0, U, ?_⟩
  have hz : negativity (measured 0 (rankOneDensity basisVector)) = -1 / 2 := by
    have hm : measured 0 (rankOneDensity basisVector) = 0 := by simp [measured]
    have hp : partialTranspose
        (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) = 0 := rfl
    rw [hm, negativity, hp]
    simp [_root_.D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm]
  have hn := traceNorm_nonneg (partialTranspose (rankOneDensity basisVector))
  change negativity (measured 0 (rankOneDensity basisVector)) ≠
    negativity (measured U (rankOneDensity basisVector))
  rw [hz, hopt]
  unfold negativity
  linarith

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
      (@_root_.D5.S3.Quantum.Entanglement.NonselectiveNegativityGainOptimum.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.NonselectiveNegativityGainOptimum.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.NonselectiveNegativityGainOptimum.source_registration
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
    (realize signature (fun _ ψ U => negativity (measured U (rankOneDensity ψ)))
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.NonselectiveNegativityGainOptimum
    definition := some {
      owner := `D5.S3.Quantum.Entanglement.NonselectiveNegativityGainOptimum
      name := `D5.S3.Quantum.Entanglement.NonselectiveNegativityGainOptimum.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.NonselectiveNegativityGainOptimum
