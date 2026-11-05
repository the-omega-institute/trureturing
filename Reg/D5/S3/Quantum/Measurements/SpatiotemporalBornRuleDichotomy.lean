import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy
import Reg.Support.DependentFamily

/-! Source-bound audit of the scalar in the sequential Born-rule dichotomy. -/

namespace Reg.D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy

open _root_.D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open _root_.D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation (IsCPTP)
open _root_.D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the normalization scalar of the maximally mixed state. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => 1 / (d : ℂ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain both dimensions, all physical hypotheses and both alternatives. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (d e : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ε : MatrixMap (Fin d) (Fin e) ℂ),
    IsDensity ρ → IsCPTP ε → 1 ≤ d → 1 ≤ e →
    (BornRuleExists ρ ε ↔ ρ = r.readout () () d • 1 ∨ DiscardPrepare ε)

private def mixed : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • 1

private theorem mixed_density : IsDensity mixed := by
  constructor
  · have hc := Complex.zero_le_real.mpr (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hc
    exact Matrix.PosSemidef.one.smul hc
  · norm_num [mixed, Matrix.trace_smul, Matrix.trace_one]

private theorem identity_cptp :
    IsCPTP (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) := by
  constructor
  · have hi : MatrixMap.of_kraus (fun _ : Unit => (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (fun _ : Unit => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = LinearMap.id := by
      ext X i j
      simp [MatrixMap.of_kraus]
    rw [← hi]
    exact MatrixMap.of_kraus_isCompletelyPositive _
  · intro X
    rfl

private theorem identity_not_discard :
    ¬ DiscardPrepare (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) := by
  rintro ⟨σ, _, hσ⟩
  have h := hσ (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ)
  have he := congrArg (fun M => M 0 0) h
  norm_num [Matrix.trace, Fin.sum_univ_two] at he

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb : BornRuleExists mixed (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) :=
    (result 2 2 mixed LinearMap.id mixed_density identity_cptp (by norm_num)
      (by norm_num)).mpr (Or.inl rfl)
  rcases (h 2 2 mixed LinearMap.id mixed_density identity_cptp (by norm_num)
    (by norm_num)).mp hb with hz | hd
  · have he := congrArg (fun M => M 0 0) hz
    norm_num [mixed, rejected, realize] at he
  · exact identity_not_discard hd

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  norm_num [actual, realize]

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
      (@_root_.D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => 1 / (d : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy
    definition := some {
      owner := `D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy
      name := `D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy
