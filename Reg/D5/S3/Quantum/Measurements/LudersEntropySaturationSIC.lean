import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurements.LudersEntropySaturationSIC
import Reg.Support.DependentFamily

/-! Source-bound audit of the SIC existence conclusion of entropy saturation. -/

namespace Reg.D5.S3.Quantum.Measurements.LudersEntropySaturationSIC

open _root_.D5.S3.Quantum.Measurements.LudersEntropySaturationSIC
open _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open _root_.D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators ComplexOrder MatrixOrder
open MeasureTheory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private instance oneIndexUnique : Unique (Fin ((1 : ℕ) ^ 2)) where
  default := ⟨0, by norm_num⟩
  uniq i := by
    apply Fin.ext
    have hi := i.isLt
    norm_num at hi
    omega

/-- Observe the SIC predicate on the candidate measurement family. -/
abbrev signature : Signature where
  Params := ℕ
  State d := Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ d f => @decide (IsSIC d f) (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- Keep the full saturation implication and vary only its SIC conclusion. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (d : ℕ) [NeZero d]
    (e : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ),
    IsMIC d e →
    typicalEntropy d e = Real.log (d + 1) - 2 / (d + 1) * Real.log 2 →
    ∃ f : Fin (d ^ 2) → Matrix (Fin d) (Fin d) ℂ, r.readout () d f = true

private theorem one_mic : IsMIC 1 (fun _ => 1) := by
  refine ⟨fun _ => Matrix.PosSemidef.one, ?_, ?_⟩
  · simp
  · exact linearIndependent_unique_iff.mpr one_ne_zero

private theorem entropy_fin_one (rho : DensityState (Fin 1)) :
    vonNeumannEntropy rho = 0 := by
  have hv : rho.val = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.trace, Matrix.diag] using rho.property.2
  simp [vonNeumannEntropy, hv, Matrix.trace, Matrix.diag]

private theorem one_saturation :
    typicalEntropy 1 (fun _ => 1) = Real.log (1 + 1) - 2 / (1 + 1) * Real.log 2 := by
  have hz : typicalEntropy 1 (fun _ => 1) = 0 := by
    unfold typicalEntropy
    simp only [entropy_fin_one, integral_zero]
  rw [hz]
  norm_num

private theorem one_sic : IsSIC 1 (fun _ => 1) := by
  refine ⟨one_mic, ?_, 1, 0, ?_⟩
  · intro i
    exact ⟨1, 1, Matrix.isHermitian_one, by simp, by simp, by simp⟩
  · intro i j
    have hij : i = j := Subsingleton.elim _ _
    simp [hij]

private theorem zero_not_sic : ¬ IsSIC 1 (fun _ => 0) := by
  intro h
  have hi := linearIndependent_unique_iff.mp h.1.2.2
  exact hi rfl

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨f, hf⟩ := h 1 (fun _ => 1) one_mic
    (by simpa only [Nat.cast_one] using one_saturation)
  change false = true at hf
  exact Bool.false_ne_true hf

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 1), (fun _ => 0), ?_⟩
  have ht : actual.readout i 1 (fun _ => 1) = true :=
    @decide_eq_true _ (Classical.propDecidable _) one_sic
  have hf : actual.readout i 1 (fun _ => 0) = false :=
    @decide_eq_false _ (Classical.propDecidable _) zero_not_sic
  rw [ht, hf]
  exact fun h => Bool.false_ne_true h.symm

def source_registration : Registration arena claim where
  actual := actual
  bridge := by
    simp only [claim, actual, realize, decide_eq_true_eq]
  variation := ⟨by
    intro d inst e he hs
    obtain ⟨f, hf⟩ := result d e he hs
    exact ⟨f, @decide_eq_true _ (Classical.propDecidable _) hf⟩,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.source_registration
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
    (fun _ d f => @decide (IsSIC d f) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.LudersEntropySaturationSIC
    definition := some {
      owner := `D5.S3.Quantum.Measurements.LudersEntropySaturationSIC
      name := `D5.S3.Quantum.Measurements.LudersEntropySaturationSIC.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurements.LudersEntropySaturationSIC
