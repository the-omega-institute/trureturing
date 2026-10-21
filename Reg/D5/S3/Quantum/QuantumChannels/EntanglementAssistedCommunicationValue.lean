import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue
import Reg.Support.DependentFamily

/-! Source-bound audit of the entanglement-assisted communication-value bound. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue

open _root_.D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Σ _a : ℕ, ℕ
  State p := MatrixMap (Fin p.1) (Fin p.2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ N => commValue N) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ N => eaCommValue N - 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b →
    ∀ N : MatrixMap (Fin a) (Fin b) ℂ, IsChannel N →
      eaCommValue N ≤ (b : ℝ) * R.readout () ⟨a, b⟩ N

private def oneChannel : MatrixMap (Fin 1) (Fin 1) ℂ :=
  MatrixMap.of_kraus (fun _ : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ))
    (fun _ : Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ))

private theorem oneChannel_eq_id : oneChannel = MatrixMap.id (Fin 1) ℂ := by
  ext X i j
  fin_cases i
  fin_cases j
  simp [oneChannel, MatrixMap.of_kraus, MatrixMap.id]

private theorem id_channel : IsChannel oneChannel := by
  constructor
  · exact MatrixMap.of_kraus_isCompletelyPositive _
  · intro X
    simp [oneChannel, MatrixMap.of_kraus, Matrix.trace]

private theorem comm_zero_upper :
    commValue (0 : MatrixMap (Fin 1) (Fin 1) ℂ) ≤ 0 := by
  have hmem : (0 : ℝ) ∈ commValues (0 : MatrixMap (Fin 1) (Fin 1) ℂ) := by
    refine ⟨1, 1, by norm_num, by norm_num,
      (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)),
      (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)), ?_, ?_, ?_, ?_⟩
    · intro x
      constructor
      · exact Matrix.PosSemidef.one
      · norm_num [Matrix.trace]
    · intro y
      exact Matrix.PosSemidef.one
    · exact Fin.sum_univ_one _
    · simp [classicalCV, oneChannel]
  unfold commValue
  apply csSup_le ⟨0, hmem⟩
  rintro v ⟨n, n', hn, hn', ρ, M, hρ, hM, hs, rfl⟩
  unfold classicalCV
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro y _
  apply Finset.sup'_eq_of_forall
  intro x _
  simp

private theorem comm_id_mem :
    (1 : ℝ) ∈ commValues oneChannel := by
  refine ⟨1, 1, by norm_num, by norm_num,
    (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)),
    (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)), ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · exact Matrix.PosSemidef.one
    · norm_num [Matrix.trace]
  · intro y
    exact Matrix.PosSemidef.one
  · exact Fin.sum_univ_one _
  · norm_num [classicalCV, oneChannel, MatrixMap.of_kraus, Matrix.trace]

private theorem comm_id_upper : BddAbove (commValues oneChannel) := by
  refine ⟨1, ?_⟩
  rintro v ⟨n, n', hn, hn', ρ, M, hρ, hM, hs, rfl⟩
  have hrho (x : Fin n) : ρ x = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.trace] using (hρ x).2
  have h (y : Fin n') := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Fin n))) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (fun x : Fin n => (trace (M y * oneChannel (ρ x))).re)
  choose f _ hf using h
  unfold classicalCV
  simp_rw [hf]
  simp only [hrho, oneChannel_eq_id, MatrixMap.id, LinearMap.id_apply, Matrix.mul_one]
  rw [← Complex.re_sum, ← trace_sum, hs]
  simp [Matrix.trace]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 1 (by norm_num) (by norm_num)
    oneChannel id_channel
  simp [rejected, realize] at hbad
  linarith

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, (0 : MatrixMap (Fin 1) (Fin 1) ℂ),
    oneChannel, ?_⟩
  change commValue (0 : MatrixMap (Fin 1) (Fin 1) ℂ) ≠
    commValue oneChannel
  have hz := comm_zero_upper
  have hi : (1 : ℝ) ≤ commValue oneChannel :=
    le_csSup comm_id_upper comm_id_mem
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
      (@_root_.D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue.source_registration
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
    (realize signature (fun _ _ N => commValue N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue
    definition := some {
      owner := `D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue
      name := `D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
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
end Reg.D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue
