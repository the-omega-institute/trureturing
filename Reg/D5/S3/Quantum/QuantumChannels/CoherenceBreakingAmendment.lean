import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment
import Reg.Support.DependentFamily

/-! # Channel-iterate readout in the minimal-index condition -/

namespace Reg.D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment
open Matrix
open _root_.D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment
open _root_.D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
  (IsKrausChannel krausApply)
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open _root_.D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation
  (pinching_kraus dephase_apply)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the channel iterates in the minimal-index condition. -/
abbrev signature : Signature where
  Params := Σ d : ℕ, Σ r : ℕ, Fin r → Matrix (Fin d) (Fin d) ℂ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1) (Fin p.1) ℂ → Matrix (Fin p.1) (Fin p.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p k => (krausApply p.2.2)^[k]) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d r : ℕ) (K : Fin r → Matrix (Fin d) (Fin d) ℂ),
    IsKrausChannel K → IsIncoherentKraus K →
    ∀ n : ℕ, 2 ≤ n → IsCoherenceBreaking (krausApply K)^[n] →
      (∀ k, 1 ≤ k → k < n → ¬ IsCoherenceBreaking (R.readout () ⟨d, r, K⟩ k)) →
      ∃ U ∈ Matrix.unitaryGroup (Fin d) ℂ, ¬ IsCoherenceBreaking (amended K U n)

theorem ones_not_breaking :
    ¬ IsCoherenceBreaking (fun _ : Matrix (Fin 2) (Fin 2) ℂ => fun _ _ => (1 : ℂ)) := by
  intro h
  let ρ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun i => if i = 0 then 1 else 0)
  have hp : ρ.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split_ifs <;> norm_num
  have ht : ρ.trace = 1 := by simp [ρ, Matrix.trace]
  have he := h ρ hp ht 0 1 (by decide)
  norm_num at he

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let K : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := fun j => Matrix.single j j 1
  have hchannel : IsKrausChannel K := by
    change (∑ j, (K j)ᴴ * K j) = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [K, Matrix.single, Matrix.conjTranspose_apply, Matrix.mul_apply,
        Fin.sum_univ_two]
  have hincoherent : IsIncoherentKraus K := by
    intro s j
    refine ⟨s, ?_⟩
    intro i hi
    simp [K, Matrix.single, Ne.symm hi]
  have hdiag (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) (hij : i ≠ j) :
      krausApply K X i j = 0 := by
    change (MatrixMap.of_kraus (fun k : Fin 2 => Matrix.single k k (1 : ℂ))
      (fun k : Fin 2 => Matrix.single k k (1 : ℂ)) X) i j = 0
    rw [← pinching_kraus, dephase_apply]
    simp [Matrix.diagonal, hij]
  have hpower : IsCoherenceBreaking (krausApply K)^[2] := by
    intro ρ _ _ i j hij
    exact hdiag (krausApply K ρ) i j hij
  obtain ⟨U, _, hU⟩ := h 2 2 K hchannel hincoherent 2 (by decide) hpower
    (by intro k _ _; exact ones_not_breaking)
  apply hU
  intro ρ _ _ i j hij
  exact hdiag _ i j hij

theorem dependence : ObservationalDependence signature actual := by
  intro _
  let K : Fin 0 → Matrix (Fin 1) (Fin 1) ℂ := Fin.elim0
  refine ⟨⟨1, 0, K⟩, 0, 1, ?_⟩
  intro he
  have hf := congrArg (fun Φ : Matrix (Fin 1) (Fin 1) ℂ →
      Matrix (Fin 1) (Fin 1) ℂ => Φ 1 0 0) he
  norm_num [actual, realize, krausApply, MatrixMap.of_kraus] at hf

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
      (@_root_.D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment.unit
  realizationName := .str
    `Reg.D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment "source_registration"
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
    (realize signature (fun _ p k => (krausApply p.2.2)^[k]) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment
    definition := some {
      owner := `D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment
      name := `D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment.claim
      path := #[] }
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "body", "body", "body", "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment
