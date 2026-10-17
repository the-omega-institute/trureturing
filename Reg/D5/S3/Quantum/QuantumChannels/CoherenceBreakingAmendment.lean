import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment
import Reg.Support.DependentFamily

/-! # Coherence-breaking minimal-index readout -/

namespace Reg.D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment
open _root_.D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment
open _root_.D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
  (IsKrausChannel krausApply)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe coherence breaking of the iterates in the minimal-index condition. -/
abbrev signature : Signature where
  Params := ℕ
  State d := Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

open Classical in
def actual : Realization signature :=
  realize signature (fun _ _ Φ => decide (IsCoherenceBreaking Φ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d r : ℕ) (K : Fin r → Matrix (Fin d) (Fin d) ℂ),
    IsKrausChannel K → IsIncoherentKraus K →
    ∀ n : ℕ, 2 ≤ n → IsCoherenceBreaking (krausApply K)^[n] →
      (∀ k, 1 ≤ k → k < n → ¬ R.readout () d (krausApply K)^[k] = true) →
      ∃ U ∈ Matrix.unitaryGroup (Fin d) ℂ, ¬ IsCoherenceBreaking (amended K U n)

theorem one_dimensional_breaking
    (Φ : Matrix (Fin 1) (Fin 1) ℂ → Matrix (Fin 1) (Fin 1) ℂ) :
    IsCoherenceBreaking Φ := by
  intro ρ _ _ i j hij
  exact (hij (Subsingleton.elim i j)).elim

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let K : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1
  have hchannel : IsKrausChannel K := by simp [IsKrausChannel, K]
  have hincoherent : IsIncoherentKraus K := by
    intro s j
    refine ⟨0, ?_⟩
    intro i hi
    exact (hi (Subsingleton.elim i 0)).elim
  obtain ⟨U, _, hU⟩ := h 1 1 K hchannel hincoherent 2 (by decide)
    (one_dimensional_breaking _) (by intro k _ _; change ¬ false = true; decide)
  exact hU (one_dimensional_breaking _)

theorem dependence : ObservationalDependence signature actual := by
  intro _
  let Φ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun _ => 0
  let Ψ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun _ _ _ => 1
  have hΦ : IsCoherenceBreaking Φ := by intro ρ _ _ i j _; rfl
  have hΨ : ¬ IsCoherenceBreaking Ψ := by
    intro h
    let ρ : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun i => if i = 0 then 1 else 0)
    have hp : ρ.PosSemidef := by
      apply Matrix.posSemidef_diagonal_iff.mpr
      intro i
      split_ifs <;> norm_num
    have ht : ρ.trace = 1 := by simp [ρ, Matrix.trace]
    have he := h ρ hp ht 0 1 (by decide)
    norm_num [Ψ] at he
  refine ⟨2, Φ, Ψ, ?_⟩
  simp [actual, realize, hΦ, hΨ]

def source_registration : Registration arena claim where
  actual := actual
  bridge := by simp [actual, realize, claim]
  variation := ⟨by simpa [actual, realize, claim] using result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

open Classical in
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
    (realize signature (fun _ _ Φ => decide (IsCoherenceBreaking Φ)) (fun e => nomatch e))
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
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "body", "body", "body", "arg"]
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
end Reg.D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment
