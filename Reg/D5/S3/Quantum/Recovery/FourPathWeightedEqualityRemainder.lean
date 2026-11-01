import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder
open scoped Matrix.Norms.Frobenius

noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder

abbrev claim : Prop := ∀ (v : Index → ℂ) (U : Matrix Index Index ℂ),
  U ∈ Matrix.unitaryGroup Index ℂ →
    ∃ phase : ℂ, ‖phase‖ = 1 ∧
      ‖transport U v - phase • Matrix.diagonal (fun i => (‖v i‖ : ℂ))‖ ^ 2 ≤
        2 * remainder U v

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop × Bool
  Anchor := Unit
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => (claim, b)) (fun _ _ => false)

def rejected : Realization signature :=
  realize signature (fun _ _ b => (claim, !b)) (fun _ _ => false)

def altered : Realization signature :=
  realize signature (fun _ _ b => (claim, b)) (fun _ _ => true)

abbrev arena : Arena where
  signature := signature
  Law R := claim ∧ R.readout () () true = (claim, true) ∧ R.anchor () () = false

theorem actual_law : arena.Law actual := by
  refine ⟨?_, rfl, rfl⟩
  intro v U hU
  exact weighted_equality_remainder v U hU

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrArg Prod.snd h.2.1
  simpa [rejected, realize] using hb

theorem altered_law : ¬ arena.Law altered := by
  intro h
  have ha := h.2.2
  simpa [altered, realize] using ha

def source_registration : Registration arena claim where
  actual := actual
  bridge := by
    constructor
    · intro h
      exact ⟨h, rfl, rfl⟩
    · intro h
      exact h.1
  variation := ⟨actual_law, ⟨rejected, rejected_law⟩⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      refine ⟨altered, rfl, ?_, altered_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
  dependence := by
    intro i
    refine ⟨(), false, true, ?_⟩
    simp [actual, realize]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder.weighted_equality_remainder)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => (claim, b)) (fun _ _ => false))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Quantum.Recovery.FourPathWeightedEqualityRemainder
