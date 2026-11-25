import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Powers.CommonWitnessCompactness
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace RegAttempt
open _root_.D5.S1.Words.Powers.CommonWitnessCompactness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Type
  State A := Set (List A × List A)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev claim (A : Type) (G : Set (List A × List A)) : Prop :=
  CommonWitness G ↔
    ∀ T : Set (List A × List A), T ⊆ G → T.Finite → CommonWitness T

noncomputable def actual : Realization signature := realize signature
  (fun _ A G => decide (claim A G)) (fun e => nomatch e)

noncomputable def rejected : Realization signature := realize signature
  (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (A : Type) (G : Set (List A × List A)),
    R.readout () A G = true ↔ claim A G

theorem actual_law : arena.Law actual := by
  intro A G
  simp [actual, claim, commonWitness_iff_finite]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h Empty (∅ : Set (List Empty × List Empty))).mp
  simp [rejected, claim] at bad

def evidence : Registration arena (∀ (A : Type) (G : Set (List A × List A)), claim A G) where
  actual := actual
  bridge := by simp [arena, actual, claim, commonWitness_iff_finite]
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨Empty, (∅ : Set (List Empty × List Empty)), (∅ : Set (List Empty × List Empty)), ?_⟩
    rfl

end RegAttempt
