import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.RegularCHS.Interface
import Reg.Support.DependentFamily

/-! Source operand registrations for regular graph CHS coefficients. -/

namespace Reg.D5.S3.Combinatorics.Graph.RegularCHS.Interface
open _root_.D5.S3.Combinatorics.Graph.RegularCHS.Defs
open _root_.D5.S3.Combinatorics.Graph.RegularCHS.Interface
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset Matrix
open scoped BigOperators
noncomputable section
open Classical
universe u

private abbrev scalarSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ x => x) (fun e => nomatch e)

private def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ => -1) (fun e => nomatch e)

private abbrev bseq_zeroArena : Arena where
  signature := scalarSignature
  Law R := ∀ n r : ℕ, R.readout () () (bseq n r 0) = 1

private theorem bseq_zeroRejected : ¬ bseq_zeroArena.Law rejected := by
  intro h
  have he := h 0 0
  norm_num [rejected, realize] at he

def bseq_zeroFamily : Registration bseq_zeroArena (type_of% @bseq_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bseq_zero, rejected, bseq_zeroRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bseq_zeroRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def bseq_zeroAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bseq_zero) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Interface.bseq_zeroUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Interface.bseq_zeroFamily
  realizationSource := none
  generated := false
  arena := .source ⟨bseq_zeroArena⟩
  objectArena := .source ⟨bseq_zeroArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source bseq_zeroArena ⟨bseq_zeroFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev bseq_succArena : Arena where
  signature := scalarSignature
  Law R := ∀ n r m : ℕ, (2 * (m + 1) : ℝ) * R.readout () () (bseq n r (m + 1)) =
    (r : ℝ) * ((n : ℝ) + 2 * (m + 1) - 2) * bseq n r m

private theorem bseq_succRejected : ¬ bseq_succArena.Law rejected := by
  intro h
  have he := h 0 0 0
  norm_num [rejected, realize] at he

def bseq_succFamily : Registration bseq_succArena (type_of% @bseq_succ) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bseq_succ, rejected, bseq_succRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bseq_succRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def bseq_succAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bseq_succ) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Interface.bseq_succUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Interface.bseq_succFamily
  realizationSource := none
  generated := false
  arena := .source ⟨bseq_succArena⟩
  objectArena := .source ⟨bseq_succArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source bseq_succArena ⟨bseq_succFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev bseq_recurrenceArena : Arena where
  signature := scalarSignature
  Law R := ∀ n r m : ℕ, 1 ≤ m → (2 * m : ℝ) * R.readout () () (bseq n r m) =
    (r : ℝ) * ((n : ℝ) + 2 * m - 2) * bseq n r (m - 1)

private theorem bseq_recurrenceRejected : ¬ bseq_recurrenceArena.Law rejected := by
  intro h
  have he := h 0 0 1 (by omega)
  norm_num [rejected, realize] at he

def bseq_recurrenceFamily : Registration bseq_recurrenceArena (type_of% @bseq_recurrence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bseq_recurrence, rejected, bseq_recurrenceRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bseq_recurrenceRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def bseq_recurrenceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@bseq_recurrence) (Realization scalarSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Interface.bseq_recurrenceUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Interface.bseq_recurrenceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨bseq_recurrenceArena⟩
  objectArena := .source ⟨bseq_recurrenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source bseq_recurrenceArena ⟨bseq_recurrenceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.RegularCHS.Interface
