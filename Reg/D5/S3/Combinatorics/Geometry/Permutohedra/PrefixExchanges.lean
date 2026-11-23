import D5.S3.Combinatorics.Geometry.Permutohedra.PrefixExchanges
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the rank of a prefix before an adjacent-exchange batch. -/

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.Geometry.Permutohedra.PrefixExchanges

open _root_.Rossi
open _root_.D5.S3.Combinatorics.Graph.PrefixHamming
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.SingleDependentReadout (sensitivity)
open LeanInformationAudit

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ Rank (fun _ => ℕ)

private def actual : Realization signature :=
  realize signature (fun _ _ s => s.1.val) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (p : Equiv.Perm (Fin n))
    (ds : List (Rank n)) (_ : ds.Nodup) (s : Rank n),
    prefixSet (batch p ds) s.1.val ≠ prefixSet p (R.readout () n s) ↔ s ∈ ds

private def first : Rank 2 := ⟨1, by decide⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law (Equiv.refl (Fin 2)) [] (by simp) first
  exact List.not_mem_nil (h.mp (by decide))

def batchEvidence : Registration arena (type_of% (@Rossi.batch_prefix_ne_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Rossi.batch_prefix_ne_iff, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    exact ⟨3, ⟨1, by decide⟩, ⟨2, by decide⟩, by decide⟩

def batchRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@Rossi.batch_prefix_ne_iff) (Realization signature) Unit Unit where
  unitName := `Rossi.batch_prefix_ne_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.Permutohedra.PrefixExchanges.batchEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨batchEvidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => s.1.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.Permutohedra.PrefixExchanges
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Geometry.Permutohedra.PrefixExchanges
