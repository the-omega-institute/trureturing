import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Kozlov.ChainedCount

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Combinatorics.Kozlov

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.Kozlov.ProperSumset

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Set (FVector n)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ n r,
    Set.SurjOn (sumTuple (n := n) (r := r))
      {s | (∀ i, s i ∈ SnF n) ∧ Chained s} (obs.readout () n r)

private def actual : Realization signature :=
  realize signature (fun _ n r => properSumset n r) (fun e _ => e.elim)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e _ => e.elim)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨s, _, hs⟩ := h 1 0 (Set.mem_univ (fun _ => (1 : ℕ)))
  have h' := congrFun hs (0 : Fin 2)
  simp [sumTuple] at h'

private theorem zero_not_proper : (fun _ => (0 : ℕ)) ∉ properSumset 1 1 := by
  rintro ⟨s, hs, he⟩
  have hp := (SnF_fixed (n := 1) le_rfl (hs 0)).1
  have h := congrFun he (0 : Fin 2)
  simp [sumTuple, hp] at h

private theorem observation_depends_on_rank : ObservationalDependence signature actual := by
  intro _
  refine ⟨1, 0, 1, ?_⟩
  intro he
  apply zero_not_proper
  change properSumset 1 0 = properSumset 1 1 at he
  rw [← he]
  exact ⟨fun i => i.elim0, fun i => i.elim0, funext fun j => by simp [sumTuple]⟩

def source : Registration arena (type_of% proper_sumset_surjOn) where
  actual := realize signature (fun _ n r => properSumset n r) (fun e _ => e.elim)
  bridge := Iff.rfl
  variation := ⟨proper_sumset_surjOn, rejected, rejected_law⟩
  sensitivity := by
    refine ⟨fun i => ⟨rejected, ?_, rfl, rejected_law⟩, fun e => e.elim⟩
    intro j h
    exact (h (Subsingleton.elim j i)).elim
  dependence := observation_depends_on_rank

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      proper_sumset_surjOn (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Kozlov.proper_sumset_surjOn.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Kozlov.ProperSumset.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n r => properSumset n r) (fun e _ => e.elim))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Kozlov.ProperSumset
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Kozlov.ProperSumset
