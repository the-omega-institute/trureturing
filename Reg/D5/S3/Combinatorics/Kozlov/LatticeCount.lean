import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Kozlov.LatticeCount

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Combinatorics.Kozlov

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.Kozlov.LatticeCount

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State p := Fin p.2 → FVector p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := FVector p.1
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {n : ℕ} (hn : 1 ≤ n) (r : ℕ) {x : FVector n}
    (_hx : x ∈ natDilation hn r),
    ∃ s : Fin r → FVector n, (∀ i, s i ∈ latticeVectors hn) ∧
      Chained s ∧ obs.readout () ⟨n, r⟩ s = x

private def actual : Realization signature :=
  realize signature (fun _ p s => sumTuple (n := p.1) (r := p.2) s) (fun e _ => e.elim)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e _ => e.elim)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn : 1 ≤ (1 : ℕ) := le_rfl
  have hx : skeleton 1 1 ∈ natDilation hn 1 :=
    (mem_latticeVectors hn).mp (skeleton_mem_latticeVectors hn le_rfl)
  obtain ⟨s, _, _, hs⟩ := h hn 1 hx
  have h' := congrFun hs (0 : Fin 2)
  change (0 : ℕ) = skeleton 1 1 0 at h'
  simp [skeleton, cap] at h'

private theorem observation_depends_on_tuple : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨1, 1⟩, fun _ _ => 0, fun _ _ => 1, ?_⟩
  intro he
  have h := congrFun he (0 : Fin 2)
  change sumTuple (r := 1) (fun _ _ => 0) (0 : Fin 2) =
    sumTuple (r := 1) (fun _ _ => 1) (0 : Fin 2) at h
  simp [sumTuple] at h

def source : Registration arena (type_of% (@lattice_chained_exists)) where
  actual := realize signature
    (fun _ p s => sumTuple (n := p.1) (r := p.2) s) (fun e _ => e.elim)
  bridge := Iff.rfl
  variation := ⟨@lattice_chained_exists, rejected, rejected_law⟩
  sensitivity := by
    refine ⟨fun i => ⟨rejected, ?_, rfl, rejected_law⟩, fun e => e.elim⟩
    intro j h
    exact (h (Subsingleton.elim j i)).elim
  dependence := observation_depends_on_tuple

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@lattice_chained_exists) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Kozlov.lattice_chained_exists.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Kozlov.LatticeCount.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s => sumTuple (n := p.1) (r := p.2) s) (fun e _ => e.elim))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Kozlov.LatticeCount
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Kozlov.LatticeCount
