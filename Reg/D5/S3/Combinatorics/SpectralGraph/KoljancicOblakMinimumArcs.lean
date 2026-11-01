import D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs
open _root_.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State n := Finset (Fin n × Fin n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ E => E.card) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem singleton_exact : ExactSupport
    (Finset.univ : Finset (Fin 1 × Fin 1)) (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  intro i j
  have hij : i = j := Subsingleton.elim _ _
  simp [hij]

private theorem singleton_nssp : HasNSSP (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  intro X hX _
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  have h := hX i j
  simpa [hij] using h

private theorem singleton_connected : ConnectedSupport
    (Finset.univ : Finset (Fin 1 × Fin 1)) := by
  intro p _ i j
  exact congrArg p (Subsingleton.elim _ _)

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨1, ∅, Finset.univ, ?_⟩
  norm_num [actual, realize]

namespace Cycle
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {n : ℕ} (E : Finset (Fin n × Fin n))
    (A : Matrix (Fin n) (Fin n) ℝ), ExactSupport E A → HasNSSP A →
    n + (incidence E).rank ≤ O.readout () n E

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h Finset.univ 1 singleton_exact singleton_nssp
  change 1 + _ ≤ 0 at hbad
  omega

def family : Registration arena (type_of% @nssp_centralizer_cycle_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nssp_centralizer_cycle_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration
    (@nssp_centralizer_cycle_bound) (Realization signature) (Type → Type) Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.nssp_centralizer_cycle_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.Cycle.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show Nonempty (Realization signature) from ⟨actual⟩)⟩ trivial
  readout := some (realize signature (fun _ _ E => E.card) (fun e => nomatch e))
  variation := .evidence ⟨family.variation⟩ trivial
  sensitivity := .evidence ⟨family.sensitivity⟩ trivial
  partialSensitivity := none
  escapeFrom := some (@Finset.{0})
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Cycle

namespace Connected
abbrev arena : Arena where
  signature := signature
  Law O := ∀ {n : ℕ}, 1 ≤ n → ∀ (E : Finset (Fin n × Fin n)), ConnectedSupport E →
    ∀ (A : Matrix (Fin n) (Fin n) ℝ), ExactSupport E A → HasNSSP A →
    2*n-1 ≤ O.readout () n E

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (by decide : 1 ≤ 1) Finset.univ singleton_connected 1 singleton_exact singleton_nssp
  change 2*1-1 ≤ 0 at hbad
  omega

def family : Registration arena (type_of% @nssp_arc_bound_of_connected) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nssp_arc_bound_of_connected, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration
    (@nssp_arc_bound_of_connected) (Realization signature) (Type → Type) Unit where
  unitName := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.nssp_arc_bound_of_connected.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.Connected.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show Nonempty (Realization signature) from ⟨actual⟩)⟩ trivial
  readout := some (realize signature (fun _ _ E => E.card) (fun e => nomatch e))
  variation := .evidence ⟨family.variation⟩ trivial
  sensitivity := .evidence ⟨family.sensitivity⟩ trivial
  partialSensitivity := none
  escapeFrom := some (@Finset.{0})
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Connected
end Reg.D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs
