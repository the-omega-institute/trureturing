import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SetFamily.SimultaneousCompression
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

/-! Two source-mass observations over the full simultaneous-compression telescope. -/

namespace Reg.D5.S3.Combinatorics.SetFamily.SimultaneousCompression
open _root_.D5.S3.Combinatorics.SetFamily.SimultaneousCompression
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
noncomputable section
universe u
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The common carrier with both independent weights. -/
abbrev Parameter := Σ α : Type u, (Finset α → ℝ) × (Finset α → ℝ)

/-- Each role observes the initial exact-trace mass of one side. -/
abbrev signature : Signature where
  Params := Parameter.{u}
  State p := Finset (Finset p.1)
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun i p F => mass (if i then p.2.2 else p.2.1) F) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete original telescope with its two input-mass observations exposed. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [DecidableEq α]
    (Ω A B : Finset (Finset α)) (s t u : α),
    A ⊆ Ω → B ⊆ Ω → s ≠ t → s ≠ u →
    (∀ X ∈ Ω, t ∈ X → s ∉ X ∧ u ∉ X) →
    (∀ X ∈ Ω, t ∈ X → shift s t X ∈ Ω) →
    ∀ (w v : Finset α → ℝ),
    (∀ X ∈ Ω, 0 ≤ w X) → (∀ X ∈ Ω, 0 ≤ v X) →
    (∀ X ∈ Ω, t ∈ X →
      w X = w (shift s t X) + if insert u (shift s t X) ∈ Ω then
        w (insert u (shift s t X)) else 0) →
    (∀ X ∈ Ω, t ∈ X →
      v X = v (shift s t X) + if insert u (shift s t X) ∈ Ω then
        v (insert u (shift s t X)) else 0) →
    CrossIntersecting A B →
    ∃ C D : Finset (Finset α),
      C ⊆ Ω.image (fun X => X.erase t) ∧ D ⊆ Ω.image (fun X => X.erase t) ∧
      CrossIntersecting C D ∧
      R.readout false ⟨α, w, v⟩ A ≤ mass (marginalWeight Ω w t) C ∧
      R.readout true ⟨α, w, v⟩ B ≤ mass (marginalWeight Ω v t) D ∧
      (A.Nonempty → C.Nonempty) ∧ (B.Nonempty → D.Nonempty)

/-- An intervention changes precisely one input-mass role. -/
def intervention (i : Bool) : Realization signature.{u} :=
  realize signature (fun j p F => if j = i then 1 else mass (if j then p.2.2 else p.2.1) F)
    (fun e => nomatch e)

private theorem intervention_law (i : Bool) : ¬ arena.{u}.Law (intervention i) := by
  intro h
  let α := ULift.{u} (Fin 3)
  let s : α := ⟨0⟩
  let t : α := ⟨1⟩
  let u : α := ⟨2⟩
  obtain ⟨C, D, hC, hD, _, hw, hv, _⟩ := h (α := α) ∅ ∅ ∅ s t u
    (by simp) (by simp) (by decide) (by decide)
    (by simp) (by simp) (fun _ => 0) (fun _ => 0)
    (by simp) (by simp) (by simp) (by simp) (by simp [CrossIntersecting])
  have hCe : C = ∅ := by simpa using hC
  have hDe : D = ∅ := by simpa using hD
  cases i with
  | false => norm_num [intervention, realize, hCe, hDe, mass] at hw
  | true => norm_num [intervention, realize, hCe, hDe, mass] at hv

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let α := ULift.{u} (Fin 3)
  obtain ⟨C, D, hC, _, _, hw, _⟩ := h (α := α) ∅ ∅ ∅ ⟨0⟩ ⟨1⟩ ⟨2⟩
    (by simp) (by simp) (by decide) (by decide)
    (by simp) (by simp) (fun _ => 0) (fun _ => 0)
    (by simp) (by simp) (by simp) (by simp) (by simp [CrossIntersecting])
  have hCe : C = ∅ := by simpa using hC
  norm_num [rejected, realize, hCe, mass] at hw

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, (fun _ => 1), (fun _ => 1)⟩, ∅, {∅}, ?_⟩
  cases i <;> simp [actual, realize, mass]

def source_registration :
    Registration arena.{u} (type_of% @exists_simultaneous_compression.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_simultaneous_compression.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervention i, ?_, rfl, intervention_law i⟩
      intro j hj
      funext p F
      simp [actual, intervention, realize, hj]
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_simultaneous_compression.{u}) (Realization signature.{u}) Bool Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SetFamily.SimultaneousCompression.unit
  realizationName := `Reg.D5.S3.Combinatorics.SetFamily.SimultaneousCompression.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun i p F => mass (if i then p.2.2 else p.2.1) F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SetFamily.SimultaneousCompression
    definition := none
    coordinates := #[0, 14, 15]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "body", "arg",
        "body", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "body", "arg",
        "body", "arg", "arg", "arg", "arg", "fn", "arg", "fn",
        "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


/-- The full support-iteration theorem with both original masses observed. -/
abbrev iteration_arena : Arena where
  signature := signature.{u}
  Law R := ∀ {α : Type u} [DecidableEq α] (J : Finset α) (S : DeletionSystem J)
    (A B : Finset (Finset α)), A ⊆ S.feasible J → B ⊆ S.feasible J →
    CrossIntersecting A B →
    ∃ K : Finset α, ∃ C D : Finset (Finset α),
      K ⊆ J ∧ S.terminal K ∧ C ⊆ S.feasible K ∧ D ⊆ S.feasible K ∧
      CrossIntersecting C D ∧ RelativelyUpper (S.feasible K) C ∧
      RelativelyUpper (S.feasible K) D ∧
      R.readout false ⟨α, S.leftWeight J, S.rightWeight J⟩ A ≤ mass (S.leftWeight K) C ∧
      R.readout true ⟨α, S.leftWeight J, S.rightWeight J⟩ B ≤ mass (S.rightWeight K) D ∧
      (A.Nonempty → C.Nonempty) ∧ (B.Nonempty → D.Nonempty)

private def empty_system : DeletionSystem (∅ : Finset (ULift.{u} Unit)) where
  feasible := fun _ => ∅
  leftWeight := fun _ _ => 0
  rightWeight := fun _ _ => 0
  terminal := fun _ => True
  left_nonneg := by simp
  right_nonneg := by simp
  projection := by simp
  left_marginal := by simp
  right_marginal := by simp
  local_move := by simp

private theorem iteration_intervention_law (i : Bool) :
    ¬ iteration_arena.{u}.Law (intervention i) := by
  intro h
  obtain ⟨K, C, D, _, _, _, _, _, _, _, hw, hv, _⟩ :=
    h ∅ empty_system ∅ ∅ (by simp [empty_system]) (by simp [empty_system])
      (by simp [CrossIntersecting])
  cases i with
  | false => norm_num [intervention, realize, empty_system, mass] at hw
  | true => norm_num [intervention, realize, empty_system, mass] at hv

private theorem iteration_rejected_law : ¬ iteration_arena.{u}.Law rejected := by
  intro h
  obtain ⟨K, C, D, _, _, _, _, _, _, _, hw, _⟩ :=
    h ∅ empty_system ∅ ∅ (by simp [empty_system]) (by simp [empty_system])
      (by simp [CrossIntersecting])
  norm_num [rejected, realize, empty_system, mass] at hw

def iteration_source_registration :
    Registration iteration_arena.{u} (type_of% @exists_terminal_compression.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_terminal_compression.{u}, rejected, iteration_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervention i, ?_, rfl, iteration_intervention_law i⟩
      intro j hj
      funext p F
      simp [actual, intervention, realize, hj]
    · intro e
      exact nomatch e
  dependence := dependence

def iteration_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_terminal_compression.{u}) (Realization signature.{u}) Bool Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SetFamily.SimultaneousCompression.iteration_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SetFamily.SimultaneousCompression.iteration_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨iteration_arena⟩
  objectArena := .source ⟨iteration_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source iteration_arena ⟨iteration_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun i p F => mass (if i then p.2.2 else p.2.1) F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SetFamily.SimultaneousCompression
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms iteration_source_registration
#print axioms iteration_registration

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Combinatorics.SetFamily.SimultaneousCompression
