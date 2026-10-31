import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SetFamily.SimultaneousCompression
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

namespace Reg.D5.S3.Combinatorics.SetFamily.SimultaneousCompression
open _root_.D5.S3.Combinatorics.SetFamily.SimultaneousCompression
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
noncomputable section
universe u
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Each role observes the initial exact-trace mass of one side. -/
abbrev signature : Signature where
  Params := Type u
  State α := (Finset α → ℝ) × Finset (Finset α)
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ p => mass p.1 p.2) (fun e => nomatch e)

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
      R.readout false α (w, A) ≤ mass (marginalWeight Ω w t) C ∧
      R.readout true α (v, B) ≤ mass (marginalWeight Ω v t) D ∧
      (A.Nonempty → C.Nonempty) ∧ (B.Nonempty → D.Nonempty)

/-- An intervention changes precisely one input-mass role. -/
def intervention (i : Bool) : Realization signature.{u} :=
  realize signature (fun j _ p => if j = i then 1 else mass p.1 p.2)
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
  cases i <;> simp [intervention, realize, hCe, hDe, mass] at hw hv

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let α := ULift.{u} (Fin 3)
  obtain ⟨C, D, hC, _, _, hw, _⟩ := h (α := α) ∅ ∅ ∅ ⟨0⟩ ⟨1⟩ ⟨2⟩
    (by simp) (by simp) (by decide) (by decide)
    (by simp) (by simp) (fun _ => 0) (fun _ => 0)
    (by simp) (by simp) (by simp) (by simp) (by simp [CrossIntersecting])
  have hCe : C = ∅ := by simpa using hC
  simp [rejected, realize, hCe, mass] at hw

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, ((fun _ => 0), {∅}), ((fun _ => 1), {∅}), ?_⟩
  simp [actual, realize, mass]

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
      funext α p
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
    (fun _ _ p => mass p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SetFamily.SimultaneousCompression
    definition := none
    coordinates := #[0]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Combinatorics.SetFamily.SimultaneousCompression
