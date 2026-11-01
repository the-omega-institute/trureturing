import D5.S0.FiniteGeometry.FiniteIncrementPathBound
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! A whole-path norm observation with the complete uniform-path telescope. -/

namespace Reg.D5.S0.FiniteGeometry.FiniteIncrementPathBound

open _root_.D5.S0.FiniteGeometry.FiniteIncrementPathBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped InnerProductSpace

universe u
noncomputable section

structure Space where
  carrier : Type u
  normed : NormedAddCommGroup carrier
  inner : InnerProductSpace ℝ carrier
  finite : FiniteDimensional ℝ carrier

attribute [instance] Space.normed Space.inner Space.finite

abbrev signature : Signature where
  Params := Space.{u}
  State p := ℕ → p.carrier
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ w k => ‖w k‖) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ k => (k : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {E : Type u} [hN : NormedAddCommGroup E]
    [hI : InnerProductSpace ℝ E] [hD : FiniteDimensional ℝ E] (V : Finset E),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (w : ℕ → E), w 0 = 0 →
      (∀ k < N, w (k + 1) - w k ∈ V ∧
        ⟪w k, w (k + 1) - w k⟫_ℝ ≤ 0) →
      ∀ k ≤ N, r.readout () ⟨E, hN, hI, hD⟩ w k ≤ C

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let E := EuclideanSpace ℝ (ULift.{u} Unit)
  obtain ⟨C, _, hC⟩ := @h E inferInstance inferInstance inferInstance {0}
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hh := hC n (fun _ => 0) rfl (by simp) n le_rfl
  change (n : ℝ) ≤ C at hh
  exact (not_le_of_gt hn) hh

private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  classical
  intro _
  let E := EuclideanSpace ℝ (ULift.{u} Unit)
  let v : E := EuclideanSpace.single (ULift.up ()) 1
  refine ⟨⟨E, inferInstance, inferInstance, inferInstance⟩,
    (fun _ => 0), (fun _ => v), ?_⟩
  intro he
  have hh := congrFun he 0
  change ‖(0 : E)‖ = ‖v‖ at hh
  simp [v, EuclideanSpace.single, PiLp.norm_single] at hh

def family : Registration arena.{u} (type_of% (@exists_uniform_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_uniform_bound.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_uniform_bound.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S0.FiniteGeometry.FiniteIncrementPathBound.exists_uniform_bound.__information_unit
  realizationName := `Reg.D5.S0.FiniteGeometry.FiniteIncrementPathBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.FiniteGeometry.FiniteIncrementPathBound
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S0.FiniteGeometry.FiniteIncrementPathBound
