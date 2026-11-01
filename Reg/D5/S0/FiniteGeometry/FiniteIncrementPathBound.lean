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
  inner : letI := normed; InnerProductSpace ℝ carrier
  finite : letI := normed; letI := inner; FiniteDimensional ℝ carrier

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
  have hv : v ≠ 0 := by
    intro hz
    have hh := congrArg (fun z : E => z (ULift.up ())) hz
    norm_num [v, EuclideanSpace.single] at hh
  refine ⟨⟨E, inferInstance, inferInstance, inferInstance⟩,
    (fun _ => 0), (fun k => if k = 0 then 0 else v), ?_⟩
  intro he
  have hh := congrFun he 1
  change ‖(0 : E)‖ = ‖(if (1 : ℕ) = 0 then 0 else v)‖ at hh
  have hz : ‖v‖ = 0 := by simpa using hh.symm
  exact hv (norm_eq_zero.mp hz)

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

end

end Reg.D5.S0.FiniteGeometry.FiniteIncrementPathBound
