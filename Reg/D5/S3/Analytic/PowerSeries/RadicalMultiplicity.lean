import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PowerSeries.RadicalMultiplicity
import Reg.Support.DependentFamily

/-! The cutoff audit observes the actual radical sum at its final conclusion. -/

open scoped PowerSeries LaurentSeries
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit CdsoRadical
noncomputable section

namespace Reg.D5.S3.Analytic.PowerSeries.RadicalMultiplicity
universe u

structure Parameters where
  index : Type u
  finiteIndex : Fintype index
  coefficient : index → Polynomial ℝ

attribute [instance] Parameters.finiteIndex

abbrev signature : Signature where
  Params := Parameters.{u}
  State P := P.index → ℝ⟦X⟧
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ⟦X⟧
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ P S => letI := P.finiteIndex; ∑ i, (P.coefficient i : ℝ⟦X⟧) * S i) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => (1 : ℝ⟦X⟧)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι]
    (S : ι → ℝ⟦X⟧) (p A : ι → Polynomial ℝ)
    (_ : ∀ j, PowerSeries.constantCoeff (S j) ≠ 0)
    (_ : ∀ j, S j ^ 2 = (p j : ℝ⟦X⟧))
    (_ : ∀ j, (p j).natDegree ≤ 2)
    (_ : ∀ j, (A j).natDegree ≤ Fintype.card ι)
    (_ : ∀ k ≤ 3 * (Fintype.card ι)^2,
      PowerSeries.coeff k (∑ j, (A j : ℝ⟦X⟧) * S j) = 0),
    R.readout () ⟨ι, inferInstance, A⟩ S = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := @h (ULift Empty) inferInstance (fun i => nomatch i.down)
    (fun i => nomatch i.down) (fun i => nomatch i.down)
    (by intro i; exact i.down.elim) (by intro i; exact i.down.elim)
    (by intro i; exact i.down.elim) (by intro i; exact i.down.elim)
    (by intros; simp)
  exact one_ne_zero he

private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨ULift Unit, inferInstance, fun _ => 1⟩,
    (fun _ => 0), (fun _ => 1), ?_⟩
  simp [actual, realize]

def family : Registration arena (type_of% @sum_eq_zero_of_coeff_eq_zero.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_eq_zero_of_coeff_eq_zero.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration
    (@sum_eq_zero_of_coeff_eq_zero.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.PowerSeries.RadicalMultiplicity.cutoff_unit
  realizationName := `Reg.D5.S3.Analytic.PowerSeries.RadicalMultiplicity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ P S => letI := P.finiteIndex; ∑ i, (P.coefficient i : ℝ⟦X⟧) * S i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PowerSeries.RadicalMultiplicity
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.PowerSeries.RadicalMultiplicity
