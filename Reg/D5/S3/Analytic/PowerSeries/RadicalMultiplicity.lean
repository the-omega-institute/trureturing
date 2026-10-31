import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PowerSeries.RadicalMultiplicity
import Reg.Support.DependentFamily

/-! The cutoff audit observes the radical family in its final sum. -/

open scoped PowerSeries LaurentSeries
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit CdsoRadical
noncomputable section

namespace Reg.D5.S3.Analytic.PowerSeries.RadicalMultiplicity
universe u

abbrev signature : Signature.{u+1,u,0,u,0} where
  Params := Type u
  State I := I → ℝ⟦X⟧
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ I := I → ℝ⟦X⟧
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ S => S) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ _ => (1 : ℝ⟦X⟧)) (fun e => nomatch e)

abbrev arena : Arena.{u+1,u,0,u,0} where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι]
    (S : ι → ℝ⟦X⟧) (p A : ι → Polynomial ℝ)
    (_ : ∀ j, PowerSeries.constantCoeff (S j) ≠ 0)
    (_ : ∀ j, S j ^ 2 = (p j : ℝ⟦X⟧))
    (_ : ∀ j, (p j).natDegree ≤ 2)
    (_ : ∀ j, (A j).natDegree ≤ Fintype.card ι)
    (_ : ∀ k ≤ 3 * (Fintype.card ι)^2,
      PowerSeries.coeff k (∑ j, (A j : ℝ⟦X⟧) * S j) = 0),
    ∑ j, (A j : ℝ⟦X⟧) * R.readout () ι S j = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let I := ULift.{u} (Fin 2)
  let S : I → ℝ⟦X⟧ := fun i => if i.down = 0 then 1 else -1
  let p : I → Polynomial ℝ := fun _ => 1
  let A : I → Polynomial ℝ := fun _ => 1
  have hS0 : ∀ i, PowerSeries.constantCoeff (S i) ≠ 0 := by
    intro i
    by_cases hi : i.down = 0 <;> simp [S, hi]
  have hs : ∀ i, S i ^ 2 = (p i : ℝ⟦X⟧) := by
    intro i
    by_cases hi : i.down = 0 <;> simp [S, p, hi]
  have hZ : (∑ i : I, (A i : ℝ⟦X⟧) * S i) = 0 := by
    simp [I, A, S, Fin.sum_univ_two]
  have he := @h I inferInstance S p A hS0 hs
    (by intro i; simp [p]) (by intro i; simp [A])
    (by intro k hk; rw [hZ]; simp)
  change (∑ _i : I, (1 : ℝ⟦X⟧) * 1) = 0 at he
  norm_num [I, Fin.sum_univ_two] at he

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
  refine ⟨ULift Unit, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have he := congrFun h (ULift.up ())
  norm_num [actual, realize] at he

def family : Registration arena (type_of% @sum_eq_zero_of_coeff_eq_zero.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_eq_zero_of_coeff_eq_zero.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{u+1,0,1,0,0,0,u+1,u,0,u,0,0}
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
  readout := some (realize signature (fun _ _ S => S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PowerSeries.RadicalMultiplicity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.PowerSeries.RadicalMultiplicity
