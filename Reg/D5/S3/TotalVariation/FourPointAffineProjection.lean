import D5.S3.TotalVariation.FourPointAffineProjection
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Data.Fin.Tuple.Sort

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.TotalVariation.FourPointAffineProjection
open _root_.D5.S3.TotalVariation.Pinsker (totalVariation)

namespace Reg.D5.S3.TotalVariation.FourPointAffineProjection

noncomputable section

open scoped BigOperators

universe u

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 4 → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ p => projectionDistance p) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law R := ∀ (p : Fin 4 → ℝ) (_hp : ∀ i, 0 ≤ p i) (_hs : ∑ i, p i = 1),
    (∀ {I : Type u} [Fintype I] (s : Point) (c : I → Point) (t : I → ℝ),
      (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) →
      projectionDistance p ≤ totalVariation p (tabulate (affineBitLaw s c t))) ∧
    ∃ (s : Point) (c : Fin 3 → Point) (t : Fin 3 → ℝ),
      (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) ∧
      totalVariation p (tabulate (affineBitLaw s c t)) = R.readout () () p

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let p : Fin 4 → ℝ := fun _ => 1 / 4
  have hp : ∀ i, 0 ≤ p i := by intro i; norm_num [p]
  have hs : ∑ i, p i = 1 := by norm_num [p, Fin.sum_univ_four]
  obtain ⟨s, c, t, _, htv⟩ := (h p hp hs).2
  change totalVariation p (tabulate (affineBitLaw s c t)) = -1 at htv
  apply (by norm_num : ¬ 0 ≤ (-1 : ℝ))
  rw [← htv]
  unfold totalVariation
  positivity

theorem dependence : ObservationalDependence signature actual := by
  intro role
  let p : Fin 4 → ℝ := fun _ => 1 / 4
  let q : Fin 4 → ℝ := fun i => (i.val : ℝ) / 6
  refine ⟨(), p, q, ?_⟩
  have hp : projectionDistance p = 0 := by
    change max 0
      (((1 : ℝ) / 4 - 1 / 4 + 1 / 4 - 1 / 4) * (1 / 4 - 1 / 4 - 1 / 4 + 1 / 4) -
        (1 / 4 + 1 / 4 - 1 / 4 - 1 / 4)) / (2 * (1 + (1 / 4 - 1 / 4 - 1 / 4 + 1 / 4))) = 0
    norm_num
  have hsort : Tuple.sort q = Equiv.refl _ := Tuple.sort_eq_refl_iff_monotone.mpr (by
    intro i j hij
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (by norm_num))
  have hnorm : normalizedMass q = ![(3 : ℝ) / 6, 0, 1 / 6, 2 / 6] := by
    funext i
    change q (Tuple.sort q ((![3, 0, 1, 2] : Fin 4 → Fin 4) i)) = _
    rw [hsort]
    fin_cases i <;> norm_num [q]
  have hq : projectionDistance q = 1 / 15 := by
    unfold projectionDistance
    rw [hnorm]
    change max 0 (((3 : ℝ) / 6 - 0 + 1 / 6 - 2 / 6) * (3 / 6 - 0 - 1 / 6 + 2 / 6) -
      (3 / 6 + 0 - 1 / 6 - 2 / 6)) / (2 * (1 + (3 / 6 - 0 - 1 / 6 + 2 / 6))) = 1 / 15
    norm_num
  change projectionDistance p ≠ projectionDistance q
  rw [hp, hq]
  norm_num

def sourceRegistration : Registration arena.{u} (type_of% @affine_projection_exact.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@affine_projection_exact, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@affine_projection_exact.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.FourPointAffineProjection.unit
  realizationName := `Reg.D5.S3.TotalVariation.FourPointAffineProjection.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => projectionDistance p) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.TotalVariation.FourPointAffineProjection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.TotalVariation.FourPointAffineProjection
