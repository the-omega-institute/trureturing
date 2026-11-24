import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.PerfectMatchings.LiteralRibbonBoundaryDelta
import Reg.Support.DependentFamily

/-! Source-bound audit of the actual signed boundary-component delta. -/

namespace Reg.D5.S3.Combinatorics.PerfectMatchings.LiteralRibbonBoundaryDelta
open _root_.D5.S3.Combinatorics.PerfectMatchings
open FiniteEndpointPairing FiniteBandSwitch FourEndpoint OriginalCut LiteralRibbonBoundaryDelta
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Equiv LeanInformationAudit

noncomputable section
universe u
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev signature : Signature where
  Params := Unit
  State _ := MarkedRibbon.{u}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ R => boundaryDelta R) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law W := ∀ R : MarkedRibbon.{u},
    let observed := W.readout () () R
    (BadAt R.s R.t R.a R.b ↔ observed = 1) ∧
    (GoodAt R.s R.t R.a R.b ↔ observed = 0) ∧
    (RegularAt R.s R.t R.a R.b ↔ observed = -1)

private abbrev liftChart : Fin 4 ≃ ULift.{u} (Fin 4) := Equiv.ulift.symm

private theorem lift_inv (p : Perm (Fin 4)) (h : Function.Involutive p) :
    Function.Involutive (liftChart.{u}.permCongr p) := by
  intro x
  change ULift.up (p (p x.down)) = x
  rw [h]

private theorem lift_free (p : Perm (Fin 4)) (h : ∀ i, p i ≠ i) :
    ∀ x, liftChart.{u}.permCongr p x ≠ x := by
  intro x eq
  exact h x.down (congrArg ULift.down eq)

private def toy (p : Perm (Fin 4)) (hp : Function.Involutive p)
    (hf : ∀ i, p i ≠ i) : MarkedRibbon.{u} where
  X := ULift.{u} (Fin 4)
  finite := inferInstance
  s := liftChart.permCongr p
  t := liftChart.permCongr J0
  hs := lift_inv p hp
  ht := lift_inv J0 (by intro i; fin_cases i <;> rfl)
  hsfree := lift_free p hf
  htfree := lift_free J0 (by decide)
  a := liftChart 0
  b := liftChart 1
  distinctFlags := by
    have h (i : Fin 4) :
        boundaryLabel (liftChart.{u}.permCongr J0) (liftChart 0) (liftChart 1) i =
          liftChart i := by fin_cases i <;> rfl
    intro i j eq
    rw [h, h] at eq
    exact liftChart.injective eq

private def badWitness : MarkedRibbon.{u} :=
  toy thirdPairing (by intro i; fin_cases i <;> rfl) (by decide)

private def regularWitness : MarkedRibbon.{u} :=
  toy J0 (by intro i; fin_cases i <;> rfl) (by decide)

private theorem badWitness_bad : BadAt badWitness.{u}.s badWitness.t badWitness.a badWitness.b := by
  change (liftChart.{u}.permCongr thirdPairing * liftChart.permCongr J0).SameCycle
    (liftChart (thirdPairing 0)) (liftChart 1)
  exact Equiv.Perm.SameCycle.refl _ (liftChart 1)

private theorem regularWitness_regular :
    RegularAt regularWitness.{u}.s regularWitness.t regularWitness.a regularWitness.b := by
  have h : J0 * J0 = 1 := square_of_involutive _ (by intro i; fin_cases i <;> rfl)
  change ¬ (liftChart.{u}.permCongr J0 * liftChart.permCongr J0).SameCycle
      (liftChart 0) (liftChart 1) ∧
    ¬ (liftChart.{u}.permCongr J0 * liftChart.permCongr J0).SameCycle
      (liftChart (J0 0)) (liftChart 1)
  simp only [← liftChart.permCongr_mul, same_cycle_perm_congr, h, Equiv.Perm.sameCycle_one]
  decide

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have eq : (0 : ℤ) = 1 := (h badWitness.{u}).1.mp badWitness_bad
  exact (by decide : (0 : ℤ) ≠ 1) eq

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  have hr : role = () := Subsingleton.elim _ _
  subst role
  refine ⟨(),badWitness.{u},regularWitness.{u},?_⟩
  change boundaryDelta badWitness.{u} ≠ boundaryDelta regularWitness.{u}
  rw [(original_boundary_delta badWitness.{u}).1.mp badWitness_bad,
    (original_boundary_delta regularWitness.{u}).2.2.mp regularWitness_regular]
  decide

def source_registration : Registration arena.{u} (type_of% @original_boundary_delta.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_boundary_delta,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@original_boundary_delta.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Combinatorics.PerfectMatchings.LiteralRibbonBoundaryDelta.original_boundary_delta.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.PerfectMatchings.LiteralRibbonBoundaryDelta.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ R => boundaryDelta R) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.PerfectMatchings.LiteralRibbonBoundaryDelta
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Combinatorics.PerfectMatchings.LiteralRibbonBoundaryDelta
