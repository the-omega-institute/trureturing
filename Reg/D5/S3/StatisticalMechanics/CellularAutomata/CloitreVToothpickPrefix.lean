import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.CellularAutomata.CloitreVToothpickPrefix
import Reg.Support.SingleDependentReadout

/-! A dependent readout of the actual integer-valued kernel row at each degree. -/

namespace Reg.D5.S3.StatisticalMechanics.CellularAutomata.CloitreVToothpickPrefix

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.HoneycombCylinderCoordination (honeycombGraph)
open _root_.D5.S3.StatisticalMechanics.CellularAutomata
open HoneycombFirstTouch HoneycombBirthKernel
open _root_.D5.S3.StatisticalMechanics.CellularAutomata.CloitreVToothpickPrefix
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

attribute [local instance] repositoryAdjacency

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ j => birthKernelEntry j) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ c => (c : ℤ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {j c : ℕ}, 1 ≤ j → c + 2 ≤ j →
    let e := R.readout () ()
    e j c = e j (c + columnPeriod j) ∧
      e j (c + columnPeriod j) = e j (periodIndex j (columnPeriod j) (c % columnPeriod j)) ∧
      e j c - e j (periodIndex j (columnPeriod j) (c % columnPeriod j)) = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h (j := 2) (c := 0) (by decide) (by decide)).1
  change (0 : ℤ) = 8 at he
  omega

private theorem entries_at_zero :
    birthKernelEntry 0 0 = 1 ∧ birthKernelEntry 1 0 = 0 := by
  have dom : omegaDomain 1 0 = {A 0 0, B 0 0} := by
    ext v
    obtain ⟨p, x, y⟩ := v
    cases p <;>
      simp [omegaDomain, heightSum, g, part, A, B, Prod.mk.injEq] <;> omega
  have cut : omegaDomain 1 1 = {A 0 0} := by
    ext v
    obtain ⟨p, x, y⟩ := v
    cases p <;>
      simp [omegaDomain, heightSum, g, part, A, Prod.mk.injEq] <;> omega
  have coefficient (j : ℕ) :
      birthKernelEntry j 0 = ∑ v ∈ omegaDomain 1 0, signedWeight honeycombGraph 1 0 (1 + j) v := by
    unfold birthKernelEntry
    rw [kernelEntry_eq_coeff repositoryNeighborLaws
      (earliestBirthIff_of_neighborLaws repositoryNeighborLaws) (b := 0) j (by decide)]
    exact coeff_delta_on (fun _ hv => hv) _
  rw [coefficient 0, coefficient 1]
  simp only [signedWeight, dom, cut]
  decide

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have eq : birthKernelEntry 0 0 = birthKernelEntry 1 0 := congrFun h 0
    rw [entries_at_zero.1, entries_at_zero.2] at eq
    omega

def audit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@_root_.D5.S3.StatisticalMechanics.CellularAutomata.CloitreVToothpickPrefix.result)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.CloitreVToothpickPrefix.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.CloitreVToothpickPrefix.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ j => birthKernelEntry j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.CloitreVToothpickPrefix
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.StatisticalMechanics.CellularAutomata.CloitreVToothpickPrefix
