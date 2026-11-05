import D5.S1.Recurrence.CyclicPowerLattice
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Polynomial-evaluation dependence of the universal cyclic power lattice theorem. -/

open D5.S1.Recurrence.CyclicPowerLattice
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Polynomial

namespace Reg.D5.S1.Recurrence.CyclicPowerLattice
noncomputable section

abbrev signature : Signature where
  Params := Data
  State _ := ℤ[X]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Fin d.N → ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ d p => evaluation d p) (fun e => nomatch e)

abbrev bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ d : Data,
    (∀ j : Fin d.N, power d j.val = Pi.single j 1) ∧
    (∀ p : ℤ[X], r.readout () d p = 0 ↔ d.q ∣ p) ∧
    (lattice d d.N).toAddSubgroup = coordinateZ d.N ∧
    (∀ l : ℕ, d.N ≤ l →
      (∀ n : ℤ, n • power d l ∈ lattice d l ↔ d.q.leadingCoeff ∣ n) ∧
      addOrderOf (quotientGenerator d l) = d.q.leadingCoeff.natAbs ∧
      Finite (SuccessiveQuotient d l) ∧
      Nat.card (SuccessiveQuotient d l) = d.q.leadingCoeff.natAbs) ∧
    (∀ L : ℕ, d.N ≤ L →
      Finite ((lattice d L).toAddSubgroup ⧸
        (coordinateZ d.N).addSubgroupOf (lattice d L).toAddSubgroup) ∧
      (coordinateZ d.N).relIndex (lattice d L).toAddSubgroup =
        d.q.leadingCoeff.natAbs ^ (L - d.N))

private def sample : Data where
  N := 1
  positive := by decide
  T := 0
  cyclic := by simp [powerMatrix, root]
  q := X
  primitive := monic_X.isPrimitive
  leading_positive := by simp
  relation := by simp

private theorem not_divides_one : ¬ sample.q ∣ (1 : ℤ[X]) := by
  simp [sample, X_dvd_iff]

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  exact not_divides_one ((h sample).2.1 1 |>.mp rfl)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨sample, 0, 1, ?_⟩
  intro h
  have he : evaluation sample 1 = 0 := by
    simpa only [actual, realize, map_zero] using h.symm
  exact not_divides_one ((cyclic_power_lattice sample).2.1 1 |>.mp he)

def evidence : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cyclic_power_lattice, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def cyclic_power_lattice_registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S1.Recurrence.CyclicPowerLattice.cyclic_power_lattice)
      (Realization signature) Type Unit := {
  unitName := `Reg.D5.S1.Recurrence.CyclicPowerLattice.lattice_unit
  realizationName := `Reg.D5.S1.Recurrence.CyclicPowerLattice.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ d p => evaluation d p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ[X]
  sourceSelection := some {
    owner := `D5.S1.Recurrence.CyclicPowerLattice
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "fn", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

/-- info: 'Reg.D5.S1.Recurrence.CyclicPowerLattice.cyclic_power_lattice_registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms cyclic_power_lattice_registration

end
end Reg.D5.S1.Recurrence.CyclicPowerLattice
