import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.Orbit.MersenneZeroSymmetries
import Reg.Support.DependentFamily

/-! Full-telescope source-family evidence. The varied readouts are the rotation
permutation and the literal zero-family subgroup, rather than their truth values.
An unknown continuation records no theorem about exhaustion of the residual. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.MersenneZeroSymmetries

namespace Reg.D5.S3.Combinatorics.Circle.MersenneZeroSymmetries

abbrev orbitSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Equiv.Perm (Fin n)
  Anchor := Empty
  finiteAnchor := inferInstance

def actualOrbit : Realization orbitSignature :=
  realize orbitSignature (fun _ n a => (finRotate n) ^ a) (fun e => nomatch e)

def rejectedOrbit : Realization orbitSignature :=
  realize orbitSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev residueArena : Arena where
  signature := orbitSignature
  Law R := ∀ (n a : ℕ) (_hn : 0 < n) (i j : Fin n),
    (R.readout () n a).SameCycle i j ↔ i.val % Nat.gcd n a = j.val % Nat.gcd n a

abbrev chartArena : Arena where
  signature := orbitSignature
  Law R := ∀ (n a : ℕ) (_hn : 0 < n) (i j : Fin n),
    (R.readout () n a).SameCycle i j ↔ (residueChart n a i).1 = (residueChart n a j).1

private theorem rejected_residue : ¬ residueArena.Law rejectedOrbit := by
  intro h
  have hh := (h 2 1 (by decide) 0 1).mpr (by decide)
  simpa [rejectedOrbit, realize, Equiv.Perm.sameCycle_one] using hh

private theorem rejected_chart : ¬ chartArena.Law rejectedOrbit := by
  intro h
  have hh := (h 2 1 (by decide) 0 1).mpr (by decide)
  simpa [rejectedOrbit, realize, Equiv.Perm.sameCycle_one] using hh

private theorem orbit_dependence : ObservationalDependence orbitSignature actualOrbit := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  simpa [actualOrbit, realize] using
    (by decide : (1 : Equiv.Perm (Fin 2)) ≠ finRotate 2)

def residue_registration : Registration residueArena (type_of% @sameCycle_iff_residue) where
  actual := actualOrbit
  bridge := Iff.rfl
  variation := ⟨sameCycle_iff_residue, rejectedOrbit, rejected_residue⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedOrbit, ?_, rfl, rejected_residue⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := orbit_dependence

def chart_registration : Registration chartArena (type_of% @sameCycle_iff_chart) where
  actual := actualOrbit
  bridge := Iff.rfl
  variation := ⟨sameCycle_iff_chart, rejectedOrbit, rejected_chart⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedOrbit, ?_, rfl, rejected_chart⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := orbit_dependence

abbrev groupSignature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Subgroup (Equiv.Perm (Fin n))
  Anchor := Empty
  finiteAnchor := inferInstance

def actualGroup : Realization groupSignature :=
  realize groupSignature (fun _ n a => ZeroFamilyAut n a) (fun e => nomatch e)

def rejectedGroup : Realization groupSignature :=
  realize groupSignature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev reconstructionArena : Arena where
  signature := groupSignature
  Law R := ∀ (n a : ℕ) (_hn : 0 < n), R.readout () n a =
    _root_.D5.S3.FiniteGroups.SuccessorQuotient.relationAut
      (((finRotate n : Equiv.Perm (Fin n)) ^ a).SameCycle)

abbrev countArena : Arena where
  signature := groupSignature
  Law R := ∀ (n a : ℕ) (_hn : 0 < n), Nat.card (R.readout () n a) =
    (n / Nat.gcd n a).factorial ^ Nat.gcd n a * (Nat.gcd n a).factorial

private theorem rejected_count : ¬ countArena.Law rejectedGroup := by
  intro h
  have hh := h 2 0 (by decide)
  norm_num [rejectedGroup, realize] at hh

private theorem rejected_reconstruction : ¬ reconstructionArena.Law rejectedGroup := by
  intro h
  have hh := h 2 0 (by decide)
  rw [← zeroFamilyAut_eq_orbitAut 2 0 (by decide)] at hh
  have hc := congrArg (fun H : Subgroup (Equiv.Perm (Fin 2)) => Nat.card H) hh
  rw [card_zeroFamilyAut 2 0 (by decide)] at hc
  norm_num [rejectedGroup, realize] at hc

private theorem group_dependence : ObservationalDependence groupSignature actualGroup := by
  intro i
  refine ⟨4, 0, 2, ?_⟩
  intro he
  change ZeroFamilyAut 4 0 = ZeroFamilyAut 4 2 at he
  have hc := congrArg (fun H : Subgroup (Equiv.Perm (Fin 4)) => Nat.card H) he
  rw [card_zeroFamilyAut 4 0 (by decide), card_zeroFamilyAut 4 2 (by decide)] at hc
  norm_num at hc

def reconstruction_registration : Registration reconstructionArena
    (type_of% @zeroFamilyAut_eq_orbitAut) where
  actual := actualGroup
  bridge := Iff.rfl
  variation := ⟨zeroFamilyAut_eq_orbitAut, rejectedGroup, rejected_reconstruction⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedGroup, ?_, rfl, rejected_reconstruction⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := group_dependence

def count_registration : Registration countArena (type_of% @card_zeroFamilyAut) where
  actual := actualGroup
  bridge := Iff.rfl
  variation := ⟨card_zeroFamilyAut, rejectedGroup, rejected_count⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedGroup, ?_, rfl, rejected_count⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := group_dependence


def residue_audit :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Circle.MersenneZeroSymmetries.sameCycle_iff_residue)
      (type_of% (realize orbitSignature (fun _ n a => (finRotate n) ^ a) (fun e => nomatch e)))
      Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.MersenneZeroSymmetries.sameCycle_iff_residue.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersenneZeroSymmetries.residue_registration
  realizationSource := none
  generated := false
  arena := .source ⟨residueArena⟩
  objectArena := .source ⟨residueArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source residueArena ⟨residue_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize orbitSignature (fun _ n a => (finRotate n) ^ a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.MersenneZeroSymmetries
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


def chart_audit :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Circle.MersenneZeroSymmetries.sameCycle_iff_chart)
      (type_of% (realize orbitSignature (fun _ n a => (finRotate n) ^ a) (fun e => nomatch e)))
      Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.MersenneZeroSymmetries.sameCycle_iff_chart.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersenneZeroSymmetries.chart_registration
  realizationSource := none
  generated := false
  arena := .source ⟨chartArena⟩
  objectArena := .source ⟨chartArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chartArena ⟨chart_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize orbitSignature (fun _ n a => (finRotate n) ^ a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.MersenneZeroSymmetries
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


def reconstruction_audit :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Circle.MersenneZeroSymmetries.zeroFamilyAut_eq_orbitAut)
      (type_of% (realize groupSignature (fun _ n a => ZeroFamilyAut n a) (fun e => nomatch e)))
      Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.MersenneZeroSymmetries.zeroFamilyAut_eq_orbitAut.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersenneZeroSymmetries.reconstruction_registration
  realizationSource := none
  generated := false
  arena := .source ⟨reconstructionArena⟩
  objectArena := .source ⟨reconstructionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source reconstructionArena ⟨reconstruction_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize groupSignature (fun _ n a => ZeroFamilyAut n a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.MersenneZeroSymmetries
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


def count_audit :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Circle.MersenneZeroSymmetries.card_zeroFamilyAut)
      (type_of% (realize groupSignature (fun _ n a => ZeroFamilyAut n a) (fun e => nomatch e)))
      Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.MersenneZeroSymmetries.card_zeroFamilyAut.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.MersenneZeroSymmetries.count_registration
  realizationSource := none
  generated := false
  arena := .source ⟨countArena⟩
  objectArena := .source ⟨countArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena ⟨count_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize groupSignature (fun _ n a => ZeroFamilyAut n a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.Orbit.MersenneZeroSymmetries
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


end Reg.D5.S3.Combinatorics.Circle.MersenneZeroSymmetries
