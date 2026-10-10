import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.LegalWordDegree

namespace Reg.D5.S3.Combinatorics.Graph.LegalWordDegree

open _root_.D5.S3.Combinatorics.Graph.LegalWordDegree
open _root_.D5.S1.Words.AdmissibleWords.AdmissibleCount
open _root_.D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev wordSignature : Signature where
  Params := ℕ
  State n := {w : Fin n → Bool // Adm n w}
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

open Classical in
def degreeActual : Realization wordSignature := realize wordSignature
  (fun role n b => Bool.rec ((legalWordGraph n).degree b)
    (flippableZeroCount b.val + occupationCount b.val) role)
  (fun e => nomatch e)

abbrev degreeArena : Arena where
  signature := wordSignature
  Law R := ∀ (n : ℕ) (b : {w : Fin n → Bool // Adm n w}),
    R.readout false n b = R.readout true n b

def degreeIntervention (role : Bool) : Realization wordSignature := realize wordSignature
  (fun j n b => if j = role then degreeActual.readout j n b + 1
    else degreeActual.readout j n b)
  (fun e => nomatch e)

theorem degreeIntervention_rejected (role : Bool) :
    ¬ degreeArena.Law (degreeIntervention role) := by
  intro h
  let b : {w : Fin 0 → Bool // Adm 0 w} := ⟨fun _ => false, trivial⟩
  have equality := h 0 b
  have positive : degreeActual.readout false 0 b = degreeActual.readout true 0 b :=
    degree_eq_flippable_add_occupation 0 b
  cases role
  · change degreeActual.readout false 0 b + 1 = degreeActual.readout true 0 b at equality
    rw [positive] at equality
    exact Nat.succ_ne_self _ equality
  · change degreeActual.readout false 0 b = degreeActual.readout true 0 b + 1 at equality
    rw [positive] at equality
    exact Nat.succ_ne_self _ equality.symm

def zeroWord : {w : Fin 3 → Bool // Adm 3 w} := ⟨fun _ => false, by decide⟩
def middleWord : {w : Fin 3 → Bool // Adm 3 w} :=
  ⟨fun i => decide (i.val = 1), by decide⟩
def alternatingWord : {w : Fin 3 → Bool // Adm 3 w} :=
  ⟨fun i => decide (i.val % 2 = 0), by decide⟩

theorem degreeDependence : ObservationalDependence wordSignature degreeActual := by
  classical
  intro role
  refine ⟨3, zeroWord, middleWord, ?_⟩
  have hz : flippableZeroCount zeroWord.val + occupationCount zeroWord.val = 3 := by
    norm_num [zeroWord, flippableZeroCount, FlippableZero, occupationCount,
      Fin.sum_univ_succ]
  have hm : flippableZeroCount middleWord.val + occupationCount middleWord.val = 1 := by
    norm_num [middleWord, flippableZeroCount, FlippableZero, occupationCount,
      Fin.sum_univ_succ, Fin.forall_fin_succ]
  cases role
  · change (legalWordGraph 3).degree zeroWord ≠ (legalWordGraph 3).degree middleWord
    rw [degree_eq_flippable_add_occupation, degree_eq_flippable_add_occupation, hz, hm]
    decide
  · change flippableZeroCount zeroWord.val + occupationCount zeroWord.val ≠
      flippableZeroCount middleWord.val + occupationCount middleWord.val
    rw [hz, hm]
    decide

def degreeRecord : Registration degreeArena (type_of% (@degree_eq_flippable_add_occupation)) where
  actual := degreeActual
  bridge := Iff.rfl
  variation := ⟨degree_eq_flippable_add_occupation,
    degreeIntervention false, degreeIntervention_rejected false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨degreeIntervention i, ?_, rfl, degreeIntervention_rejected i⟩
      intro j hji
      funext n b
      simp [degreeIntervention, realize, hji]
    · intro i
      exact nomatch i
  dependence := degreeDependence

def boundActual : Realization wordSignature := realize wordSignature
  (fun _ _ b => flippableZeroCount b.val + 2 * occupationCount b.val)
  (fun e => nomatch e)

abbrev boundArena : Arena where
  signature := wordSignature
  Law R := ∀ (n : ℕ) (b : {w : Fin n → Bool // Adm n w}),
    R.readout false n b ≤ n + 1 ∧
      (R.readout true n b = n + 1 ↔
        Odd n ∧ ∀ i : Fin n, b.val i = decide (i.val % 2 = 0))

def boundIntervention (role : Bool) : Realization wordSignature := realize wordSignature
  (fun j n b => if j = role then n + 1 + (if role then 0 else 1)
    else boundActual.readout j n b)
  (fun e => nomatch e)

theorem boundIntervention_rejected (role : Bool) :
    ¬ boundArena.Law (boundIntervention role) := by
  intro h
  let b : {w : Fin 0 → Bool // Adm 0 w} := ⟨fun _ => false, trivial⟩
  have hh := h 0 b
  cases role
  · have hb := hh.1
    norm_num [boundIntervention, realize] at hb
  · have he := hh.2.mp (by simp [boundIntervention, realize])
    exact Nat.not_odd_zero he.1

theorem boundDependence : ObservationalDependence wordSignature boundActual := by
  intro role
  refine ⟨3, zeroWord, alternatingWord, ?_⟩
  change flippableZeroCount zeroWord.val + 2 * occupationCount zeroWord.val ≠
    flippableZeroCount alternatingWord.val + 2 * occupationCount alternatingWord.val
  norm_num [zeroWord, alternatingWord, flippableZeroCount, FlippableZero,
    occupationCount, Fin.sum_univ_succ, Fin.forall_fin_succ]

def boundRecord : Registration boundArena (type_of% (@flippable_bound_and_equality)) where
  actual := boundActual
  bridge := Iff.rfl
  variation := ⟨flippable_bound_and_equality,
    boundIntervention false, boundIntervention_rejected false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨boundIntervention i, ?_, rfl, boundIntervention_rejected i⟩
      intro j hji
      funext n b
      simp [boundIntervention, realize, hji]
    · intro i
      exact nomatch i
  dependence := boundDependence

open Classical in
def degree_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Graph.LegalWordDegree.degree_eq_flippable_add_occupation)
    (type_of% (realize wordSignature
      (fun role n b => Bool.rec ((legalWordGraph n).degree b)
        (flippableZeroCount b.val + occupationCount b.val) role)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Graph.LegalWordDegree.degree_eq_flippable_add_occupation.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LegalWordDegree.degreeRecord
  realizationSource := none
  generated := false
  arena := .source ⟨degreeArena⟩
  objectArena := .source ⟨degreeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source degreeArena ⟨degreeRecord⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize wordSignature
    (fun role n b => Bool.rec ((legalWordGraph n).degree b)
      (flippableZeroCount b.val + occupationCount b.val) role)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LegalWordDegree
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

def bound_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Graph.LegalWordDegree.flippable_bound_and_equality)
    (type_of% (realize wordSignature
      (fun _ _ b => flippableZeroCount b.val + 2 * occupationCount b.val)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Graph.LegalWordDegree.flippable_bound_and_equality.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LegalWordDegree.boundRecord
  realizationSource := none
  generated := false
  arena := .source ⟨boundArena⟩
  objectArena := .source ⟨boundArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundArena ⟨boundRecord⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize wordSignature
    (fun _ _ b => flippableZeroCount b.val + 2 * occupationCount b.val)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LegalWordDegree
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms degreeRecord
#print axioms boundRecord
#print axioms degree_registration
#print axioms bound_registration

end
end Reg.D5.S3.Combinatorics.Graph.LegalWordDegree
