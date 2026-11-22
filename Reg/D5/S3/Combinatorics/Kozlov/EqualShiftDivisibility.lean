import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Kozlov.EqualShiftDivisibility

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Combinatorics.Kozlov
open Polynomial
open scoped Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.Kozlov.EqualShiftDivisibility
abbrev sig : Signature where
  Params := Unit
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def proper (n r : ℕ) : ℕ := (properSumset n r).ncard
private def lattice (n r : ℕ) : ℕ := (dilateLattice n r).ncard

private def actual : Realization sig :=
  realize sig (fun i _ n r => Bool.rec (motive := fun _ => ℕ) (proper n r) (lattice n r) i) (fun e _ => e.elim)

abbrev divisibilityArena : Arena where
  signature := sig
  Law obs := ∀ (n : ℕ) (_hn : 1 ≤ n) (A L : ℚ[X]),
    AgreesOnPositiveRanks A (fun r => obs.readout false () n r) →
    AgreesOnPositiveRanks L (fun r => obs.readout true () n r) →
    X * (X + 1) ∣ L - A

abbrev existenceArena : Arena where
  signature := sig
  Law obs := ∀ (n : ℕ) (_hn : 1 ≤ n), ∃ A L : ℚ[X],
    AgreesOnPositiveRanks A (fun r => obs.readout false () n r) ∧
    AgreesOnPositiveRanks L (fun r => obs.readout true () n r)

private def offset (i : Bool) : Realization sig :=
  realize sig (fun j _ n r =>
    if j = i then actual.readout j () n r + 1 else actual.readout j () n r)
    (fun e _ => e.elim)

private theorem agree_add_one {P : ℚ[X]} {c : ℕ → ℕ} (h : AgreesOnPositiveRanks P c) :
    AgreesOnPositiveRanks (P + 1) (fun r => c r + 1) := by
  intro r hr
  simp [h r hr]

private theorem eval_zero_sub {A L : ℚ[X]} (h : X * (X + 1) ∣ L - A) :
    L.eval 0 = A.eval 0 := by
  obtain ⟨Q, hQ⟩ := h
  have hz : (L - A).eval 0 = 0 := by rw [hQ]; simp
  simpa [sub_eq_zero] using hz

private theorem offset_law (i : Bool) : ¬ divisibilityArena.Law (offset i) := by
  intro h
  have hn : 1 ≤ (1 : ℕ) := Nat.le_refl _
  obtain ⟨A, L, hA, hL⟩ := equal_shift_count_polynomials_exist 1 hn
  have he := eval_zero_sub (equal_shift_kozlov_deficiency_divisible 1 hn A L hA hL)
  cases i
  · have hb := eval_zero_sub (h 1 hn (A + 1) L
        (by simpa [offset, actual, realize, proper] using agree_add_one hA)
        (by simpa [offset, actual, realize, lattice] using hL))
    simp only [eval_add, eval_one] at hb
    linarith
  · have hb := eval_zero_sub (h 1 hn A (L + 1)
        (by simpa [offset, actual, realize, proper] using hA)
        (by simpa [offset, actual, realize, lattice] using agree_add_one hL))
    simp only [eval_add, eval_one] at hb
    linarith

private def pulse : ℕ → ℕ := fun r => if r = 1 then 1 else 0

private def pulsed (i : Bool) : Realization sig :=
  realize sig (fun j _ n => if j = i then pulse else actual.readout j () n)
    (fun e _ => e.elim)

private theorem no_pulse (P : ℚ[X]) : ¬ AgreesOnPositiveRanks P pulse := by
  intro h
  have e : P = 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hinj : Function.Injective (fun r : ℕ => ((r + 2 : ℕ) : ℚ)) := by
      intro u v huv
      change ((u + 2 : ℕ) : ℚ) = ((v + 2 : ℕ) : ℚ) at huv
      exact Nat.add_right_cancel (m := 2) (by exact_mod_cast huv)
    apply (Set.infinite_range_of_injective hinj).mono
    rintro _ ⟨r, rfl⟩
    have hv := h (r + 2) (by omega)
    have hr : r + 2 ≠ 1 := by omega
    simpa [pulse, hr] using hv
  have h1 := h 1 (by decide)
  norm_num [e, pulse] at h1

private theorem pulsed_law (i : Bool) : ¬ existenceArena.Law (pulsed i) := by
  intro h
  obtain ⟨A, L, hA, hL⟩ := h 1 (Nat.le_refl _)
  cases i
  · exact no_pulse A (by simpa [pulsed, realize] using hA)
  · exact no_pulse L (by simpa [pulsed, realize] using hL)

private theorem singleton_matrix (T : Matrix (Fin 1) (Fin 1) ℕ)
    (h : ∀ i, T i i = 1) : T = 1 := by
  ext i j
  have he : j = i := Subsingleton.elim _ _
  subst j
  simp [h]

private theorem counts_one : proper 1 1 = 1 ∧ lattice 1 1 = 1 := by
  have hn : 1 ≤ (1 : ℕ) := le_rfl
  have hA := singleton_matrix _ (properTransfer_unitriangular hn).2
  have hL := singleton_matrix _ (latticeTransfer_unitriangular hn).2
  unfold proper lattice
  rw [proper_count_as_entry hn, lattice_count_as_entry hn, hA, hL, one_pow]
  have he := (firstState_eq_lastState_iff hn).mpr rfl
  simp [Matrix.one_apply, he]

private theorem corner_square (T : Matrix (Fin 2) (Fin 2) ℕ)
    (hdiag : ∀ i, T i i = 1) (hcorner : T 0 1 = 1) : (T ^ 2) 0 1 = 2 := by
  rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two, hdiag 0, hdiag 1, hcorner]
  decide

private theorem counts_two : proper 2 1 = 2 ∧ lattice 2 1 = 2 := by
  have hn : 1 ≤ (2 : ℕ) := by decide
  have hA : properTransfer hn 0 1 = 1 :=
    transfer_last_column hn (properVectors 2)
      (fun _ hf => SnF_bounded (mem_properVectors.mp hf))
      (fun _ hf => SnF_fixed hn (mem_properVectors.mp hf))
      (fun _ hk => mem_properVectors.mpr (skeleton_mem_SnF hk))
      (fun _ hf => SnF_terminal (mem_properVectors.mp hf)) 0
  have hL : latticeTransfer hn 0 1 = 1 :=
    transfer_last_column hn (latticeVectors hn)
      (fun _ hf => normalized_one_bounded hn ((mem_latticeVectors hn).mp hf))
      (fun _ hf => normalized_one_fixed hn ((mem_latticeVectors hn).mp hf))
      (fun _ hk => skeleton_mem_latticeVectors hn hk)
      (fun _ hf => lattice_terminal hn hf) 0
  unfold proper lattice
  rw [proper_count_as_entry hn, lattice_count_as_entry hn]
  exact ⟨corner_square _ (properTransfer_unitriangular hn).2 hA,
    corner_square _ (latticeTransfer_unitriangular hn).2 hL⟩

private theorem observed_dependence : ObservationalDependence sig actual := by
  intro i
  refine ⟨(), (1 : ℕ), (2 : ℕ), ?_⟩
  intro h
  have he := congrFun h 1
  cases i
  · change proper 1 1 = proper 2 1 at he
    simp [counts_one.1, counts_two.1] at he
  · change lattice 1 1 = lattice 2 1 at he
    simp [counts_one.2, counts_two.2] at he

def divisibility_source : Registration divisibilityArena
    (type_of% equal_shift_kozlov_deficiency_divisible) where
  actual := realize sig
    (fun i _ n r => Bool.rec (motive := fun _ => ℕ)
      ((properSumset n r).ncard) ((dilateLattice n r).ncard) i)
    (fun e _ => e.elim)
  bridge := Iff.rfl
  variation := ⟨equal_shift_kozlov_deficiency_divisible, offset false, offset_law false⟩
  sensitivity := by
    refine ⟨fun i => ⟨offset i, ?_, rfl, offset_law i⟩, fun e => e.elim⟩
    intro j hji
    funext p n r
    simp only [offset, actual, realize, hji, ite_false]
    rfl
  dependence := observed_dependence

def existence_source : Registration existenceArena
    (type_of% equal_shift_count_polynomials_exist) where
  actual := realize sig
    (fun i _ n r => Bool.rec (motive := fun _ => ℕ)
      ((properSumset n r).ncard) ((dilateLattice n r).ncard) i)
    (fun e _ => e.elim)
  bridge := Iff.rfl
  variation := ⟨equal_shift_count_polynomials_exist, pulsed false, pulsed_law false⟩
  sensitivity := by
    refine ⟨fun i => ⟨pulsed i, ?_, rfl, pulsed_law i⟩, fun e => e.elim⟩
    intro j hji
    funext p n
    simp only [pulsed, actual, realize, hji, ite_false]
    rfl
  dependence := observed_dependence

def divisibility_audit :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      equal_shift_kozlov_deficiency_divisible (Realization sig) Type Unit where
  unitName := `D5.S3.Combinatorics.Kozlov.equal_shift_kozlov_deficiency_divisible.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Kozlov.EqualShiftDivisibility.divisibility_source
  realizationSource := none
  generated := false
  arena := .source ⟨divisibilityArena⟩
  objectArena := .source ⟨divisibilityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source divisibilityArena ⟨divisibility_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig
    (fun i _ n r => Bool.rec (motive := fun _ => ℕ)
      ((properSumset n r).ncard) ((dilateLattice n r).ncard) i)
    (fun e _ => e.elim))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Kozlov.EqualShiftDivisibility
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "domain", "arg"],
        stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "domain", "arg"],
        stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

def existence_audit :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      equal_shift_count_polynomials_exist (Realization sig) Type Unit where
  unitName := `D5.S3.Combinatorics.Kozlov.equal_shift_count_polynomials_exist.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Kozlov.EqualShiftDivisibility.existence_source
  realizationSource := none
  generated := false
  arena := .source ⟨existenceArena⟩
  objectArena := .source ⟨existenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source existenceArena ⟨existence_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig
    (fun i _ n r => Bool.rec (motive := fun _ => ℕ)
      ((properSumset n r).ncard) ((dilateLattice n r).ncard) i)
    (fun e _ => e.elim))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Kozlov.EqualShiftDivisibility
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "arg", "body", "arg", "body", "arg", "arg"],
        stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "arg", "body", "arg", "body", "fn", "arg", "arg"],
        stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Kozlov.EqualShiftDivisibility
