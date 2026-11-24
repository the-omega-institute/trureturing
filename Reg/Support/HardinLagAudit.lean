import Reg.Support.DependentFamily
import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinActualTransfers

/-! A sum-preserving intervention for the coefficient operands of Hardin's lag laws. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinActualTransfers
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinColumnContinuations (Column cross columnV)
open scoped BigOperators

set_option autoImplicit false

namespace Reg.Support.HardinLagAudit

inductive Role
  | lag
  | sum
  deriving DecidableEq

private def finiteRole : Fintype Role where
  elems := ⟨([Role.lag, Role.sum] : List Role), by simp⟩
  complete := by intro role; cases role <;> simp

/-- The certificate selects the vector-relation operand before the coefficient sum. -/
abbrev signature (d : ℕ) : Signature where
  Params := Unit
  State _ := Fin d
  Role := Role
  finiteRole := finiteRole
  nonemptyRole := ⟨.lag⟩
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena {A : Type} [Fintype A] [DecidableEq A] (d : ℕ)
    (T : Matrix A A ℤ) (b : ℕ) : Arena where
  signature := signature d
  Law r := IsLagRelation T b (r.readout .lag ()) ∧ (∑ j, r.readout .sum () j) = 1

/-- Move one unit of coefficient weight from lag `minus` to lag `plus`. -/
def shiftWeight {d : ℕ} (c : Fin d → ℤ) (plus minus : Fin d) (j : Fin d) : ℤ :=
  c j + (if j = plus then 1 else 0) - (if j = minus then 1 else 0)

theorem sum_shiftWeight {d : ℕ} (c : Fin d → ℤ) (plus minus : Fin d) :
    (∑ j, shiftWeight c plus minus j) = ∑ j, c j := by
  simp [shiftWeight, Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem shiftWeight_breaks_lag {A : Type} [Fintype A] [DecidableEq A] {d : ℕ}
    {T : Matrix A A ℤ} {b : ℕ} {c : Fin d → ℤ} (h : IsLagRelation T b c)
    (plus minus : Fin d) (p : A)
    (different : ((T ^ (b + d - (plus.val + 1))).mulVec (1 : A → ℤ)) p ≠
      ((T ^ (b + d - (minus.val + 1))).mulVec (1 : A → ℤ)) p) :
    ¬ IsLagRelation T b (shiftWeight c plus minus) := by
  intro altered
  have hEq := congrFun (h.symm.trans altered) p
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hEq
  exact different (by
    simp only [shiftWeight, sub_mul, add_mul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at hEq
    linarith)

theorem joint_intervention {A : Type} [Fintype A] [DecidableEq A] {d : ℕ}
    {T : Matrix A A ℤ} {b : ℕ} {c : Fin d → ℤ}
    (source : IsLagRelation T b c ∧ (∑ j, c j) = 1) (plus minus : Fin d) (p : A)
    (different : ((T ^ (b + d - (plus.val + 1))).mulVec (1 : A → ℤ)) p ≠
      ((T ^ (b + d - (minus.val + 1))).mulVec (1 : A → ℤ)) p) :
    (∑ j, shiftWeight c plus minus j) = 1 ∧ ¬ IsLagRelation T b (shiftWeight c plus minus) :=
  ⟨(sum_shiftWeight c plus minus).trans source.2,
    shiftWeight_breaks_lag source.1 plus minus p different⟩

theorem variation {A : Type} [Fintype A] [DecidableEq A] {d : ℕ}
    {T : Matrix A A ℤ} {b : ℕ} {c : Fin d → ℤ}
    (source : IsLagRelation T b c ∧ (∑ j, c j) = 1) (plus minus : Fin d) (p : A)
    (different : ((T ^ (b + d - (plus.val + 1))).mulVec (1 : A → ℤ)) p ≠
      ((T ^ (b + d - (minus.val + 1))).mulVec (1 : A → ℤ)) p) :
    Variation (arena d T b) (realize (signature d) (fun _ _ j => c j) (fun e => Empty.elim e)) :=
  ⟨source, realize (signature d) (fun _ _ j => shiftWeight c plus minus j) (fun e => Empty.elim e),
    fun h => (joint_intervention source plus minus p different).2 h.1⟩

theorem sensitivity {A : Type} [Fintype A] [DecidableEq A] {d : ℕ}
    {T : Matrix A A ℤ} {b : ℕ} {c : Fin d → ℤ}
    (source : IsLagRelation T b c ∧ (∑ j, c j) = 1) (plus minus : Fin d) (p : A)
    (different : ((T ^ (b + d - (plus.val + 1))).mulVec (1 : A → ℤ)) p ≠
      ((T ^ (b + d - (minus.val + 1))).mulVec (1 : A → ℤ)) p) :
    Sensitivity (arena d T b) (realize (signature d) (fun _ _ j => c j) (fun e => Empty.elim e)) := by
  constructor
  · intro role
    let bad := realize (signature d) (fun i _ j =>
      if i = role then (if role = .lag then shiftWeight c plus minus j else 0) else c j)
      (fun e => Empty.elim e)
    refine ⟨bad, ?_, rfl, ?_⟩
    · intro other hother
      funext param j
      simp [bad, realize, hother]
    · cases role
      · intro h
        exact shiftWeight_breaks_lag source.1 plus minus p different (by
          simpa [bad, realize] using h.1)
      · intro h
        have hsum : (∑ _ : Fin d, (0 : ℤ)) = 1 := by simpa [bad, realize] using h.2
        simp at hsum
  · intro e
    exact nomatch e

theorem column_power_one_ne_two (h : ℕ) :
    ((C h) ^ (1 : ℕ)).mulVec (1 : Column h → ℤ) (fun _ => 0) ≠
      ((C h) ^ (2 : ℕ)).mulVec (1 : Column h → ℤ) (fun _ => 0) := by
  rw [column_power, column_power]
  exact_mod_cast (ne_of_lt (show columnV 1 (fun _ : Fin (h + 1) => 0) < columnV 2 (fun _ => 0) from by
    let p₀ : Column h := fun _ => 0
    let p₁ : Column h := fun _ => 1
    let p₂ : Column h := fun _ => 2
    change (∑ q : Column h, if cross p₀ q then 1 else 0) <
      ∑ q : Column h, if cross p₀ q then columnV 1 q else 0
    apply Finset.sum_lt_sum
    · intro q _
      split_ifs with hq
      · have hback : cross q p₀ := ⟨fun i => (hq.1 i).symm,
          fun i => ⟨(hq.2 i).2.symm, (hq.2 i).1.symm⟩⟩
        change 1 ≤ ∑ s : Column h, if cross q s then 1 else 0
        calc
          1 = (if cross q p₀ then 1 else 0) := (ite_eq_left hback).symm
          _ ≤ _ := Finset.single_le_sum (f := fun s : Column h => if cross q s then 1 else 0)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ p₀)
      · exact le_rfl
    · have h₀₁ : cross p₀ p₁ := ⟨fun _ => by decide, fun _ => by decide⟩
      have h₁₀ : cross p₁ p₀ := ⟨fun _ => by decide, fun _ => by decide⟩
      have h₁₂ : cross p₁ p₂ := ⟨fun _ => by decide, fun _ => by decide⟩
      have apart : p₀ ≠ p₂ := fun eq => (by decide : (0 : Fin 3) ≠ 2) (congrFun eq 0)
      refine ⟨p₁, Finset.mem_univ _, ?_⟩
      simp only [ite_eq_left h₀₁]
      change 1 < ∑ s : Column h, if cross p₁ s then 1 else 0
      calc
        1 < ∑ s ∈ ({p₀, p₂} : Finset (Column h)), if cross p₁ s then 1 else 0 := by
          rw [Finset.sum_pair apart, ite_eq_left h₁₀, ite_eq_left h₁₂]
          decide
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)))

end Reg.Support.HardinLagAudit
