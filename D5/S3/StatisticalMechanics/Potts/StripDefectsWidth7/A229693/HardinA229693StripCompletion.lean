/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion
   mirror-E: none(waiver:finite-completion-certificate)
   anchors: []
   utility: kind=bounded-enumeration; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exactExits_count; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.completionRows_count,D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripCompletion.completionCodes_eq
   digest: Exact enumeration of rows under adjacent and boundary match costs. -/

/-
admission_basis: escape-witness (#33283)
escape_witness: completionRows_count proves the exact-cost multiplicities computed by the pruned enumeration
completionCodes: proof_shape=content; consumers=completionCodes_eq, exitCodes, exitCodes.eq_1, exitCodes_eq
completionCodes_eq: proof_shape=content; consumers=exitCodes_eq
completionCost: proof_shape=content; consumers=completionCost_row, completionRows_count, completionRows_length_le, exactExits_count
completionRows: proof_shape=content; consumers=completionCodes_eq, completionRows_count, completionRows_length_le, exactExits_count, exitCodes_bound, exitCodes_eq
completionRows_count: proof_shape=content; consumers=completionRows_length_le, exactExits_count
matchCost: proof_shape=bind-only; consumers=completionCodes._f, completionCodes._sunfold, completionCodes._unsafe_rec, completionCodes.eq_1, completionCodes.eq_2, completionCodes.eq_def, completionCodes_eq, completionCost._f, completionCost._sunfold, completionCost._unsafe_rec, completionCost.eq_1, completionCost.eq_2, completionCost.eq_def, completionCost_row, completionRows._f, completionRows._sunfold, completionRows._unsafe_rec, completionRows.eq_1, completionRows.eq_2, completionRows.eq_def, completionRows_count, completionRows_count._proof_1_9
rowCode_cons: proof_shape=bind-only; consumers=completionCodes_eq, rowCode_tail
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripCompletion

def matchCost : Option (Fin 3) → Fin 3 → ℕ
  | none, _ => 0
  | some p, x => if p = x then 1 else 0

def completionCost : {k : ℕ} → (Fin k → Option (Fin 3)) → Option (Fin 3) →
    (Fin (k + 1) → Fin 3) → ℕ
  | 0, _, prev, r => matchCost prev (r 0)
  | _k + 1, p, prev, r =>
    matchCost prev (r 0) + matchCost (p 0) (r 0) +
      completionCost (Fin.tail p) (some (r 0)) (Fin.tail r)

def completionRows : {k : ℕ} → (Fin k → Option (Fin 3)) → Option (Fin 3) →
    ℕ → List (Fin (k + 1) → Fin 3)
  | 0, _, prev, d =>
    ((List.finRange 3).filter fun x => matchCost prev x == d).map fun x _ => x
  | _k + 1, p, prev, d => (List.finRange 3).flatMap fun x =>
    let c := matchCost prev x + matchCost (p 0) x
    if c ≤ d then (completionRows (Fin.tail p) (some x) (d - c)).map (Fin.cons x) else []

theorem completionRows_count {k : ℕ} (p : Fin k → Option (Fin 3))
    (prev : Option (Fin 3)) (d : ℕ) (f : (Fin (k + 1) → Fin 3) → Bool) :
    (completionRows p prev d).countP f =
      ∑ r, if completionCost p prev r = d ∧ f r = true then 1 else 0 := by
  induction k generalizing prev d with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) (Fin 3)).symm.sum_comp]
    simp only [completionCost, completionRows, List.countP_map, List.countP_filter,
      Equiv.funUnique_symm_apply, uniqueElim_const, Function.comp_apply, Fin.sum_univ_three]
    change ([(0 : Fin 3), 1, 2].countP
      (fun x => f (fun _ => x) && (matchCost prev x == d))) =
      (if matchCost prev 0 = d ∧ f (fun _ => 0) = true then 1 else 0) +
      (if matchCost prev 1 = d ∧ f (fun _ => 1) = true then 1 else 0) +
      (if matchCost prev 2 = d ∧ f (fun _ => 2) = true then 1 else 0)
    simp only [List.countP_cons, List.countP_nil, Bool.and_eq_true, beq_iff_eq, and_comm]
    omega
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k + 2) => Fin 3)).sum_comp, Fintype.sum_prod_type]
    simp only [completionRows, List.countP_flatMap, ← List.ofFn_id,
      List.map_ofFn, List.sum_ofFn, Function.comp_apply, id_eq]
    apply Finset.sum_congr rfl
    intro x _
    let c := matchCost prev x + matchCost (p 0) x
    change (if c ≤ d then (completionRows (Fin.tail p) (some x) (d - c)).map (Fin.cons x)
      else []).countP f = _
    split_ifs with hc
    · rw [List.countP_map, ih]
      apply Finset.sum_congr rfl
      intro r _
      change (if completionCost (Fin.tail p) (some x) r = d - c ∧ f (Fin.cons x r) = true
        then 1 else 0) = (if c + completionCost (Fin.tail p) (some x) r = d ∧
        f (Fin.cons x r) = true then 1 else 0)
      have he : completionCost (Fin.tail p) (some x) r = d - c ↔
          c + completionCost (Fin.tail p) (some x) r = d :=
        eq_comm.trans ((Nat.sub_eq_iff_eq_add' hc).trans eq_comm)
      simp only [he]
    · simp only [List.countP_nil]
      symm
      apply Finset.sum_eq_zero
      intro r _
      change (if c + completionCost (Fin.tail p) (some x) r = d ∧ f (Fin.cons x r) = true
        then 1 else 0) = 0
      apply ite_eq_right
      intro h
      exact hc (h.1 ▸ Nat.le_add_right c _)

def completionCodes : List (Option (Fin 3)) → Option (Fin 3) → ℕ → List ℕ
  | [], prev, d =>
    ((List.finRange 3).filter fun x => matchCost prev x == d).map Fin.val
  | a :: as, prev, d => (List.finRange 3).flatMap fun x =>
    let c := matchCost prev x + matchCost a x
    if c ≤ d then (completionCodes as (some x) (d - c)).map (fun r => x.val + 3 * r)
    else []

theorem rowCode_cons {k : ℕ} (x : Fin 3) (r : Fin k → Fin 3) :
    (finFunctionFinEquiv (Fin.cons x r)).val = x.val + 3 * (finFunctionFinEquiv r).val := by
  simp only [finFunctionFinEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ, pow_zero, mul_one, pow_succ', Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

theorem completionCodes_eq {k : ℕ} (p : Fin k → Option (Fin 3))
    (prev : Option (Fin 3)) (d : ℕ) :
    completionCodes (List.ofFn p) prev d =
      (completionRows p prev d).map (fun r => (finFunctionFinEquiv r).val) := by
  induction k generalizing prev d with
  | zero =>
    simp only [List.ofFn_zero, completionCodes, completionRows, List.map_map]
    apply List.map_congr_left
    intro x _
    change x.val = (finFunctionFinEquiv (fun _ : Fin 1 => x)).val
    simp only [finFunctionFinEquiv_apply, Fin.sum_univ_one, Fin.val_zero, pow_zero, mul_one]
  | succ k ih =>
    simp only [List.ofFn_succ, completionCodes, completionRows, List.map_flatMap]
    apply List.flatMap_congr
    intro x _
    split_ifs
    · simp only [show (fun i => p i.succ) = Fin.tail p from rfl, ih, List.map_map]
      apply List.map_congr_left
      intro r _
      exact (rowCode_cons x r).symm
    · rfl

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripCompletion
