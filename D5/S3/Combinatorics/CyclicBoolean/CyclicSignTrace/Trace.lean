/- GID: D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Trace
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Trace
   mirror-E: none(waiver:capacity-split-support)
   anchors: []
   utility: none
   digest: Exact ordered trace expansion and cyclic Boolean phase bridge. -/

import D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace.Prelude

/-! Exact ordered trace expansion and cyclic Boolean phase bridge. -/

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace

open D5.S3.QuantumBounds.MerminMeasurementDependence (bit_cases)

set_option backward.isDefEq.respectTransparency false in
private theorem ordered_product_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (M : Fin (r + 1) → Matrix ι ι ℤ) (i j : ι) :
    (List.ofFn M).prod i j =
      ∑ x : Fin r → ι, ∏ k : Fin (r + 1),
        M k (Fin.cons (α := fun _ => ι) i x k) (Fin.snoc (α := fun _ => ι) x j k) := by
  classical
  induction r generalizing i j with
  | zero => simp [List.ofFn_succ, Fin.prod_univ_succ, Fin.snoc_zero]
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    simp_rw [ih, Finset.mul_sum]
    trans ∑ p : ι × (Fin r → ι),
      M 0 i p.1 * ∏ k : Fin (r + 1),
        M k.succ (Fin.cons (α := fun _ => ι) p.1 p.2 k)
          (Fin.snoc (α := fun _ => ι) p.2 j k)
    · exact (Fintype.sum_prod_type (fun p : ι × (Fin r → ι) =>
        M 0 i p.1 * ∏ k : Fin (r + 1),
          M k.succ (Fin.cons (α := fun _ => ι) p.1 p.2 k)
            (Fin.snoc (α := fun _ => ι) p.2 j k))).symm
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r + 1) => ι))]
    apply Finset.sum_congr rfl
    intro x _
    change M 0 i x.1 * (∏ k : Fin (r + 1),
      M k.succ (Fin.cons (α := fun _ => ι) x.1 x.2 k)
        (Fin.snoc (α := fun _ => ι) x.2 j k)) =
      ∏ k : Fin (r + 1 + 1),
        M k (Fin.cons (α := fun _ => ι) i (Fin.cons x.1 x.2) k)
          (Fin.snoc (α := fun _ => ι) (Fin.cons x.1 x.2) j k)
    rw [← Fin.cons_snoc_eq_snoc_cons]
    conv_rhs => rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]

set_option backward.isDefEq.respectTransparency false in
private theorem cyclic_snoc {r : ℕ} (x : Fin (r + 1) → ZMod 2) (k : Fin (r + 1)) :
    Fin.snoc (α := fun _ => ZMod 2) (Fin.tail x) (x 0) k = x (k + (1 : Fin (r + 1))) := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp
  · simp [Fin.tail]

set_option backward.isDefEq.respectTransparency false in
private theorem ordered_trace_paths (r : ℕ)
    (M : Fin (r + 1) → Matrix (ZMod 2) (ZMod 2) ℤ) :
    Matrix.trace (List.ofFn M).prod =
      ∑ x : Fin (r + 1) → ZMod 2, ∏ k : Fin (r + 1), M k (x k) (x (k + (1 : Fin (r + 1)))) := by
  classical
  change (∑ i, (List.ofFn M).prod i i) = _
  calc
    _ = ∑ i, ∑ x : Fin r → ZMod 2, ∏ k : Fin (r + 1),
        M k (Fin.cons (α := fun _ => ZMod 2) i x k)
          (Fin.snoc (α := fun _ => ZMod 2) x i k) := by
      apply Finset.sum_congr rfl
      intro i _
      exact ordered_product_entry r M i i
    _ = ∑ p : ZMod 2 × (Fin r → ZMod 2), ∏ k : Fin (r + 1),
        M k (Fin.cons (α := fun _ => ZMod 2) p.1 p.2 k)
          (Fin.snoc (α := fun _ => ZMod 2) p.2 p.1 k) :=
      (Fintype.sum_prod_type (fun p : ZMod 2 × (Fin r → ZMod 2) =>
        ∏ k : Fin (r + 1), M k
          (Fin.cons (α := fun _ => ZMod 2) p.1 p.2 k)
          (Fin.snoc (α := fun _ => ZMod 2) p.2 p.1 k))).symm
    _ = _ := by
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r + 1) => ZMod 2))]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.prod_congr rfl
      intro k _
      change M k (Fin.cons (α := fun _ => ZMod 2) x.1 x.2 k)
          (Fin.snoc (α := fun _ => ZMod 2) x.2 x.1 k) =
        M k (Fin.cons (α := fun _ => ZMod 2) x.1 x.2 k)
          (Fin.cons (α := fun _ => ZMod 2) x.1 x.2 (k + 1))
      apply congrArg (M k (Fin.cons (α := fun _ => ZMod 2) x.1 x.2 k))
      simpa only [Fin.tail_cons, Fin.cons_zero] using
        cyclic_snoc (Fin.cons (α := fun _ => ZMod 2) x.1 x.2) k

private theorem sign_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | @insert i s hi ih => simp [hi, sign_add, ih]

private theorem cyclic_exponent {n : ℕ} [NeZero n] (b a x : Word n) :
    (∑ k, ((a k + a (k - 2) + b k) * x k + a (k - 1) * x k * x (k + 1))) =
      dot b x + dot a (chi x) := by
  classical
  have h2 : (∑ k, a (k - 2) * x k) = ∑ i, a i * x (i + 2) := by
    simpa using (Equiv.sum_comp (Equiv.addRight (2 : ZMod n))
      (fun k => a (k - 2) * x k)).symm
  have h1 : (∑ k, a (k - 1) * x k * x (k + 1)) =
      ∑ i, a i * x (i + 1) * x (i + 2) := by
    have hi (i : ZMod n) : i + 1 + 1 = i + 2 := by ring
    simpa only [Equiv.coe_addRight, add_sub_cancel_right, hi] using
      (Equiv.sum_comp (Equiv.addRight (1 : ZMod n))
        (fun k => a (k - 1) * x k * x (k + 1))).symm
  simp only [add_mul, Finset.sum_add_distrib, dot, chi, mul_add]
  rw [h2, h1]
  simp only [mul_assoc]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Expanding the literal ordered matrix trace gives the exact cyclic Boolean
phase sum, for every positive length, including coincident indices at length one. -/
theorem sourceTrace_eq_phase_sum {n : ℕ} [NeZero n] (b a : Word n) :
    sourceTrace b a = ∑ x, sign (dot b x + dot a (chi x)) := by
  classical
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ r =>
    rw [sourceTrace, ordered_trace_paths]
    let e : Word (r + 1) ≃ (Fin (r + 1) → ZMod 2) :=
      Equiv.arrowCongr (ZMod.finEquiv (r + 1)).symm.toEquiv (Equiv.refl _)
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro x _
    have he (k : Fin (r + 1)) : e x k = x ((ZMod.finEquiv (r + 1)) k) := rfl
    simp only [he, sourceMatrix]
    have hc (k : Fin (r + 1)) :
        (k.val : ZMod (r + 1)) = (ZMod.finEquiv (r + 1)) k := by
      change ((k.val : ZMod (r + 1))) = k
      exact ZMod.natCast_zmod_val ((ZMod.finEquiv (r + 1)) k)
    simp only [hc, map_add, map_one]
    rw [← sign_sum]
    apply congrArg sign
    rw [← cyclic_exponent b a x]
    exact Equiv.sum_comp (ZMod.finEquiv (r + 1)).toEquiv
      (fun k => (a k + a (k - 2) + b k) * x k + a (k - 1) * x k * x (k + 1))


end D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace
