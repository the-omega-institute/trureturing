/- GID: D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/ParityKernelSubcoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parity kernels keep proper coordinate records i.i.d. uniform and mix in two steps. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates

open Finset

/-- The parity character `χ(x) = x₁ ⋯ x_d` of a sign vector. -/
def parity {d : ℕ} (x : Fin d → ℤˣ) : ℝ := (((∏ j, x j : ℤˣ) : ℤ) : ℝ)

/-- The parity kernel `P_a(x, y) = (1 + a(x) χ(y)) / 2^d` on the sign hypercube. -/
noncomputable def parityKernel {d : ℕ} (a : (Fin d → ℤˣ) → ℝ) (x y : Fin d → ℤˣ) : ℝ :=
  (1 + a x * parity y) / 2 ^ d

/-- The probability, for the chain started from the uniform law, that the coordinates in `S` of the
states at times `0, …, T` read `w 0, …, w T`. -/
noncomputable def subcoordinateLaw {d : ℕ} (a : (Fin d → ℤˣ) → ℝ) (S : Finset (Fin d)) (T : ℕ)
    (w : Fin (T + 1) → Fin d → ℤˣ) : ℝ :=
  ∑ x : Fin (T + 1) → Fin d → ℤˣ,
    (1 / 2 ^ d : ℝ) * (∏ t : Fin T, parityKernel a (x t.castSucc) (x t.succ)) *
      ∏ t : Fin (T + 1), (if ∀ j ∈ S, x t j = w t j then (1 : ℝ) else 0)

/-- Flipping one coordinate negates the parity. -/
private theorem parity_flip {d : ℕ} (j : Fin d) (y : Fin d → ℤˣ) :
    parity (Function.update y j (-y j)) = -parity y := by
  unfold parity
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun i => y i) (Finset.mem_univ j)]
  have hrest : ∏ i ∈ Finset.univ.erase j, Function.update y j (-y j) i =
      ∏ i ∈ Finset.univ.erase j, y i := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hrest, Function.update_self]
  push_cast
  ring

/-- On a fiber that fixes the coordinates in a proper subset `S`, the parity sums to zero: flipping
a free coordinate is an involution of the fiber that negates the parity. -/
private theorem sum_parity_fiber {d : ℕ} (S : Finset (Fin d)) (hS : S ≠ Finset.univ)
    (w : Fin d → ℤˣ) :
    ∑ y ∈ Finset.univ.filter (fun y : Fin d → ℤˣ => ∀ j ∈ S, y j = w j), parity y = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, j ∉ S := by
    by_contra h
    exact hS (Finset.eq_univ_of_forall fun i => by_contra fun hi => h ⟨i, hi⟩)
  set F := Finset.univ.filter (fun y : Fin d → ℤˣ => ∀ j ∈ S, y j = w j)
  let σ : (Fin d → ℤˣ) → (Fin d → ℤˣ) := fun y => Function.update y j (-y j)
  have hσσ : ∀ y, σ (σ y) = y := by
    intro y
    funext i
    by_cases hi : i = j
    · subst hi; simp [σ]
    · simp [σ, Function.update_of_ne hi]
  have hmem : ∀ y ∈ F, σ y ∈ F := by
    intro y hy
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    intro i hi
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [σ, Function.update_of_ne hij, hy i hi]
  have hsum : ∑ y ∈ F, parity y = ∑ y ∈ F, parity (σ y) := by
    refine Finset.sum_nbij' σ σ hmem hmem (fun y _ => hσσ y) (fun y _ => hσσ y) ?_
    intro y _
    rw [hσσ]
  have hneg : ∑ y ∈ F, parity (σ y) = -∑ y ∈ F, parity y := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ => parity_flip j y
  linarith

/-- A fiber fixing the coordinates in `S` has `2 ^ (d - |S|)` elements. -/
private theorem card_fiber {d : ℕ} (S : Finset (Fin d)) (w : Fin d → ℤˣ) :
    ((Finset.univ.filter (fun y : Fin d → ℤˣ => ∀ j ∈ S, y j = w j)).card : ℝ) =
      2 ^ d / 2 ^ S.card := by
  have hset : Finset.univ.filter (fun y : Fin d → ℤˣ => ∀ j ∈ S, y j = w j) =
      Fintype.piFinset (fun j => if j ∈ S then ({w j} : Finset ℤˣ) else Finset.univ) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      split_ifs with hj
      · simp [h j hj]
      · exact Finset.mem_univ _
    · intro h j hj
      simpa [hj] using h j
  rw [hset, Fintype.card_piFinset]
  have hprod : ∏ j, (if j ∈ S then ({w j} : Finset ℤˣ) else Finset.univ).card =
      2 ^ (d - S.card) := by
    have hcard : ∀ j, (if j ∈ S then ({w j} : Finset ℤˣ) else Finset.univ).card =
        if j ∈ S then 1 else 2 := by
      intro j
      split_ifs
      · simp
      · rw [Finset.card_univ, Fintype.card_units_int]
    simp_rw [hcard]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
    simp
  rw [hprod]
  have hle : S.card ≤ d := by simpa using Finset.card_le_univ S
  rw [Nat.cast_pow, Nat.cast_ofNat, eq_div_iff (by positivity), ← pow_add, Nat.sub_add_cancel hle]

/-- Summing a parity kernel over a proper-subset fiber gives `2^{-|S|}`, whatever the start. -/
private theorem sum_kernel_fiber {d : ℕ} (a : (Fin d → ℤˣ) → ℝ) (S : Finset (Fin d))
    (hS : S ≠ Finset.univ) (x w : Fin d → ℤˣ) :
    ∑ y ∈ Finset.univ.filter (fun y : Fin d → ℤˣ => ∀ j ∈ S, y j = w j), parityKernel a x y =
      1 / 2 ^ S.card := by
  unfold parityKernel
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, sum_parity_fiber S hS w,
    Finset.sum_const, nsmul_eq_mul, mul_one, mul_zero, add_zero, card_fiber]
  field_simp

/-- **Proper coordinate projections are i.i.d. uniform.** For every parity kernel on the
`d`-dimensional sign hypercube, started from the uniform law, and every proper subset `S` of the
coordinates, the coordinates in `S` at times `0, …, T` are independent and uniform on `{±1}^S`. -/
theorem subcoordinateLaw_eq {d : ℕ} (a : (Fin d → ℤˣ) → ℝ) (S : Finset (Fin d))
    (hS : S ≠ Finset.univ) (T : ℕ) (w : Fin (T + 1) → Fin d → ℤˣ) :
    subcoordinateLaw a S T w = (1 / 2 ^ S.card) ^ (T + 1) := by
  induction T with
  | zero =>
    unfold subcoordinateLaw
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin d → ℤˣ)) _
      (fun y => (1 / 2 ^ d : ℝ) * (if ∀ j ∈ S, y j = w 0 j then (1 : ℝ) else 0))
      (fun x => by simp [Equiv.funUnique])]
    rw [← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      card_fiber]
    rw [zero_add, pow_one]
    field_simp
  | succ T ih =>
    unfold subcoordinateLaw
    rw [← (Fin.snocEquiv (fun _ : Fin (T + 2) => Fin d → ℤˣ)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    have hstep : ∀ (xi : Fin (T + 1) → Fin d → ℤˣ) (xl : Fin d → ℤˣ),
        (1 / 2 ^ d : ℝ) *
            (∏ t : Fin (T + 1), parityKernel a
              ((Fin.snocEquiv (fun _ : Fin (T + 2) => Fin d → ℤˣ)) (xl, xi) t.castSucc)
              ((Fin.snocEquiv (fun _ : Fin (T + 2) => Fin d → ℤˣ)) (xl, xi) t.succ)) *
            ∏ t : Fin (T + 2), (if ∀ j ∈ S,
              (Fin.snocEquiv (fun _ : Fin (T + 2) => Fin d → ℤˣ)) (xl, xi) t j = w t j
              then (1 : ℝ) else 0) =
          ((1 / 2 ^ d : ℝ) * (∏ t : Fin T, parityKernel a (xi t.castSucc) (xi t.succ)) *
            ∏ t : Fin (T + 1), (if ∀ j ∈ S, xi t j = w t.castSucc j then (1 : ℝ) else 0)) *
          (parityKernel a (xi (Fin.last T)) xl *
            (if ∀ j ∈ S, xl j = w (Fin.last (T + 1)) j then (1 : ℝ) else 0)) := by
      intro xi xl
      rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc (n := T + 1)]
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.snoc_last,
        Fin.succ_castSucc, Fin.succ_last]
      ring
    simp_rw [hstep, ← Finset.mul_sum]
    have hlast : ∀ xi : Fin (T + 1) → Fin d → ℤˣ,
        ∑ xl : Fin d → ℤˣ, parityKernel a (xi (Fin.last T)) xl *
            (if ∀ j ∈ S, xl j = w (Fin.last (T + 1)) j then (1 : ℝ) else 0) =
          1 / 2 ^ S.card := by
      intro xi
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      exact sum_kernel_fiber a S hS _ _
    simp_rw [hlast, ← Finset.sum_mul]
    have := ih (fun t => w t.castSucc)
    unfold subcoordinateLaw at this
    rw [this]
    ring

/-- **Two steps reach the uniform law.** If the second profile `b` has `∑ b = 0` and
`∑ χ b = 0`, then for every first profile `a` the product `P_a P_b` is the uniform kernel
`Π(x, z) = 2^{-d}`; in particular `P² = Π` on the family with `E a = 0` and `E[χ a] = 0`. -/
theorem parityKernel_mul_eq_uniform {d : ℕ} (hd : 1 ≤ d) (a b : (Fin d → ℤˣ) → ℝ)
    (hb : ∑ y, b y = 0) (hχb : ∑ y, parity y * b y = 0) (x z : Fin d → ℤˣ) :
    ∑ y, parityKernel a x y * parityKernel b y z = 1 / 2 ^ d := by
  have hχ : ∑ y : Fin d → ℤˣ, parity y = 0 := by
    have h := sum_parity_fiber (d := d) ∅ (by
      intro h
      have : (⟨0, hd⟩ : Fin d) ∈ (∅ : Finset (Fin d)) := h ▸ Finset.mem_univ _
      simp at this) (fun _ => 1)
    simpa using h
  unfold parityKernel
  have hexp : ∀ y, (1 + a x * parity y) / 2 ^ d * ((1 + b y * parity z) / 2 ^ d) =
      (1 + a x * parity y + parity z * b y + a x * parity z * (parity y * b y)) / (2 ^ d) ^ 2 := by
    intro y; field_simp; ring
  simp_rw [hexp]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hχ, hb, hχb]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_units_int, nsmul_eq_mul, mul_one, mul_zero, add_zero]
  push_cast
  field_simp

#print axioms subcoordinateLaw_eq
#print axioms parityKernel_mul_eq_uniform

end D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
