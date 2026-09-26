/- GID: D5/S3/Estimation/TimeArrow/ParityKernelSubcoordinates
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/ParityKernelSubcoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parity kernels keep every proper coordinate record i.i.d. uniform. -/

import D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments
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
open D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments

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

/-- **Proper coordinate projections are i.i.d. uniform.** For every parity kernel on the
`d`-dimensional sign hypercube, started from the uniform law, and every proper subset `S` of the
coordinates, the coordinates in `S` at times `0, …, T` are independent and uniform on `{±1}^S`. -/
theorem subcoordinateLaw_eq {d : ℕ} (a : (Fin d → ℤˣ) → ℝ) (S : Finset (Fin d))
    (hS : S ≠ Finset.univ) (T : ℕ) (w : Fin (T + 1) → Fin d → ℤˣ) :
    subcoordinateLaw a S T w = (1 / 2 ^ S.card) ^ (T + 1) := by
  -- on a fiber fixing the coordinates of the proper set `S` the parity sums to zero: this is the
  -- frozen equality of the proper marginals of the two parity classes, read on sign vectors
  have hfiber : ∀ w : Fin d → ℤˣ,
      ∑ y ∈ Finset.univ.filter (fun y : Fin d → ℤˣ => ∀ j ∈ S, y j = w j), parity y = 0 := by
    intro w
    classical
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; exact absurd (Subsingleton.elim S univ) hS
      · exact ⟨d - 1, by omega⟩
    let toSign : Fin 2 → ℤˣ := fun b => if b = 0 then -1 else 1
    let toBit : ℤˣ → Fin 2 := fun u => if u = 1 then 1 else 0
    have hts : ∀ u, toSign (toBit u) = u := by
      intro u
      rcases Int.units_eq_one_or u with h | h <;> subst h <;> simp [toSign, toBit] <;> decide
    have hst : ∀ b, toBit (toSign b) = b := by
      intro b; fin_cases b <;> simp [toSign, toBit] <;> decide
    let e : (Fin (k + 1) → Fin 2) ≃ (Fin (k + 1) → ℤˣ) :=
      Equiv.piCongrRight fun _ => ⟨toSign, toBit, hst, hts⟩
    have hsign : ∀ b : Fin 2, (((toSign b : ℤˣ) : ℤ) : ℝ) = ((paritySign b : ℤ) : ℝ) := by
      intro b; fin_cases b <;> simp [toSign, paritySign]
    have hpar : ∀ x : Fin (k + 1) → Fin 2, parity (e x) = ((∏ i, paritySign (x i) : ℤ) : ℝ) := by
      intro x
      simp only [parity, e, Equiv.piCongrRight_apply, Equiv.coe_fn_mk, Units.coe_prod, Int.cast_prod]
      exact Finset.prod_congr rfl fun i _ => hsign (x i)
    let yb : Fin (k + 1) → Fin 2 := fun j => toBit (w j)
    have hagree : ∀ x : Fin (k + 1) → Fin 2,
        (∀ j ∈ S, e x j = w j) ↔ (∀ j ∈ S, x j = yb j) := by
      intro x
      refine forall₂_congr fun j _ => ?_
      constructor
      · intro h; show x j = toBit (w j); rw [← h]; exact (hst (x j)).symm
      · intro h; show toSign (x j) = w j; rw [h]; exact hts (w j)
    have hmass := (parity_conditioned_probability_form k).2.2.2.2 S hS yb
    unfold parityMarginalMass at hmass
    -- pointwise: the full product is `2^k` times the difference of the two parity laws
    have hpt : ∀ x : Fin (k + 1) → Fin 2,
        ((∏ i, paritySign (x i) : ℤ) : ℚ) =
          2 ^ k * (parityLaw (k + 1) 1 x - parityLaw (k + 1) (-1) x) := by
      intro x
      have hprod : (∏ i, paritySign (x i)) = 1 ∨ (∏ i, paritySign (x i)) = -1 := by
        refine Finset.prod_induction _ (fun m : ℤ => m = 1 ∨ m = -1) ?_ (Or.inl rfl) ?_
        · rintro m n (rfl | rfl) (rfl | rfl) <;> norm_num
        · intro i _
          unfold paritySign; split_ifs <;> simp
      have hk : (2 : ℚ) ^ k ≠ 0 := by positivity
      rcases hprod with h | h
      · have h1 : x ∈ parityFiber (k + 1) 1 := by simp [parityFiber, h]
        have h2 : x ∉ parityFiber (k + 1) (-1) := by simp [parityFiber, h]
        simp only [parityLaw, if_pos h1, if_neg h2, h, Nat.add_sub_cancel]
        field_simp
        norm_num
      · have h1 : x ∉ parityFiber (k + 1) 1 := by simp [parityFiber, h]
        have h2 : x ∈ parityFiber (k + 1) (-1) := by simp [parityFiber, h]
        simp only [parityLaw, if_neg h1, if_pos h2, h, Nat.add_sub_cancel]
        field_simp
        norm_num
    rw [Finset.sum_filter, ← e.sum_comp]
    have hQ : (∑ x : Fin (k + 1) → Fin 2,
        (if ∀ j ∈ S, x j = yb j then ((∏ i, paritySign (x i) : ℤ) : ℚ) else 0)) = 0 := by
      simp_rw [hpt, ← mul_ite_zero]
      rw [← Finset.mul_sum]
      have : (∑ x : Fin (k + 1) → Fin 2, if ∀ j ∈ S, x j = yb j then
          parityLaw (k + 1) 1 x - parityLaw (k + 1) (-1) x else 0) = 0 := by
        have hsplit : ∀ x : Fin (k + 1) → Fin 2, (if ∀ j ∈ S, x j = yb j then
            parityLaw (k + 1) 1 x - parityLaw (k + 1) (-1) x else 0) =
            (if ∀ j ∈ S, x j = yb j then parityLaw (k + 1) 1 x else 0) -
              (if ∀ j ∈ S, x j = yb j then parityLaw (k + 1) (-1) x else 0) := by
          intro x; split_ifs <;> simp
        simp_rw [hsplit]
        rw [Finset.sum_sub_distrib, ← hmass, sub_self]
      rw [this, mul_zero]
    have hR : (∑ x : Fin (k + 1) → Fin 2, (if ∀ j ∈ S, e x j = w j then parity (e x) else 0)) =
        ((∑ x : Fin (k + 1) → Fin 2,
          (if ∀ j ∈ S, x j = yb j then ((∏ i, paritySign (x i) : ℤ) : ℚ) else 0) : ℚ) : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [if_congr (hagree x) rfl rfl, hpar x]
      split_ifs <;> simp
    rw [hR, hQ, Rat.cast_zero]
  -- a fiber fixing the coordinates in `S` has `2 ^ (d - |S|)` elements
  have card_fiber : ∀ w : Fin d → ℤˣ,
      ((Finset.univ.filter (fun y : Fin d → ℤˣ => ∀ j ∈ S, y j = w j)).card : ℝ) =
        2 ^ d / 2 ^ S.card := by
    intro w
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
  -- summing a parity kernel over a proper-subset fiber gives `2^{-|S|}` from every start
  have sum_kernel_fiber : ∀ x w : Fin d → ℤˣ,
      ∑ y ∈ Finset.univ.filter (fun y : Fin d → ℤˣ => ∀ j ∈ S, y j = w j), parityKernel a x y =
        1 / 2 ^ S.card := by
    intro x w
    unfold parityKernel
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hfiber w,
      Finset.sum_const, nsmul_eq_mul, mul_one, mul_zero, add_zero, card_fiber w]
    field_simp
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
      exact sum_kernel_fiber _ _
    simp_rw [hlast, ← Finset.sum_mul]
    have := ih (fun t => w t.castSucc)
    unfold subcoordinateLaw at this
    rw [this]
    ring

#print axioms subcoordinateLaw_eq

end D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
