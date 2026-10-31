/- GID: D5/S3/QuantumBounds/HighSpinCHSHNonviolation
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/HighSpinCHSHNonviolation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Local spin components satisfy the CHSH bound for every spin at least one. -/

import D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment
import D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint
import D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound
import D5.S3.QuantumBounds.LandauCommutingCollapse

/-! The symmetric-qubit dilation of linear spin observables gives the CHSH bound. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder symmDiff Matrix.Norms.L2Operator
open Matrix Complex
open D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment (spinComponent raising_entry)
open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (Jplus Jx Jy Jz)

namespace D5.S3.QuantumBounds.HighSpinCHSHNonviolation

/-- A measurement direction has Euclidean length one. -/
def unit (u : Fin 3 → ℝ) : Prop := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1

/-- The CHSH operator for the source's linear spin observables. -/
def chshOperator (n : ℕ) (a c b d : Fin 3 → ℝ) :
    Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ :=
  spinComponent n a ⊗ₖ spinComponent n b +
    spinComponent n a ⊗ₖ spinComponent n d +
    spinComponent n c ⊗ₖ spinComponent n b -
    spinComponent n c ⊗ₖ spinComponent n d

/-- Nonviolation for every density matrix and every four local spin directions, n = 2s ≥ 2. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ ρ : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ,
      ρ.PosSemidef → ρ.trace = 1 → ∀ a c b d : Fin 3 → ℝ,
        unit a → unit c → unit b → unit d →
          ‖(ρ * chshOperator n a c b d).trace‖ ≤ (n : ℝ) ^ 2 / 2

private def dicke (n : ℕ) : Matrix (Finset (Fin n)) (Fin (n + 1)) ℂ :=
  fun x k => if x.card = k.val then (1 / Real.sqrt (n.choose k.val : ℝ) : ℝ) else 0

private def slotPauli (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ :=
  fun x y =>
    (if x = y then (if r ∈ x then -(u 2 : ℂ) else (u 2 : ℂ)) else 0) +
    (if y = x ∆ {r} then
      (u 0 : ℂ) + (if r ∈ x then I * (u 1 : ℂ) else -I * (u 1 : ℂ)) else 0)

private def dilation (n : ℕ) :
    Matrix (Finset (Fin n) × Finset (Fin n)) (Fin (n + 1) × Fin (n + 1)) ℂ :=
  dicke n ⊗ₖ dicke n

private def liftedOperator (n : ℕ) (r t : Fin n) (a c b d : Fin 3 → ℝ) :
    Matrix (Finset (Fin n) × Finset (Fin n)) (Finset (Fin n) × Finset (Fin n)) ℂ :=
  let α := slotPauli n r a ⊗ₖ (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)
  let γ := slotPauli n t c ⊗ₖ (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)
  let β := (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ) ⊗ₖ slotPauli n r b
  let δ := (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ) ⊗ₖ slotPauli n t d
  α * (β + δ) + γ * (β - δ)

private lemma dicke_isometry (n : ℕ) : (dicke n)ᴴ * dicke n = 1 := by
  have hd (x : Finset (Fin n)) (k : Fin (n + 1)) :
      dicke n x k = if x.card = k.val then
        ((1 / Real.sqrt (n.choose k.val : ℝ) : ℝ) : ℂ) else 0 := rfl
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · subst j
    have hh (x : Finset (Fin n)) :
        (dicke n)ᴴ i x * dicke n x i = if x.card = i.val then
          (((1 / Real.sqrt (n.choose i.val : ℝ) : ℝ) : ℂ)) ^ 2 else 0 := by
      by_cases hx : x.card = i.val <;>
        simp [conjTranspose_apply, hd, hx, pow_two]
    simp_rw [hh]
    rw [← Finset.sum_filter]
    have hcount :
        (Finset.univ.filter (fun x : Finset (Fin n) => x.card = i.val)).card = n.choose i.val := by
      simpa only [Fintype.card_subtype, Fintype.card_fin] using
        Fintype.card_finset_len (α := Fin n) i.val
    simp only [Finset.sum_const, nsmul_eq_mul, hcount, Matrix.one_apply_eq]
    have hc : (n.choose i.val : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : i.val ≤ n)))
    have hn : (n.choose i.val : ℝ) * (1 / Real.sqrt (n.choose i.val : ℝ)) ^ 2 = 1 := by
      rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp [hc]
    exact_mod_cast hn
  · rw [Matrix.one_apply_ne hij]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hi : x.card = i.val
    · have hj : x.card ≠ j.val := fun hj => hij (Fin.ext (hi.symm.trans hj))
      simp [conjTranspose_apply, hd, hj]
    · simp [conjTranspose_apply, hd, hi]

private lemma slot_entry (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ)
    (x y : Finset (Fin n)) : slotPauli n r u x y =
      (if x = y then (if r ∈ x then -(u 2 : ℂ) else (u 2 : ℂ)) else 0) +
      (if y = x ∆ {r} then
        (u 0 : ℂ) + (if r ∈ x then I * (u 1 : ℂ) else -I * (u 1 : ℂ)) else 0) := rfl

private lemma slot_left_mul {κ : Type*} (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ)
    (m : Matrix (Finset (Fin n)) κ ℂ) (x : Finset (Fin n)) (y : κ) :
    (slotPauli n r u * m) x y =
      (if r ∈ x then -(u 2 : ℂ) else (u 2 : ℂ)) * m x y +
      ((u 0 : ℂ) + (if r ∈ x then I * (u 1 : ℂ) else -I * (u 1 : ℂ))) *
        m (x ∆ {r}) y := by
  simp only [Matrix.mul_apply, slot_entry, add_mul, ite_mul, zero_mul,
    Finset.sum_add_distrib]
  simp

private lemma slot_hermitian (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ) :
    (slotPauli n r u).IsHermitian := by
  change (slotPauli n r u)ᴴ = slotPauli n r u
  ext x y
  change star (slotPauli n r u y x) = slotPauli n r u x y
  by_cases hxy : x = y
  · subst y
    have hf : x ∆ {r} ≠ x := by
      simpa only [ne_eq, symmDiff_eq_left, Finset.bot_eq_empty] using Finset.singleton_ne_empty r
    by_cases hr : r ∈ x <;> simp [slot_entry, hf.symm, hr]
  · by_cases hy : y = x ∆ {r}
    · subst y
      have hf : x ∆ {r} ≠ x := by
        simpa only [ne_eq, symmDiff_eq_left, Finset.bot_eq_empty] using Finset.singleton_ne_empty r
      by_cases hr : r ∈ x <;>
        simp [slot_entry, hf, hf.symm, symmDiff_symmDiff_cancel_right,
          Finset.mem_symmDiff, hr]
    · have hx : x ≠ y ∆ {r} :=
        fun h => hy ((eq_comm.trans (symmDiff_left_involutive {r}).eq_iff).mp h)
      simp [slot_entry, hxy, Ne.symm hxy, hy, hx]

private lemma slot_square (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ) (hu : unit u) :
    slotPauli n r u * slotPauli n r u = 1 := by
  have huC : (u 0 : ℂ) ^ 2 + (u 1 : ℂ) ^ 2 + (u 2 : ℂ) ^ 2 = 1 := by
    exact_mod_cast hu
  ext x y
  rw [slot_left_mul, slot_entry, slot_entry, symmDiff_symmDiff_cancel_right]
  have hf : x ∆ {r} ≠ x := by
    simpa only [ne_eq, symmDiff_eq_left, Finset.bot_eq_empty] using Finset.singleton_ne_empty r
  by_cases hxy : x = y
  · subst y
    by_cases hr : r ∈ x <;>
      simp [hf, hf.symm, Finset.mem_symmDiff, hr]
    all_goals ring_nf; simp only [I_sq]; linear_combination huC
  · by_cases hy : y = x ∆ {r}
    · subst y
      by_cases hr : r ∈ x <;>
        simp [hf, hf.symm, Finset.mem_symmDiff, hr]
      all_goals ring
    · have hfy : x ∆ {r} ≠ y := Ne.symm hy
      simp [hxy, Ne.symm hxy, hy, hfy]

private lemma slots_commute (n : ℕ) (r t : Fin n) (hrt : r ≠ t)
    (u v : Fin 3 → ℝ) : Commute (slotPauli n r u) (slotPauli n t v) := by
  change slotPauli n r u * slotPauli n t v = slotPauli n t v * slotPauli n r u
  ext x y
  rw [slot_left_mul, slot_left_mul]
  have hr : r ∈ x ∆ {t} ↔ r ∈ x := by simp [Finset.mem_symmDiff, hrt]
  have ht : t ∈ x ∆ {r} ↔ t ∈ x := by simp [Finset.mem_symmDiff, hrt.symm]
  simp only [slot_entry, hr, ht, symmDiff_right_comm x {r} {t},
    (eq_comm : x ∆ {r} = y ↔ y = x ∆ {r}),
    (eq_comm : x ∆ {t} = y ↔ y = x ∆ {t})]
  split_ifs <;> ring

private lemma absent_count (n k : ℕ) (r : Fin n) :
    (Finset.univ.filter (fun x : Finset (Fin n) => x.card = k ∧ r ∉ x)).card =
      (n - 1).choose k := by
  have hf : Finset.univ.filter (fun x : Finset (Fin n) => x.card = k ∧ r ∉ x) =
      ((Finset.univ : Finset (Fin n)).erase r).powersetCard k := by
    ext x
    simp [Finset.subset_erase, and_comm]
  rw [hf, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ r),
    Finset.card_univ, Fintype.card_fin]

private lemma absent_choose_identity (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    (n : ℝ) * ((n - 1).choose k : ℝ) = ((n : ℝ) - k) * (n.choose k : ℝ) := by
  have h := congrArg (fun m : ℕ => (m : ℝ)) (Nat.choose_mul_succ_eq (n - 1) k)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
  push_cast [Nat.cast_sub hk] at h
  simpa only [mul_comm] using h

private lemma raising_coefficient (n k : ℕ) (hk : k < n) :
    ((n - 1).choose k : ℝ) * (1 / Real.sqrt (n.choose k : ℝ)) *
        (1 / Real.sqrt (n.choose (k + 1) : ℝ)) =
      (1 / n : ℝ) * Real.sqrt (((k : ℝ) + 1) * ((n : ℝ) - k)) := by
  let a : ℝ := (n - 1).choose k
  let b : ℝ := n.choose k
  let c : ℝ := n.choose (k + 1)
  let q : ℝ := ((k : ℝ) + 1) * ((n : ℝ) - k)
  have hn : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hb : 0 < b := by
    change 0 < (n.choose k : ℝ)
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt hk)
  have hc : 0 < c := by
    change 0 < (n.choose (k + 1) : ℝ)
    exact_mod_cast Nat.choose_pos (show k + 1 ≤ n by omega)
  have h₁ : (n : ℝ) * a = ((n : ℝ) - k) * b :=
    absent_choose_identity n k hn hk.le
  have hroot : (n : ℝ) * a = Real.sqrt q * Real.sqrt b * Real.sqrt c := by
    calc
      _ = ((n : ℝ) - k) * b := h₁
      _ = (((n : ℝ) - k) * Real.sqrt b) * Real.sqrt b := by
        rw [mul_assoc, ← pow_two, Real.sq_sqrt hb.le]
      _ = (Real.sqrt q * Real.sqrt c) * Real.sqrt b := by
        rw [(D5.S3.Quantum.Contextuality.TemporalHardySpinAttainment.ladder_pair n k hk).1]
      _ = _ := by
        ring
  change a * (1 / Real.sqrt b) * (1 / Real.sqrt c) = (1 / n : ℝ) * Real.sqrt q
  have hsb : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  have hsc : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  apply (mul_left_cancel₀ (ne_of_gt hnR))
  rw [one_div, one_div, one_div]
  calc
    _ = ((n : ℝ) * a) * ((Real.sqrt b)⁻¹ * (Real.sqrt c)⁻¹) := by ring
    _ = (Real.sqrt q * Real.sqrt b * Real.sqrt c) *
        ((Real.sqrt b)⁻¹ * (Real.sqrt c)⁻¹) := by rw [hroot]
    _ = Real.sqrt q * (Real.sqrt b * (Real.sqrt b)⁻¹) *
        (Real.sqrt c * (Real.sqrt c)⁻¹) := by ring
    _ = Real.sqrt q := by rw [mul_inv_cancel₀ hsb, mul_inv_cancel₀ hsc, mul_one, mul_one]
    _ = (n : ℝ) * ((n : ℝ)⁻¹ * Real.sqrt q) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hnR), one_mul]

private def raisingSlot (n : ℕ) (r : Fin n) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ :=
  fun x y => if r ∉ x ∧ y = x ∆ {r} then 1 else 0

private def zSlot (n : ℕ) (r : Fin n) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ :=
  diagonal fun x => if r ∈ x then -1 else 1

private lemma raising_action (n : ℕ) (r : Fin n) (x : Finset (Fin n)) (j : Fin (n + 1)) :
    (raisingSlot n r * dicke n) x j = if r ∉ x then dicke n (x ∆ {r}) j else 0 := by
  have he (x y : Finset (Fin n)) :
      raisingSlot n r x y = if r ∉ x ∧ y = x ∆ {r} then 1 else 0 := rfl
  by_cases hr : r ∈ x <;> simp [Matrix.mul_apply, he, hr]

private lemma raising_compression (n : ℕ) (r : Fin n) :
    (dicke n)ᴴ * raisingSlot n r * dicke n = (1 / n : ℂ) • Jplus n := by
  have hd (x : Finset (Fin n)) (k : Fin (n + 1)) :
      dicke n x k = if x.card = k.val then
        ((1 / Real.sqrt (n.choose k.val : ℝ) : ℝ) : ℂ) else 0 := rfl
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  have he (x : Finset (Fin n)) :
      (dicke n)ᴴ i x * (raisingSlot n r * dicke n) x j =
        if i.val + 1 = j.val then
          if x.card = i.val ∧ r ∉ x then
            ((1 / Real.sqrt (n.choose i.val : ℝ) : ℝ) : ℂ) *
              ((1 / Real.sqrt (n.choose j.val : ℝ) : ℝ) : ℂ) else 0
        else 0 := by
    rw [raising_action, conjTranspose_apply]
    by_cases hr : r ∈ x
    · simp [hr]
    · have hf :=
        D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint.flip_card_not_mem x r hr
      by_cases hi : x.card = i.val <;> by_cases hij : i.val + 1 = j.val <;>
        simp [hd, hr, hf, hi, hij]
  simp_rw [he]
  by_cases hij : i.val + 1 = j.val
  · simp only [ite_eq_left hij]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, absent_count, Matrix.smul_apply,
      smul_eq_mul]
    have hk : i.val < n := by have := j.isLt; omega
    have hjR : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
    have hJ : Jplus n i j =
        (Real.sqrt (((i.val : ℝ) + 1) * ((n : ℝ) - i.val)) : ℂ) := by
      rw [raising_entry, ite_eq_left hij]
      congr 1
      rw [hjR]
      congr 1
      ring
    rw [hJ, ← hij]
    have hh := raising_coefficient n i.val hk
    have hhC := congrArg Complex.ofReal hh
    push_cast at hhC ⊢
    simpa only [mul_assoc] using hhC
  · simp only [ite_eq_right hij, Finset.sum_const_zero, Matrix.smul_apply, smul_eq_mul]
    change 0 = (1 / n : ℂ) * (if i.val + 1 = j.val then _ else 0)
    rw [ite_eq_right hij, mul_zero]

private lemma z_compression (n : ℕ) (r : Fin n) :
    (dicke n)ᴴ * zSlot n r * dicke n = (2 / n : ℂ) • Jz n := by
  have hd (x : Finset (Fin n)) (k : Fin (n + 1)) :
      dicke n x k = if x.card = k.val then
        ((1 / Real.sqrt (n.choose k.val : ℝ) : ℝ) : ℂ) else 0 := rfl
  have hsum (k : ℕ) :
      (∑ x : Finset (Fin n), if x.card = k then (if r ∈ x then (-1 : ℂ) else 1) else 0) =
        2 * ((n - 1).choose k : ℂ) - (n.choose k : ℂ) := by
    have he (x : Finset (Fin n)) :
        (if x.card = k then (if r ∈ x then (-1 : ℂ) else 1) else 0) =
          2 * (if x.card = k ∧ r ∉ x then (1 : ℂ) else 0) -
            (if x.card = k then 1 else 0) := by
      by_cases hx : x.card = k <;> by_cases hr : r ∈ x <;> norm_num [hx, hr]
    simp_rw [he]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hweight :
        (Finset.univ.filter (fun x : Finset (Fin n) => x.card = k)).card = n.choose k := by
      simpa only [Fintype.card_subtype, Fintype.card_fin] using
        Fintype.card_finset_len (α := Fin n) k
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      absent_count, hweight]
  ext i j
  change ((dicke n)ᴴ * (diagonal (fun x => if r ∈ x then (-1 : ℂ) else 1) :
      Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ) * dicke n) i j =
    (2 / n : ℂ) * diagonal (fun k : Fin (n + 1) => (((n : ℝ) / 2 - k.val : ℝ) : ℂ)) i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, conjTranspose_apply]
  by_cases hij : i = j
  · subst j
    have he (x : Finset (Fin n)) :
        star (dicke n x i) * ((if r ∈ x then (-1 : ℂ) else 1) * dicke n x i) =
          (((1 / Real.sqrt (n.choose i.val : ℝ) : ℝ) : ℂ)) ^ 2 *
            (if x.card = i.val then (if r ∈ x then (-1 : ℂ) else 1) else 0) := by
      by_cases hx : x.card = i.val <;> by_cases hr : r ∈ x <;>
        simp [hd, hx, hr, pow_two]
    simp_rw [he]
    rw [← Finset.mul_sum, hsum, Matrix.diagonal_apply_eq]
    have hn : 0 < n := Fin.pos r
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hc : (n.choose i.val : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : i.val ≤ n)))
    have hA := absent_choose_identity n i.val hn (show i.val ≤ n by omega)
    have hh : (1 / Real.sqrt (n.choose i.val : ℝ)) ^ 2 *
        (2 * ((n - 1).choose i.val : ℝ) - (n.choose i.val : ℝ)) =
        (2 / n : ℝ) * ((n : ℝ) / 2 - i.val) := by
      rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      field_simp
      nlinarith [hA]
    have hhC := congrArg Complex.ofReal hh
    push_cast at hhC ⊢
    exact hhC
  · rw [Matrix.diagonal_apply_ne _ hij, mul_zero]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hi : x.card = i.val
    · have hj : x.card ≠ j.val := fun hj => hij (Fin.ext (hi.symm.trans hj))
      simp [hd, hj]
    · simp [hd, hi]

private lemma slot_decomposition (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ) :
    slotPauli n r u = ((u 0 : ℂ) - I * (u 1 : ℂ)) • raisingSlot n r +
      ((u 0 : ℂ) + I * (u 1 : ℂ)) • (raisingSlot n r)ᴴ + (u 2 : ℂ) • zSlot n r := by
  have hz (x y : Finset (Fin n)) : zSlot n r x y =
      if x = y then (if r ∈ x then (-1 : ℂ) else 1) else 0 := rfl
  have he (x y : Finset (Fin n)) :
      raisingSlot n r x y = if r ∉ x ∧ y = x ∆ {r} then 1 else 0 := rfl
  ext x y
  simp only [slot_entry, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, conjTranspose_apply,
    he, hz]
  by_cases hxy : x = y
  · subst y
    have hf : x ∆ {r} ≠ x := by
      simpa only [ne_eq, symmDiff_eq_left, Finset.bot_eq_empty] using Finset.singleton_ne_empty r
    by_cases hr : r ∈ x <;> simp [hr, Ne.symm hf]
  · by_cases hy : y = x ∆ {r}
    · subst y
      have hf : x ∆ {r} ≠ x := by
        simpa only [ne_eq, symmDiff_eq_left, Finset.bot_eq_empty] using Finset.singleton_ne_empty r
      by_cases hr : r ∈ x <;>
        simp [Ne.symm hf, symmDiff_symmDiff_cancel_right, Finset.mem_symmDiff, hr,
          sub_eq_add_neg]
    · have hx : x ≠ y ∆ {r} :=
        fun h => hy ((eq_comm.trans (symmDiff_left_involutive {r}).eq_iff).mp h)
      simp [hxy, hy, hx]

private lemma slot_compression (n : ℕ) (r : Fin n) (u : Fin 3 → ℝ) :
    (dicke n)ᴴ * slotPauli n r u * dicke n = (2 / n : ℂ) • spinComponent n u := by
  have hadj : (dicke n)ᴴ * (raisingSlot n r)ᴴ * dicke n =
      (1 / n : ℂ) • (Jplus n)ᴴ := by
    have h := congrArg (fun m : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => mᴴ)
      (raising_compression n r)
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_smul,
      star_div₀, star_one, star_natCast, Matrix.mul_assoc] using h
  rw [slot_decomposition]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [raising_compression, hadj, z_compression]
  change _ = (2 / n : ℂ) •
    ((u 0 : ℂ) • ((1 / 2 : ℂ) • (Jplus n + (Jplus n)ᴴ)) +
      (u 1 : ℂ) • ((1 / (2 * I) : ℂ) • (Jplus n - (Jplus n)ᴴ)) + (u 2 : ℂ) • Jz n)
  have hI : (1 / (2 * I) : ℂ) = -I / 2 := by
    simp only [div_eq_mul_inv, _root_.mul_inv_rev, Complex.inv_I, one_mul]
  rw [hI]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  ring

private lemma dilation_isometry (n : ℕ) : (dilation n)ᴴ * dilation n = 1 := by
  change (dicke n ⊗ₖ dicke n)ᴴ * (dicke n ⊗ₖ dicke n) = 1
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, dicke_isometry, one_kronecker_one]

private lemma lifted_expansion (n : ℕ) (hn : 2 ≤ n) (a c b d : Fin 3 → ℝ) :
    liftedOperator n ⟨0, by omega⟩ ⟨1, by omega⟩ a c b d =
      slotPauli n ⟨0, by omega⟩ a ⊗ₖ slotPauli n ⟨0, by omega⟩ b +
      slotPauli n ⟨0, by omega⟩ a ⊗ₖ slotPauli n ⟨1, by omega⟩ d +
      slotPauli n ⟨1, by omega⟩ c ⊗ₖ slotPauli n ⟨0, by omega⟩ b -
      slotPauli n ⟨1, by omega⟩ c ⊗ₖ slotPauli n ⟨1, by omega⟩ d := by
  change (_ ⊗ₖ (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)) *
      ((1 ⊗ₖ _) + (1 ⊗ₖ _)) + (_ ⊗ₖ 1) * ((1 ⊗ₖ _) - (1 ⊗ₖ _)) = _
  simp only [mul_add, mul_sub, ← mul_kronecker_mul, mul_one, one_mul]
  abel

private lemma chsh_dilation (n : ℕ) (hn : 2 ≤ n) (a c b d : Fin 3 → ℝ) :
    chshOperator n a c b d = ((n : ℂ) / 2) ^ 2 •
      ((dilation n)ᴴ * liftedOperator n ⟨0, by omega⟩ ⟨1, by omega⟩ a c b d * dilation n) := by
  have hk (r t : Fin n) (u v : Fin 3 → ℝ) :
      (dilation n)ᴴ * (slotPauli n r u ⊗ₖ slotPauli n t v) * dilation n =
        (2 / n : ℂ) ^ 2 • (spinComponent n u ⊗ₖ spinComponent n v) := by
    change (dicke n ⊗ₖ dicke n)ᴴ * _ * (dicke n ⊗ₖ dicke n) = _
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul,
      slot_compression, slot_compression, smul_kronecker, kronecker_smul, smul_smul,
      ← pow_two]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hscale : ((n : ℂ) / 2) ^ 2 * (2 / n : ℂ) ^ 2 = 1 := by
    rw [← mul_pow, div_mul_div_cancel₀ (by norm_num : (2 : ℂ) ≠ 0),
      div_self hn0, one_pow]
  rw [lifted_expansion n hn a c b d]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
    hk, ← smul_add, ← smul_sub,
    smul_smul, hscale, one_smul]
  rfl

private lemma lifted_hermitian (n : ℕ) (hn : 2 ≤ n) (a c b d : Fin 3 → ℝ) :
    (liftedOperator n ⟨0, by omega⟩ ⟨1, by omega⟩ a c b d).IsHermitian := by
  rw [lifted_expansion n hn a c b d]
  have hh (r t : Fin n) (u v : Fin 3 → ℝ) :
      (slotPauli n r u ⊗ₖ slotPauli n t v).IsHermitian :=
    D5.S3.Quantum.Information.PartialTraceMutualInformation.isHermitian_kronecker
      (slot_hermitian n r u) (slot_hermitian n t v)
  exact (((hh _ _ _ _).add (hh _ _ _ _)).add (hh _ _ _ _)).sub (hh _ _ _ _)

private lemma lifted_square (n : ℕ) (hn : 2 ≤ n) (a c b d : Fin 3 → ℝ)
    (ha : unit a) (hc : unit c) (hb : unit b) (hd : unit d) :
    (liftedOperator n ⟨0, by omega⟩ ⟨1, by omega⟩ a c b d) ^ 2 = (4 : ℂ) • 1 := by
  rw [lifted_expansion n hn a c b d]
  have hfour : (4 : ℂ) • (1 : Matrix (Finset (Fin n) × Finset (Fin n))
      (Finset (Fin n) × Finset (Fin n)) ℂ) = (4 : ℕ) • 1 :=
    Nat.cast_smul_eq_nsmul ℂ 4 1
  rw [hfour]
  exact D5.S3.QuantumBounds.LandauCommutingCollapse.chsh_square_eq_four_of_local_pair_commutes
    (slotPauli n ⟨0, by omega⟩ a) (slotPauli n ⟨1, by omega⟩ c)
    (slotPauli n ⟨0, by omega⟩ b) (slotPauli n ⟨1, by omega⟩ d)
    ⟨slot_hermitian _ _ _, by simpa only [pow_two] using slot_square _ _ _ ha⟩
    ⟨slot_hermitian _ _ _, by simpa only [pow_two] using slot_square _ _ _ hc⟩
    ⟨slot_hermitian _ _ _, by simpa only [pow_two] using slot_square _ _ _ hb⟩
    ⟨slot_hermitian _ _ _, by simpa only [pow_two] using slot_square _ _ _ hd⟩
    (Or.inl (slots_commute n _ _ (by intro h; have := congrArg Fin.val h; simp at this) a c).eq)

private lemma dilated_density (n : ℕ)
    (ρ : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    (dilation n * ρ * (dilation n)ᴴ).PosSemidef ∧
      (dilation n * ρ * (dilation n)ᴴ).trace = 1 := by
  refine ⟨hρ.mul_mul_conjTranspose_same _, ?_⟩
  rw [trace_mul_cycle, dilation_isometry, one_mul, htrace]

private lemma density_involution_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ l : Matrix ι ι ℂ) (hτ : τ.PosSemidef) (ht : τ.trace = 1)
    (hl : l.IsHermitian) (hs : l ^ 2 = (4 : ℂ) • 1) : ‖(τ * l).trace‖ ≤ 2 := by
  have hn := Matrix.l2_opNorm_conjTranspose_mul_self l
  rw [hl.eq, ← pow_two, hs, norm_smul] at hn
  have hnorm : ‖l‖ ≤ 2 := by
    by_cases hι : IsEmpty ι
    · letI := hι
      have hz : l = 0 := Subsingleton.elim _ _
      simp [hz]
    · haveI : Nonempty ι := not_isEmpty_iff.mp hι
      rw [norm_one] at hn
      norm_num at hn
      nlinarith [norm_nonneg l]
  exact (D5.S3.Quantum.Information.GeometricDiscordMutualCorrelationBound.density_expectation_bound
    τ l hτ ht).trans hnorm

private lemma expectation_bound (n : ℕ) (hn : 2 ≤ n)
    (ρ : Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) (a c b d : Fin 3 → ℝ)
    (ha : unit a) (hc : unit c) (hb : unit b) (hd : unit d) :
    ‖(ρ * chshOperator n a c b d).trace‖ ≤ (n : ℝ) ^ 2 / 2 := by
  have hτ := dilated_density n ρ hρ ht
  have hbnd := density_involution_bound _ _ hτ.1 hτ.2
    (lifted_hermitian n hn a c b d) (lifted_square n hn a c b d ha hc hb hd)
  have he := chsh_dilation n hn a c b d
  let l := liftedOperator n ⟨0, by omega⟩ ⟨1, by omega⟩ a c b d
  have htrace : (ρ * ((dilation n)ᴴ * l * dilation n)).trace =
      ((dilation n * ρ * (dilation n)ᴴ) * l).trace := by
    simpa only [Matrix.mul_assoc] using trace_mul_cycle (ρ * (dilation n)ᴴ) l (dilation n)
  rw [he, Matrix.mul_smul, trace_smul, norm_smul, htrace]
  have hnorm : ‖((n : ℂ) / 2) ^ 2‖ = ((n : ℝ) / 2) ^ 2 := by
    simp only [norm_pow, norm_div, Complex.norm_natCast, norm_ofNat]
  rw [hnorm]
  calc
    _ ≤ ((n : ℝ) / 2) ^ 2 * 2 := mul_le_mul_of_nonneg_left hbnd (sq_nonneg _)
    _ = (n : ℝ) ^ 2 / 2 := by ring

theorem result : claim := by
  intro n hn ρ hρ ht a c b d ha hc hb hd
  exact expectation_bound n hn ρ hρ ht a c b d ha hc hb hd

end D5.S3.QuantumBounds.HighSpinCHSHNonviolation
