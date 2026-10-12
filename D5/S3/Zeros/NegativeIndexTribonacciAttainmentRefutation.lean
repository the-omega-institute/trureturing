/- GID: D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation
   generality: I
   mirror-B: D5/B/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation
   mirror-E: none(waiver:exact-analytic-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.claim; result=D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.result; claim=D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.claim
   digest: Mane's negative-index root-amplitude attainment fails at k = 3 and n = -15. -/

/- result:
   proof_shape: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (#14674; Refuted)
   Direct frozen dependencies: none (pinned Mathlib only).
   Definitions: a, F, zeta, claim; proof_shape: not-applicable (definition).
   a_three_step: proof_shape: bind-only; consumers: f_eval.
   f_eval: proof_shape: bind-only; consumers: mapped_eval.
   exists_real_factor: proof_shape: bind-only; consumers: quartic_norm_bound, nonzero_root_exists.
   quotient_data: proof_shape: bind-only; consumers: quartic_norm_bound.
   cubic_norm_bound: proof_shape: bind-only; consumers: quartic_norm_bound.
   quartic_norm_bound: proof_shape: bind-only; consumers: nonzero_root_bound.
   mapped_eval: proof_shape: bind-only;
     consumers: nonzero_root_bound, nonzero_root_exists, amplitude_set_finite.
   nonzero_root_bound: proof_shape: bind-only; consumers: zeta_lt_five.
   nonzero_root_exists: proof_shape: bind-only; consumers: zeta_lt_five.
   amplitude_set_finite: proof_shape: bind-only; consumers: zeta_lt_five.
   zeta_lt_five: proof_shape: bind-only; consumers: result.
   Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.CauchyBound

set_option autoImplicit false
set_option maxRecDepth 2000

namespace D5.S3.Zeros.NegativeIndexTribonacciAttainmentRefutation
open Polynomial

noncomputable def a (k m : ℕ) : Polynomial ℤ :=
  if m = 0 then 1
  else if k = 0 ∨ m < k then 0
  else a k (m-k) - ∑ j : Fin (k-1), X ^ (k-(j.val+1)) * a k (m-k+(j.val+1))
termination_by m
decreasing_by
  · omega
  · have hj := Fin.isLt j
    omega

noncomputable def F (k : ℕ) (n : ℤ) : Polynomial ℤ := a k (1-n).toNat
noncomputable def zeta (k : ℕ) (p : Polynomial ℤ) : ℝ :=
  sSup ((fun z : ℂ => ‖z‖ ^ k) ''
    {z | z ≠ 0 ∧ (p.map (Int.castRingHom ℂ)).eval z = 0})
def claim : Prop := ∀ k : ℕ, k ≥ 3 → ∀ s : ℕ, s ≥ 1 →
  zeta k (F k (-((s*k : ℕ) : ℤ))) = (s : ℝ)

private theorem a_three_step (m : ℕ) :
    a 3 (m + 3) = a 3 m - X ^ 2 * a 3 (m + 1) - X * a 3 (m + 2) := by
  rw [a]
  simp [Fin.sum_univ_succ]
  ring


private theorem f_eval :
    F 3 (-15) = -X * (X ^ 12 + 8 * X ^ 9 + 18 * X ^ 6 + 15 * X ^ 3 + 5) := by
  have h0 : a 3 0 = 1 := by rw [a]; simp
  have h1 : a 3 1 = 0 := by rw [a]; simp
  have h2 : a 3 2 = 0 := by rw [a]; simp
  have h3 := a_three_step 0
  norm_num only [h0, h1, h2, Nat.reduceAdd] at h3
  ring_nf at h3
  have h4 := a_three_step 1
  norm_num only [h1, h2, h3, Nat.reduceAdd] at h4
  ring_nf at h4
  have h5 := a_three_step 2
  norm_num only [h2, h3, h4, Nat.reduceAdd] at h5
  ring_nf at h5
  have h6 := a_three_step 3
  norm_num only [h3, h4, h5, Nat.reduceAdd] at h6
  ring_nf at h6
  have h7 := a_three_step 4
  norm_num only [h4, h5, h6, Nat.reduceAdd] at h7
  ring_nf at h7
  have h8 := a_three_step 5
  norm_num only [h5, h6, h7, Nat.reduceAdd] at h8
  ring_nf at h8
  have h9 := a_three_step 6
  norm_num only [h6, h7, h8, Nat.reduceAdd] at h9
  ring_nf at h9
  have h10 := a_three_step 7
  norm_num only [h7, h8, h9, Nat.reduceAdd] at h10
  ring_nf at h10
  have h11 := a_three_step 8
  norm_num only [h8, h9, h10, Nat.reduceAdd] at h11
  ring_nf at h11
  have h12 := a_three_step 9
  norm_num only [h9, h10, h11, Nat.reduceAdd] at h12
  ring_nf at h12
  have h13 := a_three_step 10
  norm_num only [h10, h11, h12, Nat.reduceAdd] at h13
  ring_nf at h13
  have h14 := a_three_step 11
  norm_num only [h11, h12, h13, Nat.reduceAdd] at h14
  ring_nf at h14
  have h15 := a_three_step 12
  norm_num only [h12, h13, h14, Nat.reduceAdd] at h15
  ring_nf at h15
  have h16 := a_three_step 13
  norm_num only [h13, h14, h15, Nat.reduceAdd] at h16
  ring_nf at h16
  change a 3 16 = _
  rw [h16]
  ring


private theorem exists_real_factor :
    ∃ A : ℝ, 4 < A ∧ A < 5 ∧ A ^ 4 - 8 * A ^ 3 + 18 * A ^ 2 - 15 * A + 5 = 0 := by
  let f : ℝ → ℝ := fun u => u ^ 4 - 8 * u ^ 3 + 18 * u ^ 2 - 15 * u + 5
  have hc : Continuous f := by unfold f; fun_prop
  have hmem : (0 : ℝ) ∈ Set.Icc (f 4) (f 5) := by norm_num [f]
  obtain ⟨A, hA, hroot⟩ := intermediate_value_Icc (by norm_num : (4 : ℝ) ≤ 5)
    hc.continuousOn hmem
  refine ⟨A, ?_, ?_, hroot⟩
  · have hne : A ≠ 4 := by intro h; subst A; norm_num [f] at hroot
    exact lt_of_le_of_ne hA.1 (Ne.symm hne)
  · have hne : A ≠ 5 := by intro h; subst A; norm_num [f] at hroot
    exact lt_of_le_of_ne hA.2 hne

private theorem quotient_data (A : ℝ) (h4 : 4 < A) (h5 : A < 5)
    (hroot : A ^ 4 - 8 * A ^ 3 + 18 * A ^ 2 - 15 * A + 5 = 0) :
    let b := 8 - A
    let c := A ^ 2 - 8 * A + 18
    let d := 15 - A * c
    0 < b ∧ b < 4 ∧ 0 < c ∧ c < 3 ∧ 0 < d ∧ d < 5 / 4 ∧
    ∀ t : ℂ, t ^ 4 + 8 * t ^ 3 + 18 * t ^ 2 + 15 * t + 5 =
      (t + (A : ℂ)) * (t ^ 3 + (b : ℂ) * t ^ 2 + (c : ℂ) * t + (d : ℂ)) := by
  dsimp
  have hc0 : 0 < A ^ 2 - 8 * A + 18 := by nlinarith [sq_nonneg (A - 4)]
  have hc3 : A ^ 2 - 8 * A + 18 < 3 := by
    nlinarith [mul_pos (by linarith : 0 < A - 3) (by linarith : 0 < 5 - A)]
  have hd : A * (15 - A * (A ^ 2 - 8 * A + 18)) = 5 := by nlinarith [hroot]
  have hd0 : 0 < 15 - A * (A ^ 2 - 8 * A + 18) := by
    by_contra hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ A) (le_of_not_gt hn)
    linarith
  have hd5 : 15 - A * (A ^ 2 - 8 * A + 18) < 5 / 4 := by nlinarith
  refine ⟨by linarith, by linarith, hc0, hc3, hd0, hd5, ?_⟩
  intro t
  have hcast : (A : ℂ) * (15 - (A : ℂ) * ((A : ℂ) ^ 2 - 8 * (A : ℂ) + 18)) = 5 := by
    exact_mod_cast hd
  push_cast
  linear_combination - hcast

private theorem cubic_norm_bound (b c d : ℝ)
    (hb0 : 0 < b) (hb4 : b < 4) (hc0 : 0 < c) (hc3 : c < 3)
    (hd0 : 0 < d) (hd5 : d < 5 / 4) (t : ℂ)
    (hz : t ^ 3 + (b : ℂ) * t ^ 2 + (c : ℂ) * t + (d : ℂ) = 0) : ‖t‖ < 5 := by
  let p : Polynomial ℂ := X ^ 3 + C (b : ℂ) * X ^ 2 + C (c : ℂ) * X + C (d : ℂ)
  have hdeg : p.natDegree = 3 := by dsimp [p]; compute_degree <;> norm_num
  have hlc : p.leadingCoeff = 1 := by rw [Polynomial.leadingCoeff, hdeg]; simp [p]
  have hp : p ≠ 0 := by intro h; simp [h] at hdeg
  have hr : p.IsRoot t := by simpa [Polynomial.IsRoot, p] using hz
  have hs : (Finset.range p.natDegree).sup (fun n => ‖p.coeff n‖₊) ≤ 4 := by
    rw [hdeg]
    apply Finset.sup_le
    intro n hn
    have hn' := Finset.mem_range.mp hn
    interval_cases n
    · change ‖p.coeff 0‖₊ ≤ 4
      have hc : p.coeff 0 = (d : ℂ) := by simp [p]
      rw [hc]
      change ‖(d : ℂ)‖ ≤ (4 : ℝ)
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
      linarith
    · have hc : p.coeff 1 = (c : ℂ) := by simp [p]
      rw [hc]
      change ‖(c : ℂ)‖ ≤ (4 : ℝ)
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
      linarith
    · have hc : p.coeff 2 = (b : ℂ) := by simp [p]
      rw [hc]
      change ‖(b : ℂ)‖ ≤ (4 : ℝ)
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]
      exact hb4.le
  have hcb : p.cauchyBound ≤ 5 := by
    simp only [Polynomial.cauchyBound, hlc, nnnorm_one, div_one]
    calc
      _ ≤ (4 : NNReal) + 1 := add_le_add hs le_rfl
      _ = 5 := by norm_num
  have ht := hr.norm_lt_cauchyBound hp
  exact_mod_cast ht.trans_le hcb

private theorem quartic_norm_bound (t : ℂ)
    (h : t ^ 4 + 8 * t ^ 3 + 18 * t ^ 2 + 15 * t + 5 = 0) : ‖t‖ < 5 := by
  obtain ⟨A, h4, h5, hroot⟩ := exists_real_factor
  obtain ⟨hb0, hb4, hc0, hc3, hd0, hd5, hfactor⟩ := quotient_data A h4 h5 hroot
  rw [hfactor] at h
  rcases mul_eq_zero.mp h with h | h
  · have ht : t = -(A : ℂ) := eq_neg_of_add_eq_zero_left h
    rw [ht, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < A)]
    exact h5
  · exact cubic_norm_bound _ _ _ hb0 hb4 hc0 hc3 hd0 hd5 t h

private theorem mapped_eval (x : ℂ) :
    ((F 3 (-15)).map (Int.castRingHom ℂ)).eval x =
    -x * ((x ^ 3) ^ 4 + 8 * (x ^ 3) ^ 3 + 18 * (x ^ 3) ^ 2 + 15 * x ^ 3 + 5) := by
  rw [f_eval]
  simp only [Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
  ring

private theorem nonzero_root_bound (x : ℂ) (hx : x ≠ 0)
    (hz : ((F 3 (-15)).map (Int.castRingHom ℂ)).eval x = 0) : ‖x‖ ^ 3 < 5 := by
  rw [mapped_eval] at hz
  have hq := (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr hx)
  simpa only [norm_pow] using quartic_norm_bound (x ^ 3) hq

private theorem nonzero_root_exists :
    ∃ x : ℂ, x ≠ 0 ∧ ((F 3 (-15)).map (Int.castRingHom ℂ)).eval x = 0 := by
  obtain ⟨A, h4, h5, hroot⟩ := exists_real_factor
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (-(A : ℂ)) (by norm_num : 0 < (3 : ℕ))
  have hA : (A : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by linarith : 0 < A))
  refine ⟨x, ?_, ?_⟩
  · intro hzero
    rw [hzero, zero_pow (by decide : (3 : ℕ) ≠ 0)] at hx
    exact (neg_ne_zero.mpr hA) hx.symm
  · rw [mapped_eval, hx]
    have hc : (A : ℂ) ^ 4 - 8 * (A : ℂ) ^ 3 + 18 * (A : ℂ) ^ 2 - 15 * (A : ℂ) + 5 = 0 := by
      exact_mod_cast hroot
    have hq : (-(A : ℂ)) ^ 4 + 8 * (-(A : ℂ)) ^ 3 +
        18 * (-(A : ℂ)) ^ 2 + 15 * (-(A : ℂ)) + 5 = 0 := by
      linear_combination hc
    rw [hq, mul_zero]

private theorem amplitude_set_finite :
    (((fun z : ℂ => ‖z‖ ^ 3) ''
      {z | z ≠ 0 ∧ ((F 3 (-15)).map (Int.castRingHom ℂ)).eval z = 0}) : Set ℝ).Finite := by
  have hp : (F 3 (-15)).map (Int.castRingHom ℂ) ≠ 0 := by
    intro hp
    have he : ((F 3 (-15)).map (Int.castRingHom ℂ)).eval 1 = 0 := by rw [hp]; simp
    rw [mapped_eval] at he
    norm_num at he
  have hf := Polynomial.finite_setOfPred_isRoot hp
  exact (hf.subset (fun _ hz => hz.2)).image _

private theorem zeta_lt_five : zeta 3 (F 3 (-15)) < 5 := by
  obtain ⟨x, hx, hz⟩ := nonzero_root_exists
  have hne : ((fun z : ℂ => ‖z‖ ^ 3) ''
      {z | z ≠ 0 ∧ ((F 3 (-15)).map (Int.castRingHom ℂ)).eval z = 0}).Nonempty :=
    ⟨‖x‖ ^ 3, x, ⟨hx, hz⟩, rfl⟩
  obtain ⟨y, ⟨hy, he⟩, hye⟩ := hne.csSup_mem amplitude_set_finite
  change sSup _ < 5
  rw [← hye]
  exact nonzero_root_bound y hy he

theorem result : ¬ claim := by
  intro h
  have he := h 3 (by decide) 5 (by decide)
  have ht := zeta_lt_five
  norm_num at he
  rw [he] at ht
  exact (lt_irrefl (5 : ℝ)) ht

end D5.S3.Zeros.NegativeIndexTribonacciAttainmentRefutation
