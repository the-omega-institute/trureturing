/- GID: D5/S1/Recurrence/Periodic/EulerSecantBridge
   generality: G
   mirror-B: D5/B/S1/Recurrence/Periodic/EulerSecantBridge
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The even ordinary Euler carrier is the existing A000364 secant carrier. -/

/-
proof_shape: secant_bridge and boundary_values are content after same-delivery inlining.
secant_bridge is the
ordinary-to-A000364 recurrence identification; boundary_values supplies the exact small
indices and the strict lower bound used by the final family.
escape_witness: secant_bridge, consumed by boundary_values and the divisor-propagation
two-primary argument on the live proof path.
admission_basis: escape-witness. The external resolution basis of #31280 belongs only to
the final source assertions; this supporting bridge carries no resolution claim.
Direct frozen dependencies: D5.S1.Recurrence.Periodic.SecantNumberPurePeriodRefutation
(a_unique, initial_values); EulerUpDownSource is a same-delivery dependency.
Private theorem consumers: sum_even -> signed_convolution; H_product -> signed_convolution;
signed_convolution -> even_recurrence -> secant_bridge.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/31291.
-/

import D5.S1.Recurrence.Periodic.EulerUpDownSource
import D5.S1.Recurrence.Periodic.SecantNumberPurePeriodRefutation

/-! The existing secant recurrence determines the even ordinary subsequence. -/

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (encode eCoeff_encode eCoeff_ext)
open D5.S1.Recurrence.Periodic.EulerUpDownSource
open D5.S1.Recurrence.Periodic.EulerSignedFrequency

namespace D5.S1.Recurrence.Periodic.EulerSecantBridge

private theorem sum_even (f : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ range (2 * n + 1), if Even i then f i else 0) =
      ∑ j ∈ range (n + 1), f (2 * j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = (∑ i ∈ range (2 * n + 1), if Even i then f i else 0) +
          f (2 * (n + 1)) := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega,
          sum_range_succ, sum_range_succ]
        simp [show Even (2 * n + 1 + 1) from ⟨n + 1, by omega⟩,
          show ¬Even (2 * n + 1) from Nat.not_even_iff_odd.mpr ⟨n, by omega⟩,
          show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
      _ = (∑ j ∈ range (n + 1), f (2 * j)) + f (2 * (n + 1)) := by rw [ih]
      _ = _ := (sum_range_succ _ (n + 1)).symm

private noncomputable def H : PowerSeries ℚ :=
  encode (fun n => if Even n then 1 else 0)

private theorem H_product : H * F 1 = 1 := by
  have hh : 2 * H = exp ℚ + rescale (-1 : ℚ) (exp ℚ) := by
    apply eCoeff_ext
    intro n
    have hL : eCoeff (2 * H) n = 2 * (if Even n then 1 else 0) := by
      simp only [eCoeff, coeff_ofNat_mul]
      rw [mul_left_comm]
      change 2 * eCoeff H n = _
      rw [H, eCoeff_encode]
    have hR : eCoeff (exp ℚ + rescale (-1 : ℚ) (exp ℚ)) n =
        1 + (-1 : ℚ) ^ n := by
      have hr : eCoeff (rescale (-1 : ℚ) (exp ℚ)) n = (-1 : ℚ) ^ n := by
        simp only [eCoeff, coeff_rescale]
        rw [mul_left_comm]
        change (-1 : ℚ) ^ n * eCoeff (exp ℚ) n = _
        rw [eCoeff_exp, mul_one]
      simp only [eCoeff, map_add, mul_add] at ⊢
      change eCoeff (exp ℚ) n + eCoeff (rescale (-1 : ℚ) (exp ℚ)) n = _
      rw [eCoeff_exp, hr]
    rw [hL, hR]
    by_cases hn : Even n
    · norm_num [hn, hn.neg_one_pow]
    · simp [hn, (Nat.not_even_iff_odd.mp hn).neg_one_pow]
  have he : exp ℚ * rescale (-1 : ℚ) (exp ℚ) = 1 := by
    simpa using (exp_mul_exp_eq_exp_add (1 : ℚ) (-1))
  have hg := generating_identity 1
  norm_num only [pow_one] at hg
  have hexp : exp ℚ ≠ 0 := by
    intro hz
    have := congrArg constantCoeff hz
    norm_num at this
  apply mul_left_cancel₀ hexp
  apply mul_left_cancel₀ (show (2 : PowerSeries ℚ) ≠ 0 by
    intro hz
    have ht := congrArg constantCoeff hz
    rw [map_ofNat constantCoeff 2, map_zero] at ht
    norm_num at ht)
  have hc : C (2 : ℚ) = (2 : PowerSeries ℚ) := map_ofNat C 2
  rw [hc] at hg
  linear_combination (exp ℚ * F 1) * hh + hg + F 1 * he

private theorem signed_convolution (n : ℕ) :
    (∑ j ∈ range (n + 2), ((2 * (n + 1)).choose (2 * j) : ℤ) *
      A 1 (2 * (n + 1 - j))) = 0 := by
  have h := congrArg (fun f => eCoeff f (2 * (n + 1))) H_product
  rw [eCoeff_mul] at h
  have hs : (∑ i ∈ range (2 * (n + 1) + 1),
      ((2 * (n + 1)).choose i : ℚ) * eCoeff H i * eCoeff (F 1) (2 * (n + 1) - i)) =
      ∑ j ∈ range (n + 2), ((2 * (n + 1)).choose (2 * j) : ℚ) *
        (A 1 (2 * (n + 1 - j)) : ℚ) := by
    calc
      _ = ∑ i ∈ range (2 * (n + 1) + 1), if Even i then
          ((2 * (n + 1)).choose i : ℚ) * (A 1 (2 * (n + 1) - i) : ℚ) else 0 := by
        apply sum_congr rfl
        intro i hi
        simp only [H, F, eCoeff_encode]
        split_ifs <;> ring
      _ = _ := by
        rw [sum_even]
        apply sum_congr rfl
        intro j hj
        rw [show 2 * (n + 1) - 2 * j = 2 * (n + 1 - j) by omega]
  rw [hs] at h
  have hz : eCoeff (1 : PowerSeries ℚ) (2 * (n + 1)) = 0 := by
    simp [eCoeff, coeff_one, show 2 * (n + 1) ≠ 0 by omega]
  rw [hz] at h
  exact_mod_cast h

private theorem even_recurrence (n : ℕ) :
    (E (2 * (n + 1)) : ℤ) = ∑ j : Fin (n + 1),
      (-1 : ℤ) ^ (j.val + 2) *
        ((2 * (n + 1)).choose (2 * (j.val + 1)) : ℤ) * (E (2 * (n - j.val)) : ℤ) := by
  have h := signed_convolution n
  rw [sum_range_succ'] at h
  simp only [Nat.mul_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero] at h
  rw [signed_even]
  have he : A 1 (2 * (n + 1)) =
      -∑ j ∈ range (n + 1), ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) *
        A 1 (2 * (n - j)) := by
    have hsum : (∑ j ∈ range (n + 1),
        ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * A 1 (2 * (n + 1 - (j + 1)))) =
        ∑ j ∈ range (n + 1), ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) *
          A 1 (2 * (n - j)) := by
      apply sum_congr rfl
      intro j hj
      rw [show n + 1 - (j + 1) = n - j by omega]
    rw [hsum] at h
    linear_combination h
  rw [he, mul_neg, mul_sum,
    Fin.sum_univ_eq_sum_range (fun j => (-1 : ℤ) ^ (j + 2) *
      ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * (E (2 * (n - j)) : ℤ)),
    ← sum_neg_distrib]
  apply sum_congr rfl
  intro j hj
  rw [signed_even]
  have hjn := mem_range.mp hj
  have heven : (-1 : ℤ) ^ (j + 2) * (-1 : ℤ) ^ (n - j) =
      -(-1 : ℤ) ^ (n + 1) := by
    rw [← pow_add, show j + 2 + (n - j) = (n + 1) + 1 by omega, pow_succ]
    ring
  linear_combination -((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) *
    A 1 (2 * (n - j)) * heven

/-- The even subsequence is exactly the repository's existing A000364 carrier. -/
theorem secant_bridge (s : ℕ) :
    (E (2 * s) : ℤ) = SecantNumberPurePeriodRefutation.a s := by
  have hh := SecantNumberPurePeriodRefutation.a_unique
    (fun s => (E (2 * s) : ℤ)) (by simp [E]) even_recurrence
  exact congrFun hh s

/-- The exact source boundary values and the strict bound needed for the particular family. -/
theorem boundary_values : E 0 = 1 ∧ E 1 = 1 ∧ E 2 = 1 ∧ E 3 = 2 ∧
    ∀ k : ℕ, 4 ≤ k → 2 < E k := by
  refine ⟨by simp [E], by simp [E], ?_, ?_, ?_⟩
  · norm_num [E, Fin.sum_univ_succ]
  · norm_num [E, Fin.sum_univ_succ]
  · intro k hk
    have he4 : E 4 = 5 := by
      have he := secant_bridge 2
      rw [SecantNumberPurePeriodRefutation.initial_values.2.2.1] at he
      exact_mod_cast he
    have hh := monotone_E hk
    rw [he4] at hh
    omega

end D5.S1.Recurrence.Periodic.EulerSecantBridge
