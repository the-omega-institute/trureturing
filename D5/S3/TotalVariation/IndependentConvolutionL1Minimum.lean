/- GID: D5/S3/TotalVariation/IndependentConvolutionL1Minimum
   generality: G
   mirror-B: D5/B/S3/TotalVariation/IndependentConvolutionL1Minimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact independent finite - convolution L1 minimum on real closed simplices. -/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

open scoped BigOperators
noncomputable section
/-!
The optimization target is Conjecture 4.7, equation (21), of Nilava Metya and
Satyaki Mukherjee, * Approximate Uniformity in Finite Convolution Models*,
arXiv:2609.38243v1, §4.3 (CC BY - SA 4.0). The attaining pair is equation (22)
with parameter 1. The lower bound uses the actual independent product throughout.
-/

namespace D5.S3.TotalVariation.IndependentConvolutionL1Minimum

/-- Ordinary convolution with natural addition of the input indices. -/
def ordinaryConvolution (n : ℕ) (p q : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i.val + j.val = k then p i * q j else 0

/-- The full L1 deviation from the uniform law on the ordinary output support. -/
def fullL1 (n : ℕ) (p q : Fin n → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (2 * n - 1), |ordinaryConvolution n p q k - 1 / (2 * n - 1 : ℕ)|

private def theta (m : ℕ) : ℝ := Real.pi / m
private def ray (r θ : ℝ) : ℂ :=
  (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)

/-- Metya–Mukherjee, Conjecture 4.7: the exact minimum over every pair of real
closed real simplex factors, including boundary points and ordinary natural index convolution. -/
theorem result (n : ℕ) (hn : 3 ≤ n) :
    IsLeast {v : ℝ | ∃ p q : Fin n → ℝ,
      p ∈ stdSimplex ℝ (Fin n) ∧ q ∈ stdSimplex ℝ (Fin n) ∧ fullL1 n p q = v}
      (1 / (2 * n - 1 : ℕ)) := by
  classical
  /- Positive coefficients of an actual independent product force a nonpositive real crossing
  on the boundary ray of the nonnegative factor sector. -/
  have actual_product_crossing {m : ℕ} (hm : 2 ≤ m)
      (p q : Fin (m + 1) → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
      (hc : ∀ k < 2 * m + 1, 0 < ordinaryConvolution (m + 1) p q k) :
      ∃ r : ℝ, 0 < r ∧
        (∑ k ∈ Finset.range (2 * m + 1),
          (ordinaryConvolution (m + 1) p q k : ℂ) * ray r (theta m) ^ k).im = 0 ∧
        (∑ k ∈ Finset.range (2 * m + 1),
          (ordinaryConvolution (m + 1) p q k : ℂ) * ray r (theta m) ^ k).re ≤ 0 := by
    classical
    have hθ : 0 < theta m := by unfold theta; positivity
    have hθπ : theta m < Real.pi := by
      unfold theta
      exact div_lt_self Real.pi_pos (by exact_mod_cast (show 1 < m by omega))
    have hmθ : (m : ℝ) * theta m = Real.pi := by
      unfold theta
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      field_simp
    have hs : 0 < Real.sin (theta m) := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
    have hsin (j : ℕ) (hj : j ≤ m) : 0 ≤ Real.sin ((j : ℝ) * theta m) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (Nat.cast_nonneg _) hθ.le)
      calc
        (j : ℝ) * theta m ≤ (m : ℝ) * theta m :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hθ.le
        _ = Real.pi := hmθ
    have hpowers (r θ : ℝ) (k : ℕ) :
        ray r θ ^ k = (r ^ k : ℝ) *
          ((Real.cos (k * θ) : ℂ) + (Real.sin (k * θ) : ℂ) * Complex.I) := by

      rw [ray, mul_pow, Complex.ofReal_cos, Complex.ofReal_sin,
        Complex.cos_add_sin_mul_I_pow k (θ : ℂ)]
      simp only [Complex.ofReal_pow, Complex.ofReal_cos, Complex.ofReal_sin,
        Complex.ofReal_mul, Complex.ofReal_natCast]


    have heval (z : ℂ) :
        (∑ k ∈ Finset.range (2 * m + 1), (ordinaryConvolution (m + 1) p q k : ℂ) * z ^ k) =
          (∑ i : Fin (m + 1), (p i : ℂ) * z ^ i.val) *
          (∑ j : Fin (m + 1), (q j : ℂ) * z ^ j.val) := by

      classical
      unfold ordinaryConvolution
      calc
        (∑ k ∈ Finset.range (2 * m + 1),
          (((∑ i : Fin (m + 1), ∑ j : Fin (m + 1), if i.val + j.val = k then p i * q j else 0) : ℝ) : ℂ) * z ^ k) =
          ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            (p i : ℂ) * (q j : ℂ) * z ^ (i.val + j.val) := by
              simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_zero,
                Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro j hj
              have hlt : i.val + j.val < 2 * m + 1 := by omega
              have hrewrite : ∀ x : ℕ,
                  (((if i.val + j.val = x then p i * q j else 0 : ℝ) : ℂ) * z ^ x) =
                    (if i.val + j.val = x then (p i : ℂ) * (q j : ℂ) * z ^ (i.val + j.val) else 0) := by
                intro x
                by_cases hx : i.val + j.val = x <;> simp [hx]
              simp_rw [hrewrite]
              rw [Finset.sum_ite_eq (Finset.range (2 * m + 1)) (i.val + j.val)
                (fun _ => (p i : ℂ) * (q j : ℂ) * z ^ (i.val + j.val))]
              simp [hlt]
        _ = (∑ i : Fin (m + 1), (p i : ℂ) * z ^ i.val) * (∑ j : Fin (m + 1), (q j : ℂ) * z ^ j.val) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [pow_add]
          ring
    let c := ordinaryConvolution (m + 1) p q
    let F : ℝ → ℝ := fun r =>
      ∑ k ∈ Finset.range (2 * m + 1), c k * r ^ k * Real.sin ((k : ℝ) * theta m)
    have him (r : ℝ) :
        (∑ k ∈ Finset.range (2 * m + 1), (c k : ℂ) * ray r (theta m) ^ k).im = F r := by
      simp only [Complex.im_sum, hpowers, Complex.mul_im, Complex.mul_re,
        Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, zero_mul, mul_zero, mul_one, mul_zero,
        add_zero, zero_add, sub_zero]
      simp only [F, mul_assoc]
    have hpair (r : ℝ) : F r =
        ∑ j ∈ Finset.range m, Real.sin ((j : ℝ) * theta m) *
          (c j * r ^ j - c (m + j) * r ^ (m + j)) := by
      have h2m : ((2 * m : ℕ) : ℝ) * theta m = 2 * Real.pi := by
        push_cast; rw [mul_assoc, hmθ]
      have hadd (j : ℕ) : Real.sin (((m + j : ℕ) : ℝ) * theta m) =
          - Real.sin ((j : ℝ) * theta m) := by
        push_cast
        rw [add_mul, hmθ, add_comm, Real.sin_add_pi]
      dsimp [F]
      rw [Finset.sum_range_succ, h2m, Real.sin_two_pi, mul_zero, add_zero,
        show 2 * m = m + m by omega, Finset.sum_range_add]
      simp_rw [hadd]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    let A := ∑ j ∈ Finset.range m, c j * Real.sin ((j : ℝ) * theta m)
    let B := ∑ j ∈ Finset.range m, c (m + j) * Real.sin ((j : ℝ) * theta m)
    have hAB : 0 < A ∧ 0 < B := by
      constructor <;> apply Finset.sum_pos'
      · intro j hj
        exact mul_nonneg (hc j (by have := Finset.mem_range.mp hj; omega)).le
          (hsin j (by have := Finset.mem_range.mp hj; omega))
      · refine ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
        simpa using mul_pos (hc 1 (by omega)) hs
      · intro j hj
        exact mul_nonneg (hc (m + j) (by have := Finset.mem_range.mp hj; omega)).le
          (hsin j (by have := Finset.mem_range.mp hj; omega))
      · refine ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
        simpa using mul_pos (hc (m + 1) (by omega)) hs
    have hsmall (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) : r ^ m * (A - B * r) ≤ F r := by
      rw [hpair]
      have hexpand : r ^ m * (A - B * r) =
          ∑ j ∈ Finset.range m, Real.sin ((j : ℝ) * theta m) *
            (c j * r ^ m - c (m + j) * r ^ (m + 1)) := by
        simp only [A, B, mul_sub, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib,
          pow_succ]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> ring
      rw [hexpand]
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j; simp
      · have hjm := Finset.mem_range.mp hj
        apply mul_le_mul_of_nonneg_left _ (hsin j (by omega))
        apply sub_le_sub
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hr.le hr1 (by omega)) (hc j (by omega)).le
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hr.le hr1 (by omega)) (hc (m + j) (by omega)).le
    have hlarge (r : ℝ) (hr : 1 ≤ r) : F r ≤ r ^ m * (A - B * r) := by
      rw [hpair]
      have hexpand : r ^ m * (A - B * r) =
          ∑ j ∈ Finset.range m, Real.sin ((j : ℝ) * theta m) *
            (c j * r ^ m - c (m + j) * r ^ (m + 1)) := by
        simp only [A, B, mul_sub, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib,
          pow_succ]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;> ring
      rw [hexpand]
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j; simp
      · have hjm := Finset.mem_range.mp hj
        apply mul_le_mul_of_nonneg_left _ (hsin j (by omega))
        apply sub_le_sub
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (by omega))
            (hc j (by omega)).le
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (by omega))
            (hc (m + j) (by omega)).le
    let a := min 1 (A / (2 * B))
    let b := max 1 (2 * A / B)
    have hBpos : 0 < B := hAB.2
    have ha : 0 < a := lt_min zero_lt_one (div_pos hAB.1 (mul_pos (by norm_num) hBpos))
    have hab : a ≤ b := (min_le_left _ _).trans (le_max_left _ _)
    have habA : B * a ≤ A / 2 := by
      have h := min_le_right (1 : ℝ) (A / (2 * B))
      change a ≤ A / (2 * B) at h
      have hh := (le_div_iff₀ (show 0 < 2 * B from mul_pos (by norm_num) hBpos)).mp h
      nlinarith
    have hbA : 2 * A ≤ B * b := by
      have h := le_max_right (1 : ℝ) (2 * A / B)
      change 2 * A / B ≤ b at h
      have hh := (div_le_iff₀ hAB.2).mp h
      nlinarith
    have hFa : 0 < F a := lt_of_lt_of_le
      (mul_pos (pow_pos ha _) (by linarith [hAB.1])) (hsmall a ha (min_le_left _ _))
    have hFb : F b < 0 := lt_of_le_of_lt (hlarge b (le_max_left _ _))
      (mul_neg_of_pos_of_neg (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _)
        (by linarith [hAB.1]))
    have hcont : Continuous F := by dsimp [F]; fun_prop
    obtain ⟨r, hrab, hFr⟩ := intermediate_value_Icc' hab hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (F b) (F a) from ⟨hFb.le, hFa.le⟩)
    have hr : 0 < r := ha.trans_le hrab.1
    have hI : (∑ k ∈ Finset.range (2 * m + 1), (c k : ℂ) * ray r (theta m) ^ k).im = 0 := by
      rw [him, hFr]
    have hfactor (v : Fin (m + 1) → ℝ) (hv : ∀ i, 0 ≤ v i) :
        (∑ i, (v i : ℂ) * ray r (theta m) ^ i.val).im =
          ∑ i, v i * r ^ i.val * Real.sin ((i.val : ℝ) * theta m) := by
      simp only [Complex.im_sum, hpowers, Complex.mul_im, Complex.mul_re,
        Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, zero_mul, mul_zero, mul_one, add_zero, zero_add,
        sub_zero, mul_assoc]
    have hnonneg (v : Fin (m + 1) → ℝ) (hv : ∀ i, 0 ≤ v i) :
        0 ≤ (∑ i, (v i : ℂ) * ray r (theta m) ^ i.val).im := by
      rw [hfactor v hv]
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (hv i) (pow_nonneg hr.le _)) (hsin i.val (by omega))
    let one : Fin (m + 1) := ⟨1, by omega⟩
    have hstrict : 0 < p one ∨ 0 < q one := by
      by_contra! h
      have hp1 : p one = 0 := le_antisymm h.1 (hp _)
      have hq1 : q one = 0 := le_antisymm h.2 (hq _)
      have hz : c 1 = 0 := by
        dsimp [c, ordinaryConvolution]
        apply Finset.sum_eq_zero; intro i hi
        apply Finset.sum_eq_zero; intro j hj
        by_cases hij : i.val + j.val = 1
        · rw [if_pos hij]
          have : i = one ∨ j = one := by
            have : i.val = 1 ∨ j.val = 1 := by omega
            rcases this with h | h
            · exact Or.inl (Fin.ext h)
            · exact Or.inr (Fin.ext h)
          rcases this with h | h
          · rw [h, hp1, zero_mul]
          · rw [h, hq1, mul_zero]
        · rw [if_neg hij]
      have h := hc 1 (by omega)
      change 0 < c 1 at h
      rw [hz] at h
      exact lt_irrefl _ h
    have hpositive (v : Fin (m + 1) → ℝ) (hv : ∀ i, 0 ≤ v i) (hv1 : 0 < v one) :
        0 < (∑ i, (v i : ℂ) * ray r (theta m) ^ i.val).im := by
      rw [hfactor v hv]
      apply Finset.sum_pos'
      · intro i hi
        exact mul_nonneg (mul_nonneg (hv i) (pow_nonneg hr.le _)) (hsin i.val (by omega))
      · refine ⟨one, Finset.mem_univ _, ?_⟩
        simpa [one] using mul_pos (mul_pos hv1 hr) hs
    have hsign (P Q : ℂ) (hP : 0 < P.im) (hQ : 0 ≤ Q.im)
        (hI : (P * Q).im = 0) : (P * Q).re ≤ 0 := by
      have hid : P.im * (P * Q).re = P.re * (P * Q).im - Q.im * (P.re ^ 2 + P.im ^ 2) := by
        simp only [Complex.mul_re, Complex.mul_im]; ring
      have hh : P.im * (P * Q).re ≤ 0 := by
        rw [hid, hI, mul_zero, zero_sub]
        exact neg_nonpos.mpr (mul_nonneg hQ (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      exact nonpos_of_mul_nonpos_left (by simpa [mul_comm] using hh) hP
    refine ⟨r, hr, hI, ?_⟩
    rw [heval]
    dsimp [c] at hI
    rw [heval] at hI
    rcases hstrict with hp1 | hq1
    · exact hsign _ _ (hpositive p hp hp1) (hnonneg q hq) hI
    · rw [mul_comm] at hI ⊢
      exact hsign _ _ (hpositive q hq hq1) (hnonneg p hp) hI

  /- A nonpositive real evaluation on the sector boundary gives an L1 certificate for
  arbitrary real coefficients of the fixed nominal width. -/
  have nonpositive_real_coefficient_certificate {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1)
      (a : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t)
      (hI : (∑ k ∈ Finset.range (2 * d + 1), (a k : ℂ) * ray r (theta d) ^ k).im = 0)
      (hR : (∑ k ∈ Finset.range (2 * d + 1), (a k : ℂ) * ray r (theta d) ^ k).re ≤ 0) :
      t ≤ ∑ k ∈ Finset.range (2 * d + 1), |a k - t| := by
    let weight (r θ : ℝ) (k : ℕ) : ℝ :=
      r ^ k * (Real.cos (k * θ) + (1 - r * Real.cos θ) / (r * Real.sin θ) * Real.sin (k * θ))

    have theta_positive {d : ℕ} (hd : 2 ≤ d) : 0 < theta d := by
      unfold theta
      positivity

    have theta_lt_pi {d : ℕ} (hd : 2 ≤ d) : theta d < Real.pi := by
      unfold theta
      have h : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
      exact (div_lt_self Real.pi_pos h)

    have d_theta {d : ℕ} (hd : 2 ≤ d) : (d : ℝ) * theta d = Real.pi := by
      unfold theta
      have h : (d : ℝ) ≠ 0 := by positivity
      field_simp

    have weight_zero (r θ : ℝ) : weight r θ 0 = 1 := by
      simp [weight]

    have weight_one {r θ : ℝ} (hr : r ≠ 0) (hs : Real.sin θ ≠ 0) : weight r θ 1 = 1 := by
      simp only [weight, pow_one, Nat.cast_one, one_mul]
      field_simp
      ring

    have weight_difference {r θ : ℝ} (hr : r ≠ 0) (hs : Real.sin θ ≠ 0) (k : ℕ) :
        weight r θ (k + 1) - weight r θ k =
          - (1 - 2 * r * Real.cos θ + r ^ 2) * r ^ k * Real.sin (k * θ) / (r * Real.sin θ) := by
      have hangle : ((k + 1 : ℕ) : ℝ) * θ = (k : ℝ) * θ + θ := by push_cast; ring
      simp only [weight, hangle, pow_succ, Real.cos_add, Real.sin_add]
      field_simp
      linear_combination (-r ^ 2 * Real.sin ((k : ℝ) * θ)) * (Real.sin_sq_add_cos_sq θ)

    have denominator_positive {r θ : ℝ} (hs : 0 < Real.sin θ) :
        0 < 1 - 2 * r * Real.cos θ + r ^ 2 := by
      nlinarith [sq_nonneg (r - Real.cos θ), sq_pos_of_pos hs, Real.sin_sq_add_cos_sq θ]

    have weight_at_d {d : ℕ} (hd : 2 ≤ d) (r : ℝ) : weight r (theta d) d = - r ^ d := by
      simp [weight, d_theta hd]

    have weight_at_two_d {d : ℕ} (hd : 2 ≤ d) (r : ℝ) : weight r (theta d) (2 * d) = r ^ (2 * d) := by
      have hangle : ((2 * d : ℕ) : ℝ) * theta d = 2 * Real.pi := by
        push_cast
        rw [mul_assoc, d_theta hd]
      unfold weight
      rw [hangle, Real.cos_two_pi, Real.sin_two_pi]
      simp

    have sin_first_half {d k : ℕ} (hd : 2 ≤ d) (hk : k ≤ d) :
        0 ≤ Real.sin ((k : ℝ) * theta d) := by
      have hθ := (theta_positive hd).le
      apply Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg (Nat.cast_nonneg k) hθ)
      calc
        (k : ℝ) * theta d ≤ (d : ℝ) * theta d := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hθ
        _ = Real.pi := d_theta hd

    have sin_second_half {d k : ℕ} (hd : 2 ≤ d) (hk : d ≤ k) (hk' : k ≤ 2 * d) :
        Real.sin ((k : ℝ) * theta d) ≤ 0 := by
      have hθ := (theta_positive hd).le
      have hlo : Real.pi ≤ (k : ℝ) * theta d := by
        rw [← d_theta hd]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hθ
      have hhi : (k : ℝ) * theta d ≤ 2 * Real.pi := by
        calc
          (k : ℝ) * theta d ≤ ((2 * d : ℕ) : ℝ) * theta d :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hk') hθ
          _ = 2 * Real.pi := by push_cast; rw [mul_assoc, d_theta hd]
      have heq : Real.sin ((k : ℝ) * theta d) = - Real.sin ((k : ℝ) * theta d - Real.pi) := by
        have h := Real.sin_add_pi ((k : ℝ) * theta d - Real.pi)
        simpa using h
      rw [heq]
      exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))


    have weight_first_step {d k : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) (hk : k ≤ d) :
        weight r (theta d) (k + 1) ≤ weight r (theta d) k := by
      have hs := Real.sin_pos_of_pos_of_lt_pi (theta_positive hd) (theta_lt_pi hd)
      have hD := denominator_positive (r := r) hs
      have hdiff : weight r (theta d) (k + 1) - weight r (theta d) k ≤ 0 := by
        rw [weight_difference hr.ne' hs.ne']
        apply div_nonpos_of_nonpos_of_nonneg
        · exact mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hD.le) (pow_nonneg hr.le _))
            (sin_first_half hd hk)
        · positivity
      linarith

    have weight_second_step {d k : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r)
        (hk : d ≤ k) (hk' : k ≤ 2 * d) :
        weight r (theta d) k ≤ weight r (theta d) (k + 1) := by
      have hs := Real.sin_pos_of_pos_of_lt_pi (theta_positive hd) (theta_lt_pi hd)
      have hD := denominator_positive (r := r) hs
      have hdiff : 0 ≤ weight r (theta d) (k + 1) - weight r (theta d) k := by
        rw [weight_difference hr.ne' hs.ne']
        apply div_nonneg
        · exact mul_nonneg_of_nonpos_of_nonpos
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hD.le) (pow_nonneg hr.le _))
            (sin_second_half hd hk hk')
        · positivity
      linarith

    have weight_bounds {d k : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1)
        (hk : k ≤ 2 * d) : |weight r (theta d) k| ≤ 1 := by
      have hfirst : ∀ i j : ℕ, i ≤ j → j ≤ d → weight r (theta d) j ≤ weight r (theta d) i := by
        intro i j hij
        induction j, hij using Nat.le_induction with
        | base => intro _; exact le_rfl
        | succ j hij ih =>
          intro hj
          exact (weight_first_step hd hr (by omega)).trans (ih (by omega))
      have hsecond : ∀ i j : ℕ, d ≤ i → i ≤ j → j ≤ 2 * d → weight r (theta d) i ≤ weight r (theta d) j := by
        intro i j hdi hij
        induction j, hij using Nat.le_induction with
        | base => intro _; exact le_rfl
        | succ j hij ih =>
          intro hj
          exact (ih (by omega)).trans (weight_second_step hd hr (by omega) (by omega))
      have hpow : r ^ d ≤ 1 := pow_le_one₀ hr.le hr'
      have hpow' : r ^ (2 * d) ≤ 1 := pow_le_one₀ hr.le hr'
      rw [abs_le]
      by_cases hkd : k ≤ d
      · constructor
        · have h := hfirst k d hkd (le_refl _)
          rw [weight_at_d hd] at h
          linarith
        · have h := hfirst 0 k (Nat.zero_le _) hkd
          simpa [weight_zero] using h
      · constructor
        · have h := hsecond d k (le_refl _) (by omega) hk
          rw [weight_at_d hd] at h
          linarith
        · have h := hsecond k (2 * d) (by omega) hk (le_refl _)
          rw [weight_at_two_d hd] at h
          exact h.trans hpow'


    have ray_power (r θ : ℝ) (k : ℕ) :
        ray r θ ^ k = (r ^ k : ℝ) * ((Real.cos (k * θ) : ℂ) + (Real.sin (k * θ) : ℂ) * Complex.I) := by
      rw [ray, mul_pow, Complex.ofReal_cos, Complex.ofReal_sin,
        Complex.cos_add_sin_mul_I_pow k (θ : ℂ)]
      simp only [Complex.ofReal_pow, Complex.ofReal_cos, Complex.ofReal_sin,
        Complex.ofReal_mul, Complex.ofReal_natCast]

    have weight_is_projection (r θ : ℝ) (k : ℕ) :
        weight r θ k = (ray r θ ^ k).re +
          (1 - r * Real.cos θ) / (r * Real.sin θ) * (ray r θ ^ k).im := by
      rw [ray_power]
      simp only [weight, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        zero_mul, mul_zero, mul_one, sub_zero, add_zero, zero_add]
      ring

    have ray_power_d {d : ℕ} (hd : 2 ≤ d) (r : ℝ) :
        ray r (theta d) ^ d = - (r ^ d : ℝ) := by
      rw [ray_power, d_theta hd]
      simp

    have ray_power_last {d : ℕ} (hd : 2 ≤ d) (r : ℝ) :
        ray r (theta d) ^ (2 * d + 1) = (r ^ (2 * d) : ℝ) * ray r (theta d) := by
      rw [pow_succ, show 2 * d = d + d by omega, pow_add, ray_power_d hd]
      push_cast
      ring

    have weight_sum_identity {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) :
        (1 - 2 * r * Real.cos (theta d) + r ^ 2) * (∑ k ∈ Finset.range (2 * d + 1), weight r (theta d) k) =
          2 - 2 * r * Real.cos (theta d) - r ^ (2 * d) + r ^ (2 * d + 2) := by
      let θ := theta d
      let Z := ∑ k ∈ Finset.range (2 * d + 1), ray r θ ^ k
      have hp : ray r θ ^ (2 * d + 1) = (r ^ (2 * d) : ℝ) * ray r θ := ray_power_last hd r
      have hgeom := geom_sum_mul_neg (ray r θ) (2 * d + 1)
      rw [hp] at hgeom
      change Z * (1 - ray r θ) = 1 - (r ^ (2 * d) : ℝ) * ray r θ at hgeom
      have h1 : (1 - r * Real.cos θ) * Z.re + r * Real.sin θ * Z.im = 1 - r ^ (2 * d) * r * Real.cos θ := by
        have h := congrArg Complex.re hgeom
        simp only [ray, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          zero_mul, mul_zero, mul_one, sub_zero, add_zero, zero_add] at h
        convert h using 1 <;> ring
      have h2 : (1 - r * Real.cos θ) * Z.im - r * Real.sin θ * Z.re = - r ^ (2 * d) * r * Real.sin θ := by
        have h := congrArg Complex.im hgeom
        simp only [ray, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          zero_mul, mul_zero, mul_one, sub_zero, add_zero, zero_add] at h
        convert h using 1 <;> ring
      have hsum : (∑ k ∈ Finset.range (2 * d + 1), weight r θ k) =
          Z.re + (1 - r * Real.cos θ) / (r * Real.sin θ) * Z.im := by
        simp only [weight_is_projection, Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [Z]
      change (1 - 2 * r * Real.cos θ + r ^ 2) * (∑ k ∈ Finset.range (2 * d + 1), weight r θ k) = _
      rw [hsum, show 2 * d + 2 = 2 * d + 2 by rfl, pow_add, pow_two]
      have hs := Real.sin_pos_of_pos_of_lt_pi (theta_positive hd) (theta_lt_pi hd)
      have hr0 := hr.ne'
      have hs0 : Real.sin θ ≠ 0 := hs.ne'
      field_simp
      linear_combination
        (2 * (1 - r * Real.cos θ) * (r * Real.sin θ)) * h1 +
        ((1 - r * Real.cos θ) ^ 2 - (r * Real.sin θ) ^ 2) * h2 -
        (r ^ 2 * (r * Real.sin θ * Z.re + (1 - r * Real.cos θ) * Z.im - r ^ (2 * d) * r * Real.sin θ)) *
          (Real.sin_sq_add_cos_sq θ)


    have weight_sum_ge_one {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
        1 ≤ ∑ k ∈ Finset.range (2 * d + 1), weight r (theta d) k := by
      have hs := Real.sin_pos_of_pos_of_lt_pi (theta_positive hd) (theta_lt_pi hd)
      have hD := denominator_positive (r := r) hs
      have h := weight_sum_identity hd hr
      have hp2 : r ^ 2 ≤ 1 := pow_le_one₀ hr.le hr'
      have hp2d : r ^ (2 * d) ≤ 1 := pow_le_one₀ hr.le hr'
      have hn : 0 ≤ (1 - r ^ 2) * (1 - r ^ (2 * d)) := mul_nonneg (by linarith) (by linarith)
      rw [pow_add, pow_two] at h
      nlinarith


    have hproj : (∑ k ∈ Finset.range (2 * d + 1), a k * weight r (theta d) k) ≤ 0 := by
      simp only [weight_is_projection, mul_add, Finset.sum_add_distrib]
      simp only [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add, add_zero] at hR hI
      have heq : (∑ k ∈ Finset.range (2 * d + 1),
          a k * ((1 - r * Real.cos (theta d)) / (r * Real.sin (theta d)) * (ray r (theta d) ^ k).im)) =
          ((1 - r * Real.cos (theta d)) / (r * Real.sin (theta d))) *
            (∑ k ∈ Finset.range (2 * d + 1), a k * (ray r (theta d) ^ k).im) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      rw [heq, hI, mul_zero, add_zero]
      exact hR
    calc
      t ≤ t * (∑ k ∈ Finset.range (2 * d + 1), weight r (theta d) k) := by
        simpa using mul_le_mul_of_nonneg_left (weight_sum_ge_one hd hr hr') ht
      _ ≤ t * (∑ k ∈ Finset.range (2 * d + 1), weight r (theta d) k) -
          (∑ k ∈ Finset.range (2 * d + 1), a k * weight r (theta d) k) := by linarith
      _ = ∑ k ∈ Finset.range (2 * d + 1), (t - a k) * weight r (theta d) k := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      _ ≤ ∑ k ∈ Finset.range (2 * d + 1), |a k - t| := by
        apply Finset.sum_le_sum
        intro k hk
        have hw := weight_bounds hd hr hr' (k := k) (by have h := Finset.mem_range.mp hk; omega)
        calc
          (t - a k) * weight r (theta d) k ≤ |(t - a k) * weight r (theta d) k| := le_abs_self _
          _ = |t - a k| * |weight r (theta d) k| := abs_mul _ _
          _ ≤ |t - a k| * 1 := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
          _ = |a k - t| := by rw [mul_one, abs_sub_comm]



  cases n with
  | zero => omega
  | succ m =>
    have hm : 2 ≤ m := by omega
    have hwidth : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    let t : ℝ := 1 / (2 * m + 1 : ℕ)
    have ht : 0 < t := by dsimp [t]; positivity
    have hpowers (r θ : ℝ) (k : ℕ) :
        ray r θ ^ k = (r ^ k : ℝ) *
          ((Real.cos (k * θ) : ℂ) + (Real.sin (k * θ) : ℂ) * Complex.I) := by
      rw [ray, mul_pow, Complex.ofReal_cos, Complex.ofReal_sin,
        Complex.cos_add_sin_mul_I_pow k (θ : ℂ)]
      simp only [Complex.ofReal_pow, Complex.ofReal_cos, Complex.ofReal_sin,
        Complex.ofReal_mul, Complex.ofReal_natCast]
    have hlower (p q : Fin (m + 1) → ℝ) (hp : p ∈ stdSimplex ℝ (Fin (m + 1)))
        (hq : q ∈ stdSimplex ℝ (Fin (m + 1))) :
        t ≤ ∑ k ∈ Finset.range (2 * m + 1), |ordinaryConvolution (m + 1) p q k - t| := by
      let c := ordinaryConvolution (m + 1) p q
      have hnonneg (k : ℕ) : 0 ≤ c k := by
        dsimp [c, ordinaryConvolution]
        apply Finset.sum_nonneg; intro i hi
        apply Finset.sum_nonneg; intro j hj
        split_ifs <;> first | exact mul_nonneg (hp.1 i) (hq.1 j) | exact le_rfl
      by_cases hc : ∀ k < 2 * m + 1, 0 < c k
      · obtain ⟨r, hr, hI, hR⟩ := actual_product_crossing hm p q hp.1 hq.1 hc
        change (∑ k ∈ Finset.range (2 * m + 1), (c k : ℂ) * ray r (theta m) ^ k).im = 0 at hI
        change (∑ k ∈ Finset.range (2 * m + 1), (c k : ℂ) * ray r (theta m) ^ k).re≤0 at hR
        by_cases hr1 : r ≤ 1
        · exact nonpositive_real_coefficient_certificate hm hr hr1 c ht.le hI hR
        · have hr1' : 1 < r := lt_of_not_ge hr1
          have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
          have hrinv1 : r⁻¹ ≤ 1 := (inv_le_one₀ hr).mpr hr1'.le
          let crev : ℕ → ℝ := fun k => c (2 * m - k)
          have hmθ : (m : ℝ) * theta m = Real.pi := by
            unfold theta
            have hm0 : (m : ℝ) ≠ 0 := by positivity
            field_simp
          have h2mθ : ((2 * m : ℕ) : ℝ) * theta m = 2 * Real.pi := by
            push_cast; rw [mul_assoc, hmθ]
          have htransport (k : ℕ) (hk : k < 2 * m + 1) :
              ray r⁻¹ (theta m) ^ (2 * m - k) =
                ((r⁻¹) ^ (2 * m) : ℝ) * star (ray r (theta m) ^ k) := by
            have hkle : k ≤ 2 * m := by omega
            have hang : ((2 * m - k : ℕ) : ℝ) * theta m = 2 * Real.pi - (k : ℝ) * theta m := by
              rw [Nat.cast_sub hkle, sub_mul, h2mθ]
            have hcoss : Real.cos (2 * Real.pi - (k : ℝ) * theta m) =
                Real.cos ((k : ℝ) * theta m) := by rw [Real.cos_sub]; simp
            have hsins : Real.sin (2 * Real.pi - (k : ℝ) * theta m) =
                - Real.sin ((k : ℝ) * theta m) := by rw [Real.sin_sub]; simp
            have hrad : (r⁻¹) ^ (2 * m - k) = (r⁻¹) ^ (2 * m) * r ^ k := by
              simpa only [inv_pow] using inv_pow_sub₀ hr.ne' hkle
            rw [hpowers, hpowers, hang, hcoss, hsins, hrad]
            apply Complex.ext <;>
              simp only [Complex.star_def, Complex.mul_re, Complex.mul_im,
                Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
                Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
                zero_mul, mul_zero, mul_one, add_zero, zero_add, sub_zero] <;> ring
          have hevalrev :
              (∑ k ∈ Finset.range (2 * m + 1), (crev k : ℂ) * ray r⁻¹ (theta m) ^ k) =
              ((r⁻¹) ^ (2 * m) : ℝ) *
                star (∑ k ∈ Finset.range (2 * m + 1), (c k : ℂ) * ray r (theta m) ^ k) := by
            calc
              _ = ∑ k ∈ Finset.range (2 * m + 1),
                (c k : ℂ) * ray r⁻¹ (theta m) ^ (2 * m - k) := by
                  symm
                  convert Finset.sum_range_reflect
                    (fun k => (crev k : ℂ) * ray r⁻¹ (theta m) ^ k) (2 * m + 1) using 1
                  apply Finset.sum_congr rfl; intro k hk
                  have hkle : k ≤ 2 * m := by have := Finset.mem_range.mp hk; omega
                  simp [crev, Nat.sub_sub_self hkle]
              _ = _ := by
                simp only [Complex.star_def, Finset.mul_sum, map_sum, map_mul, Complex.conj_ofReal]
                apply Finset.sum_congr rfl; intro k hk
                rw [htransport k (Finset.mem_range.mp hk), Complex.star_def]
                ring
          have hIrev :
              (∑ k ∈ Finset.range (2 * m + 1), (crev k : ℂ) * ray r⁻¹ (theta m) ^ k).im = 0 := by
            rw [hevalrev]
            simp only [Complex.star_def, Complex.mul_im, Complex.ofReal_re,
              Complex.ofReal_im, Complex.conj_im, hI, neg_zero, mul_zero, zero_mul, add_zero]
          have hRrev :
              (∑ k ∈ Finset.range (2 * m + 1), (crev k : ℂ) * ray r⁻¹ (theta m) ^ k).re ≤ 0 := by
            rw [hevalrev]
            simp only [Complex.star_def, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
              Complex.conj_re, zero_mul, sub_zero]
            exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hrinv.le _) hR
          have hbound := nonpositive_real_coefficient_certificate hm hrinv hrinv1
            crev ht.le hIrev hRrev
          have hperm : (∑ k ∈ Finset.range (2 * m + 1), |crev k - t|) =
              ∑ k ∈ Finset.range (2 * m + 1), |c k - t| := by
            simpa [crev] using Finset.sum_range_reflect (fun k => |c k - t|) (2 * m + 1)
          rwa [hperm] at hbound
      · push Not at hc
        obtain ⟨k, hk, hk0⟩ := hc
        have hcz : c k = 0 := le_antisymm hk0 (hnonneg k)
        have hterm : |c k - t|=t := by rw [hcz, zero_sub, abs_neg, abs_of_pos ht]
        calc
          t = |c k - t| := hterm.symm
          _ ≤ ∑ j ∈ Finset.range (2 * m + 1), |c j - t| :=
            Finset.single_le_sum (fun j hj => abs_nonneg (c j - t)) (Finset.mem_range.mpr hk)
    let z : Fin (m + 1) := ⟨0, by omega⟩
    let e : Fin (m + 1) := ⟨m, by omega⟩
    have hze : z ≠ e := by intro h; have := congrArg Fin.val h; dsimp [z, e] at this; omega
    let p : Fin (m + 1) → ℝ := fun i => (Pi.single z (1 / 2 : ℝ) : Fin (m + 1) → ℝ) i + (Pi.single e (1 / 2 : ℝ) : Fin (m + 1) → ℝ) i
    let q : Fin (m + 1) → ℝ := fun j => if j = z then t else 2 * t
    have hp : p ∈ stdSimplex ℝ (Fin (m + 1)) := by
      constructor
      · intro i; dsimp [p]; simp only [Pi.single_apply]; split_ifs <;> norm_num
      · norm_num [p, Finset.sum_add_distrib]
    have hq : q ∈ stdSimplex ℝ (Fin (m + 1)) := by
      constructor
      · intro j; dsimp [q]; split_ifs <;> positivity
      · have hqform : q = fun j => 2 * t - (Pi.single z t : Fin (m + 1) → ℝ) j := by
          funext j; dsimp [q]; by_cases h : j = z <;> simp [h] <;> ring
        rw [hqform, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        simp only [Finset.sum_pi_single', Finset.mem_univ, if_true]
        dsimp [t]
        push_cast
        field_simp
        ring
    have houtput (k : ℕ) (hk : k < 2 * m + 1) :
        ordinaryConvolution (m + 1) p q k =
          if k = 0 then t / 2 else if k = m then 3 * t / 2 else t := by
      have hexpand : ordinaryConvolution (m + 1) p q k =
          (∑ j : Fin (m + 1), if j.val = k then (1 / 2:ℝ) * q j else 0) +
          (∑ j : Fin (m + 1), if m + j.val = k then (1 / 2:ℝ) * q j else 0) := by
        unfold ordinaryConvolution
        have hsplit (i j : Fin (m + 1)) :
            (if i.val + j.val = k then p i * q j else 0) =
              ((Pi.single z (1 / 2 : ℝ) : Fin (m + 1) → ℝ) i) * (if j.val = k then q j else 0) +
              ((Pi.single e (1 / 2 : ℝ) : Fin (m + 1) → ℝ) i) * (if m + j.val = k then q j else 0) := by
          dsimp [p]; simp only [Pi.single_apply]
          by_cases hi0 : i = z
          · subst i
            simp only [if_pos rfl, if_neg hze, if_neg (Ne.symm hze)]
            simp [z]
          · by_cases him : i = e
            · subst i
              simp only [if_pos rfl, if_neg hi0]
              simp [e]
            · simp [hi0, him]
        simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [← Finset.sum_mul, Finset.sum_pi_single', Finset.mem_univ, if_true]
        simp only [Finset.mul_sum, mul_ite, mul_zero]
      rw [hexpand]
      have hsum (a : ℕ) :
          (∑ j : Fin (m + 1), if j.val = a then (1 / 2:ℝ) * q j else 0) =
            if ha : a < m + 1 then (1 / 2:ℝ) * q ⟨a, ha⟩ else 0 := by
        by_cases ha : a < m + 1
        · rw [dif_pos ha]
          rw [Finset.sum_eq_single (⟨a, ha⟩ : Fin (m + 1))
            (by
              intro b hb hba
              have hne : b.val≠a := by
                intro h
                exact hba (Fin.ext h)
              simp [hne])
            (by simp)]
          simp
        · rw [dif_neg ha]
          apply Finset.sum_eq_zero; intro j hj
          have : j.val≠a := by intro h; rw [← h] at ha; exact ha j.isLt
          simp [this]
      have hshift :
          (∑ j : Fin (m + 1), if m + j.val = k then (1 / 2:ℝ) * q j else 0) =
          if m ≤ k then (∑ j : Fin (m + 1), if j.val = k - m then (1 / 2:ℝ) * q j else 0) else 0 := by
        by_cases hmk : m ≤ k
        · rw [if_pos hmk]
          apply Finset.sum_congr rfl; intro j hj
          have heq : m + j.val = k ↔ j.val = k - m := by omega
          simp [heq]
        · rw [if_neg hmk]
          apply Finset.sum_eq_zero; intro j hj
          have : m + j.val≠k := by omega
          simp [this]
      rw [hshift]
      simp_rw [hsum]
      by_cases hk0 : k = 0
      · subst k; simp [q, z, show ¬m≤0 by omega, ht.ne']; ring
      · by_cases hkm : k = m
        · subst k; simp [q, z, hze, show m≠0 by omega]; ring
        · by_cases hkl : k<m
          · rw [dif_pos (show k<m + 1 by omega), if_neg (show ¬m≤k by omega),
              if_neg hk0, if_neg hkm]
            have hjz : (⟨k, by omega⟩ : Fin (m + 1))≠z := by
              intro h; have := congrArg Fin.val h; exact hk0 this
            simp only [q, if_neg hjz, add_zero]
            ring
          · rw [dif_neg (show ¬k<m + 1 by omega), if_pos (show m≤k by omega),
              dif_pos (show k - m<m + 1 by omega), if_neg hk0, if_neg hkm]
            have hjz : (⟨k - m, by omega⟩ : Fin (m + 1))≠z := by
              intro h; have := congrArg Fin.val h; dsimp [z] at this; omega
            simp only [q, if_neg hjz, zero_add]
            ring
    have hattain : (∑ k ∈ Finset.range (2 * m + 1),
        |ordinaryConvolution (m + 1) p q k - t|) = t := by
      have hterms (k : ℕ) (hk : k ∈ Finset.range (2 * m + 1)) :
          |ordinaryConvolution (m + 1) p q k - t| =
            (if k = 0 then t / 2 else 0) + (if k = m then t / 2 else 0) := by
        rw [houtput k (Finset.mem_range.mp hk)]
        by_cases hk0 : k = 0
        · subst k; simp [show m≠0 by omega, show 0≠m by omega]
          rw [show t / 2 - t = - (t / 2) by ring, abs_neg, abs_of_nonneg (by positivity)]
        · by_cases hkm : k = m
          · subst k; simp [hk0]
            rw [show 3 * t / 2 - t = t / 2 by ring, abs_of_nonneg (by positivity)]
          · simp [hk0, hkm]
      calc
        _ = ∑ k ∈ Finset.range (2 * m + 1),
          ((if k = 0 then t / 2 else 0) + (if k = m then t / 2 else 0)) :=
          Finset.sum_congr rfl hterms
        _ = t := by
          rw [Finset.sum_add_distrib]
          simp [show m<2 * m + 1 by omega]
    constructor
    · refine ⟨p, q, hp, hq, ?_⟩
      simpa only [fullL1, hwidth] using hattain
    · rintro v ⟨p', q', hp', hq', rfl⟩
      simpa only [fullL1, hwidth] using hlower p' q' hp' hq'

#check result
#print axioms result

end D5.S3.TotalVariation.IndependentConvolutionL1Minimum
