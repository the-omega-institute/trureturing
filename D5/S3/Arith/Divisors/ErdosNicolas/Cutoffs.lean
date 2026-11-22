/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Cutoffs
   generality: I
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Cutoffs.first_cutoff_test,D5/S3/Arith/Divisors/ErdosNicolas/Cutoffs.second_cutoff_test
   digest: Exact rational exponent tables and largest-prime kernel comparisons. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Residual

/-! Exact two-level cutoff constants and their analytic propagation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

private theorem linear_test_mono {a₀ a c d X : ℚ}
    (ha₀ : 0 < a₀) (ha : a₀ ≤ a) (hd : 0 ≤ d)
    (hR : 0 < a₀ * c - d) (hsq : a₀ * X < (a₀ * c - d) ^ 2) :
    0 < a * c - d ∧ a * X < (a * c - d) ^ 2 := by
  have ha' : 0 < a := lt_of_lt_of_le ha₀ ha
  have hc : 0 < c := by nlinarith
  have hR' : 0 < a * c - d := by nlinarith
  by_cases hX : 0 ≤ X
  swap
  · exact ⟨hR', lt_of_lt_of_le (mul_neg_of_pos_of_neg ha' (lt_of_not_ge hX))
      (sq_nonneg _)⟩
  have hscale : a * (a₀ * c - d) ≤ a₀ * (a * c - d) := by
    nlinarith [mul_nonneg hd (sub_nonneg.mpr ha)]
  have hscale0 : 0 ≤ a * (a₀ * c - d) := mul_nonneg ha'.le hR.le
  have hs := mul_self_le_mul_self hscale0 hscale
  have ht := mul_lt_mul_of_pos_left hsq (sq_pos_of_pos ha')
  have hu : a₀ ^ 2 * (a * X) ≤ a ^ 2 * (a₀ * X) := by
    have h := mul_nonneg (mul_nonneg (mul_nonneg ha₀.le ha'.le) hX)
      (sub_nonneg.mpr ha)
    nlinarith only [h]
  refine ⟨hR', ?_⟩
  have hv : a₀ ^ 2 * (a * X) < a₀ ^ 2 * (a * c - d) ^ 2 := by
    nlinarith only [hu, ht, hs]
  exact (mul_lt_mul_iff_right₀ (sq_pos_of_pos ha₀)).mp (by nlinarith only [hv])

/-- Exponent propagation uses precisely the nonnegative intercept `b + F - 1`. -/
theorem kernelTest_exponent_mono {a₀ a : ℕ} {p L b F : ℚ}
    (ha₀ : 0 < a₀) (ha : a₀ ≤ a) (hd : 0 ≤ b + F - 1)
    (h : KernelTest a₀ p L b b F) : KernelTest a p L b b F := by
  have he : ∀ k : ℕ,
      criterionGap k p b b F = (k : ℚ) * (1 - b / p) - (b + F - 1) := by
    intro k
    unfold criterionGap
    ring
  rcases h with ⟨hR, hsq⟩
  rw [he] at hR hsq
  have h' := linear_test_mono (a₀ := (a₀ : ℚ)) (a := (a : ℚ))
    (c := 1 - b / p) (d := b + F - 1)
    (X := 4 * ((b + 1 / L) * (b / p + 1 / L)))
    (by exact_mod_cast ha₀) (by exact_mod_cast ha) hd hR
    (by nlinarith only [hsq])
  constructor
  · simpa only [he] using h'.1
  · rw [he]
    nlinarith only [h'.2]

/-- Increasing the positive prime parameter preserves a valid rational comparison. -/
private theorem kernelTest_prime_mono {a : ℕ} {p₀ p L b F : ℚ}
    (hp₀ : 0 < p₀) (hpp : p₀ ≤ p) (hL : 0 < L) (hb : 0 ≤ b)
    (h : KernelTest a p₀ L b b F) : KernelTest a p L b b F := by
  have hp : 0 < p := hp₀.trans_le hpp
  have hdiv : b / p ≤ b / p₀ := div_le_div_of_nonneg_left hb hp₀ hpp
  have hgap : criterionGap a p₀ b b F ≤ criterionGap a p b b F := by
    unfold criterionGap
    have hmul : (a : ℚ) * b / p ≤ (a : ℚ) * b / p₀ := by
      simpa only [mul_div_assoc] using
        mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg a : (0 : ℚ) ≤ a)
    linarith
  have hR : 0 < criterionGap a p b b F := lt_of_lt_of_le h.1 hgap
  constructor
  · exact hR
  · calc
      4 * a * (b + 1 / L) * (b / p + 1 / L) ≤
          4 * a * (b + 1 / L) * (b / p₀ + 1 / L) := by
        have hsum : b / p + 1 / L ≤ b / p₀ + 1 / L := by linarith only [hdiv]
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ < (criterionGap a p₀ b b F) ^ 2 := h.2
      _ ≤ (criterionGap a p b b F) ^ 2 := by
        exact pow_le_pow_left₀ h.1.le hgap 2

/-- First-layer exponent threshold, for the uniform induction bound `8/7`. -/
def firstExponent (p : ℕ) : ℕ :=
  if p = 2 then 28 else if p = 3 then 11 else if p = 5 then 6 else
  if p = 7 then 4 else if p < 29 then 3 else 2

/-- First-layer tent length. -/
def firstLength (p : ℕ) : ℕ :=
  if p = 2 then 8 else if p = 3 then 6 else if p = 5 then 5 else
  if p = 7 then 8 else if p = 11 then 11 else if p = 13 then 8 else
  if p < 29 then 6 else 27

/-- Exact maximum residual in each first-layer row. -/
def firstResidual (p : ℕ) : ℚ :=
  if p = 2 then 389 / 210 else if p = 3 then 19 / 20 else
  if p = 5 then 13 / 20 else if p = 7 then 149 / 192 else
  if p = 11 then 91 / 110 else if p = 13 then 49 / 64 else
  if p < 29 then 25 / 36 else 676 / 729

/-- Second-layer exponent threshold, after excluding exceptional induction inputs. -/
def secondExponent (p : ℕ) : ℕ :=
  if p = 2 then 18 else if p = 3 then 8 else if p = 5 then 5 else
  if p = 7 then 4 else if p < 17 then 3 else 2

/-- Second-layer tent length. -/
def secondLength (p : ℕ) : ℕ :=
  if p = 2 then 7 else if p = 3 then 6 else if p = 5 then 4 else
  if p = 7 then 4 else if p < 17 then 5 else if p = 17 then 18 else 14

/-- Exact maximum residual in each second-layer row. -/
def secondResidual (p : ℕ) : ℚ :=
  if p = 2 then 1264 / 735 else if p = 3 then 19 / 20 else
  if p = 5 then 9 / 16 else if p = 7 then 9 / 16 else
  if p < 17 then 16 / 25 else if p = 17 then 1157 / 1296 else 169 / 196

/-- The complete first-layer base-exponent comparison, including both unbounded rows. -/
theorem first_cutoff_test {p : ℕ} (hp : p.Prime) :
    KernelTest (firstExponent p) p (firstLength p) (8 / 7) (8 / 7)
      (firstResidual p) := by
  by_cases h29p : 29 ≤ p
  · simp only [firstExponent, firstLength, firstResidual, ite_eq_right (by omega : p ≠ 2),
      ite_eq_right (by omega : p ≠ 3), ite_eq_right (by omega : p ≠ 5),
      ite_eq_right (by omega : p ≠ 7), ite_eq_right (by omega : p ≠ 11),
      ite_eq_right (by omega : p ≠ 13), ite_eq_right (by omega : ¬p < 29)]
    exact kernelTest_prime_mono (by norm_num) (by exact_mod_cast h29p)
      (by norm_num) (by norm_num)
      (by norm_num [KernelTest, criterionGap] :
        KernelTest 2 29 27 (8 / 7) (8 / 7) (676 / 729))
  · have hp28 : p ≤ 28 := by omega
    interval_cases p <;> norm_num at hp <;>
      norm_num [firstExponent, firstLength, firstResidual, KernelTest, criterionGap]

/-- The complete second-layer base-exponent comparison. -/
theorem second_cutoff_test {p : ℕ} (hp : p.Prime) :
    KernelTest (secondExponent p) p (secondLength p) 1 1 (secondResidual p) := by
  by_cases h19p : 19 ≤ p
  · simp only [secondExponent, secondLength, secondResidual,
      ite_eq_right (by omega : p ≠ 2), ite_eq_right (by omega : p ≠ 3),
      ite_eq_right (by omega : p ≠ 5), ite_eq_right (by omega : p ≠ 7),
      ite_eq_right (by omega : ¬p < 17), ite_eq_right (by omega : p ≠ 17)]
    exact kernelTest_prime_mono (by norm_num) (by exact_mod_cast h19p)
      (by norm_num) (by norm_num)
      (by norm_num [KernelTest, criterionGap] : KernelTest 2 19 14 1 1 (169 / 196))
  · have hp18 : p ≤ 18 := by omega
    interval_cases p <;> norm_num at hp <;>
      norm_num [secondExponent, secondLength, secondResidual, KernelTest, criterionGap]

/-- Every exponent beyond its first-layer threshold satisfies the same comparison. -/
theorem first_cutoff_exponent {p a : ℕ} (hp : p.Prime)
    (ha : firstExponent p ≤ a) :
    KernelTest a p (firstLength p) (8 / 7) (8 / 7) (firstResidual p) := by
  have ha₀ : 0 < firstExponent p := by
    unfold firstExponent
    split_ifs <;> norm_num
  have hL : (0 : ℚ) < firstLength p := by
    unfold firstLength
    split_ifs <;> norm_num
  have hF : (0 : ℚ) ≤ 8 / 7 + firstResidual p - 1 := by
    unfold firstResidual
    split_ifs <;> norm_num
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp.pos
  exact kernelTest_exponent_mono ha₀ ha hF (first_cutoff_test hp)

/-- Every exponent beyond its second-layer threshold satisfies the comparison. -/
theorem second_cutoff_exponent {p a : ℕ} (hp : p.Prime)
    (ha : secondExponent p ≤ a) :
    KernelTest a p (secondLength p) 1 1 (secondResidual p) := by
  have ha₀ : 0 < secondExponent p := by
    unfold secondExponent
    split_ifs <;> norm_num
  have hL : (0 : ℚ) < secondLength p := by
    unfold secondLength
    split_ifs <;> norm_num
  have hF : (0 : ℚ) ≤ 1 + secondResidual p - 1 := by
    unfold secondResidual
    split_ifs <;> norm_num
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp.pos
  exact kernelTest_exponent_mono ha₀ ha hF (second_cutoff_test hp)

/-- Exact square margin for the ordinary largest-prime cutoff. -/
private theorem cutoff107_margin {p : ℚ} (hp : p ≠ 0) :
    (criterionGap 1 p 1 1 (3 / 4)) ^ 2 -
        4 * (1 + 1 / (2 * p)) * (1 / p + 1 / (2 * p)) =
      (p ^ 2 - 104 * p - 32) / (16 * p ^ 2) := by
  unfold criterionGap
  norm_num
  field_simp [hp]
  <;> ring

/-- Exact square margin for the uniform largest-prime cutoff. -/
private theorem cutoff677_margin {p : ℚ} (hp : p ≠ 0) :
    (criterionGap 1 p (8 / 7) (8 / 7) (3 / 4)) ^ 2 -
        4 * (8 / 7 + 1 / (2 * p)) * (8 / (7 * p) + 1 / (2 * p)) =
      (9 * p ^ 2 - 6080 * p - 1552) / (784 * p ^ 2) := by
  unfold criterionGap
  norm_num
  field_simp [hp]
  <;> ring

/-- Every integer parameter at least 105: the ordinary kernel test for every exponent. -/
theorem largest_prime_test_one {p a : ℕ} (hp : 105 ≤ p) (ha : 1 ≤ a) :
    KernelTest a p (2 * p) 1 1 (3 / 4) := by
  have hpq : (105 : ℚ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℚ) < p := by linarith
  have hpoly : (0 : ℚ) < (p : ℚ) ^ 2 - 104 * p - 32 := by
    nlinarith [sq_nonneg ((p : ℚ) - 105)]
  have hbase : KernelTest 1 (p : ℚ) (2 * p) 1 1 (3 / 4) := by
    constructor
    · unfold criterionGap
      norm_num
      have hdiv : 1 / (p : ℚ) < 1 / 4 := by
        rw [div_lt_div_iff₀ hp0 (by norm_num : (0 : ℚ) < 4)]
        linarith
      simp only [one_div] at hdiv
      linarith
    · have he := cutoff107_margin hp0.ne'
      have hpositive : (0 : ℚ) <
          ((p : ℚ) ^ 2 - 104 * p - 32) / (16 * (p : ℚ) ^ 2) :=
        div_pos hpoly (by positivity)
      linarith
  exact kernelTest_exponent_mono (by norm_num) ha (by norm_num)
    hbase

/-- Every integer parameter at least 676: the uniform kernel test for every exponent. -/
theorem largest_prime_test_eight_sevenths {p a : ℕ}
    (hp : 676 ≤ p) (ha : 1 ≤ a) :
    KernelTest a p (2 * p) (8 / 7) (8 / 7) (3 / 4) := by
  have hpq : (676 : ℚ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℚ) < p := by linarith
  have hpoly : (0 : ℚ) < 9 * (p : ℚ) ^ 2 - 6080 * p - 1552 := by
    nlinarith [sq_nonneg ((p : ℚ) - 676)]
  have hbase : KernelTest 1 (p : ℚ) (2 * p) (8 / 7) (8 / 7) (3 / 4) := by
    constructor
    · unfold criterionGap
      norm_num
      have hdiv : (8 / 7 : ℚ) / p < 3 / 28 := by
        rw [div_lt_iff₀ hp0]
        linarith
      linarith
    · have he := cutoff677_margin hp0.ne'
      have hpositive : (0 : ℚ) <
          (9 * (p : ℚ) ^ 2 - 6080 * p - 1552) / (784 * (p : ℚ) ^ 2) :=
        div_pos hpoly (by positivity)
      have hrewrite : (8 / 7 : ℚ) / p = 8 / (7 * (p : ℚ)) := by ring
      rw [hrewrite]
      linarith
  exact kernelTest_exponent_mono (by norm_num) ha (by norm_num)
    hbase

private theorem w_chord {L g : ℕ} (hL : 1 ≤ L) (hg : 1 ≤ g) :
    w L g ≤ ((L - g : ℕ) : ℚ) * (L - 1 : ℕ) / (L : ℚ) ^ 2 := by
  by_cases hgL : L ≤ g
  · simp [w, Nat.sub_eq_zero_of_le hgL]
  · have hgL' : g ≤ L := by omega
    have hLq : (0 : ℚ) < L := by exact_mod_cast (show 0 < L by omega)
    have hgq : (0 : ℚ) < g := by exact_mod_cast (show 0 < g by omega)
    have h1g : (1 : ℚ) ≤ g := by exact_mod_cast hg
    have hgLq : (g : ℚ) ≤ L := by exact_mod_cast hgL'
    unfold w
    rw [Nat.cast_sub hgL', Nat.cast_sub hL]
    push_cast
    rw [mul_comm ((L : ℚ) ^ 2) (g : ℚ), ← div_div]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hLq)).mpr
    rw [div_le_iff₀ hgq]
    nlinarith [mul_nonneg (sub_nonneg.mpr hgLq) (sub_nonneg.mpr h1g)]

/-- A convex chord bounds both residuals even when both short gaps are present. -/
private theorem w_reflection_endpoint {p L r : ℕ} (hL : 1 ≤ L) (hp : L + 1 ≤ p)
    (hr : 1 ≤ r) (hrp : r < p) :
    w L r + w L (p - r) ≤ w L 1 := by
  have hpr : 1 ≤ p - r := by omega
  have hsum : (L - r) + (L - (p - r)) ≤ L - 1 := by omega
  have hsumq : ((L - r : ℕ) : ℚ) + ((L - (p - r) : ℕ) : ℚ) ≤
      ((L - 1 : ℕ) : ℚ) := by exact_mod_cast hsum
  have hbound := add_le_add (w_chord hL hr) (w_chord hL hpr)
  calc
    w L r + w L (p - r) ≤
        (((L - r : ℕ) : ℚ) + ((L - (p - r) : ℕ) : ℚ)) *
          (L - 1 : ℕ) / (L : ℚ) ^ 2 := by
      convert hbound using 1 <;> ring
    _ ≤ ((L - 1 : ℕ) : ℚ) ^ 2 / (L : ℚ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_right hsumq
        (Nat.cast_nonneg (L - 1) : (0 : ℚ) ≤ (L - 1 : ℕ))]
    _ = w L 1 := by simp [w, sq]

/-- The endpoint is the exact maximum when the tent is shorter than the modulus. -/
private theorem f_max_of_lt {p L : ℕ} (hL : 1 ≤ L) (hp : L + 1 ≤ p) :
    (∀ r : ℕ, 0 < r → r < p → f p L r ≤ w L 1) ∧ f p L 1 = w L 1 := by
  constructor
  · intro r hr hrp
    rw [(f_eq_two_terms hrp.le).2 (Or.inr (by omega))]
    exact w_reflection_endpoint hL hp hr hrp
  · rw [(f_eq_two_terms (by omega)).2 (Or.inr (by omega))]
    rw [w_eq_zero_iff.mpr (Or.inr (by omega : L ≤ p - 1))]
    simp

private theorem first_row_2 :
    (∀ r : ℕ, 0 < r → r < 2 → f 2 8 r ≤ (389 / 210 : ℚ)) ∧
      f 2 8 1 = (389 / 210 : ℚ) := by
  constructor
  · intro r hr hrp
    interval_cases r <;>
      norm_num [f, Int.Icc_eq_finset_map, Finset.sum_map, Finset.sum_range_succ, w]
  · norm_num [f, Int.Icc_eq_finset_map, Finset.sum_map, Finset.sum_range_succ, w]

private theorem first_row_3 :
    (∀ r : ℕ, 0 < r → r < 3 → f 3 6 r ≤ (19 / 20 : ℚ)) ∧
      f 3 6 1 = (19 / 20 : ℚ) := by
  constructor
  · intro r hr hrp
    interval_cases r <;>
      norm_num [f, Int.Icc_eq_finset_map, Finset.sum_map, Finset.sum_range_succ, w]
  · norm_num [f, Int.Icc_eq_finset_map, Finset.sum_map, Finset.sum_range_succ, w]

private theorem first_row_5 :
    (∀ r : ℕ, 0 < r → r < 5 → f 5 5 r ≤ (13 / 20 : ℚ)) ∧
      f 5 5 1 = (13 / 20 : ℚ) := by
  constructor
  · intro r hr hrp
    rw [(f_eq_two_terms hrp.le).2 (Or.inr (by omega))]
    interval_cases r <;> norm_num [w]
  · rw [(f_eq_two_terms (by norm_num)).2 (Or.inr (by omega))]
    norm_num [w]

private theorem first_row_7 :
    (∀ r : ℕ, 0 < r → r < 7 → f 7 8 r ≤ (149 / 192 : ℚ)) ∧
      f 7 8 1 = (149 / 192 : ℚ) := by
  constructor
  · intro r hr hrp
    interval_cases r <;>
      norm_num [f, Int.Icc_eq_finset_map, Finset.sum_map, Finset.sum_range_succ, w]
  · norm_num [f, Int.Icc_eq_finset_map, Finset.sum_map, Finset.sum_range_succ, w]

private theorem first_row_11 :
    (∀ r : ℕ, 0 < r → r < 11 → f 11 11 r ≤ (91 / 110 : ℚ)) ∧
      f 11 11 1 = (91 / 110 : ℚ) := by
  constructor
  · intro r hr hrp
    rw [(f_eq_two_terms hrp.le).2 (Or.inr (by omega))]
    interval_cases r <;> norm_num [w]
  · rw [(f_eq_two_terms (by norm_num)).2 (Or.inr (by omega))]
    norm_num [w]

private theorem first_row_13 :
    (∀ r : ℕ, 0 < r → r < 13 → f 13 8 r ≤ (49 / 64 : ℚ)) ∧
      f 13 8 1 = (49 / 64 : ℚ) := by
  constructor
  · intro r hr hrp
    rw [(f_eq_two_terms hrp.le).2 (Or.inr (by omega))]
    interval_cases r <;> norm_num [w]
  · rw [(f_eq_two_terms (by norm_num)).2 (Or.inr (by omega))]
    norm_num [w]

/-- Exact first-layer maxima, including the uniform endpoint row for every `p ≥ 29`. -/
theorem first_residual_max {p : ℕ} (hp : p.Prime) :
    (∀ r : ℕ, 0 < r → r < p → f p (firstLength p) r ≤ firstResidual p) ∧
      f p (firstLength p) 1 = firstResidual p := by
  by_cases h29p : 29 ≤ p
  · have hlen : firstLength p = 27 := by
      simp [firstLength, show p ≠ 2 by omega, show p ≠ 3 by omega,
        show p ≠ 5 by omega, show p ≠ 7 by omega, show p ≠ 11 by omega,
        show p ≠ 13 by omega, show ¬p < 29 by omega]
    have hres : firstResidual p = 676 / 729 := by
      simp [firstResidual, show p ≠ 2 by omega, show p ≠ 3 by omega,
        show p ≠ 5 by omega, show p ≠ 7 by omega, show p ≠ 11 by omega,
        show p ≠ 13 by omega, show ¬p < 29 by omega]
    rw [hlen, hres]
    have he : w 27 1 = (676 / 729 : ℚ) := by norm_num [w]
    simpa only [he] using f_max_of_lt (p := p) (L := 27) (by norm_num) (by omega)
  · by_cases h17p : 17 ≤ p
    · have hlen : firstLength p = 6 := by
        simp [firstLength, show p ≠ 2 by omega, show p ≠ 3 by omega,
          show p ≠ 5 by omega, show p ≠ 7 by omega, show p ≠ 11 by omega,
          show p ≠ 13 by omega, show p < 29 by omega]
      have hres : firstResidual p = 25 / 36 := by
        simp [firstResidual, show p ≠ 2 by omega, show p ≠ 3 by omega,
          show p ≠ 5 by omega, show p ≠ 7 by omega, show p ≠ 11 by omega,
          show p ≠ 13 by omega, show p < 29 by omega]
      rw [hlen, hres]
      have he : w 6 1 = (25 / 36 : ℚ) := by norm_num [w]
      simpa only [he] using f_max_of_lt (p := p) (L := 6) (by norm_num) (by omega)
    · have hp16 : p ≤ 16 := by omega
      interval_cases p <;> norm_num at hp
      all_goals first
        | simpa [firstLength, firstResidual] using first_row_2
        | simpa [firstLength, firstResidual] using first_row_3
        | simpa [firstLength, firstResidual] using first_row_5
        | simpa [firstLength, firstResidual] using first_row_7
        | simpa [firstLength, firstResidual] using first_row_11
        | simpa [firstLength, firstResidual] using first_row_13

/-- Exact second-layer maxima, including the uniform endpoint row for every `p ≥ 19`. -/
theorem second_residual_max {p : ℕ} (hp : p.Prime) :
    (∀ r : ℕ, 0 < r → r < p → f p (secondLength p) r ≤ secondResidual p) ∧
      f p (secondLength p) 1 = secondResidual p := by
  by_cases h19p : 19 ≤ p
  · have hlen : secondLength p = 14 := by
      simp [secondLength, show p ≠ 2 by omega, show p ≠ 3 by omega,
        show p ≠ 5 by omega, show p ≠ 7 by omega, show ¬p < 17 by omega,
        show p ≠ 17 by omega]
    have hres : secondResidual p = 169 / 196 := by
      simp [secondResidual, show p ≠ 2 by omega, show p ≠ 3 by omega,
        show p ≠ 5 by omega, show p ≠ 7 by omega, show ¬p < 17 by omega,
        show p ≠ 17 by omega]
    rw [hlen, hres]
    have he : w 14 1 = (169 / 196 : ℚ) := by norm_num [w]
    simpa only [he] using f_max_of_lt (p := p) (L := 14) (by norm_num) (by omega)
  · have hp18 : p ≤ 18 := by omega
    interval_cases p <;> norm_num at hp
    all_goals
      constructor
      · intro r hr hrp
        interval_cases r <;>
          norm_num [secondLength, secondResidual, f, Int.Icc_eq_finset_map,
            Finset.sum_map, Finset.sum_range_succ, w]
      · norm_num [secondLength, secondResidual, f, Int.Icc_eq_finset_map,
          Finset.sum_map, Finset.sum_range_succ, w]

theorem divisor_residue_average_le {p L m : ℕ} {F : ℚ}
    (hp : 0 < p) (hm : 0 < m) (hpm : ¬p ∣ m)
    (hF : ∀ r : ℕ, 0 < r → r < p → f p L r ≤ F) :
    (∑ d ∈ m.divisors, f p L (d % p)) / (m.divisors.card : ℚ) ≤ F := by
  have ht : (0 : ℚ) < m.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm.ne'⟩
  apply (div_le_iff₀ ht).mpr
  calc
    (∑ d ∈ m.divisors, f p L (d % p)) ≤ ∑ _d ∈ m.divisors, F := by
      apply Finset.sum_le_sum
      intro d hd
      apply hF (d % p) _ (Nat.mod_lt _ hp)
      apply Nat.pos_of_ne_zero
      intro hz
      exact hpm ((Nat.dvd_of_mod_eq_zero hz).trans (Nat.dvd_of_mem_divisors hd))
    _ = F * m.divisors.card := by simp [mul_comm]

#print axioms divisor_residue_average_le
#print axioms f_max_of_lt
#print axioms first_residual_max
#print axioms second_residual_max
#print axioms w_reflection_endpoint
#print axioms first_cutoff_exponent
#print axioms second_cutoff_exponent
#print axioms cutoff107_margin
#print axioms cutoff677_margin
#print axioms largest_prime_test_one
#print axioms largest_prime_test_eight_sevenths
#print axioms kernelTest_prime_mono
#print axioms first_cutoff_test
#print axioms second_cutoff_test

#print axioms kernelTest_exponent_mono

end D5.S3.Arith.ErdosNicolas
