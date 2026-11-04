/- GID: D5/S3/Arith/FactorialRatio/BalaA295431Divisibility
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/BalaA295431Divisibility
   mirror-E: none(waiver:unbounded-prime-valuation-proof)
   anchors: []
   utility: none
   digest: Fixed and uniform divisibilities of the actual A295431 factorial ratio. -/

import D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral
import Mathlib.Data.Int.NatAbs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-!
The source is Ma and Zhang, revision 3 (4 November 2026), Corollary 5
and its proof, CC BY 4.0. The posing questions are Bala's A295431
Comments (28 August 2025). Integrality is prior work of Bober and is
reused from the original repository producer, not claimed anew.
The constants below are sufficient, with no minimality or priority claim.
-/

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Arith.FactorialRatio.BalaA295431Divisibility

open OeisA347854BalaHalfIndexIntegral

/-- The actual factorial ratio, in the rationals. -/
def ratio (n : ℕ) : ℚ :=
  ((12 * n).factorial : ℚ) * n.factorial /
    ((6 * n).factorial * (4 * n).factorial * (3 * n).factorial)

/-- Consecutive positive factors, including the empty product at `R = 0`. -/
def rising_denominator (k n R : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 R, (k * n + i)

/-- Signed factors. Coprimality to twelve excludes zero, even for large `R`. -/
def signed_denominator (n R : ℕ) : ℤ :=
  ∏ i ∈ (Finset.Icc 1 R).filter (fun i => i.Coprime 12), (12 * (n : ℤ) - i)

/-- One sufficient constant for every one of the three positive progressions. -/
def first_constant (R : ℕ) : ℕ := 36 * (R - 1).factorial * Nat.lcmUpto (12 * R)

/-- The sufficient constant for the progression restricted to units modulo twelve. -/
def second_constant (R : ℕ) : ℕ := (R - 1).factorial * Nat.lcmUpto R

/-- All five fixed expressions and both families on the actual rational ratio.
The final equality records the negative value at zero without natural subtraction. -/
def claim : Prop :=
  (∀ n : ℕ,
    (∃ z : ℤ, (z : ℚ) = 385 * ratio n / (n + 1)) ∧
    (∃ z : ℤ, (z : ℚ) = 5 * ratio n / (2 * n + 1)) ∧
    (∃ z : ℤ, (z : ℚ) = ratio n / (3 * n + 1)) ∧
    (∃ z : ℤ, (z : ℚ) = 770 * ratio n / ((n + 1) * (2 * n + 1) * (3 * n + 1))) ∧
    (∃ z : ℤ, (z : ℚ) = ratio n / (12 * (n : ℚ) - 1)) ∧
    (∀ R : ℕ, 1 ≤ R → ∀ k : ℕ, 1 ≤ k ∧ k ≤ 3 →
      rising_denominator k n R ≠ 0 ∧
      ∃ z : ℤ, (z : ℚ) = (first_constant R : ℚ) * ratio n / rising_denominator k n R) ∧
    (∀ R : ℕ, 1 ≤ R → signed_denominator n R ≠ 0 ∧
      ∃ z : ℤ, (z : ℚ) = (second_constant R : ℚ) * ratio n / signed_denominator n R)) ∧
    ratio 0 / (12 * (0 : ℚ) - 1) = -1

private def numerator (n : ℕ) := (12 * n).factorial * n.factorial
private def denominator (n : ℕ) := (6 * n).factorial * (4 * n).factorial * (3 * n).factorial
private def value (n : ℕ) := numerator n / denominator n

private lemma denominator_dvd (n : ℕ) : denominator n ∣ numerator n := by
  simpa [numerator, denominator] using even_dvd n

private lemma numerator_ne_zero (n : ℕ) : numerator n ≠ 0 := by
  simp [numerator, Nat.factorial_ne_zero]

private lemma denominator_ne_zero (n : ℕ) : denominator n ≠ 0 := by
  simp [denominator, Nat.factorial_ne_zero]

private lemma value_ne_zero (n : ℕ) : value n ≠ 0 := by
  intro h
  have he := Nat.div_mul_cancel (denominator_dvd n)
  change value n * denominator n = numerator n at he
  rw [h, zero_mul] at he
  exact numerator_ne_zero n he.symm

private lemma ratio_eq_value (n : ℕ) : ratio n = (value n : ℚ) := by
  have he := congrArg (fun a : ℕ => (a : ℚ)) (Nat.div_mul_cancel (denominator_dvd n))
  push_cast at he
  apply (div_eq_iff (by exact_mod_cast denominator_ne_zero n)).mpr
  simpa [ratio, numerator, denominator, value] using he.symm

private def valuation (p n : ℕ) : ℤ :=
  (padicValNat p (12 * n).factorial : ℤ) + padicValNat p n.factorial -
    (padicValNat p (6 * n).factorial + padicValNat p (4 * n).factorial +
      padicValNat p (3 * n).factorial)

private lemma valuation_eq (p n : ℕ) [Fact p.Prime] :
    valuation p n = (padicValNat p (value n) : ℤ) := by
  have he := congrArg (padicValNat p) (Nat.div_mul_cancel (denominator_dvd n))
  change padicValNat p (value n * denominator n) = padicValNat p (numerator n) at he
  rw [padicValNat.mul (value_ne_zero n) (denominator_ne_zero n)] at he
  simp only [numerator, denominator,
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    padicValNat.mul (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _)] at he
  dsimp [valuation]
  omega

private lemma valuation_nonneg (p n : ℕ) [Fact p.Prime] : 0 ≤ valuation p n := by
  rw [valuation_eq]
  positivity

private lemma valuation_sum (p n b : ℕ) [hp : Fact p.Prime] (hb : 12 * n < b) :
    valuation p n = ∑ j ∈ Finset.Ico 1 b, h854 n (p ^ j) := by
  have vf (m : ℕ) (hm : m ≤ 12 * n) :
      padicValNat p m.factorial = ∑ j ∈ Finset.Ico 1 b, m / p ^ j :=
    padicValNat_factorial (lt_of_le_of_lt (p.log_le_self m) (lt_of_le_of_lt hm hb))
  simp only [valuation, vf (12 * n) (by omega), vf n (by omega),
    vf (6 * n) (by omega), vf (4 * n) (by omega), vf (3 * n) (by omega),
    Nat.cast_sum, h854, one_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]

private lemma defect_reduce (n q : ℕ) (hq : 0 < q) : h854 n q = h854 (n % q) q := by
  unfold h854
  rw [mul_div_reduce 12 n q hq, mul_div_reduce 6 n q hq,
    mul_div_reduce 4 n q hq, mul_div_reduce 3 n q hq, mul_div_reduce 1 n q hq]
  push_cast
  ring

private lemma defect_grid (r q : ℕ) (hq : 0 < q) (hr : r < q) :
    h854 r q = (12 * r / q : ℕ) -
      (((12 * r / q) / 2 : ℕ) + ((12 * r / q) / 3 : ℕ) + ((12 * r / q) / 4 : ℕ) : ℤ) := by
  unfold h854
  rw [grid_floor 12 6 2 r q hq (by decide) (by decide),
    grid_floor 12 4 3 r q hq (by decide) (by decide),
    grid_floor 12 3 4 r q hq (by decide) (by decide)]
  simp [Nat.div_eq_of_lt hr]

private lemma left_floor (n q k i : ℕ) (hq : 0 < q) (hi : 0 < i)
    (hsize : 12 * i ≤ q) (hk : 1 ≤ k ∧ k ≤ 3) (hd : q ∣ k * n + i) :
    h854 n q = 1 := by
  let r := n % q
  have hr : r < q := Nat.mod_lt n hq
  have hd' : q ∣ k * r + i := by
    apply Nat.dvd_of_mod_eq_zero
    simpa [r, Nat.add_mod, Nat.mul_mod] using Nat.mod_eq_zero_of_dvd hd
  obtain ⟨t, ht⟩ := hd'
  have ht0 : 1 ≤ t := by nlinarith
  have htk : t ≤ k := by
    by_contra hn
    have hkr : k * r < k * q := Nat.mul_lt_mul_of_pos_left hr (by omega)
    have hqt : q * (k + 1) ≤ q * t := Nat.mul_le_mul_left q (by omega)
    nlinarith
  rw [defect_reduce n q hq, defect_grid r q hq hr]
  suffices hh : 12 * r / q = 3 ∨ 12 * r / q = 5 ∨ 12 * r / q = 7 ∨ 12 * r / q = 11 by
    rcases hh with hh | hh | hh | hh <;> norm_num [hh]
  rcases hk with ⟨hk1, hk3⟩
  interval_cases k <;> interval_cases t <;> norm_num at ht htk
  all_goals first
    | exact Or.inl ((Nat.div_eq_iff hq).mpr (by omega))
    | exact Or.inr (Or.inl ((Nat.div_eq_iff hq).mpr (by omega)))
    | exact Or.inr (Or.inr (Or.inl ((Nat.div_eq_iff hq).mpr (by omega))))
    | exact Or.inr (Or.inr (Or.inr ((Nat.div_eq_iff hq).mpr (by omega))))

private lemma fixed_floor (n q k : ℕ) (hq : 5 ≤ q)
    (h2 : ¬2 ∣ q) (h3 : ¬3 ∣ q) (hk : 1 ≤ k ∧ k ≤ 3)
    (hd : q ∣ k * n + 1)
    (hex : ¬(k = 1 ∧ (q = 5 ∨ q = 7 ∨ q = 11)) ∧ ¬(k = 2 ∧ q = 5)) :
    h854 n q = 1 := by
  by_cases hbig : 12 ≤ q
  · exact left_floor n q k 1 (by omega) (by omega) (by omega) hk hd
  have hqcases : q = 5 ∨ q = 7 ∨ q = 11 := by omega
  rw [defect_reduce n q (by omega)]
  have hr := Nat.mod_lt n (by omega : 0 < q)
  have hd' : (k * (n % q) + 1) % q = 0 := by
    simpa [Nat.add_mod, Nat.mul_mod] using Nat.mod_eq_zero_of_dvd hd
  rcases hk with ⟨hk1, hk3⟩
  rcases hqcases with rfl | rfl | rfl <;> interval_cases k <;>
    norm_num [h854] at * <;> omega

private lemma valuation_of_levels (p n E e : ℕ) [hp : Fact p.Prime]
    (h : ∀ j : ℕ, E < j → j ≤ e → h854 n (p ^ j) = 1) :
    (e : ℤ) ≤ valuation p n + E := by
  classical
  let b := 12 * n + e + E + 2
  have hs : Finset.Ico (E + 1) (e + 1) ⊆ Finset.Ico 1 b := by
    intro j hj
    simp only [Finset.mem_Ico] at hj ⊢
    dsimp [b]
    omega
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun j _ _ => h854_nonneg n (p ^ j) (pow_pos hp.out.pos j))
  have heq : (∑ j ∈ Finset.Ico (E + 1) (e + 1), h854 n (p ^ j)) = (e - E : ℕ) := by
    calc
      _ = ∑ _j ∈ Finset.Ico (E + 1) (e + 1), (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact h j (by simpa using (Finset.mem_Ico.mp hj).1) (by simpa using (Finset.mem_Ico.mp hj).2)
      _ = _ := by simp
  rw [heq, ← valuation_sum p n b (by dsimp [b]; omega)] at hsum
  have hn := valuation_nonneg p n
  omega

private lemma right_floor (n q i : ℕ) (hq : 0 < q) (hi : i < q)
    (hcop : i.Coprime 12) (hd : (q : ℤ) ∣ 12 * (n : ℤ) - i) : h854 n q = 1 := by
  let r := n % q
  have hr : r < q := Nat.mod_lt n hq
  have hn : (n : ℤ) = (q : ℤ) * (n / q : ℕ) + (r : ℤ) := by
    exact_mod_cast (Nat.div_add_mod n q).symm
  have hd' : (q : ℤ) ∣ 12 * (r : ℤ) - i := by
    have heq : 12 * (r : ℤ) - (i : ℤ) =
        (12 * (n : ℤ) - i) - (q : ℤ) * (12 * (n / q : ℕ)) := by rw [hn]; ring
    rw [heq]
    exact dvd_sub hd (dvd_mul_right _ _)
  obtain ⟨t, ht⟩ := hd'
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hrz : (r : ℤ) < q := by exact_mod_cast hr
  have hiz : (i : ℤ) < q := by exact_mod_cast hi
  have ht0 : 0 ≤ t := by nlinarith
  have ht12 : t < 12 := by nlinarith
  have hi2 : ¬2 ∣ i := by
    intro hh
    have hh' := Nat.dvd_gcd hh (by decide : 2 ∣ 12)
    rw [hcop] at hh'
    norm_num at hh'
  have hi3 : ¬3 ∣ i := by
    intro hh
    have hh' := Nat.dvd_gcd hh (by decide : 3 ∣ 12)
    rw [hcop] at hh'
    norm_num at hh'
  have ht2 : t % 2 ≠ 0 := by
    intro hh
    have he := congrArg (fun a : ℤ => a % 2) ht
    simp [Int.sub_emod, Int.mul_emod, hh] at he
    have hni : i % 2 = 0 := by omega
    exact hi2 (Nat.dvd_of_mod_eq_zero hni)
  have ht3 : t % 3 ≠ 0 := by
    intro hh
    have he := congrArg (fun a : ℤ => a % 3) ht
    simp [Int.sub_emod, Int.mul_emod, hh] at he
    have hni : i % 3 = 0 := by omega
    exact hi3 (Nat.dvd_of_mod_eq_zero hni)
  have htc : t = 1 ∨ t = 5 ∨ t = 7 ∨ t = 11 := by omega
  rw [defect_reduce n q hq, defect_grid r q hq hr]
  rcases htc with rfl | rfl | rfl | rfl
  all_goals
    have hj : 12 * r / q = 1 ∨ 12 * r / q = 5 ∨ 12 * r / q = 7 ∨ 12 * r / q = 11 := by
      first
      | exact Or.inl ((Nat.div_eq_iff hq).mpr (by omega))
      | exact Or.inr (Or.inl ((Nat.div_eq_iff hq).mpr (by omega)))
      | exact Or.inr (Or.inr (Or.inl ((Nat.div_eq_iff hq).mpr (by omega))))
      | exact Or.inr (Or.inr (Or.inr ((Nat.div_eq_iff hq).mpr (by omega))))
    rcases hj with hj | hj | hj | hj <;> norm_num [hj]

private lemma first_factor_lower (p n R k i : ℕ) [hp : Fact p.Prime]
    (hk : 1 ≤ k ∧ k ≤ 3) (hi : i ∈ Finset.Icc 1 R) :
    (padicValNat p (k * n + i) : ℤ) ≤ valuation p n + p.log (12 * R) := by
  have hi' := Finset.mem_Icc.mp hi
  apply valuation_of_levels
  intro j hj hje
  have hq : 12 * R < p ^ j := Nat.lt_pow_of_log_lt hp.out.one_lt hj
  apply left_floor n (p ^ j) k i (pow_pos hp.out.pos j) hi'.1 (by nlinarith) hk
  exact (padicValNat_dvd_iff_le (by omega : k * n + i ≠ 0)).mpr hje

private lemma signed_factor_ne_zero (n i : ℕ) (hi : i.Coprime 12) :
    12 * (n : ℤ) - i ≠ 0 := by
  intro hz
  have hi12 : 12 ∣ i := by
    refine ⟨n, ?_⟩
    exact_mod_cast (show (i : ℤ) = 12 * n by omega)
  have hh := Nat.dvd_gcd hi12 (dvd_refl 12)
  rw [hi] at hh
  norm_num at hh

private lemma second_factor_lower (p n R i : ℕ) [hp : Fact p.Prime]
    (hi : i ∈ Finset.Icc 1 R) (hcop : i.Coprime 12) :
    (padicValNat p (12 * (n : ℤ) - i).natAbs : ℤ) ≤ valuation p n + p.log R := by
  apply valuation_of_levels
  intro j hj hje
  have hq : R < p ^ j := Nat.lt_pow_of_log_lt hp.out.one_lt hj
  apply right_floor n (p ^ j) i (pow_pos hp.out.pos j)
    (lt_of_le_of_lt (Finset.mem_Icc.mp hi).2 hq) hcop
  apply Int.natCast_dvd.mpr
  exact (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr (signed_factor_ne_zero n i hcop))).mpr hje

private lemma valuation_mono (p a b : ℕ) [Fact p.Prime] (hb : b ≠ 0)
    (h : a ∣ b) : padicValNat p a ≤ padicValNat p b := by
  exact (padicValNat_dvd_iff_le hb).mp (pow_padicValNat_dvd.trans h)

private lemma valuation_product (p : ℕ) [hp : Fact p.Prime] (s : Finset ℕ)
    (f : ℕ → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  have he : (padicValNat p (∏ i ∈ s, f i) : ℕ∞) =
      ((∑ i ∈ s, padicValNat p (f i) : ℕ) : ℕ∞) := by
    rw [padicValNat_eq_emultiplicity (Finset.prod_ne_zero_iff.mpr hf), Nat.cast_sum]
    exact (Finset.emultiplicity_prod (Nat.prime_iff.mp hp.out) s f).trans
      (Finset.sum_congr rfl (fun i hi => (padicValNat_eq_emultiplicity (hf i hi)).symm))
  exact_mod_cast he

private lemma distance_product (R a : ℕ) (ha : a ∈ Finset.Icc 1 R) :
    (∏ i ∈ (Finset.Icc 1 R).erase a, ((i : ℤ) - a).natAbs) =
      (a - 1).factorial * (R - a).factorial := by
  classical
  have ha' := Finset.mem_Icc.mp ha
  have hs : (Finset.Icc 1 R).erase a = Finset.Ico 1 a ∪ Finset.Ico (a + 1) (R + 1) := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdis : Disjoint (Finset.Ico 1 a) (Finset.Ico (a + 1) (R + 1)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [Finset.mem_Ico] at hi hj
    omega
  rw [hs, Finset.prod_union hdis]
  have hl : (∏ i ∈ Finset.Ico 1 a, ((i : ℤ) - a).natAbs) = (a - 1).factorial := by
    calc
      _ = ∏ i ∈ Finset.Ico 1 a, (a - i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi' := Finset.mem_Ico.mp hi
        have he : (i : ℤ) - a = -((a - i : ℕ) : ℤ) := by omega
        simp [he]
      _ = ∏ i ∈ Finset.Ico 1 a, i := by
        simpa using Finset.prod_Ico_reflect (fun i : ℕ => i) 1 (m := a) (n := a) (by omega)
      _ = _ := by simpa [show a - 1 + 1 = a by omega] using Finset.prod_Ico_id_eq_factorial (a - 1)
  have hr : (∏ i ∈ Finset.Ico (a + 1) (R + 1), ((i : ℤ) - a).natAbs) = (R - a).factorial := by
    calc
      _ = ∏ i ∈ Finset.Ico (a + 1) (R + 1), (i - a) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi' := Finset.mem_Ico.mp hi
        have he : (i : ℤ) - a = ((i - a : ℕ) : ℤ) := by omega
        simp [he]
      _ = ∏ i ∈ Finset.range (R - a), (i + 1) := by
        rw [Finset.prod_Ico_eq_prod_range]
        apply Finset.prod_congr (by congr 1; omega)
        intro i hi
        congr 1
        omega
      _ = _ := Finset.prod_range_add_one_eq_factorial _
  rw [hl, hr]

/-- Removing a factor of largest valuation leaves only valuations of index differences. -/
private lemma progression_product_bound (p R : ℕ) [hp : Fact p.Prime]
    (s : Finset ℕ) (hs : s ⊆ Finset.Icc 1 R) (f : ℕ → ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0)
    (hdiff : ∀ i ∈ s, ∀ j ∈ s, (f i - f j).natAbs = ((i : ℤ) - j).natAbs)
    (B : ℤ) (hB : 0 ≤ B)
    (hbound : ∀ i ∈ s, (padicValNat p (f i).natAbs : ℤ) ≤ B) :
    (padicValNat p (∏ i ∈ s, (f i).natAbs) : ℤ) ≤
      B + padicValNat p (R - 1).factorial := by
  classical
  rw [valuation_product p s (fun i => (f i).natAbs)
    (fun i hi => Int.natAbs_ne_zero.mpr (hf i hi))]
  by_cases hempty : s = ∅
  · simp [hempty]
    positivity
  obtain ⟨a, ha, hmax⟩ := s.exists_max_image (fun i => padicValNat p (f i).natAbs)
    (Finset.nonempty_iff_ne_empty.mpr hempty)
  have had := hs ha
  have hpair (i : ℕ) (hi : i ∈ s.erase a) :
      padicValNat p (f i).natAbs ≤ padicValNat p ((i : ℤ) - a).natAbs := by
    have hi' := Finset.mem_erase.mp hi
    have he : (i : ℤ) - a ≠ 0 := by omega
    have hpi : (p ^ padicValNat p (f i).natAbs : ℕ) ∣ (f i).natAbs := pow_padicValNat_dvd
    have hpa : (p ^ padicValNat p (f i).natAbs : ℕ) ∣ (f a).natAbs :=
      (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr (hf a ha))).mpr (hmax i hi'.2)
    have hh := dvd_sub (Int.natCast_dvd.mpr hpi) (Int.natCast_dvd.mpr hpa)
    have hh' := Int.natCast_dvd.mp hh
    rw [hdiff i hi'.2 a ha] at hh'
    exact (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr he)).mp hh'
  have hsub : s.erase a ⊆ (Finset.Icc 1 R).erase a := by
    intro i hi
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hi).1, hs (Finset.mem_erase.mp hi).2⟩
  have hsum : (∑ i ∈ s.erase a, padicValNat p (f i).natAbs) ≤
      ∑ i ∈ (Finset.Icc 1 R).erase a, padicValNat p ((i : ℤ) - a).natAbs :=
    (Finset.sum_le_sum (fun i hi => hpair i hi)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))
  have hdist : ∀ i ∈ (Finset.Icc 1 R).erase a, ((i : ℤ) - a).natAbs ≠ 0 := by
    intro i hi
    apply Int.natAbs_ne_zero.mpr
    have hia := (Finset.mem_erase.mp hi).1
    omega
  rw [← valuation_product p _ _ hdist, distance_product R a had,
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)] at hsum
  have hfact := Nat.factorial_mul_factorial_dvd_factorial_add (a - 1) (R - a)
  rw [show a - 1 + (R - a) = R - 1 by have := Finset.mem_Icc.mp had; omega] at hfact
  have hmono := valuation_mono p _ _ (Nat.factorial_ne_zero _) hfact
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)] at hmono
  have hba := hbound a ha
  have heq := Finset.sum_erase_add s (fun i => padicValNat p (f i).natAbs) ha
  omega

private lemma lcm_valuation (p m : ℕ) [hp : Fact p.Prime] :
    padicValNat p (Nat.lcmUpto m) = p.log m := by
  rw [← Nat.factorization_def _ hp.out, Nat.factorization_lcmUpto m hp.out]

private lemma dvd_of_valuations (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : ℕ, p.Prime → padicValNat p a ≤ padicValNat p b) : a ∣ b := by
  apply (Nat.factorization_prime_le_iff_dvd ha hb).mp
  intro p hp
  simpa only [Nat.factorization_def _ hp] using h p hp

private lemma rising_ne_zero (k n R : ℕ) : rising_denominator k n R ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have := (Finset.mem_Icc.mp hi).1
  omega

private lemma signed_ne_zero (n R : ℕ) : signed_denominator n R ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact signed_factor_ne_zero n i (Finset.mem_filter.mp hi).2

private lemma first_dvd (n R k : ℕ) (hk : 1 ≤ k ∧ k ≤ 3) :
    rising_denominator k n R ∣ first_constant R * value n := by
  have hc : first_constant R ≠ 0 := by
    simp [first_constant, Nat.factorial_ne_zero, Nat.lcmUpto_ne_zero]
  apply dvd_of_valuations _ _ (rising_ne_zero k n R) (mul_ne_zero hc (value_ne_zero n))
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  have hh := progression_product_bound p R (Finset.Icc 1 R) (by rfl)
    (fun i => ((k * n + i : ℕ) : ℤ))
    (by intro i hi; have := (Finset.mem_Icc.mp hi).1; positivity)
    (by intro i hi j hj; congr 1; push_cast; ring)
    (valuation p n + p.log (12 * R)) (by have := valuation_nonneg p n; positivity)
    (by intro i hi; simpa only [Int.natAbs_natCast] using first_factor_lower p n R k i hk hi)
  simp only [Int.natAbs_natCast] at hh
  rw [valuation_eq] at hh
  rw [padicValNat.mul hc (value_ne_zero n)]
  have hcv : padicValNat p (first_constant R) =
      padicValNat p 36 + padicValNat p (R - 1).factorial + p.log (12 * R) := by
    simp only [first_constant,
      padicValNat.mul (mul_ne_zero (by norm_num : (36 : ℕ) ≠ 0) (Nat.factorial_ne_zero _)) (Nat.lcmUpto_ne_zero _),
      padicValNat.mul (by norm_num : 36 ≠ 0) (Nat.factorial_ne_zero _), lcm_valuation]
  rw [hcv]
  change (padicValNat p (rising_denominator k n R) : ℤ) ≤ _ at hh
  omega

private lemma second_dvd (n R : ℕ) :
    signed_denominator n R ∣ ((second_constant R * value n : ℕ) : ℤ) := by
  have hc : second_constant R ≠ 0 := by
    simp [second_constant, Nat.factorial_ne_zero, Nat.lcmUpto_ne_zero]
  apply Int.dvd_natCast.mpr
  apply dvd_of_valuations _ _ (Int.natAbs_ne_zero.mpr (signed_ne_zero n R))
    (mul_ne_zero hc (value_ne_zero n))
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  have hh := progression_product_bound p R
    ((Finset.Icc 1 R).filter (fun i => i.Coprime 12)) (Finset.filter_subset _ _)
    (fun i => 12 * (n : ℤ) - i)
    (by intro i hi; exact signed_factor_ne_zero n i (Finset.mem_filter.mp hi).2)
    (by intro i hi j hj; rw [show 12 * (n : ℤ) - i - (12 * n - j) = -((i : ℤ) - j) by ring, Int.natAbs_neg])
    (valuation p n + p.log R) (by have := valuation_nonneg p n; positivity)
    (by intro i hi; exact second_factor_lower p n R i
          (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2)
  have habs : (signed_denominator n R).natAbs =
      ∏ i ∈ (Finset.Icc 1 R).filter (fun i => i.Coprime 12), (12 * (n : ℤ) - i).natAbs := by
    exact map_prod Int.natAbsHom _ _
  rw [← habs, valuation_eq] at hh
  rw [padicValNat.mul hc (value_ne_zero n)]
  have hcv : padicValNat p (second_constant R) =
      padicValNat p (R - 1).factorial + p.log R := by
    simp only [second_constant,
      padicValNat.mul (Nat.factorial_ne_zero _) (Nat.lcmUpto_ne_zero _), lcm_valuation]
  rw [hcv]
  omega

private lemma rational_of_dvd (n c : ℕ) (d : ℤ) (hd : d ≠ 0)
    (h : d ∣ ((c * value n : ℕ) : ℤ)) :
    ∃ z : ℤ, (z : ℚ) = (c : ℚ) * ratio n / (d : ℚ) := by
  obtain ⟨z, hz⟩ := h
  refine ⟨z, ?_⟩
  rw [ratio_eq_value]
  apply (eq_div_iff (by exact_mod_cast hd)).mpr
  have he := congrArg (fun a : ℤ => (a : ℚ)) hz
  push_cast at he
  nlinarith

private lemma first_integral (n R k : ℕ) (hk : 1 ≤ k ∧ k ≤ 3) :
    ∃ z : ℤ, (z : ℚ) = (first_constant R : ℚ) * ratio n / rising_denominator k n R := by
  simpa only [Int.cast_natCast] using rational_of_dvd n (first_constant R)
    (rising_denominator k n R) (by exact_mod_cast rising_ne_zero k n R)
    (by exact_mod_cast first_dvd n R k hk)

private lemma second_integral (n R : ℕ) :
    ∃ z : ℤ, (z : ℚ) = (second_constant R : ℚ) * ratio n / signed_denominator n R :=
  rational_of_dvd n (second_constant R) (signed_denominator n R)
    (signed_ne_zero n R) (second_dvd n R)

private lemma choose_valuation (p N a : ℕ) [Fact p.Prime] (ha : a ≤ N) :
    (padicValNat p (N.choose a) : ℤ) = padicValNat p N.factorial -
      padicValNat p a.factorial - padicValNat p (N - a).factorial := by
  have he := congrArg (padicValNat p) (Nat.choose_mul_factorial_mul_factorial ha)
  rw [padicValNat.mul
      (mul_ne_zero (Nat.choose_ne_zero ha) (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
    padicValNat.mul (Nat.choose_ne_zero ha) (Nat.factorial_ne_zero _)] at he
  omega

private lemma choose_next_lower (p N a : ℕ) [Fact p.Prime] (ha : a < N)
    (hunit : ¬p ∣ N - a) :
    padicValNat p (a + 1) ≤ padicValNat p (N.choose a) := by
  have he := congrArg (padicValNat p) (Nat.choose_succ_right_eq N a)
  rw [padicValNat.mul (Nat.choose_ne_zero (by omega)) (by omega),
    padicValNat.mul (Nat.choose_ne_zero (by omega)) (by omega),
    padicValNat.eq_zero_of_not_dvd hunit] at he
  omega

private lemma two_choose_four (n : ℕ) :
    valuation 2 n = padicValNat 2 ((4 * n).choose n) := by
  have he := choose_valuation 2 (4 * n) n (by omega)
  rw [show 4 * n - n = 3 * n by omega] at he
  have h12 := padicValNat_factorial_mul (p := 2) (6 * n)
  have h6 := padicValNat_factorial_mul (p := 2) (3 * n)
  have h4 := padicValNat_factorial_mul (p := 2) (2 * n)
  have h2 := padicValNat_factorial_mul (p := 2) n
  norm_num only [show 2 * (6 * n) = 12 * n by ring, show 2 * (3 * n) = 6 * n by ring,
    show 2 * (2 * n) = 4 * n by ring] at h12 h6 h4
  dsimp [valuation]
  omega

private lemma two_choose_six (n : ℕ) :
    valuation 2 n = padicValNat 2 ((6 * n).choose (3 * n)) := by
  have he := choose_valuation 2 (6 * n) (3 * n) (by omega)
  rw [show 6 * n - 3 * n = 3 * n by omega] at he
  have h12 := padicValNat_factorial_mul (p := 2) (6 * n)
  have h6 := padicValNat_factorial_mul (p := 2) (3 * n)
  have h4 := padicValNat_factorial_mul (p := 2) (2 * n)
  have h2 := padicValNat_factorial_mul (p := 2) n
  norm_num only [show 2 * (6 * n) = 12 * n by ring, show 2 * (3 * n) = 6 * n by ring,
    show 2 * (2 * n) = 4 * n by ring] at h12 h6 h4
  dsimp [valuation]
  omega

private lemma three_choose (n k : ℕ) (hk : k = 1 ∨ k = 2) :
    valuation 3 n = padicValNat 3 ((3 * n).choose (k * n)) := by
  have h12 := padicValNat_factorial_mul (p := 3) (4 * n)
  have h6 := padicValNat_factorial_mul (p := 3) (2 * n)
  have h3 := padicValNat_factorial_mul (p := 3) n
  norm_num only [show 3 * (4 * n) = 12 * n by ring, show 3 * (2 * n) = 6 * n by ring] at h12 h6
  have he := choose_valuation 3 (3 * n) (k * n) (by rcases hk with rfl | rfl <;> omega)
  rcases hk with rfl | rfl
  all_goals
    norm_num only [one_mul, show 3 * n - n = 2 * n by omega,
      show 3 * n - 2 * n = n by omega] at he ⊢
    dsimp [valuation]
    omega

private lemma small_prime_fixed (p n k : ℕ) [hp : Fact p.Prime]
    (hp23 : p = 2 ∨ p = 3) (hk : 1 ≤ k ∧ k ≤ 3) :
    (padicValNat p (k * n + 1) : ℤ) ≤ valuation p n := by
  by_cases hn : n = 0
  · simp [hn, valuation]
  by_cases hunit : ¬p ∣ k * n + 1
  · rw [padicValNat.eq_zero_of_not_dvd hunit]
    exact valuation_nonneg p n
  have hdiv : p ∣ k * n + 1 := not_not.mp hunit
  rcases hk with ⟨hk1, hk3⟩
  rcases hp23 with rfl | rfl
  · interval_cases k
    · rw [two_choose_four]
      norm_num only [one_mul]
      exact_mod_cast choose_next_lower 2 (4 * n) n (by omega) (by
        rw [show 4 * n - n = 3 * n by omega]
        intro hh
        have hh' := (Nat.prime_two.dvd_mul.mp hh).resolve_left (by decide)
        have := Nat.dvd_add hdiv hh'
        norm_num [Nat.dvd_iff_mod_eq_zero] at *
        omega)
    · have : ¬2 ∣ 2 * n + 1 := by omega
      contradiction
    · rw [two_choose_six]
      exact_mod_cast choose_next_lower 2 (6 * n) (3 * n) (by omega) (by
        rw [show 6 * n - 3 * n = 3 * n by omega]
        omega)
  · interval_cases k
    · rw [three_choose n 1 (Or.inl rfl)]
      norm_num only [one_mul]
      exact_mod_cast choose_next_lower 3 (3 * n) n (by omega) (by
        rw [show 3 * n - n = 2 * n by omega]
        intro hh
        have hh' := (Nat.prime_three.dvd_mul.mp hh).resolve_left (by decide)
        omega)
    · rw [three_choose n 2 (Or.inr rfl)]
      exact_mod_cast choose_next_lower 3 (3 * n) (2 * n) (by omega) (by
        rw [show 3 * n - 2 * n = n by omega]
        omega)
    · have : ¬3 ∣ 3 * n + 1 := by omega
      contradiction

private def fixed_constant (k : ℕ) : ℕ := if k = 1 then 385 else if k = 2 then 5 else 1

private lemma fixed_constant_ne_zero (k : ℕ) : fixed_constant k ≠ 0 := by
  unfold fixed_constant
  split_ifs <;> norm_num

private lemma large_prime_levels (p n k E : ℕ) [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hk : 1 ≤ k ∧ k ≤ 3)
    (he : (k = 1 ∧ (p = 5 ∨ p = 7 ∨ p = 11)) ∨ (k = 2 ∧ p = 5) → 1 ≤ E) :
    (padicValNat p (k * n + 1) : ℤ) ≤ valuation p n + E := by
  apply valuation_of_levels
  intro j hj hje
  have hd : p ^ j ∣ k * n + 1 := (padicValNat_dvd_iff_le (by omega)).mpr hje
  by_cases hj1 : j = 1
  · subst j
    simp only [pow_one] at hd ⊢
    apply fixed_floor n p k hp5
      (by intro hh; have := hp.out.eq_one_or_self_of_dvd 2 hh; omega)
      (by intro hh; have := hp.out.eq_one_or_self_of_dvd 3 hh; omega) hk hd
    constructor <;> intro hex
    · have := he (Or.inl hex); omega
    · have := he (Or.inr hex); omega
  · have hj2 : 2 ≤ j := by omega
    have hq := Nat.pow_le_pow_right hp.out.pos hj2
    have hp25 : 25 ≤ p ^ 2 := by nlinarith
    exact left_floor n (p ^ j) k 1 (pow_pos hp.out.pos j) (by omega) (by omega) hk hd

private lemma fixed_bound (p n k : ℕ) [hp : Fact p.Prime] (hk : 1 ≤ k ∧ k ≤ 3) :
    (padicValNat p (k * n + 1) : ℤ) ≤ valuation p n + padicValNat p (fixed_constant k) := by
  by_cases hp23 : p = 2 ∨ p = 3
  · have := small_prime_fixed p n k hp23 hk
    omega
  have hp5 : 5 ≤ p := by
    have := hp.out.two_le
    have := hp.out.ne_one
    have hn4 : p ≠ 4 := by intro h; subst p; exact (by decide : ¬Nat.Prime 4) hp.out
    omega
  apply large_prime_levels p n k (padicValNat p (fixed_constant k)) hp5 hk
  intro hex
  rcases hex with ⟨rfl, hp⟩ | ⟨rfl, rfl⟩
  · rcases hp with rfl | rfl | rfl <;>
      apply one_le_padicValNat_of_dvd (by norm_num [fixed_constant]) <;>
      norm_num [fixed_constant]
  · apply one_le_padicValNat_of_dvd (by norm_num [fixed_constant])
    norm_num [fixed_constant]

private lemma fixed_dvd (n k : ℕ) (hk : 1 ≤ k ∧ k ≤ 3) :
    k * n + 1 ∣ fixed_constant k * value n := by
  apply dvd_of_valuations _ _ (by omega)
    (mul_ne_zero (fixed_constant_ne_zero k) (value_ne_zero n))
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  have hh := fixed_bound p n k hk
  rw [valuation_eq] at hh
  rw [padicValNat.mul (fixed_constant_ne_zero k) (value_ne_zero n)]
  omega

private lemma common_dvd_combination (a b d c : ℕ) (u v : ℤ)
    (ha : d ∣ a) (hb : d ∣ b) (he : u * (a : ℤ) + v * (b : ℤ) = c) : d ∣ c := by
  apply Int.natCast_dvd_natCast.mp
  rw [← he]
  exact dvd_add (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr ha) u)
    (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hb) v)

private lemma triple_dvd (n : ℕ) :
    (n + 1) * (2 * n + 1) * (3 * n + 1) ∣ 770 * value n := by
  have hcop : (n + 1).Coprime (2 * n + 1) := by
    apply Nat.dvd_one.mp
    exact common_dvd_combination (n + 1) (2 * n + 1) _ 1 2 (-1)
      (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) (by push_cast; ring)
  have h1 : n + 1 ∣ 385 * value n := by simpa [fixed_constant] using fixed_dvd n 1 (by omega)
  have h2 : 2 * n + 1 ∣ 385 * value n := by
    have hh : 5 * value n ∣ 385 * value n := Nat.mul_dvd_mul_right (by norm_num : 5 ∣ 385) _
    have hx : 2 * n + 1 ∣ 5 * value n := by simpa [fixed_constant] using fixed_dvd n 2 (by omega)
    exact hx.trans hh
  have h3 : 3 * n + 1 ∣ 385 * value n := by
    have hh : 3 * n + 1 ∣ value n := by simpa [fixed_constant] using fixed_dvd n 3 (by omega)
    exact hh.trans (dvd_mul_left _ _)
  have hab : (n + 1) * (2 * n + 1) ∣ 385 * value n := hcop.mul_dvd_of_dvd_of_dvd h1 h2
  have hg : Nat.gcd ((n + 1) * (2 * n + 1)) (3 * n + 1) ∣ 2 :=
    common_dvd_combination ((n + 1) * (2 * n + 1)) (3 * n + 1) _ 2 9 (-(6 * (n : ℤ) + 7))
      (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) (by push_cast; ring)
  have hl := Nat.lcm_dvd hab h3
  have hh := Nat.mul_dvd_mul hg hl
  rw [Nat.gcd_mul_lcm] at hh
  convert hh using 1 <;> ring

/-- The complete actual-expression package, with all natural indices and both unbounded families. -/
theorem result : claim := by
  constructor
  · intro n
    have hf (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 3) :
        ∃ z : ℤ, (z : ℚ) = (fixed_constant k : ℚ) * ratio n / ((k * n + 1 : ℕ) : ℚ) := by
      simpa only [Int.cast_natCast] using rational_of_dvd n (fixed_constant k) ((k * n + 1 : ℕ) : ℤ)
        (by positivity) (by exact_mod_cast fixed_dvd n k hk)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [fixed_constant] using hf 1 (by omega)
    · simpa [fixed_constant, Nat.cast_add, Nat.cast_mul] using hf 2 (by omega)
    · simpa [fixed_constant, Nat.cast_add, Nat.cast_mul] using hf 3 (by omega)
    · simpa only [Int.cast_natCast, Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_ofNat,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat] using rational_of_dvd n 770 (((n + 1) * (2 * n + 1) * (3 * n + 1) : ℕ) : ℤ)
          (by positivity) (by exact_mod_cast triple_dvd n)
    · have hh := second_integral n 1
      simpa [second_constant, signed_denominator, Nat.lcmUpto, Finset.filter_singleton, Nat.cast_sub] using hh
    · intro R hR k hk
      exact ⟨rising_ne_zero k n R, first_integral n R k hk⟩
    · intro R hR
      exact ⟨signed_ne_zero n R, second_integral n R⟩
  · norm_num [ratio]

end D5.S3.Arith.FactorialRatio.BalaA295431Divisibility
