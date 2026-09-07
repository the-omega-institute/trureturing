/- GID: D5/S3/Arith/GoldenResource/GoldenCell5040Certificate
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenCell5040Certificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=terminal=atom:3e88ff962e8dc5d296f916ab7325c90ab9da3ea7f35f610adf5f8002ea7d8cc3; result=D5/S3/Arith/GoldenResource/GoldenCell5040Certificate.robin_log_margin_5040_cell_certificate
   digest: Exact rational brackets certify the strict Robin margin on the six-point 5040 cell. -/

import D5.S3.Arith.GoldenResource.RobinRationalBasis
import Mathlib.Data.Nat.Fib.Zeckendorf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.Arith.GoldenResource.GoldenCell5040Certificate

open D5.S3.Arith.GoldenResource.RobinRationalBasis
open scoped BigOperators

/-- The volume's golden weights `G_L = F_(L+2)`. -/
def goldenWeight (L : ℕ) : ℕ := Nat.fib (L + 2)

/-- The left endpoint `G_lambda - 1` of the golden exponent window containing `a`. -/
def goldenBaseExponent (a : ℕ) : ℕ :=
  Nat.fib (Nat.greatestFib (a + 1)) - 1

private theorem goldenBaseExponent_zero : goldenBaseExponent 0 = 0 := by decide

private theorem two_le_greatestFib_add_one (a : ℕ) :
    2 ≤ Nat.greatestFib (a + 1) := by
  rw [Nat.le_greatestFib]
  simp

private theorem greatestFib_eq_of_goldenBaseExponent {a k L : ℕ}
    (hk : goldenBaseExponent a = k) (hL : Nat.fib (L + 2) = k + 1) :
    Nat.greatestFib (a + 1) = L + 2 := by
  have hpos : 0 < Nat.fib (Nat.greatestFib (a + 1)) := Nat.fib_pos.2 <|
    lt_of_lt_of_le (by omega) (two_le_greatestFib_add_one a)
  have hf : Nat.fib (Nat.greatestFib (a + 1)) = k + 1 := by
    unfold goldenBaseExponent at hk
    omega
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (two_le_greatestFib_add_one a)
  rw [hq] at hf ⊢
  rw [add_comm 2 q] at hf
  have hqL : q = L := Nat.fib_add_two_strictMono.injective (hf.trans hL.symm)
  omega

/-- The zero golden exponent window contains only zero. -/
theorem goldenBaseExponent_eq_zero_iff {a : ℕ} :
    goldenBaseExponent a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hg := greatestFib_eq_of_goldenBaseExponent h (L := 0) (by decide)
    have hu := Nat.lt_fib_greatestFib_add_one (a + 1)
    rw [hg] at hu
    norm_num [Nat.fib] at hu
    omega
  · rintro rfl
    exact goldenBaseExponent_zero

/-- The golden exponent window with base exponent one is the singleton `{1}`. -/
theorem goldenBaseExponent_eq_one_iff {a : ℕ} :
    goldenBaseExponent a = 1 ↔ a = 1 := by
  constructor
  · intro h
    have hg := greatestFib_eq_of_goldenBaseExponent h (L := 1) (by decide)
    have hlo := Nat.fib_greatestFib_le (a + 1)
    have hu := Nat.lt_fib_greatestFib_add_one (a + 1)
    rw [hg] at hlo hu
    norm_num [Nat.fib] at hlo hu
    omega
  · rintro rfl
    decide

/-- The golden exponent window with base exponent two consists of exponents two and three. -/
theorem goldenBaseExponent_eq_two_iff {a : ℕ} :
    goldenBaseExponent a = 2 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro h
    have hg := greatestFib_eq_of_goldenBaseExponent h (L := 2) (by decide)
    have hlo := Nat.fib_greatestFib_le (a + 1)
    have hu := Nat.lt_fib_greatestFib_add_one (a + 1)
    rw [hg] at hlo hu
    norm_num [Nat.fib] at hlo hu
    omega
  · rintro (rfl | rfl) <;> decide

/-- The golden exponent window with base exponent four consists of exponents four through six. -/
theorem goldenBaseExponent_eq_four_iff {a : ℕ} :
    goldenBaseExponent a = 4 ↔ a = 4 ∨ a = 5 ∨ a = 6 := by
  constructor
  · intro h
    have hg := greatestFib_eq_of_goldenBaseExponent h (L := 3) (by decide)
    have hlo := Nat.fib_greatestFib_le (a + 1)
    have hu := Nat.lt_fib_greatestFib_add_one (a + 1)
    rw [hg] at hlo hu
    norm_num [Nat.fib] at hlo hu
    omega
  · rintro (rfl | rfl | rfl) <;> decide

/-- Prime exponents after applying the volume's golden observation map. -/
noncomputable def goldenFactorization (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange goldenBaseExponent goldenBaseExponent_zero

/-- The golden observation `G(n) = product p^(b(a_p(n)))`. -/
noncomputable def goldenObservation (n : ℕ) : ℕ :=
  (goldenFactorization n).prod (fun p a => p ^ a)

/-- The positive-natural fibre of the golden observation containing `m`. -/
def goldenCell (m : ℕ) : Set ℕ :=
  {n | 0 < n ∧ goldenObservation n = m}

/-- The part of a golden cell strictly beyond Robin's boundary 5040. -/
def goldenCellPlus (m : ℕ) : Set ℕ :=
  goldenCell m ∩ {n | 5040 < n}

private theorem factorization_goldenObservation (n : ℕ) :
    (goldenObservation n).factorization = goldenFactorization n := by
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  by_contra hprime
  have hz : goldenFactorization n p = 0 := by
    simp [goldenFactorization, Nat.factorization_eq_zero_of_not_prime n hprime,
      goldenBaseExponent_zero]
  exact (Finsupp.mem_support_iff.mp hp) hz

private theorem factorization_eq_of_mem_cell {m n p : ℕ} (hn : n ∈ goldenCell m) :
    goldenBaseExponent (n.factorization p) = m.factorization p := by
  have h := congrArg (fun x : ℕ => x.factorization p) hn.2
  rw [factorization_goldenObservation] at h
  simpa [goldenFactorization] using h

private theorem factorization_5040_apply (p : ℕ) :
    (5040 : ℕ).factorization p =
      if p = 2 then 4 else if p = 3 then 2 else if p = 5 then 1 else if p = 7 then 1 else 0 := by
  rw [show (5040 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num),
    (by decide : Nat.Prime 2).factorization_pow,
    (by decide : Nat.Prime 3).factorization_pow,
    (by decide : Nat.Prime 5).factorization_pow,
    (by decide : Nat.Prime 7).factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

private theorem cell_5040_factorization_options {n p : ℕ} (hn : n ∈ goldenCell 5040) :
    (p = 2 ∧ (n.factorization p = 4 ∨ n.factorization p = 5 ∨ n.factorization p = 6)) ∨
    (p = 3 ∧ (n.factorization p = 2 ∨ n.factorization p = 3)) ∨
    ((p = 5 ∨ p = 7) ∧ n.factorization p = 1) ∨
    (p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7 ∧ n.factorization p = 0) := by
  have h := factorization_eq_of_mem_cell (p := p) hn
  rw [factorization_5040_apply] at h
  by_cases h2 : p = 2
  · subst p; left
    exact ⟨rfl, goldenBaseExponent_eq_four_iff.mp (by simpa using h)⟩
  by_cases h3 : p = 3
  · subst p; right; left
    exact ⟨rfl, goldenBaseExponent_eq_two_iff.mp (by simp [h2] at h; exact h)⟩
  by_cases h5 : p = 5
  · subst p; right; right; left
    exact ⟨Or.inl rfl, goldenBaseExponent_eq_one_iff.mp (by simp [h2, h3] at h; exact h)⟩
  by_cases h7 : p = 7
  · subst p; right; right; left
    exact ⟨Or.inr rfl,
      goldenBaseExponent_eq_one_iff.mp (by simp [h2, h3, h5] at h; exact h)⟩
  · right; right; right
    exact ⟨h2, h3, h5, h7,
      goldenBaseExponent_eq_zero_iff.mp (by simpa [h2, h3, h5, h7] using h)⟩

private theorem cell_5040_factorization_eq {n : ℕ} (hn : n ∈ goldenCell 5040) :
    n.factorization =
      Finsupp.single 2 (n.factorization 2) + Finsupp.single 3 (n.factorization 3) +
        Finsupp.single 5 1 + Finsupp.single 7 1 := by
  ext p
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  rcases cell_5040_factorization_options (p := p) hn with h | h | h | h
  · rcases h with ⟨rfl, _⟩; simp
  · rcases h with ⟨rfl, _⟩; simp
  · rcases h with ⟨rfl | rfl, hp⟩ <;> simp [hp]
  · rcases h with ⟨h2, h3, h5, h7, hp⟩
    simp [Ne.symm h2, Ne.symm h3, Ne.symm h5, Ne.symm h7, hp]

private theorem mem_cell_5040_value {n : ℕ} (hn : n ∈ goldenCell 5040) :
    n = 2 ^ (n.factorization 2) * 3 ^ (n.factorization 3) * 5 * 7 := by
  calc
    n = n.factorization.prod (fun p a => p ^ a) :=
      (Nat.prod_factorization_pow_eq_self hn.1.ne').symm
    _ = (Finsupp.single 2 (n.factorization 2) + Finsupp.single 3 (n.factorization 3) +
          Finsupp.single 5 1 + Finsupp.single 7 1).prod (fun p a => p ^ a) := by
      exact congrArg (fun f : ℕ →₀ ℕ => f.prod (fun p a => p ^ a))
        (cell_5040_factorization_eq hn)
    _ = 2 ^ (n.factorization 2) * 3 ^ (n.factorization 3) * 5 * 7 := by
      repeat' rw [Finsupp.prod_add_index' (fun p => pow_zero p) (fun p a b => pow_add p a b)]
      simp

private theorem goldenObservation_ne_zero (n : ℕ) : goldenObservation n ≠ 0 := by
  apply Finsupp.prod_ne_zero_iff.mpr
  intro p hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    have hz : goldenFactorization n 0 = 0 := by
      simp [goldenFactorization, goldenBaseExponent_zero]
    exact (Finsupp.mem_support_iff.mp hp) hz
  exact pow_ne_zero _ hp0

private theorem mem_cell_of_goldenFactorization_eq {m n : ℕ} (hn : 0 < n) (hm : m ≠ 0)
    (h : goldenFactorization n = m.factorization) : n ∈ goldenCell m := by
  refine ⟨hn, Nat.factorization_inj (goldenObservation_ne_zero n) hm ?_⟩
  rw [factorization_goldenObservation, h]

private theorem golden_factorization_of_exponents (a b : ℕ)
    (ha : goldenBaseExponent a = 4) (hb : goldenBaseExponent b = 2) :
    goldenFactorization (2 ^ a * 3 ^ b * 5 * 7) = (5040 : ℕ).factorization := by
  unfold goldenFactorization
  rw [Nat.factorization_mul (by positivity) (by norm_num),
    Nat.factorization_mul (by positivity) (by norm_num),
    Nat.factorization_mul (by positivity) (by norm_num),
    (by decide : Nat.Prime 2).factorization_pow,
    (by decide : Nat.Prime 3).factorization_pow,
    (by decide : Nat.Prime 5).factorization,
    (by decide : Nat.Prime 7).factorization]
  ext p
  simp only [Finsupp.mapRange_apply, Finsupp.add_apply, Finsupp.single_apply]
  rw [factorization_5040_apply]
  by_cases h2 : p = 2
  · subst p; simp [ha]
  by_cases h3 : p = 3
  · subst p; simp [h2, hb]
  by_cases h5 : p = 5
  · subst p; simp [h2, h3, goldenBaseExponent_eq_one_iff.mpr rfl]
  by_cases h7 : p = 7
  · subst p; simp [h2, h3, h5, goldenBaseExponent_eq_one_iff.mpr rfl]
  · simp [h2, h3, h5, h7, Ne.symm h2, Ne.symm h3, Ne.symm h5, Ne.symm h7,
      goldenBaseExponent_zero]

private theorem cell_5040_member_of_exponents {a b : ℕ}
    (ha : goldenBaseExponent a = 4) (hb : goldenBaseExponent b = 2) :
    2 ^ a * 3 ^ b * 5 * 7 ∈ goldenCell 5040 :=
  mem_cell_of_goldenFactorization_eq (by positivity) (by norm_num)
    (golden_factorization_of_exponents a b ha hb)

/-- The 5040 golden cell is exactly the six integers displayed in theorem 4.5. -/
theorem golden_cell_5040_identity :
    goldenCell 5040 = {5040, 10080, 15120, 20160, 30240, 60480} := by
  ext n
  constructor
  · intro hn
    have h2 : goldenBaseExponent (n.factorization 2) = 4 := by
      simpa [factorization_5040_apply] using factorization_eq_of_mem_cell (p := 2) hn
    have h3 : goldenBaseExponent (n.factorization 3) = 2 := by
      simpa [factorization_5040_apply] using factorization_eq_of_mem_cell (p := 3) hn
    have h2 := goldenBaseExponent_eq_four_iff.mp h2
    have h3 := goldenBaseExponent_eq_two_iff.mp h3
    have hv := mem_cell_5040_value hn
    rcases h2 with h2 | h2 | h2 <;> rcases h3 with h3 | h3 <;>
      simp only [h2, h3] at hv <;> norm_num at hv ⊢ <;> omega
  · intro hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using cell_5040_member_of_exponents (a := 4) (b := 2) (by decide) (by decide)
    · simpa using cell_5040_member_of_exponents (a := 5) (b := 2) (by decide) (by decide)
    · simpa using cell_5040_member_of_exponents (a := 4) (b := 3) (by decide) (by decide)
    · simpa using cell_5040_member_of_exponents (a := 6) (b := 2) (by decide) (by decide)
    · simpa using cell_5040_member_of_exponents (a := 5) (b := 3) (by decide) (by decide)
    · simpa using cell_5040_member_of_exponents (a := 6) (b := 3) (by decide) (by decide)

private theorem golden_cell_plus_5040_identity :
    goldenCellPlus 5040 = {10080, 15120, 20160, 30240, 60480} := by
  rw [goldenCellPlus, golden_cell_5040_identity]
  ext n
  simp
  omega

private theorem goldenBaseExponent_le_twice (a : ℕ) : a ≤ 2 * goldenBaseExponent a := by
  by_cases ha : a = 0
  · simp [ha, goldenBaseExponent_zero]
  let g := Nat.greatestFib (a + 1)
  have hg2 : 2 ≤ g := two_le_greatestFib_add_one a
  have hu : a + 1 < Nat.fib (g + 1) := Nat.lt_fib_greatestFib_add_one (a + 1)
  have hmono : Nat.fib (g - 1) ≤ Nat.fib g := Nat.fib_mono (Nat.sub_le g 1)
  have hrec : Nat.fib (g + 1) = Nat.fib (g - 1) + Nat.fib g :=
    Nat.fib_add_one (by omega)
  have hpos : 0 < Nat.fib g := Nat.fib_pos.2 (by omega)
  rw [hrec] at hu
  unfold goldenBaseExponent
  change a ≤ 2 * (Nat.fib g - 1)
  omega

private theorem goldenCell_finite (m : ℕ) : (goldenCell m).Finite := by
  by_cases hm : m = 0
  · subst m
    have hzero : goldenCell 0 = ∅ := by
      ext n
      constructor
      · intro hn
        exact (goldenObservation_ne_zero n) hn.2
      · intro hn
        exact hn.elim
    rw [hzero]
    exact Set.finite_empty
  apply (Set.finite_Icc 1 (m ^ 2)).subset
  intro n hn
  refine ⟨hn.1, Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hm) 2) ?_⟩
  apply (Nat.factorization_le_iff_dvd hn.1.ne' (pow_ne_zero 2 hm)).mp
  intro p
  rw [Nat.factorization_pow]
  have h := goldenBaseExponent_le_twice (n.factorization p)
  rw [factorization_eq_of_mem_cell (p := p) hn] at h
  simpa [nsmul_eq_mul] using h

/-- Every positive part of a golden cell is finite. -/
theorem goldenCellPlus_finite (m : ℕ) : (goldenCellPlus m).Finite :=
  (goldenCell_finite m).subset Set.inter_subset_left

private theorem sigma_four_coprime {a b c d : ℕ}
    (hab : Nat.Coprime a b) (habc : Nat.Coprime (a * b) c)
    (habcd : Nat.Coprime (a * b * c) d) :
    ArithmeticFunction.sigma 1 (a * b * c * d) =
      ArithmeticFunction.sigma 1 a * ArithmeticFunction.sigma 1 b *
        ArithmeticFunction.sigma 1 c * ArithmeticFunction.sigma 1 d := by
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime habcd,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime habc,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hab]

private theorem sigma_prime_power_values :
    ArithmeticFunction.sigma 1 (2 ^ 4) = 31 ∧
    ArithmeticFunction.sigma 1 (2 ^ 5) = 63 ∧
    ArithmeticFunction.sigma 1 (2 ^ 6) = 127 ∧
    ArithmeticFunction.sigma 1 (3 ^ 2) = 13 ∧
    ArithmeticFunction.sigma 1 (3 ^ 3) = 40 ∧
    ArithmeticFunction.sigma 1 5 = 6 ∧ ArithmeticFunction.sigma 1 7 = 8 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 2),
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 2),
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 2),
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 3),
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 3),
    show (5 : ℕ) = 5 ^ 1 by norm_num,
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 5),
    show (7 : ℕ) = 7 ^ 1 by norm_num,
    ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 7)]
  norm_num

/-- Exact divisor sums at every point of the 5040 golden cell. -/
theorem sigma_5040_cell_values :
    ArithmeticFunction.sigma 1 5040 = 19344 ∧
    ArithmeticFunction.sigma 1 10080 = 39312 ∧
    ArithmeticFunction.sigma 1 15120 = 59520 ∧
    ArithmeticFunction.sigma 1 20160 = 79248 ∧
    ArithmeticFunction.sigma 1 30240 = 120960 ∧
    ArithmeticFunction.sigma 1 60480 = 243840 := by
  rcases sigma_prime_power_values with ⟨s24, s25, s26, s32, s33, s5, s7⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (5040 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 * 7 by norm_num,
      sigma_four_coprime (by decide) (by decide) (by decide), s24, s32, s5, s7]
  · rw [show (10080 : ℕ) = 2 ^ 5 * 3 ^ 2 * 5 * 7 by norm_num,
      sigma_four_coprime (by decide) (by decide) (by decide), s25, s32, s5, s7]
  · rw [show (15120 : ℕ) = 2 ^ 4 * 3 ^ 3 * 5 * 7 by norm_num,
      sigma_four_coprime (by decide) (by decide) (by decide), s24, s33, s5, s7]
  · rw [show (20160 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 * 7 by norm_num,
      sigma_four_coprime (by decide) (by decide) (by decide), s26, s32, s5, s7]
  · rw [show (30240 : ℕ) = 2 ^ 5 * 3 ^ 3 * 5 * 7 by norm_num,
      sigma_four_coprime (by decide) (by decide) (by decide), s25, s33, s5, s7]
  · rw [show (60480 : ℕ) = 2 ^ 6 * 3 ^ 3 * 5 * 7 by norm_num,
      sigma_four_coprime (by decide) (by decide) (by decide), s26, s33, s5, s7]

/-- The triple logarithm in the volume's logarithmic Robin margin. -/
noncomputable def tripleLog (n : ℕ) : ℝ := Real.log (Real.log (Real.log n))

/-- The logarithm of the exact divisor-sum ratio `sigma(n) / n`. -/
noncomputable def logSigmaRatio (n : ℕ) : ℝ :=
  Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n)

/-- The chapter-9 logarithmic Robin margin. -/
noncomputable def robinLogMargin (n : ℕ) : ℝ :=
  Real.eulerMascheroniConstant + tripleLog n - logSigmaRatio n

/-- The additive form of the Robin margin. -/
noncomputable def robinAdditiveMargin (n : ℕ) : ℝ :=
  (ArithmeticFunction.sigma 1 n : ℝ) * (Real.exp (robinLogMargin n) - 1)

/-- Definition 14.1: the infimum, hence minimum when nonempty, over the positive cell. -/
noncomputable def cellMinimum (m : ℕ) : ℝ :=
  sInf (robinLogMargin '' goldenCellPlus m)

/-- On every nonempty golden cell above 5040, `cellMinimum` is attained. -/
theorem cellMinimum_mem {m : ℕ} (hne : (goldenCellPlus m).Nonempty) :
    ∃ n ∈ goldenCellPlus m, cellMinimum m = robinLogMargin n := by
  have himageNonempty : (robinLogMargin '' goldenCellPlus m).Nonempty := hne.image _
  have himageFinite : (robinLogMargin '' goldenCellPlus m).Finite :=
    (goldenCellPlus_finite m).image _
  have hmem := himageNonempty.csInf_mem himageFinite
  rcases hmem with ⟨n, hn, heq⟩
  exact ⟨n, hn, by simpa [cellMinimum] using heq.symm⟩

private theorem log_5040_bounds :
    (170503227 / 20000000 : ℝ) < Real.log 5040 ∧
      Real.log 5040 < (852516137 / 100000000 : ℝ) := by
  refine rational_log_bounds 5040 (315 / 256) _ _ 12 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_15120_bounds :
    (240594341 / 25000000 : ℝ) < Real.log 15120 ∧
      Real.log 15120 < (481188683 / 50000000 : ℝ) := by
  refine rational_log_bounds 15120 (945 / 512) _ _ 13 7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_20160_bounds :
    (991145571 / 100000000 : ℝ) < Real.log 20160 ∧
      Real.log 20160 < (991145573 / 100000000 : ℝ) := by
  refine rational_log_bounds 20160 (315 / 256) _ _ 14 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_30240_bounds :
    (515846041 / 50000000 : ℝ) < Real.log 30240 ∧
      Real.log 30240 < (257923021 / 25000000 : ℝ) := by
  refine rational_log_bounds 30240 (945 / 512) _ _ 14 7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem log_60480_bounds :
    (2752517 / 250000 : ℝ) < Real.log 60480 ∧
      Real.log 60480 < (550503401 / 50000000 : ℝ) := by
  refine rational_log_bounds 60480 (945 / 512) _ _ 15 7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem logLog_5040_bounds :
    (107151097 / 50000000 : ℝ) < Real.log (Real.log 5040) ∧
      Real.log (Real.log 5040) < (53575549 / 25000000 : ℝ) := by
  have hlo := rational_log_bounds (170503227 / 20000000) (170503227 / 160000000)
    (107151097 / 50000000) (53575549 / 25000000) 3 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hhi := rational_log_bounds (852516137 / 100000000) (852516137 / 800000000)
    (107151097 / 50000000) (53575549 / 25000000) 3 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact log_interval_bounds (by norm_num) log_5040_bounds.1 log_5040_bounds.2 hlo.1 hhi.2

private theorem logLog_15120_bounds :
    (45284729 / 20000000 : ℝ) < Real.log (Real.log 15120) ∧
      Real.log (Real.log 15120) < (226423647 / 100000000 : ℝ) := by
  have hlo := rational_log_bounds (240594341 / 25000000) (240594341 / 200000000)
    (45284729 / 20000000) (226423647 / 100000000) 3 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hhi := rational_log_bounds (481188683 / 50000000) (481188683 / 400000000)
    (45284729 / 20000000) (226423647 / 100000000) 3 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact log_interval_bounds (by norm_num) log_15120_bounds.1 log_15120_bounds.2 hlo.1 hhi.2

private theorem logLog_20160_bounds :
    (114684561 / 50000000 : ℝ) < Real.log (Real.log 20160) ∧
      Real.log (Real.log 20160) < (57342281 / 25000000 : ℝ) := by
  have hlo := rational_log_bounds (991145571 / 100000000) (991145571 / 800000000)
    (114684561 / 50000000) (57342281 / 25000000) 3 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hhi := rational_log_bounds (991145573 / 100000000) (991145573 / 800000000)
    (114684561 / 50000000) (57342281 / 25000000) 3 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact log_interval_bounds (by norm_num) log_20160_bounds.1 log_20160_bounds.2 hlo.1 hhi.2

private theorem logLog_30240_bounds :
    (116689267 / 50000000 : ℝ) < Real.log (Real.log 30240) ∧
      Real.log (Real.log 30240) < (46675707 / 20000000 : ℝ) := by
  have hlo := rational_log_bounds (515846041 / 50000000) (515846041 / 400000000)
    (116689267 / 50000000) (46675707 / 20000000) 3 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hhi := rational_log_bounds (257923021 / 25000000) (257923021 / 200000000)
    (116689267 / 50000000) (46675707 / 20000000) 3 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact log_interval_bounds (by norm_num) log_30240_bounds.1 log_30240_bounds.2 hlo.1 hhi.2

private theorem logLog_60480_bounds :
    (59970253 / 25000000 : ℝ) < Real.log (Real.log 60480) ∧
      Real.log (Real.log 60480) < (239881013 / 100000000 : ℝ) := by
  have hlo := rational_log_bounds (2752517 / 250000) (2752517 / 2000000)
    (59970253 / 25000000) (239881013 / 100000000) 3 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hhi := rational_log_bounds (550503401 / 50000000) (550503401 / 400000000)
    (59970253 / 25000000) (239881013 / 100000000) 3 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact log_interval_bounds (by norm_num) log_60480_bounds.1 log_60480_bounds.2 hlo.1 hhi.2

private theorem tripleLog_5040_bounds :
    (7622169 / 10000000 : ℝ) < tripleLog 5040 ∧ tripleLog 5040 < (762217 / 1000000 : ℝ) := by
  have hlo := rational_log_bounds (107151097 / 50000000) (107151097 / 100000000)
    (7622169 / 10000000) (762217 / 1000000) 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hhi := rational_log_bounds (53575549 / 25000000) (53575549 / 50000000)
    (7622169 / 10000000) (762217 / 1000000) 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact log_interval_bounds (by norm_num) logLog_5040_bounds.1 logLog_5040_bounds.2 hlo.1 hhi.2

private theorem tripleLog_10080_bounds :
    (7980437 / 10000000 : ℝ) < tripleLog 10080 ∧
      tripleLog 10080 < (3990219 / 5000000 : ℝ) := by
  have hlo := rational_log_bounds (55529789 / 25000000) (55529789 / 50000000)
    (7980437 / 10000000) (3990219 / 5000000) 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hhi := rational_log_bounds (222119157 / 100000000) (222119157 / 200000000)
    (7980437 / 10000000) (3990219 / 5000000) 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact log_interval_bounds (by norm_num) logLog_10080_bounds.1 logLog_10080_bounds.2 hlo.1 hhi.2

private theorem tripleLog_15120_bounds :
    (65379 / 80000 : ℝ) < tripleLog 15120 ∧ tripleLog 15120 < (8172377 / 10000000 : ℝ) := by
  have hlo := rational_log_bounds (45284729 / 20000000) (45284729 / 40000000)
    (65379 / 80000) (8172377 / 10000000) 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hhi := rational_log_bounds (226423647 / 100000000) (226423647 / 200000000)
    (65379 / 80000) (8172377 / 10000000) 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact log_interval_bounds (by norm_num) logLog_15120_bounds.1 logLog_15120_bounds.2 hlo.1 hhi.2

private theorem tripleLog_20160_bounds :
    (1037703 / 1250000 : ℝ) < tripleLog 20160 ∧ tripleLog 20160 < (66413 / 80000 : ℝ) := by
  have hlo := rational_log_bounds (114684561 / 50000000) (114684561 / 100000000)
    (1037703 / 1250000) (66413 / 80000) 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hhi := rational_log_bounds (57342281 / 25000000) (57342281 / 50000000)
    (1037703 / 1250000) (66413 / 80000) 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact log_interval_bounds (by norm_num) logLog_20160_bounds.1 logLog_20160_bounds.2 hlo.1 hhi.2

private theorem tripleLog_30240_bounds :
    (1694983 / 2000000 : ℝ) < tripleLog 30240 ∧
      tripleLog 30240 < (2118729 / 2500000 : ℝ) := by
  have hlo := rational_log_bounds (116689267 / 50000000) (116689267 / 100000000)
    (1694983 / 2000000) (2118729 / 2500000) 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hhi := rational_log_bounds (46675707 / 20000000) (46675707 / 40000000)
    (1694983 / 2000000) (2118729 / 2500000) 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact log_interval_bounds (by norm_num) logLog_30240_bounds.1 logLog_30240_bounds.2 hlo.1 hhi.2

private theorem tripleLog_60480_bounds :
    (273429 / 312500 : ℝ) < tripleLog 60480 ∧ tripleLog 60480 < (8749729 / 10000000 : ℝ) := by
  have hlo := rational_log_bounds (59970253 / 25000000) (59970253 / 50000000)
    (273429 / 312500) (8749729 / 10000000) 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  have hhi := rational_log_bounds (239881013 / 100000000) (239881013 / 200000000)
    (273429 / 312500) (8749729 / 10000000) 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [atanhPartial, Finset.sum_range_succ])
  exact log_interval_bounds (by norm_num) logLog_60480_bounds.1 logLog_60480_bounds.2 hlo.1 hhi.2

private theorem ratio_5040_bounds :
    (6724881 / 5000000 : ℝ) < Real.log ((19344 : ℝ) / 5040) ∧
      Real.log ((19344 : ℝ) / 5040) < (13449763 / 10000000 : ℝ) := by
  refine rational_log_bounds ((19344 : ℝ) / 5040) (403 / 210) _ _ 1 7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem ratio_10080_bounds :
    (2721953 / 2000000 : ℝ) < Real.log ((39312 : ℝ) / 10080) ∧
      Real.log ((39312 : ℝ) / 10080) < (6804883 / 5000000 : ℝ) := by
  refine rational_log_bounds ((39312 : ℝ) / 10080) (39 / 20) _ _ 1 7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem ratio_15120_bounds :
    (685147 / 500000 : ℝ) < Real.log ((59520 : ℝ) / 15120) ∧
      Real.log ((59520 : ℝ) / 15120) < (13702941 / 10000000 : ℝ) := by
  refine rational_log_bounds ((59520 : ℝ) / 15120) (124 / 63) _ _ 1 7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem ratio_20160_bounds :
    (13688817 / 10000000 : ℝ) < Real.log ((79248 : ℝ) / 20160) ∧
      Real.log ((79248 : ℝ) / 20160) < (6844409 / 5000000 : ℝ) := by
  refine rational_log_bounds ((79248 : ℝ) / 20160) (1651 / 840) _ _ 1 7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem ratio_30240_bounds :
    (13862943 / 10000000 : ℝ) < Real.log ((120960 : ℝ) / 30240) ∧
      Real.log ((120960 : ℝ) / 30240) < (433217 / 312500 : ℝ) := by
  refine rational_log_bounds ((120960 : ℝ) / 30240) 1 _ _ 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

private theorem ratio_60480_bounds :
    (2788399 / 2000000 : ℝ) < Real.log ((243840 : ℝ) / 60480) ∧
      Real.log ((243840 : ℝ) / 60480) < (3485499 / 2500000 : ℝ) := by
  refine rational_log_bounds ((243840 : ℝ) / 60480) (127 / 126) _ _ 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  norm_num [atanhPartial, Finset.sum_range_succ]

/-- Outward exact rational brackets for gamma and the twelve pointwise analytic leaves. -/
structure RelaxedAnalyticBracketWitness : Prop where
  gamma : Real.eulerMascheroniConstant ∈
    Set.Ioo ((5772155 : ℝ) / 10000000) (5772161 / 10000000)
  tlog5040 : tripleLog 5040 ∈ Set.Ioo ((7622169 : ℝ) / 10000000) (762217 / 1000000)
  ratio5040 : Real.log ((19344 : ℝ) / 5040) ∈
    Set.Ioo ((6724881 : ℝ) / 5000000) (13449763 / 10000000)
  tlog10080 : tripleLog 10080 ∈ Set.Ioo ((7980437 : ℝ) / 10000000) (3990219 / 5000000)
  ratio10080 : Real.log ((39312 : ℝ) / 10080) ∈
    Set.Ioo ((2721953 : ℝ) / 2000000) (6804883 / 5000000)
  tlog15120 : tripleLog 15120 ∈ Set.Ioo ((65379 : ℝ) / 80000) (8172377 / 10000000)
  ratio15120 : Real.log ((59520 : ℝ) / 15120) ∈
    Set.Ioo ((685147 : ℝ) / 500000) (13702941 / 10000000)
  tlog20160 : tripleLog 20160 ∈ Set.Ioo ((1037703 : ℝ) / 1250000) (66413 / 80000)
  ratio20160 : Real.log ((79248 : ℝ) / 20160) ∈
    Set.Ioo ((13688817 : ℝ) / 10000000) (6844409 / 5000000)
  tlog30240 : tripleLog 30240 ∈ Set.Ioo ((1694983 : ℝ) / 2000000) (2118729 / 2500000)
  ratio30240 : Real.log ((120960 : ℝ) / 30240) ∈
    Set.Ioo ((13862943 : ℝ) / 10000000) (433217 / 312500)
  tlog60480 : tripleLog 60480 ∈ Set.Ioo ((273429 : ℝ) / 312500) (8749729 / 10000000)
  ratio60480 : Real.log ((243840 : ℝ) / 60480) ∈
    Set.Ioo ((2788399 : ℝ) / 2000000) (3485499 / 2500000)

/-- All thirteen analytic leaves are constructed without hypotheses or floating point. -/
theorem analytic_bracket_witness_constructed : RelaxedAnalyticBracketWitness := by
  exact ⟨eulerMascheroni_decimal_bounds, tripleLog_5040_bounds, ratio_5040_bounds,
    tripleLog_10080_bounds, ratio_10080_bounds, tripleLog_15120_bounds, ratio_15120_bounds,
    tripleLog_20160_bounds, ratio_20160_bounds, tripleLog_30240_bounds, ratio_30240_bounds,
    tripleLog_60480_bounds, ratio_60480_bounds⟩

private theorem robinLogMargin_eq_of_sigma {n s : ℕ}
    (hs : ArithmeticFunction.sigma 1 n = s) :
    robinLogMargin n =
      Real.eulerMascheroniConstant + tripleLog n - Real.log ((s : ℝ) / n) := by
  simp only [robinLogMargin, logSigmaRatio, hs]

/-- Certified pointwise margin bounds at all six points of the 5040 golden cell. -/
theorem robin_log_margin_5040_point_bounds :
    (-5545 / 1000000 : ℝ) < robinLogMargin 5040 ∧
    robinLogMargin 5040 < (-5542 / 1000000 : ℝ) ∧
    (1 / 100 : ℝ) < robinLogMargin 10080 ∧
    (1 / 100 : ℝ) < robinLogMargin 15120 ∧
    (1 / 100 : ℝ) < robinLogMargin 20160 ∧
    (1 / 100 : ℝ) < robinLogMargin 30240 ∧
    (1 / 100 : ℝ) < robinLogMargin 60480 := by
  rcases sigma_5040_cell_values with ⟨s5040, s10080, s15120, s20160, s30240, s60480⟩
  rw [robinLogMargin_eq_of_sigma s5040, robinLogMargin_eq_of_sigma s10080,
    robinLogMargin_eq_of_sigma s15120, robinLogMargin_eq_of_sigma s20160,
    robinLogMargin_eq_of_sigma s30240, robinLogMargin_eq_of_sigma s60480]
  rcases analytic_bracket_witness_constructed with
    ⟨⟨gammaLo, gammaHi⟩, ⟨t5040Lo, t5040Hi⟩, ⟨r5040Lo, r5040Hi⟩,
      ⟨t10080Lo, t10080Hi⟩, ⟨r10080Lo, r10080Hi⟩,
      ⟨t15120Lo, t15120Hi⟩, ⟨r15120Lo, r15120Hi⟩,
      ⟨t20160Lo, t20160Hi⟩, ⟨r20160Lo, r20160Hi⟩,
      ⟨t30240Lo, t30240Hi⟩, ⟨r30240Lo, r30240Hi⟩,
      ⟨t60480Lo, t60480Hi⟩, ⟨r60480Lo, r60480Hi⟩⟩
  norm_num at gammaLo gammaHi t5040Lo t5040Hi r5040Lo r5040Hi
  norm_num at t10080Lo t10080Hi r10080Lo r10080Hi
  norm_num at t15120Lo t15120Hi r15120Lo r15120Hi
  norm_num at t20160Lo t20160Hi r20160Lo r20160Hi
  norm_num at t30240Lo t30240Hi r30240Lo r30240Hi
  norm_num at t60480Lo t60480Hi r60480Lo r60480Hi ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The certified outward rational bracket for the logarithmic margin at 5040. -/
theorem robin_log_margin_5040_bracket :
    (-5545 / 1000000 : ℝ) < robinLogMargin 5040 ∧
      robinLogMargin 5040 < (-5542 / 1000000 : ℝ) :=
  ⟨robin_log_margin_5040_point_bounds.1, robin_log_margin_5040_point_bounds.2.1⟩

/-- Every point of the positive 5040 cell has logarithmic margin above `1/100`. -/
theorem robin_log_margin_5040_cell_plus_gt {n : ℕ} (hn : n ∈ goldenCellPlus 5040) :
    (1 / 100 : ℝ) < robinLogMargin n := by
  obtain ⟨_, _, h10080, h15120, h20160, h30240, h60480⟩ :=
    robin_log_margin_5040_point_bounds
  rw [golden_cell_plus_5040_identity] at hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact h10080
  · exact h15120
  · exact h20160
  · exact h30240
  · exact h60480

private theorem golden_cell_5040_diff_eq_plus :
    goldenCell 5040 \ {5040} = goldenCellPlus 5040 := by
  rw [goldenCellPlus, golden_cell_5040_identity]
  ext n
  simp
  omega

/-- Theorem 11.2: the 5040 margin is negative and every other cell margin exceeds 0.0047. -/
theorem robin_log_margin_5040_cell_certificate :
    robinLogMargin 5040 < 0 ∧
      ∀ n ∈ goldenCell 5040 \ {5040}, (47 / 10000 : ℝ) < robinLogMargin n := by
  constructor
  · nlinarith [robin_log_margin_5040_bracket.2]
  · intro n hn
    rw [golden_cell_5040_diff_eq_plus] at hn
    nlinarith [robin_log_margin_5040_cell_plus_gt hn]

/-- The chapter-14 critical margin of the 5040 cell exceeds `1/100`. -/
theorem cell_minimum_5040_gt_one_hundredth :
    (1 / 100 : ℝ) < cellMinimum 5040 := by
  obtain ⟨_, _, h10080, h15120, h20160, h30240, h60480⟩ :=
    robin_log_margin_5040_point_bounds
  unfold cellMinimum
  rw [golden_cell_plus_5040_identity]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rw [show sInf ({robinLogMargin 10080, robinLogMargin 15120, robinLogMargin 20160,
      robinLogMargin 30240, robinLogMargin 60480} : Set ℝ) =
        min (robinLogMargin 10080) (min (robinLogMargin 15120)
          (min (robinLogMargin 20160) (min (robinLogMargin 30240)
            (robinLogMargin 60480)))) by simp]
  exact lt_min h10080 (lt_min h15120 (lt_min h20160 (lt_min h30240 h60480)))

/-- The requested unconditional instance `delta_cell(5040) > 0`. -/
theorem cell_minimum_5040_pos : 0 < cellMinimum 5040 := by
  nlinarith [cell_minimum_5040_gt_one_hundredth]

example :
    2 ^ 4 * 3 ^ 2 * 5 * 7 = 5040 ∧ 2 ^ 5 * 3 ^ 2 * 5 * 7 = 10080 ∧
    2 ^ 4 * 3 ^ 3 * 5 * 7 = 15120 ∧ 2 ^ 6 * 3 ^ 2 * 5 * 7 = 20160 ∧
    2 ^ 5 * 3 ^ 3 * 5 * 7 = 30240 ∧ 2 ^ 6 * 3 ^ 3 * 5 * 7 = 60480 := by norm_num

example :
    5040 ∈ goldenCell 5040 ∧ 10080 ∈ goldenCell 5040 ∧
    15120 ∈ goldenCell 5040 ∧ 20160 ∈ goldenCell 5040 ∧
    30240 ∈ goldenCell 5040 ∧ 60480 ∈ goldenCell 5040 := by
  rw [golden_cell_5040_identity]
  simp

example :
    31 * 13 * 6 * 8 = 19344 ∧ 63 * 13 * 6 * 8 = 39312 ∧
    31 * 40 * 6 * 8 = 59520 ∧ 127 * 13 * 6 * 8 = 79248 ∧
    63 * 40 * 6 * 8 = 120960 ∧ 127 * 40 * 6 * 8 = 243840 := by norm_num

example : ∃ n : ℕ, n ∈ goldenCellPlus 5040 := by
  refine ⟨10080, ?_⟩
  rw [golden_cell_plus_5040_identity]
  simp

#print axioms goldenWeight
#print axioms goldenBaseExponent
#print axioms goldenBaseExponent_eq_zero_iff
#print axioms goldenBaseExponent_eq_one_iff
#print axioms goldenBaseExponent_eq_two_iff
#print axioms goldenBaseExponent_eq_four_iff
#print axioms goldenFactorization
#print axioms goldenObservation
#print axioms goldenCell
#print axioms goldenCellPlus
#print axioms golden_cell_5040_identity
#print axioms goldenCellPlus_finite
#print axioms sigma_5040_cell_values
#print axioms tripleLog
#print axioms logSigmaRatio
#print axioms robinLogMargin
#print axioms robinAdditiveMargin
#print axioms cellMinimum
#print axioms cellMinimum_mem
#print axioms RelaxedAnalyticBracketWitness
#print axioms analytic_bracket_witness_constructed
#print axioms robin_log_margin_5040_point_bounds
#print axioms robin_log_margin_5040_bracket
#print axioms robin_log_margin_5040_cell_plus_gt
#print axioms robin_log_margin_5040_cell_certificate
#print axioms cell_minimum_5040_gt_one_hundredth
#print axioms cell_minimum_5040_pos

end D5.S3.Arith.GoldenResource.GoldenCell5040Certificate
