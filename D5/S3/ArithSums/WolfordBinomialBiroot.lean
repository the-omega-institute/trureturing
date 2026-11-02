/- GID: D5/S3/ArithSums/WolfordBinomialBiroot
   generality: G
   mirror-B: D5/B/S3/ArithSums/WolfordBinomialBiroot
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Positive weighted binomial multisections and the original generalized biroot quotient. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Weighted binomial residue sums on finite cyclic groups. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.WolfordBinomialBiroot

open scoped BigOperators Topology
open Filter Matrix

variable {n : ℕ} [NeZero n]

private def shift : Matrix (ZMod n) (ZMod n) ℝ :=
  fun i j => if i + 1 = j then 1 else 0

private theorem shift_pow (m : ℕ) (i j : ZMod n) :
    (shift ^ m) i j = if i + (m : ZMod n) = j then 1 else 0 := by
  induction m generalizing i j with
  | zero => simp [Matrix.one_apply]
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [shift, ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [ih]
    congr 1
    push_cast
    ring_nf

private def walk (a b : ℝ) : Matrix (ZMod n) (ZMod n) ℝ :=
  a • 1 + b • shift

private theorem walk_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (i j : ZMod n) : 0 ≤ walk a b i j := by
  simp only [walk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  apply add_nonneg
  · exact mul_nonneg ha (by simp [Matrix.one_apply]; split_ifs <;> norm_num)
  · exact mul_nonneg hb (by simp [shift]; split_ifs <;> norm_num)

private theorem walk_stochastic (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : walk (n := n) a b ∈ Matrix.rowStochastic ℝ (ZMod n) := by
  apply Matrix.mem_rowStochastic_iff_sum.mpr
  refine ⟨walk_nonneg a b ha hb, ?_⟩
  intro i
  simpa [walk, shift, Matrix.one_apply, Finset.sum_add_distrib,
    Finset.mul_sum] using hab

private theorem matrix_mul_nat (A : Matrix (ZMod n) (ZMod n) ℝ) (k : ℕ) :
    A * (k : Matrix (ZMod n) (ZMod n) ℝ) = (k : ℝ) • A := by
  ext i j
  simp [Matrix.mul_apply, Matrix.natCast_apply, Matrix.smul_apply, mul_ite, mul_comm]

private theorem walk_pow (a b : ℝ) (m : ℕ) (i j : ZMod n) :
    (walk a b ^ m) i j = ∑ k ∈ Finset.range (m + 1),
      (m.choose k : ℝ) * a ^ (m-k) * b ^ k *
        (if i + (k : ZMod n) = j then 1 else 0) := by
  have hc : Commute (b • (shift : Matrix (ZMod n) (ZMod n) ℝ)) (a • 1) :=
    ((Commute.one_right shift).smul_left b).smul_right a
  rw [walk, add_comm, hc.add_pow]
  simp_rw [smul_pow, one_pow, Matrix.smul_mul, Matrix.mul_smul, mul_one, matrix_mul_nat]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, shift_pow]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem walk_primitive (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Matrix.IsPrimitive (walk (n := n) a b) := by
  refine ⟨walk_nonneg a b ha.le hb.le, n, NeZero.pos n, ?_⟩
  intro i j
  rw [walk_pow]
  apply (Finset.sum_pos_iff_of_nonneg ?_).mpr
  · refine ⟨(j-i).val, Finset.mem_range.mpr (by have := (j-i).val_lt; omega), ?_⟩
    have hv : i + ((j-i).val : ZMod n) = j := by simp
    rw [if_pos hv, mul_one]
    apply mul_pos
    · apply mul_pos
      · exact_mod_cast Nat.choose_pos (by have := (j-i).val_lt; omega)
      · positivity
    · positivity
  · intro k hk
    apply mul_nonneg
    · positivity
    · split_ifs <;> norm_num

private theorem walk_column (a b : ℝ) (j : ZMod n) :
    ∑ i, walk a b i j = a + b := by
  simp only [walk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, shift, ← eq_sub_iff_add_eq]
  simp [Finset.sum_add_distrib, mul_ite]

private theorem walk_limit (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) :
    Tendsto (fun m : ℕ => walk (n := n) a b ^ m) atTop
      (𝓝 (fun _ _ => 1 / (n : ℝ))) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  let μ : ZMod n → ℝ := fun _ => 1 / (n : ℝ)
  have hμnonneg : ∀ j, 0 ≤ μ j := by intro j; dsimp [μ]; positivity
  have hμsum : ∑ j, μ j = 1 := by simp [μ, hn]
  have hμstat : μ ᵥ* walk a b = μ := by
    ext j
    simp only [Matrix.vecMul, dotProduct, μ, ← Finset.mul_sum]
    rw [walk_column, hab, mul_one]
  obtain ⟨ν, hnν, hsν, htν, huν, hlν⟩ :=
    D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteStochasticMixing.primitive_convergence
      (walk (n := n) a b) (walk_stochastic a b ha.le hb.le hab) (walk_primitive a b ha hb)
  have heq := huν μ hμnonneg hμsum hμstat
  simpa [← heq, μ] using hlν

private def residue (m : ℕ) (c r : ℝ) (j : ZMod n) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * c ^ (m-k) * r ^ k *
    (if (k : ZMod n) = j then 1 else 0)

private theorem normalized_residue (m : ℕ) (c r : ℝ) (j : ZMod n) :
    (walk (c / (c+r)) (r / (c+r)) ^ m) 0 j = residue m c r j / (c+r)^m := by
  rw [walk_pow, residue, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
  have hp : (c+r)^(m-k) * (c+r)^k = (c+r)^m := by
    rw [← pow_add, Nat.sub_add_cancel hkm]
  simp only [zero_add, div_pow]
  rw [← mul_div_assoc, div_mul_div_comm, hp, div_mul_eq_mul_div]

private theorem residue_limit (c r : ℝ) (hc : 0 < c) (hr : 0 < r) (j : ZMod n) :
    Tendsto (fun m : ℕ => residue m c r j / (c+r)^m) atTop (𝓝 (1 / (n : ℝ))) := by
  have ht : 0 < c+r := add_pos hc hr
  have hl := walk_limit (n := n) (c/(c+r)) (r/(c+r))
    (div_pos hc ht) (div_pos hr ht) (by rw [← add_div]; exact div_self ht.ne')
  have he := ((tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hl) 0)) j)
  simpa only [normalized_residue] using he

private theorem residue_ratio_limit (c r : ℝ) (hc : 0 < c) (hr : 0 < r)
    (i j : ZMod n) :
    Tendsto (fun m : ℕ => r * residue m c r i / residue m c r j) atTop (𝓝 r) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hlim := (residue_limit c r hc hr i).div (residue_limit c r hc hr j)
    (one_div_ne_zero hn)
  have heq (m : ℕ) :
      (residue m c r i / (c+r)^m) / (residue m c r j / (c+r)^m) =
        residue m c r i / residue m c r j := by
    exact div_div_div_cancel_right₀ (pow_ne_zero m (add_pos hc hr).ne') _ _
  have h1 : Tendsto (fun m : ℕ => residue m c r i / residue m c r j) atTop (𝓝 1) := by
    simpa only [Pi.div_apply, heq, div_self (one_div_ne_zero hn)] using hlim
  simpa [mul_div_assoc] using h1.const_mul r

/-- The exact rational ceiling used in the original source. -/
def ceiling (m n : ℕ) : ℕ := ⌈(m : ℚ) / (n : ℚ)⌉₊

/-- Original inclusive numerator, with signed integer exponents. -/
def numerator (x c : ℝ) (n m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (ceiling m n + 1),
    x^k * c^((m : ℤ) - (n : ℤ)*k) * (m.choose (n*k) : ℝ)

/-- Original inclusive denominator, with signed integer exponents. -/
def denominator (x c : ℝ) (n m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range ((ceiling m n - 1) + 1),
    x^k * c^((m : ℤ) - (n : ℤ)*k - 1) * (m.choose (n*k+1) : ℝ)

/-- The source quotient on positive indices, explicitly totalized at zero. -/
def beta (x c : ℝ) (n m : ℕ) : ℝ :=
  if m = 0 then 0 else numerator x c n m / denominator x c n m

private theorem ceiling_bound (m : ℕ) : m ≤ n * ceiling m n := by
  have hn : (0 : ℚ) < n := by exact_mod_cast NeZero.pos n
  have h := (Nat.le_ceil ((m : ℚ) / n))
  have h' : (m : ℚ) ≤ (n : ℚ) * (ceiling m n : ℚ) := by
    dsimp [ceiling]
    exact (div_le_iff₀ hn).mp h |>.trans_eq (mul_comm _ _)
  exact_mod_cast h'

private theorem multisection (m d K : ℕ) (hd : d < n) (f : ℕ → ℝ)
    (hf : ∀ l, m < l → f l = 0)
    (hK : ∀ l, l ≤ m → l % n = d → l / n < K) :
    (∑ k ∈ Finset.range K, f (n*k+d)) =
      ∑ l ∈ Finset.range (m+1), f l *
        (if (l : ZMod n) = (d : ZMod n) then 1 else 0) := by
  classical
  apply Finset.sum_bij_ne_zero (fun k _ _ => n*k+d)
  · intro k hk hne
    apply Finset.mem_range.mpr
    by_contra h
    have hz := hf (n*k+d) (by omega)
    exact hne hz
  · intro k hk hne k' hk' hne' heq
    exact Nat.eq_of_mul_eq_mul_left (NeZero.pos n) (Nat.add_right_cancel heq)
  · intro l hl hne
    have he : (l : ZMod n) = (d : ZMod n) := by
      by_contra h
      simp [h] at hne
    have hm : l % n = d := by
      have ht := (ZMod.natCast_eq_natCast_iff' l d n).mp he
      simpa [Nat.mod_eq_of_lt hd] using ht
    have heq : n*(l/n)+d = l := by
      have ht := Nat.mod_add_div l n
      omega
    refine ⟨l/n, Finset.mem_range.mpr (hK l (by have := Finset.mem_range.mp hl; omega) hm), ?_, heq⟩
    rw [heq]
    intro hz
    simp [hz] at hne
  · intro k hk hne
    have he : ((n*k+d : ℕ) : ZMod n) = (d : ZMod n) := by simp
    simp [he]

end D5.S3.ArithSums.WolfordBinomialBiroot
