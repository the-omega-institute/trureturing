/- GID: D5/S3/Arith/GoldenResource/RationalCapacityTailRealization
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/RationalCapacityTailRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cofinal divisible capacities fill rational tails and exact tail filling realizes every extended nonnegative total. -/
import D5.S3.Analytic.WeightedCapacity.DyadicTailFilling
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Arith.GoldenResource.RationalCapacityTailRealization

open D5.S3.Analytic.WeightedCapacity.DyadicTailFilling

/-- rational reading for a positive integral denominator row. -/
noncomputable def weightedRead (g : ℕ → ℕ) {A : ℕ → ℕ} (u : B A) : ℚ :=
  ∑ n ∈ u.property.toFinset, ((u.val n : ℕ) : ℚ) / (g n : ℚ)

/-- the mass strictly after the cutoff, including possible infinity. -/
noncomputable def tailMass (g A : ℕ → ℕ) (N : ℕ) : ENNReal :=
  ∑' n, if N < n then ENNReal.ofReal ((A n : ℝ) / (g n : ℝ)) else 0

/-- one positive threshold works for every modulus and cutoff. -/
def CofinalDivisibleCapacity (g A : ℕ → ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ d : ℕ, 0 < d → ∀ N : ℕ,
    ∃ n : ℕ, N < n ∧ d ∣ g n ∧ ε ≤ (A n : ℝ) / (g n : ℝ)

/-- exact nonnegative rational filling by a legal finite tail. -/
def FillsRationalTails (g A : ℕ → ℕ) : Prop :=
  ∀ q : ℚ, 0 ≤ q → ∀ N : ℕ, ∃ u : B A,
    (∀ n : ℕ, n ≤ N → (u.val n : ℕ) = 0) ∧ weightedRead g u = q

set_option maxHeartbeats 800000 in
/-- Cofinal divisible capacities fill every rational tail, and exact filling forces infinite tail mass. -/
theorem cofinal_capacity_rational_tail_filling (g A : ℕ → ℕ) (hg : ∀ n, 0 < g n) :
    (CofinalDivisibleCapacity g A → FillsRationalTails g A) ∧
    (FillsRationalTails g A → ∀ N : ℕ, tailMass g A N = ⊤) := by
  classical
  constructor
  · rintro ⟨ε, hε, hcof⟩ q hq N
    obtain ⟨k, hk⟩ := exists_nat_gt (max ((q : ℝ) / ε) 0)
    have hk0 : 0 < k := by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hk)
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    let r : ℚ := q / k
    have hr0 : 0 ≤ r := div_nonneg hq (Nat.cast_nonneg _)
    have hrε : (r : ℝ) ≤ ε := by
      dsimp [r]
      push_cast
      apply (div_le_iff₀ hkR).mpr
      have h := (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_left _ _) hk)
      linarith
    let a := r.num.toNat
    let b := r.den
    have hab : (a : ℚ) / b = r := by
      dsimp [a, b]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr hr0)]
      exact r.num_div_den
    let S : Set ℕ := {n | N < n ∧ b ∣ g n ∧ ε ≤ (A n : ℝ) / g n}
    have hS : S.Infinite := by
      intro hf
      obtain ⟨n, hn, hd, hc⟩ := hcof b r.den_pos (max N (hf.toFinset.sup id))
      have hmem : n ∈ hf.toFinset := by
        exact hf.mem_toFinset.mpr ⟨lt_of_le_of_lt (le_max_left _ _) hn, hd, hc⟩
      have hle : n ≤ hf.toFinset.sup id := Finset.le_sup (f := id) hmem
      have := le_max_right N (hf.toFinset.sup id)
      omega
    obtain ⟨s, hsS, hsk⟩ := hS.exists_subset_card_eq k
    have hvalue (n : ℕ) (hn : n ∈ s) :
        ((a * (g n / b) : ℕ) : ℚ) / (g n : ℚ) = r := by
      rw [Nat.cast_mul, Nat.cast_div_charZero (hsS hn).2.1]
      calc
        (a : ℚ) * ((g n : ℚ) / b) / g n = ((a : ℚ) / b) *
            ((g n : ℚ) / g n) := by ring
        _ = r := by rw [div_self (by exact_mod_cast (hg n).ne'), mul_one, hab]
    have hcap (n : ℕ) (hn : n ∈ s) : a * (g n / b) ≤ A n := by
      have hv : ((a * (g n / b) : ℕ) : ℝ) / g n = (r : ℝ) := by
        simpa only [Rat.cast_div, Rat.cast_natCast] using
          congrArg (fun z : ℚ => (z : ℝ)) (hvalue n hn)
      have hle := hrε.trans (hsS hn).2.2
      rw [← hv] at hle
      exact_mod_cast (div_le_div_iff_of_pos_right (show (0 : ℝ) < g n by
        exact_mod_cast hg n)).mp hle
    let x : X A := fun n => if hn : n ∈ s then
      ⟨a * (g n / b), Nat.lt_succ_of_le (hcap n hn)⟩ else ⟨0, Nat.zero_lt_succ _⟩
    have hsupport : Function.support (fun n => (x n : ℕ)) ⊆ (s : Set ℕ) := by
      intro n hn
      by_contra h
      exact hn (by simp [x, show n ∉ s from h])
    let u : B A := ⟨x, s.finite_toSet.subset hsupport⟩
    refine ⟨u, ?_, ?_⟩
    · intro n hn
      have hns : n ∉ s := fun h => (Nat.not_lt_of_ge hn) (hsS h).1
      simp [u, x, hns]
    · unfold weightedRead
      calc
        _ = ∑ n ∈ s, ((x n : ℕ) : ℚ) / (g n : ℚ) := by
          apply Finset.sum_subset
          · intro n hn
            exact hsupport (by simpa using hn)
          · intro n _ hn
            have hz : (x n : ℕ) = 0 := by simpa [u] using hn
            simp [u, hz]
        _ = ∑ _n ∈ s, r := by
          apply Finset.sum_congr rfl
          intro n hn
          simpa [x, hn] using hvalue n hn
        _ = q := by
          simp only [Finset.sum_const, nsmul_eq_mul, hsk]
          dsimp [r]
          exact mul_div_cancel₀ q (by exact_mod_cast hk0.ne')
  · intro hfill N
    by_contra htop
    obtain ⟨k, hk⟩ := exists_nat_gt (tailMass g A N).toReal
    obtain ⟨u, huN, huq⟩ := hfill k (Nat.cast_nonneg _) N
    have hr : (weightedRead g u : ℝ) = k := by exact_mod_cast huq
    have hbound : ENNReal.ofReal (k : ℝ) ≤ tailMass g A N := by
      rw [← hr]
      unfold weightedRead
      simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_natCast]
      unfold tailMass
      rw [ENNReal.ofReal_sum_of_nonneg (by intros; positivity)]
      apply le_trans (Finset.sum_le_sum ?_) (ENNReal.sum_le_tsum _)
      intro n hn
      have hne : (u.val n : ℕ) ≠ 0 := by simpa using hn
      have hN : N < n := by
        by_contra h
        exact hne (huN n (by omega))
      rw [if_pos hN]
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast Nat.le_of_lt_succ (u.val n).isLt
    have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop).mpr hbound
    rw [ENNReal.toReal_ofReal (Nat.cast_nonneg _)] at hreal
    exact (not_le_of_gt hk) hreal

/-- the exact extended supremum of the inclusive real partial sums. -/
noncomputable def weightedTotal (g : ℕ → ℕ) {A : ℕ → ℕ} (x : X A) : ENNReal :=
  ⨆ N : ℕ, ENNReal.ofReal
    (∑ n ∈ Finset.range (N + 1), ((x n : ℕ) : ℝ) / (g n : ℝ))

/-- Every extended nonnegative real is the total reading of a capacity state when rational tails fill exactly. -/
theorem rational_tail_filling_full_range (g A : ℕ → ℕ) (hg : ∀ n, 0 < g n)
    (hfill : FillsRationalTails g A) :
    Function.Surjective (@weightedTotal g A) := by
  sorry

end D5.S3.Arith.GoldenResource.RationalCapacityTailRealization
