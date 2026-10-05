/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangePrefix
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangePrefix
   mirror-E: none(waiver:analytic-prefix-supplier)
   anchors: [mathlib/module/Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions]
   utility: none
   digest: Positive continued-fraction prefixes contract all real tails uniformly. -/

import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open GenContFract

/-- An arbitrary positive simple prefix has Fibonacci growth and contracts every pair
of tails in `[0,1]`. Only the first `n` digits are constrained, so finite tails and arbitrary
later extensions are covered by the same estimate. -/
theorem prefix_geometry (g : GenContFract ℝ) (n : ℕ)
    (hg : ∀ i < n, ∃ a : ℝ, 1 ≤ a ∧ g.s.get? i = some ⟨1, a⟩) :
    (Nat.fib (n + 1) : ℝ) ≤ g.dens n ∧
      ∀ z ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (0 : ℝ) 1,
        |GenContFract.compExactValue (g.contsAux n) (g.conts n) z -
          GenContFract.compExactValue (g.contsAux n) (g.conts n) w| =
            |z - w| / ((g.dens n + (g.contsAux n).b * z) *
              (g.dens n + (g.contsAux n).b * w)) ∧
          |GenContFract.compExactValue (g.contsAux n) (g.conts n) z -
          GenContFract.compExactValue (g.contsAux n) (g.conts n) w| ≤
            1 / (Nat.fib (n + 1) : ℝ) ^ 2 := by
  have hform : ∀ z : ℝ,
      GenContFract.compExactValue (g.contsAux n) (g.conts n) z =
        (g.nums n + (g.contsAux n).a * z) / (g.dens n + (g.contsAux n).b * z) := by
    intro z
    by_cases hz : z = 0
    · simp [hz, GenContFract.compExactValue, GenContFract.num_eq_conts_a,
        GenContFract.den_eq_conts_b]
    · simp only [GenContFract.compExactValue, if_neg hz, GenContFract.nextConts,
        GenContFract.nextNum, GenContFract.nextDen, one_mul,
        GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b]
      rw [← mul_div_mul_right _ _ hz]
      congr 1 <;> field_simp [hz]
  have hb : ∀ m, m ≤ n + 1 → (Nat.fib m : ℝ) ≤ (g.contsAux m).b := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hm
        rcases m with (_ | _ | m)
        · simp [GenContFract.contsAux]
        · simp [GenContFract.contsAux]
        · obtain ⟨a, ha, hs⟩ := hg m (by omega)
          have h₀ := ih m (by omega) (by omega)
          have h₁ := ih (m + 1) (by omega) (by omega)
          have hpos : 0 ≤ (g.contsAux (m + 1)).b :=
            le_trans (by positivity) h₁
          have hmul : (g.contsAux (m + 1)).b ≤ a * (g.contsAux (m + 1)).b :=
            le_mul_of_one_le_left hpos ha
          rw [GenContFract.contsAux_recurrence hs rfl rfl]
          simp only [one_mul, Nat.fib_add_two, Nat.cast_add]
          linarith
  have hq : (Nat.fib (n + 1) : ℝ) ≤ g.dens n := by
    simpa only [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
      using hb (n + 1) le_rfl
  have hf : 0 < (Nat.fib (n + 1) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)
  have hqpos : 0 < g.dens n := lt_of_lt_of_le hf hq
  have hprev : 0 ≤ (g.contsAux n).b := le_trans (by positivity) (hb n (by omega))
  have hdet : |(g.contsAux n).a * g.dens n - g.nums n * (g.contsAux n).b| = 1 := by
    cases n with
    | zero => simp [GenContFract.contsAux, GenContFract.zeroth_den_eq_one]
    | succ m =>
        have hp : (∏ i ∈ Finset.range (m + 1), -(g.partNums.get? i).getD 0) =
            (-1 : ℝ) ^ (m + 1) := by
          calc
            _ = ∏ _i ∈ Finset.range (m + 1), (-1 : ℝ) := by
              apply Finset.prod_congr rfl
              intro i hi
              obtain ⟨a, _ha, hs⟩ := hg i (Finset.mem_range.mp hi)
              rw [GenContFract.partNum_eq_s_a hs]
              rfl
            _ = _ := by simp
        have hd := g.determinant (n := m)
        rw [hp] at hd
        simpa only [GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b,
          GenContFract.nth_cont_eq_succ_nth_contAux, abs_pow, abs_neg, abs_one,
          one_pow, mul_comm] using congrArg abs hd
  refine ⟨hq, ?_⟩
  intro z hz w hw
  have hzden : 0 < g.dens n + (g.contsAux n).b * z :=
    add_pos_of_pos_of_nonneg hqpos (mul_nonneg hprev hz.1)
  have hwden : 0 < g.dens n + (g.contsAux n).b * w :=
    add_pos_of_pos_of_nonneg hqpos (mul_nonneg hprev hw.1)
  have heq : GenContFract.compExactValue (g.contsAux n) (g.conts n) z -
      GenContFract.compExactValue (g.contsAux n) (g.conts n) w =
      ((g.contsAux n).a * g.dens n - g.nums n * (g.contsAux n).b) * (z - w) /
        ((g.dens n + (g.contsAux n).b * z) *
          (g.dens n + (g.contsAux n).b * w)) := by
    rw [hform z, hform w]
    rw [div_sub_div _ _ (ne_of_gt hzden) (ne_of_gt hwden)]
    congr 1
    ring
  have heqabs : |GenContFract.compExactValue (g.contsAux n) (g.conts n) z -
          GenContFract.compExactValue (g.contsAux n) (g.conts n) w| =
      |z - w| / ((g.dens n + (g.contsAux n).b * z) *
        (g.dens n + (g.contsAux n).b * w)) := by
    rw [heq, abs_div, abs_mul, hdet, one_mul, abs_of_pos (mul_pos hzden hwden)]
  refine ⟨heqabs, ?_⟩
  rw [heqabs]
  have hzw : |z - w| ≤ 1 := abs_le.mpr ⟨by linarith [hw.2, hz.1],
    by linarith [hz.2, hw.1]⟩
  have hzge : (Nat.fib (n + 1) : ℝ) ≤ g.dens n + (g.contsAux n).b * z :=
    le_trans hq (le_add_of_nonneg_right (mul_nonneg hprev hz.1))
  have hwge : (Nat.fib (n + 1) : ℝ) ≤ g.dens n + (g.contsAux n).b * w :=
    le_trans hq (le_add_of_nonneg_right (mul_nonneg hprev hw.1))
  have hprod : (Nat.fib (n + 1) : ℝ) ^ 2 ≤
      (g.dens n + (g.contsAux n).b * z) * (g.dens n + (g.contsAux n).b * w) := by
    simpa only [pow_two] using mul_le_mul hzge hwge hf.le hzden.le
  exact le_trans (div_le_div_of_nonneg_right hzw (mul_pos hzden hwden).le)
    (one_div_le_one_div_of_le (sq_pos_of_pos hf) hprod)

end D5.S1.Words.KAbelianLagrange
