/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeDigits
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeDigits
   mirror-E: none(waiver:integer-digit-recovery)
   anchors: []
   utility: none
   digest: Nested positive integer cylinders recover the computed continued fraction. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangePrefix
import D5.S1.Depth.ContinuedFractions.GaussInverseStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open GenContFract
open D5.S1.Depth.ContinuedFractions.GaussInverseStep

/-- Every point in all cylinders of an infinite positive integer stream has exactly that
computed expansion. Consecutive cylinder tails satisfy the Gauss recurrence; looking one
step further makes every tail interior, so the floor algorithm never terminates. -/
theorem stream_digit_recovery (g : GenContFract ℝ) (hhead : g.h = 0)
    (hg : ∀ i, ∃ a : ℕ, 0 < a ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩)
    (x : ℝ)
    (hx : ∀ n, x ∈ GenContFract.compExactValue (g.contsAux n) (g.conts n) ''
      Set.Icc (0 : ℝ) 1) :
    GenContFract.of x = g := by
  classical
  let a (n : ℕ) : ℕ := (hg n).choose
  have ha (n : ℕ) : 0 < a n ∧ g.s.get? n = some ⟨1, (a n : ℝ)⟩ :=
    (hg n).choose_spec
  let T (n : ℕ) := GenContFract.compExactValue (g.contsAux n) (g.conts n)
  have htails : ∀ n, ∃ z ∈ Set.Icc (0 : ℝ) 1, T n z = x := hx
  choose z hz he using htails
  have hreal : ∀ i, ∃ b : ℝ, 1 ≤ b ∧ g.s.get? i = some ⟨1, b⟩ := by
    intro i
    exact ⟨a i, by exact_mod_cast (ha i).1, (ha i).2⟩
  have hform : ∀ n w, T n w =
      (g.nums n + (g.contsAux n).a * w) / (g.dens n + (g.contsAux n).b * w) := by
    intro n w
    by_cases hw : w = 0
    · simp [T, hw, GenContFract.compExactValue, GenContFract.num_eq_conts_a,
        GenContFract.den_eq_conts_b]
    · simp only [T, GenContFract.compExactValue, if_neg hw, GenContFract.nextConts,
        GenContFract.nextNum, GenContFract.nextDen, one_mul,
        GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b]
      rw [← mul_div_mul_right _ _ hw]
      congr 1 <;> field_simp [hw]
  have hq : ∀ n, 0 < g.dens n := by
    intro n
    have hf : 0 < (Nat.fib (n + 1) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)
    exact lt_of_lt_of_le hf (prefix_geometry g n (fun i _ => hreal i)).1
  have hprev : ∀ n, 0 ≤ (g.contsAux n).b := by
    intro n
    cases n with
    | zero => simp [GenContFract.contsAux]
    | succ n =>
        simpa only [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
          using (hq n).le
  have hden : ∀ n w, 0 ≤ w → 0 < g.dens n + (g.contsAux n).b * w := by
    intro n w hw
    exact add_pos_of_pos_of_nonneg (hq n) (mul_nonneg (hprev n) hw)
  have hstep : ∀ n w, w ∈ Set.Icc (0 : ℝ) 1 →
      T (n + 1) w = T n (1 / ((a n : ℝ) + w)) := by
    intro n w hw
    have hap : 0 < (a n : ℝ) + w := by
      exact add_pos_of_pos_of_nonneg (by exact_mod_cast (ha n).1) hw.1
    have ht : 0 ≤ 1 / ((a n : ℝ) + w) := (one_div_pos.mpr hap).le
    have hd := hden n _ ht
    have hn := hden (n + 1) w hw.1
    rw [hform, hform]
    simp only [GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b,
      GenContFract.nth_cont_eq_succ_nth_contAux] at hn hd ⊢
    rw [GenContFract.contsAux_recurrence (ha n).2 rfl rfl] at hn ⊢
    simp only [one_mul] at hn ⊢
    apply (div_eq_div_iff (ne_of_gt hn) (ne_of_gt hd)).2
    field_simp [ne_of_gt hap]
    ring
  have hrec : ∀ n, z n = 1 / ((a n : ℝ) + z (n + 1)) := by
    intro n
    have hap : 0 < (a n : ℝ) + z (n + 1) := by
      exact add_pos_of_pos_of_nonneg (by exact_mod_cast (ha n).1) (hz (n + 1)).1
    have ht : 1 / ((a n : ℝ) + z (n + 1)) ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨(one_div_pos.mpr hap).le, (div_le_one hap).mpr ?_⟩
      have haone : (1 : ℝ) ≤ a n := by exact_mod_cast (ha n).1
      linarith [(hz (n + 1)).1]
    have heq : T n (z n) = T n (1 / ((a n : ℝ) + z (n + 1))) := by
      rw [← hstep n _ (hz (n + 1)), he n, he (n + 1)]
    have hdiff := ((prefix_geometry g n (fun i _ => hreal i)).2
      (z n) (hz n) _ ht).1
    change |T n (z n) - T n (1 / ((a n : ℝ) + z (n + 1)))| = _ at hdiff
    rw [heq, sub_self, abs_zero] at hdiff
    have hp := mul_pos (hden n _ (hz n).1) (hden n _ ht.1)
    have habs : |z n - 1 / ((a n : ℝ) + z (n + 1))| = 0 := by
      exact (div_eq_zero_iff.mp hdiff.symm).resolve_right (ne_of_gt hp)
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  have hzpos : ∀ n, 0 < z n := by
    intro n
    rw [hrec]
    apply one_div_pos.mpr
    exact add_pos_of_pos_of_nonneg (by exact_mod_cast (ha n).1) (hz (n + 1)).1
  have hzlt : ∀ n, z n < 1 := by
    intro n
    rw [hrec]
    have haone : (1 : ℝ) ≤ a n := by exact_mod_cast (ha n).1
    have hp : 1 < (a n : ℝ) + z (n + 1) := by linarith [hzpos (n + 1)]
    exact (div_lt_one (by linarith : 0 < (a n : ℝ) + z (n + 1))).mpr hp
  have hz0 : z 0 = x := by
    simpa [hform, GenContFract.contsAux, GenContFract.zeroth_num_eq_h,
      GenContFract.zeroth_den_eq_one, hhead] using he 0
  have hfloor : ∀ n, ⌊(z n)⁻¹⌋ = (a n : ℤ) := by
    intro n
    rw [hrec n]
    simpa only [one_div] using gauss_inverse_step_recovers_quotient (a n)
      ⟨(hzpos (n + 1)).le, hzlt (n + 1)⟩
  have hinv : ∀ n, (z n)⁻¹ = (a n : ℝ) + z (n + 1) := by
    intro n
    rw [hrec n]
    simp only [one_div, inv_inv]
  have hpair : ∀ n, IntFractPair.of (z n)⁻¹ = ⟨(a n : ℤ), z (n + 1)⟩ := by
    intro n
    simp only [IntFractPair.of, Int.fract]
    rw [hfloor n, hinv n]
    simp
  have hstream : ∀ n, ∃ b : ℤ,
      IntFractPair.stream x n = some ⟨b, z n⟩ := by
    intro n
    induction n with
    | zero =>
        refine ⟨0, ?_⟩
        have hfx : ⌊x⌋ = (0 : ℤ) :=
          Int.floor_eq_zero_iff.mpr ⟨hz0 ▸ (hzpos 0).le, hz0 ▸ hzlt 0⟩
        simp only [IntFractPair.stream, IntFractPair.of, Int.fract, hfx,
          Int.cast_zero, sub_zero, hz0]
    | succ n ih =>
        obtain ⟨b, hb⟩ := ih
        refine ⟨a n, ?_⟩
        rw [IntFractPair.stream_succ_of_some hb (ne_of_gt (hzpos n))]
        rw [hpair n]
  have hs : (GenContFract.of x).s = g.s := by
    apply Stream'.Seq.ext
    intro n
    obtain ⟨b, hb⟩ := hstream n
    have hsnext := IntFractPair.stream_succ_of_some hb (ne_of_gt (hzpos n))
    have hsnext' : IntFractPair.stream x (n + 1) =
        some ⟨(a n : ℤ), z (n + 1)⟩ := by
      simpa only [hpair n] using hsnext
    rw [GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hsnext', (ha n).2]
    simp
  have hh : (GenContFract.of x).h = g.h := by
    rw [GenContFract.of_h_eq_floor, hhead]
    have hfx : ⌊x⌋ = (0 : ℤ) :=
      Int.floor_eq_zero_iff.mpr ⟨hz0 ▸ (hzpos 0).le, hz0 ▸ hzlt 0⟩
    simp [hfx]
  exact GenContFract.ext hh hs

end D5.S1.Words.KAbelianLagrange
