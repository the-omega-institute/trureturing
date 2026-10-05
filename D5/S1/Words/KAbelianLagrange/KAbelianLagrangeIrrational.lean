/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeIrrational
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeIrrational
   mirror-E: none(waiver:irrational-value-supplier)
   anchors: []
   utility: none
   digest: Positive integer digit streams have irrational values in the open unit interval. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open GenContFract Filter
open scoped Topology

/-- Integrality rules out rational limits of infinite positive simple streams.
The proof separates a hypothetical rational from each convergent by its integer
cross product, then contradicts that separation using the next denominator. -/
theorem integer_stream_value (g : GenContFract ℝ) (hhead : g.h = 0)
    (hg : ∀ i, ∃ a : ℕ, 0 < a ∧ g.s.get? i = some ⟨1, (a : ℝ)⟩) :
    ∃ x : ℝ, Irrational x ∧ 0 < x ∧ x < 1 ∧ Tendsto g.convs atTop (𝓝 x) ∧
      ∀ n, x ∈ GenContFract.compExactValue (g.contsAux n) (g.conts n) ''
        Set.Icc (0 : ℝ) 1 := by
  have hreal : ∀ i, ∃ a : ℝ, 1 ≤ a ∧ g.s.get? i = some ⟨1, a⟩ := by
    intro i
    obtain ⟨a, ha, hs⟩ := hg i
    exact ⟨a, by exact_mod_cast ha, hs⟩
  obtain ⟨x, hx, _⟩ := positive_stream_value g hreal
  have hform : ∀ n z,
      GenContFract.compExactValue (g.contsAux n) (g.conts n) z =
        (g.nums n + (g.contsAux n).a * z) / (g.dens n + (g.contsAux n).b * z) := by
    intro n z
    by_cases hz : z = 0
    · simp [hz, GenContFract.compExactValue, GenContFract.num_eq_conts_a,
        GenContFract.den_eq_conts_b]
    · simp only [GenContFract.compExactValue, if_neg hz, GenContFract.nextConts,
        GenContFract.nextNum, GenContFract.nextDen, one_mul,
        GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b]
      rw [← mul_div_mul_right _ _ hz]
      congr 1 <;> field_simp [hz]
  have hq : ∀ n, 0 < g.dens n := by
    intro n
    have hf : 0 < (Nat.fib (n + 1) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)
    exact lt_of_lt_of_le hf (prefix_geometry g n (fun i _ => hreal i)).1
  have hint : ∀ n, ∃ p q : ℤ, g.contsAux n = ⟨(p : ℝ), (q : ℝ)⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        rcases n with (_ | _ | n)
        · exact ⟨1, 0, by simp [GenContFract.contsAux]⟩
        · exact ⟨0, 1, by simp [GenContFract.contsAux, hhead]⟩
        · obtain ⟨p, q, hpq⟩ := ih n (by omega)
          obtain ⟨p', q', hpq'⟩ := ih (n + 1) (by omega)
          obtain ⟨a, _ha, hs⟩ := hg n
          refine ⟨(a : ℤ) * p' + p, (a : ℤ) * q' + q, ?_⟩
          rw [GenContFract.contsAux_recurrence hs hpq hpq']
          simp
  have hirr : Irrational x := by
    by_contra hr
    obtain ⟨r, hxr⟩ := exists_rat_of_not_irrational hr
    let n := r.den + 5
    have hnext : (r.den : ℝ) < g.dens (n + 1) := by
      have hf : r.den < Nat.fib (n + 2) :=
        lt_of_lt_of_le (by dsimp [n]; omega) (Nat.le_fib_self (by dsimp [n]; omega))
      exact lt_of_lt_of_le (by exact_mod_cast hf)
        (prefix_geometry g (n + 1) (fun i _ => hreal i)).1
    obtain ⟨z, hz, hxz⟩ := hx.2 (n + 1)
    have hD : 0 < g.dens (n + 1) + g.dens n * z :=
      add_pos_of_pos_of_nonneg (hq (n + 1)) (mul_nonneg (hq n).le hz.1)
    have hdet : |g.nums n * g.dens (n + 1) - g.dens n * g.nums (n + 1)| = 1 := by
      have hp : (∏ i ∈ Finset.range (n + 1), -(g.partNums.get? i).getD 0) =
          (-1 : ℝ) ^ (n + 1) := by
        calc
          _ = ∏ _i ∈ Finset.range (n + 1), (-1 : ℝ) := by
            apply Finset.prod_congr rfl
            intro i _hi
            obtain ⟨a, _ha, hs⟩ := hg i
            rw [GenContFract.partNum_eq_s_a hs]
            rfl
          _ = _ := by simp
      rw [g.determinant, hp, abs_pow, abs_neg, abs_one, one_pow]
    have heq : x - g.convs n =
        -(g.nums n * g.dens (n + 1) - g.dens n * g.nums (n + 1)) /
          (g.dens n * (g.dens (n + 1) + g.dens n * z)) := by
      rw [← hxz, hform, GenContFract.conv_eq_num_div_den]
      simp only [← GenContFract.nth_cont_eq_succ_nth_contAux,
        ← GenContFract.num_eq_conts_a, ← GenContFract.den_eq_conts_b]
      rw [div_sub_div _ _ (ne_of_gt hD) (ne_of_gt (hq n)),
        mul_comm (g.dens n) (g.dens (n + 1) + g.dens n * z)]
      congr 1
      ring
    have herror : |x - g.convs n| =
        1 / (g.dens n * (g.dens (n + 1) + g.dens n * z)) := by
      rw [heq, abs_div, abs_neg, hdet, abs_of_pos (mul_pos (hq n) hD)]
    have herrorpos : 0 < |x - g.convs n| := by
      rw [herror]
      exact one_div_pos.mpr (mul_pos (hq n) hD)
    obtain ⟨p, q, hpq⟩ := hint (n + 1)
    have hpn : g.nums n = (p : ℝ) := by
      simpa only [GenContFract.num_eq_conts_a,
        GenContFract.nth_cont_eq_succ_nth_contAux] using congrArg Pair.a hpq
    have hqn : g.dens n = (q : ℝ) := by
      simpa only [GenContFract.den_eq_conts_b,
        GenContFract.nth_cont_eq_succ_nth_contAux] using congrArg Pair.b hpq
    have hb : 0 < (r.den : ℝ) := by exact_mod_cast r.pos
    have hsepEq : |x - g.convs n| =
        |((r.num * q - (r.den : ℤ) * p : ℤ) : ℝ)| / ((r.den : ℝ) * g.dens n) := by
      rw [hxr, Rat.cast_def, GenContFract.conv_eq_num_div_den, hpn,
        div_sub_div _ _ (ne_of_gt hb) (ne_of_gt (hq n)), abs_div,
        abs_of_pos (mul_pos hb (hq n))]
      congr 2
      rw [hqn]
      push_cast
      ring
    have hnum_ne : r.num * q - (r.den : ℤ) * p ≠ 0 := by
      intro he
      rw [hsepEq, he] at herrorpos
      simp at herrorpos
    have hnum : (1 : ℝ) ≤ |((r.num * q - (r.den : ℤ) * p : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hnum_ne
    have hsep : 1 / ((r.den : ℝ) * g.dens n) ≤ |x - g.convs n| := by
      rw [hsepEq]
      exact div_le_div_of_nonneg_right hnum (mul_pos hb (hq n)).le
    have hstrict : |x - g.convs n| < 1 / ((r.den : ℝ) * g.dens n) := by
      rw [herror]
      apply one_div_lt_one_div_of_lt (mul_pos hb (hq n))
      have hd : (r.den : ℝ) < g.dens (n + 1) + g.dens n * z :=
        lt_of_lt_of_le hnext (le_add_of_nonneg_right (mul_nonneg (hq n).le hz.1))
      calc
        (r.den : ℝ) * g.dens n = g.dens n * (r.den : ℝ) := mul_comm _ _
        _ < _ := mul_lt_mul_of_pos_left hd (hq n)
    exact (not_lt_of_ge hsep) hstrict
  have hx01 : x ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨z, hz, he⟩ := hx.2 0
    have he' : z = x := by
      rw [hform] at he
      simpa [GenContFract.contsAux, GenContFract.zeroth_num_eq_h,
        GenContFract.zeroth_den_eq_one, hhead] using he
    exact he' ▸ hz
  exact ⟨x, hirr, lt_of_le_of_ne hx01.1 hirr.ne_zero.symm,
    lt_of_le_of_ne hx01.2 hirr.ne_one, hx.1, hx.2⟩

end D5.S1.Words.KAbelianLagrange
