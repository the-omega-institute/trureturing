/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeReverse
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeReverse
   mirror-E: none(waiver:reversed-prefix-supplier)
   anchors: [mathlib/module/Mathlib.Data.List.OfFn]
   utility: none
   digest: Reversing a positive simple prefix gives the preceding denominator ratio. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangePrefix
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open GenContFract

/-- Evaluation of the reversed finite prefix is the ratio of its two last denominators.
The proof follows the newly prepended digit under reversal and the forward continuant
recurrence in a single induction. Real digits are allowed. -/
theorem reversed_prefix_ratio (g : GenContFract ℝ) (a : ℕ → ℝ)
    (ha : ∀ i, 1 ≤ a i) (hg : ∀ i, g.s.get? i = some ⟨1, a i⟩) (n : ℕ) :
    GenContFract.convs'Aux
      (Stream'.Seq.ofList (List.ofFn (fun i : Fin n => (⟨1, a i⟩ : Pair ℝ))).reverse) n =
        (g.contsAux n).b / g.dens n := by
  have hq : ∀ m, 0 < g.dens m := by
    intro m
    have hf : 0 < (Nat.fib (m + 1) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos m)
    exact lt_of_lt_of_le hf
      (prefix_geometry g m (fun i _ => ⟨a i, ha i, hg i⟩)).1
  have hprev : ∀ m, 0 ≤ (g.contsAux m).b := by
    intro m
    cases m with
    | zero => simp [GenContFract.contsAux]
    | succ m =>
        simpa only [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
          using (hq m).le
  induction n with
  | zero => simp [GenContFract.contsAux, GenContFract.zeroth_den_eq_one]
  | succ n ih =>
      have hlist :
          (List.ofFn (fun i : Fin (n + 1) => (⟨1, a i⟩ : Pair ℝ))).reverse =
            ⟨1, a n⟩ :: (List.ofFn (fun i : Fin n => (⟨1, a i⟩ : Pair ℝ))).reverse := by
        rw [List.ofFn_succ', List.concat_eq_append, List.reverse_concat]
        rfl
      rw [hlist, Stream'.Seq.ofList_cons]
      simp only [GenContFract.convs'Aux, Stream'.Seq.head_cons,
        Stream'.Seq.tail_cons, one_div]
      rw [ih]
      have hrec : g.dens (n + 1) = a n * g.dens n + (g.contsAux n).b := by
        simp only [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux]
        rw [GenContFract.contsAux_recurrence (hg n) rfl rfl]
        simp
      have hden : 0 < a n + (g.contsAux n).b / g.dens n :=
        add_pos_of_pos_of_nonneg (lt_of_lt_of_le zero_lt_one (ha n))
          (div_nonneg (hprev n) (hq n).le)
      simp only [← GenContFract.nth_cont_eq_succ_nth_contAux,
        ← GenContFract.den_eq_conts_b]
      rw [hrec]
      rw [inv_eq_one_div]
      field_simp [ne_of_gt (hq n), ne_of_gt hden]

end D5.S1.Words.KAbelianLagrange
