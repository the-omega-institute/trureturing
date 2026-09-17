/- GID: D5/S3/Weil/Separator/LiteralRationalBoundaryGrid
   generality: G
   mirror-B: D5/B/S3/Weil/Separator/LiteralRationalBoundaryGrid
   mirror-E: none(waiver:certified-rational-boundary-producer)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/LiteralRationalBoundaryCertified.boundaryCertified; instance=D5/S3/Weil/Separator/LiteralRationalBoundaryCertified.boundaryCertified
   digest: Computable signed rational enclosures and grids for the literal smooth-transition boundary. -/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import D5.S0.Certificates.BoxCover.RationalIntervalExpression
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.AlgebraMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Separator.LiteralRationalBoundaryGrid

open Filter Topology Polynomial
open scoped BigOperators
open D5.S0.Certificates.BoxCover.RationalIntervalExpression

set_option quotPrecheck false

private abbrev S (q : ℚ) (n : ℕ) := ∑ i ∈ Finset.range n, q ^ i / (Nat.factorial i : ℚ)
private abbrev r (q : ℚ) (n : ℕ) := 2 * |q| ^ n / (Nat.factorial n : ℚ)
private abbrev I (q : ℚ) (n : ℕ) := (S q n - r q n, S q n + r q n)
private abbrev g (q : ℚ) (n : ℕ) := |q| / ((n + 1 : ℕ) : ℚ) ≤ 1 / 2

set_option maxRecDepth 2048

section Cutoff


local notation "A" => (fun (t : ℚ) (n : ℕ) => I (-1 / t) n)
local notation "B" => (fun (t : ℚ) (n : ℕ) => I (-1 / (1 - t)) n)
private abbrev dL (t : ℚ) (n : ℕ) := (A t n).1 + (B t n).1
private abbrev dU (t : ℚ) (n : ℕ) := (A t n).2 + (B t n).2
private abbrev C (t : ℚ) (n : ℕ) := ((A t n).1 / dU t n, (A t n).2 / dL t n)
private abbrev box (t : ℚ) (n : ℕ) (i : Fin 2) := if i = 0 then A t n else B t n
private abbrev ea (t : ℚ) (n : ℕ) := Expr.input (0 : Fin 2) (A t n).1 (A t n).2
private abbrev eb (t : ℚ) (n : ℕ) := Expr.input (1 : Fin 2) (B t n).1 (B t n).2
private abbrev den (t : ℚ) (n : ℕ) := Expr.add (dL t n) (dU t n) (ea t n) (eb t n)
private abbrev invden (t : ℚ) (n : ℕ) := Expr.inv (1 / dU t n) (1 / dL t n) (den t n)
private abbrev cut (t : ℚ) (n : ℕ) := Expr.mul (C t n).1 (C t n).2 (ea t n) (invden t n)
private abbrev P (t : ℚ) (m n : ℕ) :=
  0 < n ∧ g (-1 / t) n ∧ g (-1 / (1 - t)) n ∧
  0 ≤ (A t n).1 ∧ 0 < dL t n ∧ check (box t n) (cut t n) = true ∧
  (C t n).2 - (C t n).1 ≤ (1 / 2 : ℚ) ^ m

set_option maxHeartbeats 2000000 in
-- The Taylor and limit argument needs a larger elaboration budget.
/-- Exact rational cutoff evaluation. Depth zero denotes an exact endpoint
branch. For an interior input the depth is the first depth passing the stated
finite rational predicate, and the interval is exactly the Taylor quotient.
All analytic evidence inhabits Prop and is erased by the compiler. -/
def cutoffCertified (t : ℚ) (m : ℕ) :
    { out : ℕ × (ℚ × ℚ) //
      out.2.1 ≤ out.2.2 ∧
      (out.2.1 : ℝ) ≤ Real.smoothTransition (t : ℝ) ∧
      Real.smoothTransition (t : ℝ) ≤ (out.2.2 : ℝ) ∧
      out.2.2 - out.2.1 ≤ (1 / 2 : ℚ) ^ m ∧
      (t ≤ 0 → out = (0, (0, 0))) ∧
      (1 ≤ t → out = (0, (1, 1))) ∧
      (0 < t → t < 1 → out.2 = C t out.1 ∧ P t m out.1 ∧
        check (box t out.1) (den t out.1) = true ∧
        check (box t out.1) (invden t out.1) = true ∧
        ∀ k < out.1, ¬ P t m k) } := by
  have original :
      (∀ (q : ℚ) (n : ℕ), g q n →
    (((I q n).1 : ℝ) ≤ Real.exp (q : ℝ) ∧
      Real.exp (q : ℝ) ≤ ((I q n).2 : ℝ))) ∧
      (∀ q : ℚ, ∀ m : ℕ, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
    g q n ∧ (I q n).2 - (I q n).1 ≤ (1 / 2 : ℚ) ^ m) ∧
      (∀ (q : ℚ) (n : ℕ), (I q n).2 - (I q n).1 = 4 * |q| ^ n / (n.factorial : ℚ)) ∧
      (∀ t : ℚ, 0 < t → t < 1 → ∀ m : ℕ,
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
    P t m n ∧ check (box t n) (den t n) = true ∧
    check (box t n) (invden t n) = true ∧
    ((C t n).1 : ℝ) ≤ Real.smoothTransition (t : ℝ) ∧
    Real.smoothTransition (t : ℝ) ≤ ((C t n).2 : ℝ)) := by
    as_aux_lemma =>
    have scalar_sound : ∀ (q : ℚ) (n : ℕ), g q n →
        (((I q n).1 : ℝ) ≤ Real.exp (q : ℝ) ∧
          Real.exp (q : ℝ) ≤ ((I q n).2 : ℝ)) := by
      intro q n hg
      have hgc : ‖((q : ℝ) : ℂ)‖ / n.succ ≤ 1 / 2 := by
        simp only [Complex.norm_real, Real.norm_eq_abs, Nat.succ_eq_add_one]
        simpa only [Rat.cast_div, Rat.cast_abs, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat] using
          (show ((|q| / ((n + 1 : ℕ) : ℚ) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) from Rat.cast_le.mpr hg)
      have h := Complex.exp_bound' hgc
      have he : ‖((q : ℝ) : ℂ)‖ = |(q : ℝ)| := by simp
      rw [he] at h
      have hs : (∑ i ∈ Finset.range n, ((q : ℝ) : ℂ) ^ i / (Nat.factorial i : ℂ)) =
          (((S q n : ℚ) : ℝ) : ℂ) := by push_cast; rfl
      rw [hs, ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] at h
      have hr : |(q : ℝ)| ^ n / (Nat.factorial n : ℝ) * 2 = (r q n : ℝ) := by
        push_cast
        ring
      rw [hr, abs_le] at h
      push_cast at h ⊢
      constructor <;> linarith [h.1, h.2]

    have scalar_guard (q : ℚ) : ∀ᶠ n : ℕ in atTop, g q n := by
      obtain ⟨N, hN⟩ := exists_nat_gt (2 * |q|)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hne : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by positivity
      apply (div_le_iff₀ hne).2
      have hn' : (N : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
      push_cast
      linarith
    have scalar_limit (q : ℚ) :
        Tendsto (fun n => ((I q n).1 : ℝ)) atTop (𝓝 (Real.exp (q : ℝ))) ∧
        Tendsto (fun n => ((I q n).2 : ℝ)) atTop (𝓝 (Real.exp (q : ℝ))) := by
      have hr : Tendsto (fun n => (r q n : ℝ)) atTop (𝓝 0) := by
        simpa [mul_div_assoc] using
          (FloorSemiring.tendsto_pow_div_factorial_atTop |(q : ℝ)|).const_mul 2
      have hs : Tendsto (fun n => (S q n : ℝ)) atTop (𝓝 (Real.exp (q : ℝ))) := by
        rw [tendsto_iff_dist_tendsto_zero]
        refine squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) ?_ hr
        filter_upwards [scalar_guard q] with n hg
        have hb := scalar_sound q n hg
        rw [Real.dist_eq, abs_le]
        push_cast at hb ⊢
        constructor <;> linarith [hb.1, hb.2]
      constructor
      · simpa only [Rat.cast_sub, sub_zero] using hs.sub hr
      · simpa only [Rat.cast_add, add_zero] using hs.add hr
    have accepts (t : ℚ) (n : ℕ) (ha : 0 ≤ (A t n).1) (hd : 0 < dL t n) :
        check (box t n) (den t n) = true ∧
        check (box t n) (invden t n) = true ∧
        check (box t n) (cut t n) = true := by
      have hab : (A t n).1 ≤ (A t n).2 := by
        have : (0 : ℚ) ≤ r (-1 / t) n := by positivity
        linarith
      have hbb : (B t n).1 ≤ (B t n).2 := by
        have : (0 : ℚ) ≤ r (-1 / (1 - t)) n := by positivity
        linarith
      have hdd : dL t n ≤ dU t n := add_le_add hab hbb
      have hi : 1 / dU t n ≤ 1 / dL t n := one_div_le_one_div_of_le hd hdd
      have hlu : (A t n).1 / dU t n ≤ (A t n).2 / dL t n := by
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul hab hi (one_div_nonneg.mpr (hd.le.trans hdd)) (ha.trans hab)
      have hia : check (box t n) (ea t n) = true := by
        simpa only [check, decide_eq_true_eq, if_pos rfl, ite_true, le_refl, and_true] using hab
      have hib : check (box t n) (eb t n) = true := by
        simpa only [check, decide_eq_true_eq, if_neg (show (1 : Fin 2) ≠ 0 by decide),
          le_refl, and_true] using hbb
      have hden : check (box t n) (den t n) = true := by
        rw [check, hia, hib, Bool.true_and, Bool.true_and, decide_eq_true_eq]
        exact ⟨hdd, le_rfl, le_rfl⟩
      have hinv : check (box t n) (invden t n) = true := by
        rw [check, hden, Bool.true_and, decide_eq_true_eq]
        exact ⟨hi, Or.inr hd, le_rfl, le_rfl⟩
      refine ⟨hden, hinv, ?_⟩
      rw [check, hia, hinv, Bool.true_and, Bool.true_and, decide_eq_true_eq]
      simp only [bounds]
      simp only [← div_eq_mul_one_div]
      have h1 : (A t n).1 / dU t n ≤ (A t n).1 / dL t n :=
        div_le_div_of_nonneg_left ha hd hdd
      have h2 : (A t n).1 / dU t n ≤ (A t n).2 / dU t n :=
        div_le_div_of_nonneg_right hab (hd.le.trans hdd)
      have h3 : (A t n).1 / dL t n ≤ (A t n).2 / dL t n :=
        div_le_div_of_nonneg_right hab hd.le
      have h4 : (A t n).2 / dU t n ≤ (A t n).2 / dL t n :=
        div_le_div_of_nonneg_left (ha.trans hab) hd hdd
      exact ⟨hlu, le_rfl, h1, h2, hlu, hlu, h3, h4, le_rfl⟩
    have scalar_precision : ∀ q : ℚ, ∀ m : ℕ, ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      g q n ∧ (I q n).2 - (I q n).1 ≤ (1 / 2 : ℚ) ^ m := by
      intro q m
      have hg : ∀ᶠ n : ℕ in atTop, g q n := by
        obtain ⟨N, hN⟩ := exists_nat_gt (2 * |q|)
        filter_upwards [eventually_ge_atTop N] with n hn
        have hne : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by positivity
        apply (div_le_iff₀ hne).2
        have hn' : (N : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
        push_cast
        linarith
      have hr : Tendsto (fun n : ℕ => 4 * |q| ^ n / (Nat.factorial n : ℚ)) atTop (𝓝 0) := by
        simpa [mul_div_assoc] using (FloorSemiring.tendsto_pow_div_factorial_atTop |q|).const_mul 4
      have hw := hr.eventually (gt_mem_nhds (show (0 : ℚ) < (1 / 2 : ℚ) ^ m by positivity))
      have hh : ∀ᶠ n : ℕ in atTop, 0 < n ∧ g q n ∧
          (I q n).2 - (I q n).1 ≤ (1 / 2 : ℚ) ^ m := by
        filter_upwards [eventually_gt_atTop 0, hg, hw] with n hn hg hw
        refine ⟨hn, hg, ?_⟩
        calc
          _ = 4 * |q| ^ n / (Nat.factorial n : ℚ) := by ring
          _ ≤ _ := hw.le
      obtain ⟨N, hN⟩ := eventually_atTop.1 hh
      exact ⟨N, (hN N le_rfl).1, fun n hn => (hN n hn).2⟩
    refine ⟨scalar_sound, scalar_precision, (by intros; dsimp; ring), ?_⟩
    intro t ht0 ht1 m
    have ht0r : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht0
    have ht1r : (t : ℝ) < 1 := by exact_mod_cast ht1
    have hA := scalar_limit (-1 / t)
    have hB := scalar_limit (-1 / (1 - t))
    have heq : Real.exp ((-1 / t : ℚ) : ℝ) /
        (Real.exp ((-1 / t : ℚ) : ℝ) + Real.exp ((-1 / (1-t) : ℚ) : ℝ)) =
        Real.smoothTransition (t : ℝ) := by
      simp [Real.smoothTransition, expNegInvGlue, not_le.mpr ht0r,
        not_le.mpr (sub_pos.mpr ht1r), neg_div, one_div]
    have hdpos : 0 < Real.exp ((-1 / t : ℚ) : ℝ) + Real.exp ((-1 / (1-t) : ℚ) : ℝ) :=
      add_pos (Real.exp_pos _) (Real.exp_pos _)
    have hdl : Tendsto (fun n => (dL t n : ℝ)) atTop
        (𝓝 (Real.exp ((-1 / t : ℚ) : ℝ) + Real.exp ((-1 / (1-t) : ℚ) : ℝ))) := by
      simpa only [Rat.cast_add] using hA.1.add hB.1
    have hdu : Tendsto (fun n => (dU t n : ℝ)) atTop
        (𝓝 (Real.exp ((-1 / t : ℚ) : ℝ) + Real.exp ((-1 / (1-t) : ℚ) : ℝ))) := by
      simpa only [Rat.cast_add] using hA.2.add hB.2
    have hcl : Tendsto (fun n => ((C t n).1 : ℝ)) atTop (𝓝 (Real.smoothTransition (t : ℝ))) := by
      rw [← heq]
      convert hA.1.div hdu hdpos.ne' using 1
      ext n
      simp only [Pi.div_apply, Rat.cast_div]
    have hcu : Tendsto (fun n => ((C t n).2 : ℝ)) atTop (𝓝 (Real.smoothTransition (t : ℝ))) := by
      rw [← heq]
      convert hA.2.div hdl hdpos.ne' using 1
      ext n
      simp only [Pi.div_apply, Rat.cast_div]
    have hw : Tendsto (fun n => ((C t n).2 : ℝ) - ((C t n).1 : ℝ)) atTop (𝓝 0) := by
      simpa only [sub_self] using hcu.sub hcl
    have hsmall := hw.eventually (gt_mem_nhds (show (0 : ℝ) < ((1 / 2 : ℚ) ^ m : ℚ) by positivity))
    have hsignA := hA.1.eventually (lt_mem_nhds (Real.exp_pos _))
    have hsignd := hdl.eventually (lt_mem_nhds hdpos)
    have eventual : ∀ᶠ n : ℕ in atTop,
        0 < n ∧ P t m n ∧ check (box t n) (den t n) = true ∧
        check (box t n) (invden t n) = true ∧
        ((C t n).1 : ℝ) ≤ Real.smoothTransition (t : ℝ) ∧
        Real.smoothTransition (t : ℝ) ≤ ((C t n).2 : ℝ) := by
      filter_upwards [eventually_gt_atTop 0, scalar_guard (-1/t), scalar_guard (-1/(1-t)),
        hsignA, hsignd, hsmall] with n hn hga hgb ha hd hw
      have haq : 0 ≤ (A t n).1 := by exact_mod_cast ha.le
      have hdq : 0 < dL t n := by exact_mod_cast hd
      have hwq : (C t n).2 - (C t n).1 ≤ (1/2 : ℚ)^m := by exact_mod_cast hw.le
      have hc := accepts t n haq hdq
      refine ⟨hn, ⟨hn, hga, hgb, haq, hdq, hc.2.2, hwq⟩, hc.1, hc.2.1, ?_⟩
      let x : Fin 2 → ℝ := fun i => if i = 0 then Real.exp ((-1/t : ℚ) : ℝ)
        else Real.exp ((-1/(1-t) : ℚ) : ℝ)
      have hx : ∀ i, ((box t n i).1 : ℝ) ≤ x i ∧ x i ≤ ((box t n i).2 : ℝ) := by
        intro i
        dsimp [x]
        split_ifs
        · exact scalar_sound (-1/t) n hga
        · exact scalar_sound (-1/(1-t)) n hgb
      have hcheck := checked_expression_encloses (box t n) x hx (cut t n) hc.2.2
      have hvalue : value x (cut t n) = Real.smoothTransition (t : ℝ) := by
        simpa [value, x, div_eq_mul_inv] using heq
      simpa only [bounds, hvalue] using hcheck
    obtain ⟨N, hN⟩ := eventually_atTop.1 eventual
    exact ⟨N, (hN N le_rfl).1, fun n hn => (hN n hn).2⟩
  by_cases h0 : t ≤ 0
  · have he : Real.smoothTransition (t : ℝ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by exact_mod_cast h0)
    refine ⟨(0, (0, 0)), le_rfl, ?_, ?_, ?_, (fun _ => rfl), ?_, ?_⟩
    · simpa only [Rat.cast_zero, he] using (le_refl (0 : ℝ))
    · simpa only [Rat.cast_zero, he] using (le_refl (0 : ℝ))
    · simpa only [sub_self] using pow_nonneg (show (0 : ℚ) ≤ 1/2 by norm_num) m
    · intro h1; exfalso; linarith
    · intro ht0; exfalso; linarith
  · by_cases h1 : 1 ≤ t
    · have he : Real.smoothTransition (t : ℝ) = 1 :=
        Real.smoothTransition.one_of_one_le (by exact_mod_cast h1)
      refine ⟨(0, (1, 1)), le_rfl, ?_, ?_, ?_, ?_, (fun _ => rfl), ?_⟩
      · simpa only [Rat.cast_one, he] using (le_refl (1 : ℝ))
      · simpa only [Rat.cast_one, he] using (le_refl (1 : ℝ))
      · simpa only [sub_self] using pow_nonneg (show (0 : ℚ) ≤ 1/2 by norm_num) m
      · intro ht; exact (h0 ht).elim
      · intro ht0 ht1; exfalso; linarith
    · have ht0 : 0 < t := lt_of_not_ge h0
      have ht1 : t < 1 := lt_of_not_ge h1
      -- This instance uses only concrete rational and Boolean decisions.
      let finiteDecision : DecidablePred (P t m) := fun n => inferInstance
      have exists_depth : ∃ n : ℕ, P t m n := by
        obtain ⟨N, _, hN⟩ := original.2.2.2 t ht0 ht1 m
        exact ⟨N, (hN N le_rfl).1⟩
      let n := @Nat.find (P t m) finiteDecision exists_depth
      have hn : P t m n := @Nat.find_spec (P t m) finiteDecision exists_depth
      have hcut : check (box t n) (cut t n) = true := hn.2.2.2.2.2.1
      have hinv : check (box t n) (invden t n) = true := by
        have h := hcut
        rw [check, Bool.and_eq_true_iff, Bool.and_eq_true_iff] at h
        exact h.2.1
      have hden : check (box t n) (den t n) = true := by
        have h := hinv
        rw [check, Bool.and_eq_true_iff] at h
        exact h.1
      have hsem : ((C t n).1 : ℝ) ≤ Real.smoothTransition (t : ℝ) ∧
          Real.smoothTransition (t : ℝ) ≤ ((C t n).2 : ℝ) := by
        let x : Fin 2 → ℝ := fun i => if i = 0 then Real.exp ((-1/t : ℚ) : ℝ)
          else Real.exp ((-1/(1-t) : ℚ) : ℝ)
        have hx : ∀ i, ((box t n i).1 : ℝ) ≤ x i ∧ x i ≤ ((box t n i).2 : ℝ) := by
          intro i
          dsimp [x]
          split_ifs
          · exact original.1 (-1/t) n hn.2.1
          · exact original.1 (-1/(1-t)) n hn.2.2.1
        have hh := checked_expression_encloses (box t n) x hx (cut t n) hcut
        have hvalue : value x (cut t n) = Real.smoothTransition (t : ℝ) := by
          have ht0r : (0 : ℝ) < t := by exact_mod_cast ht0
          have ht1r : (t : ℝ) < 1 := by exact_mod_cast ht1
          simp [value, x, Real.smoothTransition, expNegInvGlue,
            not_le.mpr ht0r, not_le.mpr (sub_pos.mpr ht1r),
            div_eq_mul_inv]
        simpa only [bounds, hvalue] using hh
      refine ⟨(n, C t n), ?_, hsem.1, hsem.2, hn.2.2.2.2.2.2,
        (fun h => (h0 h).elim), (fun h => (h1 h).elim), ?_⟩
      · exact_mod_cast (hsem.1.trans hsem.2)
      · intro _ _
        exact ⟨rfl, hn, hden, hinv, @Nat.find_min (P t m) finiteDecision exists_depth⟩

end Cutoff

section BoundaryExp

private abbrev Q (q : ℚ) (m n : ℕ) :=
  0 < n ∧ g q n ∧
  4 * |q| ^ n / (Nat.factorial n : ℚ) ≤ (1 / 2 : ℚ) ^ m

set_option maxHeartbeats 2000000 in
-- The Taylor and limit argument needs a larger elaboration budget.
/-- The first accepted Taylor enclosure for a rational exponential.
    The interval is the actual signed Taylor sum plus or minus its remainder. -/
def boundaryExpCertified_v1 (q : ℚ) (m : ℕ) :
    { out : ℕ × (ℚ × ℚ) //
      out.2 = I q out.1 ∧ Q q m out.1 ∧
      out.2.1 ≤ out.2.2 ∧
      (out.2.1 : ℝ) ≤ Real.exp (q : ℝ) ∧
      Real.exp (q : ℝ) ≤ (out.2.2 : ℝ) ∧
      out.2.2 - out.2.1 ≤ (1 / 2 : ℚ) ^ m ∧
      ∀ j < out.1, ¬ Q q m j } := by
  have scalar_sound : ∀ (q : ℚ) (n : ℕ), g q n →
      (((I q n).1 : ℝ) ≤ Real.exp (q : ℝ) ∧
        Real.exp (q : ℝ) ≤ ((I q n).2 : ℝ)) := by
    intro q n hg
    have hgc : ‖((q : ℝ) : ℂ)‖ / n.succ ≤ 1 / 2 := by
      simp only [Complex.norm_real, Real.norm_eq_abs, Nat.succ_eq_add_one]
      simpa only [Rat.cast_div, Rat.cast_abs, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat] using
        (show ((|q| / ((n + 1 : ℕ) : ℚ) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) from Rat.cast_le.mpr hg)
    have h := Complex.exp_bound' hgc
    have he : ‖((q : ℝ) : ℂ)‖ = |(q : ℝ)| := by simp
    rw [he] at h
    have hs : (∑ i ∈ Finset.range n, ((q : ℝ) : ℂ) ^ i / (Nat.factorial i : ℂ)) =
        (((S q n : ℚ) : ℝ) : ℂ) := by push_cast; rfl
    rw [hs, ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at h
    have hr : |(q : ℝ)| ^ n / (Nat.factorial n : ℝ) * 2 = (r q n : ℝ) := by
      push_cast
      ring
    rw [hr, abs_le] at h
    push_cast at h ⊢
    constructor <;> linarith [h.1, h.2]
  have scalar_precision : ∀ q : ℚ, ∀ m : ℕ, ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → Q q m n := by
    intro q m
    have hg : ∀ᶠ n : ℕ in atTop, g q n := by
      obtain ⟨N, hN⟩ := exists_nat_gt (2 * |q|)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hne : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by positivity
      apply (div_le_iff₀ hne).2
      have hn' : (N : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
      push_cast
      linarith
    have hr : Tendsto (fun n : ℕ => 4 * |q| ^ n / (Nat.factorial n : ℚ))
        atTop (𝓝 0) := by
      simpa [mul_div_assoc] using
        (FloorSemiring.tendsto_pow_div_factorial_atTop |q|).const_mul 4
    have hw := hr.eventually
      (gt_mem_nhds (show (0 : ℚ) < (1 / 2 : ℚ) ^ m by positivity))
    have hh : ∀ᶠ n : ℕ in atTop, Q q m n := by
      filter_upwards [eventually_gt_atTop 0, hg, hw] with n hn hg hw
      exact ⟨hn, hg, hw.le⟩
    exact eventually_atTop.1 hh
  let finiteDecision : DecidablePred (Q q m) := fun n => inferInstance
  have exists_depth : ∃ n : ℕ, Q q m n := by
    obtain ⟨N, hN⟩ := scalar_precision q m
    exact ⟨N, hN N le_rfl⟩
  let n := @Nat.find (Q q m) finiteDecision exists_depth
  have hn : Q q m n := @Nat.find_spec (Q q m) finiteDecision exists_depth
  have hs := scalar_sound q n hn.2.1
  have hwidth : (I q n).2 - (I q n).1 ≤ (1 / 2 : ℚ) ^ m := by
    calc
      _ = 4 * |q| ^ n / (Nat.factorial n : ℚ) := by dsimp; ring
      _ ≤ _ := hn.2.2
  refine ⟨(n, I q n), rfl, hn, ?_, hs.1, hs.2, hwidth, ?_⟩
  · exact_mod_cast (hs.1.trans hs.2)
  · exact @Nat.find_min (Q q m) finiteDecision exists_depth

end BoundaryExp

/-- Multiplying two ordered rational intervals preserves order, amplitude bounds,
and admits a first-order width estimate. -/
theorem rationalIntervalMul_bounds (a b : Rat × Rat) (A B : Rat)
    (ha : a.1 <= a.2) (hb : b.1 <= b.2) (hA : 0 <= A) (_hB : 0 <= B)
    (hal : |a.1| <= A) (hau : |a.2| <= A)
    (hbl : |b.1| <= B) (hbu : |b.2| <= B) :
    let out :=
      (min (min (a.1 * b.1) (a.1 * b.2)) (min (a.2 * b.1) (a.2 * b.2)),
       max (max (a.1 * b.1) (a.1 * b.2)) (max (a.2 * b.1) (a.2 * b.2)))
    out.1 <= out.2 ∧ |out.1| <= A * B ∧ |out.2| <= A * B ∧
      out.2 - out.1 <= A * (b.2 - b.1) + B * (a.2 - a.1) := by
  dsimp only
  have horder :
      min (min (a.1 * b.1) (a.1 * b.2)) (min (a.2 * b.1) (a.2 * b.2)) <=
        max (max (a.1 * b.1) (a.1 * b.2)) (max (a.2 * b.1) (a.2 * b.2)) := by
    exact (min_le_left _ _).trans
      ((min_le_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hprod (x y : Rat) (hx : x = a.1 ∨ x = a.2)
      (hy : y = b.1 ∨ y = b.2) : |x * y| <= A * B := by
    rw [abs_mul]
    have hxA : |x| <= A := by
      rcases hx with hx | hx
      · rw [hx]
        exact hal
      · rw [hx]
        exact hau
    have hyB : |y| <= B := by
      rcases hy with hy | hy
      · rw [hy]
        exact hbl
      · rw [hy]
        exact hbu
    exact mul_le_mul hxA hyB (abs_nonneg y) hA
  have min_endpoint : ∀ u v : Rat, min u v = u ∨ min u v = v := by
    intro u v
    by_cases h : u <= v
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (min_eq_right (le_of_not_ge h))
  have max_endpoint : ∀ u v : Rat, max u v = u ∨ max u v = v := by
    intro u v
    by_cases h : u <= v
    · exact Or.inr (max_eq_right h)
    · exact Or.inl (max_eq_left (le_of_not_ge h))
  have hlowLeft : ∃ x y : Rat, (x = a.1 ∨ x = a.2) ∧
      (y = b.1 ∨ y = b.2) ∧ min (a.1 * b.1) (a.1 * b.2) = x * y := by
    rcases min_endpoint (a.1 * b.1) (a.1 * b.2) with h | h
    · exact ⟨a.1, b.1, Or.inl rfl, Or.inl rfl, h⟩
    · exact ⟨a.1, b.2, Or.inl rfl, Or.inr rfl, h⟩
  have hlowRight : ∃ x y : Rat, (x = a.1 ∨ x = a.2) ∧
      (y = b.1 ∨ y = b.2) ∧ min (a.2 * b.1) (a.2 * b.2) = x * y := by
    rcases min_endpoint (a.2 * b.1) (a.2 * b.2) with h | h
    · exact ⟨a.2, b.1, Or.inr rfl, Or.inl rfl, h⟩
    · exact ⟨a.2, b.2, Or.inr rfl, Or.inr rfl, h⟩
  have hlow : ∃ x y : Rat, (x = a.1 ∨ x = a.2) ∧
      (y = b.1 ∨ y = b.2) ∧
      min (min (a.1 * b.1) (a.1 * b.2)) (min (a.2 * b.1) (a.2 * b.2)) = x * y := by
    rcases min_endpoint (min (a.1 * b.1) (a.1 * b.2))
        (min (a.2 * b.1) (a.2 * b.2)) with h | h
    · obtain ⟨x, y, hx, hy, hv⟩ := hlowLeft
      exact ⟨x, y, hx, hy, h.trans hv⟩
    · obtain ⟨x, y, hx, hy, hv⟩ := hlowRight
      exact ⟨x, y, hx, hy, h.trans hv⟩
  have huppLeft : ∃ x y : Rat, (x = a.1 ∨ x = a.2) ∧
      (y = b.1 ∨ y = b.2) ∧ max (a.1 * b.1) (a.1 * b.2) = x * y := by
    rcases max_endpoint (a.1 * b.1) (a.1 * b.2) with h | h
    · exact ⟨a.1, b.1, Or.inl rfl, Or.inl rfl, h⟩
    · exact ⟨a.1, b.2, Or.inl rfl, Or.inr rfl, h⟩
  have huppRight : ∃ x y : Rat, (x = a.1 ∨ x = a.2) ∧
      (y = b.1 ∨ y = b.2) ∧ max (a.2 * b.1) (a.2 * b.2) = x * y := by
    rcases max_endpoint (a.2 * b.1) (a.2 * b.2) with h | h
    · exact ⟨a.2, b.1, Or.inr rfl, Or.inl rfl, h⟩
    · exact ⟨a.2, b.2, Or.inr rfl, Or.inr rfl, h⟩
  have hupp : ∃ x y : Rat, (x = a.1 ∨ x = a.2) ∧
      (y = b.1 ∨ y = b.2) ∧
      max (max (a.1 * b.1) (a.1 * b.2)) (max (a.2 * b.1) (a.2 * b.2)) = x * y := by
    rcases max_endpoint (max (a.1 * b.1) (a.1 * b.2))
        (max (a.2 * b.1) (a.2 * b.2)) with h | h
    · obtain ⟨x, y, hx, hy, hv⟩ := huppLeft
      exact ⟨x, y, hx, hy, h.trans hv⟩
    · obtain ⟨x, y, hx, hy, hv⟩ := huppRight
      exact ⟨x, y, hx, hy, h.trans hv⟩
  obtain ⟨x, y, hx, hy, hl⟩ := hlow
  obtain ⟨x', y', hx', hy', hu⟩ := hupp
  have hdx : |x' - x| <= a.2 - a.1 := by
    rcases hx with hx | hx <;> rcases hx' with hx' | hx'
    · rw [hx, hx', sub_self, abs_zero]
      exact sub_nonneg.mpr ha
    · rw [hx, hx', abs_of_nonneg (sub_nonneg.mpr ha)]
    · rw [hx, hx', abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ha)]
    · rw [hx, hx', sub_self, abs_zero]
      exact sub_nonneg.mpr ha
  have hdy : |y' - y| <= b.2 - b.1 := by
    rcases hy with hy | hy <;> rcases hy' with hy' | hy'
    · rw [hy, hy', sub_self, abs_zero]
      exact sub_nonneg.mpr hb
    · rw [hy, hy', abs_of_nonneg (sub_nonneg.mpr hb)]
    · rw [hy, hy', abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hb)]
    · rw [hy, hy', sub_self, abs_zero]
      exact sub_nonneg.mpr hb
  refine ⟨horder, ?_, ?_, ?_⟩
  · rw [hl]
    exact hprod x y hx hy
  · rw [hu]
    exact hprod x' y' hx' hy'
  · rw [hl, hu]
    calc
      x' * y' - x * y <= |x' * y' - x * y| := le_abs_self _
      _ = |x' * (y' - y) + (x' - x) * y| := by congr 1; ring
      _ <= |x' * (y' - y)| + |(x' - x) * y| := abs_add_le _ _
      _ = |x'| * |y' - y| + |x' - x| * |y| := by rw [abs_mul, abs_mul]
      _ <= A * (b.2 - b.1) + (a.2 - a.1) * B := by
        apply add_le_add
        · have hxA : |x'| <= A := by
            rcases hx' with hx' | hx'
            · rw [hx']
              exact hal
            · rw [hx']
              exact hau
          exact mul_le_mul hxA hdy (abs_nonneg (y' - y)) hA
        · have hyB : |y| <= B := by
            rcases hy with hy | hy
            · rw [hy]
              exact hbl
            · rw [hy]
              exact hbu
          exact mul_le_mul hdx hyB (abs_nonneg y) (sub_nonneg.mpr ha)
      _ = _ := by ring

/-- The completed square interval, including the zero-crossing branch, has
width controlled by the input amplitude and width. -/
theorem rationalIntervalSquare_width (a : Rat × Rat) (cap : Rat)
    (ha : a.1 <= a.2) (hcap : 0 <= cap)
    (hal : |a.1| <= cap) (hau : |a.2| <= cap) :
    let out :=
      (if 0 <= a.1 then a.1 ^ 2 else if a.2 <= 0 then a.2 ^ 2 else 0,
       max (a.1 ^ 2) (a.2 ^ 2))
    out.2 - out.1 <= 2 * cap * (a.2 - a.1) := by
  obtain ⟨hal', hal⟩ := abs_le.mp hal
  obtain ⟨hau', hau⟩ := abs_le.mp hau
  dsimp only
  split_ifs with h0 h1
  · have hsq : a.1 ^ 2 <= a.2 ^ 2 := by
      nlinarith only [ha, h0, sq_nonneg (a.2 - a.1)]
    rw [max_eq_right hsq]
    have hfac : 0 <= 2 * cap - a.2 - a.1 := by
      linarith only [hal, hau]
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha) hfac]
  · have hsq : a.2 ^ 2 <= a.1 ^ 2 := by
      nlinarith only [ha, h1, sq_nonneg (a.2 - a.1)]
    rw [max_eq_left hsq]
    have hfac : 0 <= 2 * cap + a.2 + a.1 := by
      linarith only [hal', hau']
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha) hfac]
  · rw [sub_zero, max_le_iff]
    have ha0 : a.1 <= 0 := le_of_not_ge h0
    have hb0 : 0 <= a.2 := le_of_not_ge h1
    constructor
    · have hn : 0 <= -a.1 := by linarith only [ha0]
      have hs : 0 <= cap + a.1 := by linarith only [hal']
      nlinarith only [mul_nonneg hn hs, mul_nonneg hcap hb0,
        mul_nonneg hcap (sub_nonneg.mpr ha)]
    · have hs : 0 <= cap - a.2 := by linarith only [hau]
      have hn : 0 <= -a.1 := by linarith only [ha0]
      nlinarith only [mul_nonneg hb0 hs, mul_nonneg hcap hn,
        mul_nonneg hcap (sub_nonneg.mpr ha)]

private abbrev derivBound (p : Rat[X]) (B : Rat) :=
  p.sum fun n a => |a| * (n : Rat) * B ^ (n - 1)
private abbrev valueBound (p : Rat[X]) (B : Rat) :=
  p.sum fun n a => |a| * B ^ n
private abbrev evenEval (p : Rat[X]) (c : Rat) :=
  (p.eval c + p.eval (-c)) / 2
private abbrev polyBox (p : Rat[X]) (B eta c : Rat) :=
  (evenEval p c - derivBound p B * eta / 2,
   evenEval p c + derivBound p B * eta / 2)
private abbrev mulBox (a b : Rat × Rat) :=
  (min (min (a.1 * b.1) (a.1 * b.2)) (min (a.2 * b.1) (a.2 * b.2)),
   max (max (a.1 * b.1) (a.1 * b.2)) (max (a.2 * b.1) (a.2 * b.2)))
private abbrev sqBox (a : Rat × Rat) :=
  (if 0 <= a.1 then a.1 ^ 2 else if a.2 <= 0 then a.2 ^ 2 else 0,
   max (a.1 ^ 2) (a.2 ^ 2))
private abbrev cellInputs (w a b : Rat × Rat) (i : Fin 3) :=
  if i = 0 then w else if i = 1 then a else b
private abbrev cellExpr (w a b : Rat × Rat) :=
  let ew : Expr 3 := .input 0 w.1 w.2
  let ea : Expr 3 := .input 1 a.1 a.2
  let eb : Expr 3 := .input 2 b.1 b.2
  let ab := mulBox a b
  let wab := mulBox w ab
  Expr.mul wab.1 wab.2 ew (.mul ab.1 ab.2 ea eb)
private abbrev finalInputs (a b : Rat × Rat) (i : Fin 2) :=
  if i = 0 then a else b
private abbrev finalExpr (a b : Rat × Rat) :=
  let sa := sqBox a
  let sb := sqBox b
  let sum := (sa.1 + sb.1, sa.2 + sb.2)
  let out := (2 * sum.1, 2 * sum.2)
  let ea : Expr 2 := .input 0 a.1 a.2
  let eb : Expr 2 := .input 1 b.1 b.2
  let esa : Expr 2 := .square sa.1 sa.2 ea
  let esb : Expr 2 := .square sb.1 sb.2 eb
  let esum : Expr 2 := .add sum.1 sum.2 esa esb
  Expr.mul out.1 out.2 (.const 2 2 2) esum
local notation "GridNode" =>
  (Nat × Rat × Rat) × ((Nat × Rat × Rat) × (Nat × Rat × Rat))
local notation "GridCell" =>
  ((Fin 3 → Rat × Rat) × Expr 3) × ((Fin 3 → Rat × Rat) × Expr 3)

private def boundaryGridNodes (R k s : Nat) : Array GridNode :=
  let N : Nat := 2 ^ k
  let Br : Rat := 2 * R
  let eta : Rat := Br / N
  let xq : Nat -> Rat := fun j => j * eta
  Array.ofFn fun (j : Fin (N + 1)) =>
    ((cutoffCertified (2 - xq j / R) s).val,
     ((boundaryExpCertified_v1 (xq j / 2) s).val,
      (boundaryExpCertified_v1 (-xq j / 2) s).val))

private def boundaryGridCells (R : Nat) (p q : Rat[X]) (k : Nat)
    (nodes : Array GridNode) :
    Array GridCell :=
  let N : Nat := 2 ^ k
  let Br : Rat := 2 * R
  let eta : Rat := Br / N
  let xq : Nat -> Rat := fun j => j * eta
  Array.ofFn fun (i : Fin N) =>
    let c := (xq i + xq (i + 1)) / 2
    let ni := nodes[i.val]!
    let nip := nodes[i.val + 1]!
    let a := (nip.1.2.1, ni.1.2.2)
    let w := (ni.2.1.2.1 + nip.2.2.2.1,
      nip.2.1.2.2 + ni.2.2.2.2)
    let bp := polyBox p Br eta c
    let bq := polyBox q Br eta c
    ((cellInputs w a bp, cellExpr w a bp),
     (cellInputs w a bq, cellExpr w a bq))

def boundaryGrid (R : Nat) (p q : Rat[X]) (k s : Nat) :
    Array GridNode × Array GridCell :=
  let nodes := boundaryGridNodes R k s
  (nodes, boundaryGridCells R p q k nodes)

end D5.S3.Weil.Separator.LiteralRationalBoundaryGrid
