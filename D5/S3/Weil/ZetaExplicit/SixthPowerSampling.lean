/- GID: D5/S3/Weil/ZetaExplicit/SixthPowerSampling
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaExplicit/SixthPowerSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A global convex interpolant obstructs square-root control from sixth-power samples. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set

namespace D5.S3.Weil.ZetaExplicit.SixthPowerSampling

private def g (x : ℝ) : ℝ := x * Real.log x
private def node (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ 6
private def secantSlope (n : ℕ) : ℝ :=
  (g (node (n+1)) - g (node n)) / (node (n+1) - node n)
private def line (n : ℕ) (x : ℝ) : ℝ :=
  g (node n) + secantSlope n * (x - node n)
private def interpolant (x : ℝ) : ℝ := sSup (range fun n => line n x)

private lemma node_pos (n : ℕ) : 0 < node n := by unfold node; positivity
private lemma node_one_le (n : ℕ) : 1 ≤ node n := by
  exact one_le_pow₀ (by positivity : (1 : ℝ) ≤ (n : ℝ)+1)
private lemma node_strict : StrictMono node := by
  intro n m h
  dsimp [node]
  gcongr
  exact_mod_cast h

private lemma secantSlope_nonneg (n : ℕ) : 0 ≤ secantSlope n := by
  have h := (node_strict (Nat.lt_succ_self n)).le
  apply div_nonneg _ (sub_nonneg.mpr h)
  exact sub_nonneg.mpr (mul_le_mul h
    (Real.log_le_log (node_pos n) h) (Real.log_nonneg (node_one_le n))
    (node_pos (n+1)).le)

private lemma line_left (n : ℕ) : line n (node n) = g (node n) := by simp [line]
private lemma line_right (n : ℕ) : line n (node (n+1)) = g (node (n+1)) := by
  dsimp [line, secantSlope]
  rw [div_mul_cancel₀ _ (sub_pos.mpr (node_strict (Nat.lt_succ_self n))).ne']
  ring

private lemma line_node_le (n m : ℕ) : line n (node m) ≤ g (node m) := by
  by_cases hm : m = n
  · subst m; exact (line_left n).le
  by_cases hm' : m = n+1
  · subst m; exact (line_right n).le
  have hgap := sub_pos.mpr (node_strict (Nat.lt_succ_self n))
  have hs : secantSlope n * (node (n+1) - node n) =
      g (node (n+1)) - g (node n) := div_mul_cancel₀ _ hgap.ne'
  apply (mul_le_mul_iff_of_pos_right hgap).mp
  dsimp [line]
  rcases lt_or_ge m n with hmn | hnm
  · have h := Real.convexOn_mul_log.secant_mono_aux1
      (node_pos m).le (node_pos (n+1)).le (node_strict hmn)
      (node_strict (Nat.lt_succ_self n))
    change (node (n+1) - node m) * g (node n) ≤
      (node (n+1) - node n) * g (node m) + (node n - node m) * g (node (n+1)) at h
    linear_combination h + (node m - node n) * hs
  · have hnm' : n+1 < m := by omega
    have h := Real.convexOn_mul_log.secant_mono_aux1
      (node_pos n).le (node_pos m).le (node_strict (Nat.lt_succ_self n))
      (node_strict hnm')
    change (node m - node n) * g (node (n+1)) ≤
      (node m - node (n+1)) * g (node n) + (node (n+1) - node n) * g (node m) at h
    linear_combination h + (node m - node n) * hs

private lemma line_mono (n : ℕ) : Monotone (line n) := by
  intro x y h
  dsimp [line]
  exact add_le_add_left (mul_le_mul_of_nonneg_left (sub_le_sub_right h _)
    (secantSlope_nonneg n)) _

private lemma bounded_lines (x : ℝ) : BddAbove (range fun n => line n x) := by
  obtain ⟨m, hm⟩ := exists_nat_ge x
  have hx : x ≤ node m := hm.trans ((by linarith : (m : ℝ) ≤ (m : ℝ)+1).trans
    (le_self_pow (by positivity : (1 : ℝ) ≤ (m : ℝ)+1) (by decide : 6 ≠ 0)))
  refine ⟨g (node m), ?_⟩
  rintro y ⟨n, rfl⟩
  exact (line_mono n hx).trans (line_node_le n m)

private lemma line_le_interpolant (n : ℕ) (x : ℝ) : line n x ≤ interpolant x :=
  le_csSup (bounded_lines x) (mem_range_self n)

private lemma interpolant_node (n : ℕ) : interpolant (node n) = g (node n) := by
  apply le_antisymm
  · exact csSup_le (range_nonempty _) (by rintro _ ⟨m, rfl⟩; exact line_node_le m n)
  · simpa [line] using line_le_interpolant n (node n)

private lemma interpolant_convex : ConvexOn ℝ univ interpolant := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  change interpolant (a*x+b*y) ≤ a*interpolant x+b*interpolant y
  apply csSup_le (range_nonempty _)
  rintro z ⟨n, rfl⟩
  calc
    line n (a*x+b*y) = a*line n x+b*line n y := by
      dsimp [line]
      linear_combination (secantSlope n * node n - g (node n)) * hab
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (line_le_interpolant n x) ha)
      (mul_le_mul_of_nonneg_left (line_le_interpolant n y) hb)

private lemma log_midpoint_gap {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b-a)^2 / 8 ≤ b * ((g a+g b)/2-g ((a+b)/2)) := by
  have hb : 0 < b := ha.trans_le hab
  let f : ℝ → ℝ := fun x => b * (x * Real.log x) - x^2/2
  have hconv : ConvexOn ℝ (Icc a b) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fun x => b*(Real.log x+1)-x)
      (f'' := fun x => b/x-1) (convex_Icc a b)
    · exact ((Real.continuous_mul_log.const_mul b).sub
        ((continuous_id.pow 2).div_const 2)).continuousOn
    · intro x hx
      have hxpos : 0 < x := ha.trans_le (interior_subset hx).1
      convert (((Real.hasDerivAt_mul_log hxpos.ne').const_mul b).sub
        (((hasDerivAt_id x).pow 2).div_const 2)).hasDerivWithinAt using 1 <;> dsimp [f] <;> ring
    · intro x hx
      have hxpos : 0 < x := ha.trans_le (interior_subset hx).1
      convert ((((Real.hasDerivAt_log hxpos.ne').add_const 1).const_mul b).sub
        (hasDerivAt_id x)).hasDerivWithinAt using 1 <;> simp [div_eq_mul_inv]
    · intro x hx
      have hxpos : 0 < x := ha.trans_le (interior_subset hx).1
      have hxb : x ≤ b := (interior_subset hx).2
      exact sub_nonneg.mpr ((le_div_iff₀ hxpos).mpr (by simpa using hxb))
  have h := hconv.2 (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at h
  dsimp [f] at h
  dsimp [g]
  have heq : (1/2:ℝ)*a+(1/2)*b = (a+b)/2 := by ring
  rw [heq] at h
  nlinarith only [h]

private lemma midpoint_bound (n : ℕ) :
    (9/1024 : ℝ) * ((n : ℝ)+1) * Real.sqrt ((node n + node (n+1))/2) ≤
      interpolant ((node n + node (n+1))/2) - g ((node n + node (n+1))/2) := by
  let t : ℝ := (n : ℝ)+1
  have ht : 1 ≤ t := by dsimp [t]; positivity
  have ht0 : 0 < t := by linarith
  have ha : node n = t^6 := rfl
  have hb : node (n+1) = (t+1)^6 := by simp [node, t, Nat.cast_add]; ring
  have hgap : 6*t^5 ≤ node (n+1)-node n := by
    rw [ha, hb]
    nlinarith [sq_nonneg t, pow_nonneg ht0.le 3, pow_nonneg ht0.le 4, pow_nonneg ht0.le 5]
  have hbnd : node (n+1) ≤ 64*t^6 := by
    rw [hb]
    calc
      (t+1)^6 ≤ (2*t)^6 := by gcongr; linarith
      _ = 64*t^6 := by ring
  have hsqrt : Real.sqrt ((node n+node (n+1))/2) ≤ 8*t^3 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hnn := (node_strict (Nat.lt_succ_self n)).le
    nlinarith only [hbnd, hnn]
  have hg := log_midpoint_gap (node_pos n) (node_strict (Nat.lt_succ_self n)).le
  have hl := line_le_interpolant n ((node n+node (n+1))/2)
  have hline : line n ((node n+node (n+1))/2) = (g (node n)+g (node (n+1)))/2 := by
    dsimp [line, secantSlope]
    field_simp [(sub_pos.mpr (node_strict (Nat.lt_succ_self n))).ne']
    <;> ring
  rw [hline] at hl
  have he := mul_le_mul_of_nonneg_left hl (node_pos (n+1)).le
  have hgap2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 6*t^5) hgap 2
  have hbase : (9/128 : ℝ)*t^4 ≤
      interpolant ((node n+node (n+1))/2)-g ((node n+node (n+1))/2) := by
    have hdiff : 0 ≤ interpolant ((node n+node (n+1))/2)-g ((node n+node (n+1))/2) := by
      have hprod : 0 ≤ node (n+1) *
          (interpolant ((node n+node (n+1))/2)-g ((node n+node (n+1))/2)) := by
        nlinarith only [hg, he, sq_nonneg (node (n+1)-node n)]
      exact (mul_nonneg_iff_of_pos_left (node_pos (n+1))).mp hprod
    have hm := mul_le_mul_of_nonneg_right hbnd hdiff
    have ht6 : 0 < t^6 := pow_pos ht0 6
    apply (mul_le_mul_iff_of_pos_right ht6).mp
    nlinarith only [hg, he, hgap2, hm]
  calc
    _ ≤ (9/1024 : ℝ)*t*(8*t^3) := mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = (9/128 : ℝ)*t^4 := by ring
    _ ≤ _ := hbase

/-- One global convex function matches every positive sixth power but has growing
square-root-normalized midpoint deviations. -/
theorem sixth_power_convex_sampling_countermodel :
    ∃ H : ℝ → ℝ, ConvexOn ℝ univ H ∧
      (∀ n : ℕ, 1 ≤ n → H ((n : ℝ)^6) = (n : ℝ)^6 * Real.log ((n : ℝ)^6)) ∧
      (∀ n : ℕ, 1 ≤ n →
        (9/1024 : ℝ) * (n : ℝ) * Real.sqrt (((n : ℝ)^6+((n : ℝ)+1)^6)/2) ≤
        H (((n : ℝ)^6+((n : ℝ)+1)^6)/2) -
          (((n : ℝ)^6+((n : ℝ)+1)^6)/2) * Real.log (((n : ℝ)^6+((n : ℝ)+1)^6)/2)) := by
  refine ⟨interpolant, interpolant_convex, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa [node, g, Nat.cast_add] using interpolant_node m
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa [node, g, Nat.cast_add, add_assoc] using midpoint_bound m

end D5.S3.Weil.ZetaExplicit.SixthPowerSampling
