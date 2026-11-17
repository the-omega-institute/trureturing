/- GID: D5/S3/Analytic/YangChuZhangPsiCM/Refutation
   generality: G
   mirror-B: D5/B/S3/Analytic/YangChuZhangPsiCM/Refutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/YangChuZhangPsiCM/Refutation.claim; result=D5/S3/Analytic/YangChuZhangPsiCM/Refutation.result; claim=D5/S3/Analytic/YangChuZhangPsiCM/Refutation.claim
   digest: Refute Yang-Chu-Zhang Conjecture 1(ii) by a negative second derivative. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#21602; Refuted)
  Direct frozen dependencies:
    D5/S3/Analytic/ExpRatioCM/Defs.CompletelyMonotoneOn sha256:f25bdc23dc3c3d7bb2a8e428111edb1df2af60971e1fe8d8bb2e2ab069581ea0
    D5/S3/Weil/ZetaGamma/AnalyticStirling.hasSum_trigamma sha256:7fe2194b4c44e460f801d3a12d89afeefc1b7d461fa4ab83e453e97f9bbc9b21
    D5/S3/Weil/ZetaGamma/AnalyticStirling.differentiableAt_digamma sha256:3419a1f11efb8693377d563c01ebbe886eaa209078a71491400378130272c122
    D5/S3/Weil/ZetaGamma/GammaMu.abscissa_mem sha256:34e0d9a476626c722ca6cba1919a118c4388b48efe63be36921c55c77afc0c65

The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The complete-monotonicity predicate is reused from ExpRatioCM.Defs, retaining smoothness
and every natural derivative order including zero. The source real digamma expression
is inlined in R rather than adding a forwarding abbreviation alongside
A400361SecondTerm.realDigamma. R and G retain (1.10), (3.3). The reciprocal-square
and reciprocal-cube series use the existing
D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.sourceHurwitz owner at
exponents 2 and 3 directly; its declaration statement_id is
sha256:809e18c661a3cb1913b33569128c54a454432242feb57b97ac16b841f931c86b.
All supporting theorems are consumed helpers, with proof_shape: bind-only and
escape_witness: none. Their calculus, order and series inputs are instantiated before
algebraic normalization; the reciprocal-cube tail uses a telescoping rational majorant.

Supporting declarations (same-delivery helpers are inlined for dependency lists):
R:
  proof_shape: bind-only
  escape_witness: none
  consumers: G, R_lower, G1, G2, R_hasDerivAt, uniform_second_deriv
  Direct frozen dependencies: none
G:
  proof_shape: bind-only
  escape_witness: none
  consumers: claim, G_hasDerivAt, second_deriv_G, uniform_second_deriv, result
  Direct frozen dependencies: none
claim:
  proof_shape: bind-only
  escape_witness: none
  consumers: result
  Direct frozen dependencies:
    D5/S3/Analytic/ExpRatioCM/Defs.CompletelyMonotoneOn sha256:f25bdc23dc3c3d7bb2a8e428111edb1df2af60971e1fe8d8bb2e2ab069581ea0
real_mem:
  proof_shape: bind-only
  escape_witness: none
  consumers: psi_hasDerivAt, summable_sq
  Direct frozen dependencies:
    D5/S3/Weil/ZetaGamma/GammaMu.abscissa_mem sha256:34e0d9a476626c722ca6cba1919a118c4388b48efe63be36921c55c77afc0c65
psi_hasDerivAt:
  proof_shape: bind-only
  escape_witness: none
  consumers: R_lower, R_hasDerivAt
  Direct frozen dependencies:
    D5/S3/Weil/ZetaGamma/AnalyticStirling.differentiableAt_digamma sha256:3419a1f11efb8693377d563c01ebbe886eaa209078a71491400378130272c122
    D5/S3/Weil/ZetaGamma/GammaMu.abscissa_mem sha256:34e0d9a476626c722ca6cba1919a118c4388b48efe63be36921c55c77afc0c65
    D5/S3/Weil/ZetaGamma/AnalyticStirling.hasSum_trigamma sha256:7fe2194b4c44e460f801d3a12d89afeefc1b7d461fa4ab83e453e97f9bbc9b21
summable_sq:
  proof_shape: bind-only
  escape_witness: none
  consumers: sourceHurwitz_two_hasDerivAt
  Direct frozen dependencies:
    D5/S3/Weil/ZetaGamma/AnalyticStirling.hasSum_trigamma sha256:7fe2194b4c44e460f801d3a12d89afeefc1b7d461fa4ab83e453e97f9bbc9b21
    D5/S3/Weil/ZetaGamma/GammaMu.abscissa_mem sha256:34e0d9a476626c722ca6cba1919a118c4388b48efe63be36921c55c77afc0c65
summable_shift_cube:
  proof_shape: bind-only
  escape_witness: none
  consumers: sourceHurwitz_two_hasDerivAt
  Direct frozen dependencies: none
sourceHurwitz_two_hasDerivAt:
  proof_shape: bind-only
  escape_witness: none
  consumers: R1_hasDerivAt
  Direct frozen dependencies:
    D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.sourceHurwitz sha256:809e18c661a3cb1913b33569128c54a454432242feb57b97ac16b841f931c86b
    D5/S3/Weil/ZetaGamma/AnalyticStirling.hasSum_trigamma sha256:7fe2194b4c44e460f801d3a12d89afeefc1b7d461fa4ab83e453e97f9bbc9b21
    D5/S3/Weil/ZetaGamma/GammaMu.abscissa_mem sha256:34e0d9a476626c722ca6cba1919a118c4388b48efe63be36921c55c77afc0c65
sourceHurwitz_two_nonneg:
  proof_shape: bind-only
  escape_witness: none
  consumers: R_lower, R1_lower
  Direct frozen dependencies:
    D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.sourceHurwitz sha256:809e18c661a3cb1913b33569128c54a454432242feb57b97ac16b841f931c86b
R_lower:
  proof_shape: bind-only
  escape_witness: none
  consumers: uniform_second_deriv
  Direct frozen dependencies:
    D5/S3/Weil/ZetaGamma/AnalyticStirling.differentiableAt_digamma sha256:3419a1f11efb8693377d563c01ebbe886eaa209078a71491400378130272c122
    D5/S3/Weil/ZetaGamma/GammaMu.abscissa_mem sha256:34e0d9a476626c722ca6cba1919a118c4388b48efe63be36921c55c77afc0c65
    D5/S3/Weil/ZetaGamma/AnalyticStirling.hasSum_trigamma sha256:7fe2194b4c44e460f801d3a12d89afeefc1b7d461fa4ab83e453e97f9bbc9b21
sourceHurwitz_three_bound:
  proof_shape: bind-only
  escape_witness: none
  consumers: R2_lower
  Direct frozen dependencies:
    D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder.sourceHurwitz sha256:809e18c661a3cb1913b33569128c54a454432242feb57b97ac16b841f931c86b
coefficient_bound:
  proof_shape: bind-only
  escape_witness: none
  consumers: uniform_second_deriv
  Direct frozen dependencies: none
R1:
  proof_shape: bind-only
  escape_witness: none
  consumers: G1, G2, R_hasDerivAt, R1_hasDerivAt, R1_lower, uniform_second_deriv
  Direct frozen dependencies: none
R2:
  proof_shape: bind-only
  escape_witness: none
  consumers: G2, R1_hasDerivAt, R2_lower, uniform_second_deriv
  Direct frozen dependencies: none
P:
  proof_shape: bind-only
  escape_witness: none
  consumers: G1, G2, P_hasDerivAt, G_hasDerivAt, uniform_second_deriv
  Direct frozen dependencies: none
P1:
  proof_shape: bind-only
  escape_witness: none
  consumers: G1, G2, P_hasDerivAt, P1_hasDerivAt, uniform_second_deriv
  Direct frozen dependencies: none
P2:
  proof_shape: bind-only
  escape_witness: none
  consumers: G2, P1_hasDerivAt, uniform_second_deriv
  Direct frozen dependencies: none
G1:
  proof_shape: bind-only
  escape_witness: none
  consumers: G_hasDerivAt, G1_hasDerivAt, second_deriv_G
  Direct frozen dependencies: none
G2:
  proof_shape: bind-only
  escape_witness: none
  consumers: G1_hasDerivAt, second_deriv_G, uniform_second_deriv
  Direct frozen dependencies: none
R_hasDerivAt:
  proof_shape: bind-only
  escape_witness: none
  consumers: G_hasDerivAt, G1_hasDerivAt
  Direct frozen dependencies:
    D5/S3/Weil/ZetaGamma/AnalyticStirling.differentiableAt_digamma sha256:3419a1f11efb8693377d563c01ebbe886eaa209078a71491400378130272c122
    D5/S3/Weil/ZetaGamma/GammaMu.abscissa_mem sha256:34e0d9a476626c722ca6cba1919a118c4388b48efe63be36921c55c77afc0c65
    D5/S3/Weil/ZetaGamma/AnalyticStirling.hasSum_trigamma sha256:7fe2194b4c44e460f801d3a12d89afeefc1b7d461fa4ab83e453e97f9bbc9b21
R1_hasDerivAt:
  proof_shape: bind-only
  escape_witness: none
  consumers: G1_hasDerivAt
  Direct frozen dependencies:
    D5/S3/Weil/ZetaGamma/AnalyticStirling.hasSum_trigamma sha256:7fe2194b4c44e460f801d3a12d89afeefc1b7d461fa4ab83e453e97f9bbc9b21
    D5/S3/Weil/ZetaGamma/GammaMu.abscissa_mem sha256:34e0d9a476626c722ca6cba1919a118c4388b48efe63be36921c55c77afc0c65
P_hasDerivAt:
  proof_shape: bind-only
  escape_witness: none
  consumers: G_hasDerivAt, G1_hasDerivAt
  Direct frozen dependencies: none
P1_hasDerivAt:
  proof_shape: bind-only
  escape_witness: none
  consumers: G1_hasDerivAt
  Direct frozen dependencies: none
G_hasDerivAt:
  proof_shape: bind-only
  escape_witness: none
  consumers: second_deriv_G
  Direct frozen dependencies:
    D5/S3/Weil/ZetaGamma/AnalyticStirling.differentiableAt_digamma sha256:3419a1f11efb8693377d563c01ebbe886eaa209078a71491400378130272c122
    D5/S3/Weil/ZetaGamma/GammaMu.abscissa_mem sha256:34e0d9a476626c722ca6cba1919a118c4388b48efe63be36921c55c77afc0c65
    D5/S3/Weil/ZetaGamma/AnalyticStirling.hasSum_trigamma sha256:7fe2194b4c44e460f801d3a12d89afeefc1b7d461fa4ab83e453e97f9bbc9b21
G1_hasDerivAt:
  proof_shape: bind-only
  escape_witness: none
  consumers: second_deriv_G
  Direct frozen dependencies:
    D5/S3/Weil/ZetaGamma/AnalyticStirling.differentiableAt_digamma sha256:3419a1f11efb8693377d563c01ebbe886eaa209078a71491400378130272c122
    D5/S3/Weil/ZetaGamma/GammaMu.abscissa_mem sha256:34e0d9a476626c722ca6cba1919a118c4388b48efe63be36921c55c77afc0c65
    D5/S3/Weil/ZetaGamma/AnalyticStirling.hasSum_trigamma sha256:7fe2194b4c44e460f801d3a12d89afeefc1b7d461fa4ab83e453e97f9bbc9b21
second_deriv_G:
  proof_shape: bind-only
  escape_witness: none
  consumers: uniform_second_deriv
  Direct frozen dependencies:
    D5/S3/Weil/ZetaGamma/AnalyticStirling.differentiableAt_digamma sha256:3419a1f11efb8693377d563c01ebbe886eaa209078a71491400378130272c122
    D5/S3/Weil/ZetaGamma/GammaMu.abscissa_mem sha256:34e0d9a476626c722ca6cba1919a118c4388b48efe63be36921c55c77afc0c65
    D5/S3/Weil/ZetaGamma/AnalyticStirling.hasSum_trigamma sha256:7fe2194b4c44e460f801d3a12d89afeefc1b7d461fa4ab83e453e97f9bbc9b21
R1_lower:
  proof_shape: bind-only
  escape_witness: none
  consumers: uniform_second_deriv
  Direct frozen dependencies: none
R2_lower:
  proof_shape: bind-only
  escape_witness: none
  consumers: uniform_second_deriv
  Direct frozen dependencies: none
uniform_second_deriv:
  proof_shape: bind-only
  escape_witness: none
  consumers: result
  Direct frozen dependencies:
    D5/S3/Weil/ZetaGamma/AnalyticStirling.differentiableAt_digamma sha256:3419a1f11efb8693377d563c01ebbe886eaa209078a71491400378130272c122
    D5/S3/Weil/ZetaGamma/GammaMu.abscissa_mem sha256:34e0d9a476626c722ca6cba1919a118c4388b48efe63be36921c55c77afc0c65
    D5/S3/Weil/ZetaGamma/AnalyticStirling.hasSum_trigamma sha256:7fe2194b4c44e460f801d3a12d89afeefc1b7d461fa4ab83e453e97f9bbc9b21
-/

import D5.S3.Analytic.ExpRatioCM.Defs
import D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder

import D5.S3.Weil.ZetaGamma.AnalyticStirling
import D5.S3.Weil.ZetaGamma.GammaMu
import Mathlib.Analysis.Calculus.SmoothSeries

namespace D5.S3.Analytic.YangChuZhangPsiCM.Refutation

-- Source (1.10), for x > 0.
noncomputable def R (x : ℝ) : ℝ := (Complex.digamma ((x + 1 / 2 : ℝ) : ℂ)).re - Real.log x

-- Source (3.3); a is an arbitrary real parameter.
noncomputable def G (a x : ℝ) : ℝ :=
  24 * (x ^ 4 + a * x ^ 2 + (7 / 40 : ℝ) * a - 31 / 336) * R x -
    (x ^ 2 - 7 / 40 + a)

-- Reuse the existing complete-monotonicity owner, whose full definition is
-- ContDiffOn ℝ ⊤ f (Set.Ioi 0) ∧
--   ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1) ^ n * iteratedDeriv n f x.
-- Thus n = 0 is included and every x in (0, ∞) is quantified.
-- Source Conjecture 1(ii), with both directions of the equivalence retained.
def claim : Prop :=
  ∀ a : ℝ, D5.S3.Analytic.ExpRatioCM.Defs.CompletelyMonotoneOn (fun x : ℝ => -G a x) ↔
    a ≤ (155 / 294 : ℝ)

end D5.S3.Analytic.YangChuZhangPsiCM.Refutation

namespace D5.S3.Analytic.YangChuZhangPsiCM.Refutation
open Filter Topology
set_option maxHeartbeats 1600000

private theorem real_mem {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    (x : ℂ) ∈ Complex.integerComplement := by
  simpa using (Zeta23.MuFields.abscissa_mem hx hx1 0)

private theorem psi_hasDerivAt {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y : ℝ => (Complex.digamma (y : ℂ)).re) (D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz 2 x) x := by
  have hr := (Zeta23.Stirling.differentiableAt_digamma (real_mem hx hx1)).hasDerivAt.real_of_complex
  have hs := Complex.hasSum_re (Zeta23.Stirling.hasSum_trigamma (real_mem hx hx1))
  have hs' : HasSum (fun n : ℕ => 1 / (x + n) ^ 2)
      (deriv Complex.digamma (x : ℂ)).re := by
    convert hs using 1
    ext n
    rw [show (x : ℂ) + (n : ℂ) = ((x + (n : ℝ) : ℝ) : ℂ) by push_cast; rfl]
    norm_cast
  change HasDerivAt (fun y : ℝ => (Complex.digamma (y : ℂ)).re) (deriv Complex.digamma (x : ℂ)).re x at hr
  rw [D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz]
  rw [← hs'.tsum_eq] at hr
  convert hr using 1
  apply tsum_congr
  intro n
  congr 1
  ring

private theorem summable_sq {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    Summable (fun n : ℕ => 1 / (x + n) ^ 2) := by
  have hs := Complex.hasSum_re (Zeta23.Stirling.hasSum_trigamma (real_mem hx hx1))
  convert hs.summable using 1
  ext n
  rw [show (x : ℂ) + (n : ℂ) = ((x + (n : ℝ) : ℝ) : ℂ) by push_cast; rfl]
  norm_cast


private theorem summable_shift_cube : Summable (fun n : ℕ => 16 / ((n : ℝ) + 1) ^ 3) := by
  have hs := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
  convert hs.mul_left 16 using 1
  funext n
  simp [Nat.cast_add, div_eq_mul_inv]

private theorem sourceHurwitz_two_hasDerivAt {x : ℝ} (hx : 1 / 2 < x) (hx1 : x < 1) :
    HasDerivAt (D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz 2) (-2 * D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz 3 x) x := by
  have hg (n : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (1 / 2 : ℝ) 1) :
      HasDerivAt (fun y : ℝ => 1 / (y + n) ^ 2) (-2 / (y + n) ^ 3) y := by
    have hn : y + n ≠ 0 := ne_of_gt (by linarith [hy.1, (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)])
    convert ((((hasDerivAt_id y).add_const (n : ℝ)).pow 2).inv (pow_ne_zero 2 hn)) using 1
    · funext z
      simp [one_div]
    · dsimp
      field_simp [hn]
  have hb (n : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (1 / 2 : ℝ) 1) :
      ‖-2 / (y + n) ^ 3‖ ≤ 16 / ((n : ℝ) + 1) ^ 3 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hyp : 0 < y + n := by linarith [hy.1]
    norm_num only [norm_div, Real.norm_eq_abs, abs_of_pos (pow_pos hyp 3), abs_neg, show |(2 : ℝ)| = 2 by norm_num]
    calc 2 / (y + n) ^ 3 ≤ 2 / (((n : ℝ) + 1) / 2) ^ 3 := by gcongr; linarith [hy.1]
         _ = 16 / ((n : ℝ) + 1) ^ 3 := by field_simp; ring
  have hd := hasDerivAt_tsum_of_isPreconnected summable_shift_cube isOpen_Ioo
    (convex_Ioo (1 / 2 : ℝ) 1).isPreconnected hg hb
    (show x ∈ Set.Ioo (1 / 2 : ℝ) 1 from ⟨hx, hx1⟩)
    (summable_sq (by linarith) hx1)
    (show x ∈ Set.Ioo (1 / 2 : ℝ) 1 from ⟨hx, hx1⟩)
  have he : (∑' n : ℕ, -2 / (x + n) ^ 3) = -2 * D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz 3 x := by
    rw [D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz,
      ← tsum_mul_left]
    congr 1
    ext n
    ring
  rw [he] at hd
  have hfun :
      (fun z : ℝ => ∑' n : ℕ, 1 / (z + n) ^ 2) =
        D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz 2 := by
    funext y
    rw [D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz]
    apply tsum_congr
    intro n
    congr 1
    ring
  rw [← hfun]
  exact hd

private theorem sourceHurwitz_two_nonneg (x : ℝ) : 0 ≤ D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz 2 x := by
  exact tsum_nonneg fun n => by positivity

private theorem R_lower : (5 / 3 : ℝ) < R (1 / 64) := by
  have hm : MonotoneOn (fun y : ℝ => (Complex.digamma (y : ℂ)).re) (Set.Icc (1 / 2 : ℝ) (33 / 64)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz 2) (convex_Icc _ _)
    · intro x hx
      exact (psi_hasDerivAt (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      have hi : x ∈ Set.Icc (1 / 2 : ℝ) (33 / 64) := interior_subset hx
      exact (psi_hasDerivAt (by linarith [hi.1]) (by linarith [hi.2])).hasDerivWithinAt
    · intro x hx
      exact sourceHurwitz_two_nonneg x
  have hmono : (Complex.digamma ((1 / 2 : ℝ) : ℂ)).re ≤ (Complex.digamma ((33 / 64 : ℝ) : ℂ)).re := hm (by norm_num) (by norm_num) (by norm_num)
  have hhalf : (Complex.digamma ((1 / 2 : ℝ) : ℂ)).re = -2 * Real.log 2 - Real.eulerMascheroniConstant := by
    have h := congrArg Complex.re Complex.digamma_one_half
    simpa [Complex.log_re] using h
  have hlog : Real.log (1 / 64 : ℝ) = -6 * Real.log 2 := by
    rw [show (1 / 64 : ℝ) = (2 ^ 6 : ℝ)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    ring
  change 5 / 3 < (Complex.digamma ((1 / 64 + 1 / 2 : ℝ) : ℂ)).re - Real.log (1 / 64)
  rw [show (1 / 64 + 1 / 2 : ℝ) = 33 / 64 by norm_num, hlog]
  rw [hhalf] at hmono
  linarith [Real.log_two_gt_d9, Real.eulerMascheroniConstant_lt_two_thirds]


private theorem sourceHurwitz_three_bound : D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz 3 (33 / 64) < 9 := by
  let f : ℕ → ℝ := fun n => 1 / ((33 / 64 : ℝ) + (n + 1)) ^ 3
  have hp (n : ℕ) : f n ≤ 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : 0 < (n : ℝ) + 1 := by exact Nat.cast_add_one_pos n
    have h2 : 0 < (n : ℝ) + 2 := by positivity
    have hpoly : ((n : ℝ) + 1) * (n + 2) ≤ ((33 / 64 : ℝ) + (n + 1)) ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) hn, sq_nonneg (n : ℝ)]
    calc f n ≤ 1 / (((n : ℝ) + 1) * (n + 2)) := by
           dsimp [f]
           exact one_div_le_one_div_of_le (mul_pos h1 h2) hpoly
         _ = 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) := by field_simp; ring
  have hsum (N : ℕ) : ∑ n ∈ Finset.range N, f n ≤ 1 - 1 / ((N : ℝ) + 1) := by
    calc
      ∑ n ∈ Finset.range N, f n ≤
          ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) :=
        Finset.sum_le_sum fun n _ => hp n
      _ = 1 - 1 / ((N : ℝ) + 1) := by
        have ht := Finset.sum_range_sub (fun n : ℕ => -(1 / ((n : ℝ) + 1))) N
        simpa [Nat.cast_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
          show (1 : ℝ) + 1 = 2 by norm_num] using ht
  have hle (N : ℕ) : ∑ n ∈ Finset.range N, f n ≤ 1 := by
    exact (hsum N).trans (by linarith [one_div_nonneg.mpr (show 0 ≤ (N : ℝ) + 1 by positivity)])
  have hs : Summable f := summable_of_sum_range_le (fun n => by dsimp [f]; positivity) hle
  have ht : ∑' n, f n ≤ 1 := Real.tsum_le_of_sum_range_le (fun n => by dsimp [f]; positivity) hle
  have hs' : Summable (fun n : ℕ => 1 / ((33 / 64 : ℝ) + n) ^ 3) := by
    exact (summable_nat_add_iff 1).mp (by simpa [f, Nat.cast_add] using hs)
  have he := hs'.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one] at he
  have he' : 1 / (33 / 64 : ℝ) ^ 3 + ∑' n, f n =
      D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz 3 (33 / 64) := by
    rw [D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz]
    convert he using 1
    apply tsum_congr
    intro n
    ring
  norm_num only [show 1 / (33 / 64 : ℝ) ^ 3 = 262144 / 35937 by norm_num] at he'
  linarith

private theorem coefficient_bound (a v w z : ℝ)
    (ha : (155 / 294 : ℝ) - 1 / 10000 ≤ a)
    (hv : (5 / 3 : ℝ) ≤ v) (hw : (-64 : ℝ) ≤ w) (hz : (4078 : ℝ) ≤ z) :
    (1 / 2 : ℝ) < 24 * ((12 * (1 / 64 : ℝ) ^ 2 + 2 * a) * v +
      (8 * (1 / 64 : ℝ) ^ 3 + 4 * a * (1 / 64)) * w +
      ((1 / 64 : ℝ) ^ 4 + a * (1 / 64) ^ 2 + 7 / 40 * a - 31 / 336) * z) - 2 := by
  have hP : 0 ≤ (1 / 64 : ℝ) ^ 4 + a * (1 / 64) ^ 2 + 7 / 40 * a - 31 / 336 := by
    linarith
  have hC : 0 ≤ 12 * (1 / 64 : ℝ) ^ 2 + 2 * a := by linarith
  have hD : 0 ≤ 8 * (1 / 64 : ℝ) ^ 3 + 4 * a * (1 / 64) := by linarith
  have h0 := mul_le_mul_of_nonneg_left hv hC
  have h1 := mul_le_mul_of_nonneg_left hw hD
  have h2 := mul_le_mul_of_nonneg_left hz hP
  nlinarith


private noncomputable def R1 (x : ℝ) : ℝ := D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz 2 (x + 1 / 2) - 1 / x
private noncomputable def R2 (x : ℝ) : ℝ := -2 * D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder.sourceHurwitz 3 (x + 1 / 2) + 1 / x ^ 2
private noncomputable def P (a x : ℝ) : ℝ := x ^ 4 + a * x ^ 2 + (7 / 40 : ℝ) * a - 31 / 336
private noncomputable def P1 (a x : ℝ) : ℝ := 4 * x ^ 3 + 2 * a * x
private noncomputable def P2 (a x : ℝ) : ℝ := 12 * x ^ 2 + 2 * a
private noncomputable def G1 (a x : ℝ) : ℝ := 24 * (P1 a x * R x + P a x * R1 x) - 2 * x
private noncomputable def G2 (a x : ℝ) : ℝ :=
  24 * (P2 a x * R x + 2 * P1 a x * R1 x + P a x * R2 x) - 2

private theorem R_hasDerivAt {x : ℝ} (hx : 0 < x) (hx1 : x < 1 / 2) :
    HasDerivAt R (R1 x) x := by
  have hp := (psi_hasDerivAt (x := x + 1 / 2) (by linarith) (by linarith)).comp x
    ((hasDerivAt_id x).add_const (1 / 2))
  unfold R R1
  simpa only [Function.comp_def, id_eq, mul_one, one_div] using! hp.fun_sub (Real.hasDerivAt_log (ne_of_gt hx))

private theorem R1_hasDerivAt {x : ℝ} (hx : 0 < x) (hx1 : x < 1 / 2) :
    HasDerivAt R1 (R2 x) x := by
  have ht := (sourceHurwitz_two_hasDerivAt (x := x + 1 / 2) (by linarith) (by linarith)).comp x
    ((hasDerivAt_id x).add_const (1 / 2))
  have hi := (hasDerivAt_const x (1 : ℝ)).fun_div (hasDerivAt_id x) (ne_of_gt hx)
  convert! ht.fun_sub hi using 1
  dsimp [R2]
  ring

private theorem P_hasDerivAt (a x : ℝ) : HasDerivAt (P a) (P1 a x) x := by
  convert! ((((hasDerivAt_id x).pow 4).fun_add (((hasDerivAt_id x).pow 2).const_mul a)).add_const
    ((7 / 40 : ℝ) * a - 31 / 336)) using 1 <;>
    first | (funext y; dsimp [P, P1]; ring) | (dsimp [P, P1]; ring)

private theorem P1_hasDerivAt (a x : ℝ) : HasDerivAt (P1 a) (P2 a x) x := by
  convert! (((hasDerivAt_id x).pow 3).const_mul 4).fun_add
    ((hasDerivAt_id x).const_mul (2 * a)) using 1
  dsimp [P2]
  ring

private theorem G_hasDerivAt (a : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : x < 1 / 2) :
    HasDerivAt (G a) (G1 a x) x := by
  convert! (((P_hasDerivAt a x).fun_mul (R_hasDerivAt hx hx1)).const_mul 24).fun_sub
    ((((hasDerivAt_id x).pow 2).sub_const (7 / 40)).add_const a) using 1 <;>
    first | (funext y; dsimp [G, G1, P]; ring) | (dsimp [G, G1, P]; ring)

private theorem G1_hasDerivAt (a : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : x < 1 / 2) :
    HasDerivAt (G1 a) (G2 a x) x := by
  have hd := ((((P1_hasDerivAt a x).fun_mul (R_hasDerivAt hx hx1)).fun_add
    ((P_hasDerivAt a x).fun_mul (R1_hasDerivAt hx hx1))).const_mul 24).fun_sub
      ((hasDerivAt_id x).const_mul 2)
  convert! hd using 1
  dsimp [G2]
  ring

private theorem second_deriv_G (a : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : x < 1 / 2) :
    iteratedDeriv 2 (G a) x = G2 a x := by
  have he : deriv (G a) =ᶠ[nhds x] G1 a := by
    filter_upwards [Ioo_mem_nhds hx hx1] with y hy
    exact (G_hasDerivAt a hy.1 hy.2).deriv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [he.deriv_eq]
  exact (G1_hasDerivAt a hx hx1).deriv

private theorem R1_lower : (-64 : ℝ) ≤ R1 (1 / 64) := by
  have h := sourceHurwitz_two_nonneg (33 / 64)
  dsimp [R1]
  norm_num
  linarith

private theorem R2_lower : (4078 : ℝ) ≤ R2 (1 / 64) := by
  have h := sourceHurwitz_three_bound
  dsimp [R2]
  norm_num
  norm_num [show (1 / 64 + 1 / 2 : ℝ) = 33 / 64 by norm_num] at *
  linarith

private theorem uniform_second_deriv (a : ℝ) (ha : (155 / 294 : ℝ) - 1 / 10000 ≤ a) :
    (1 / 2 : ℝ) < iteratedDeriv 2 (G a) (1 / 64) := by
  rw [second_deriv_G a (by norm_num) (by norm_num)]
  have h := coefficient_bound a (R (1 / 64)) (R1 (1 / 64)) (R2 (1 / 64)) ha
    R_lower.le R1_lower R2_lower
  convert h using 1
  dsimp [G2, P, P1, P2]
  ring

theorem result : ¬ claim := by
  intro hc
  have hcm := (hc ((155 / 294 : ℝ) - 1 / 10000)).mpr (by norm_num)
  have hs := hcm.2 2 (1 / 64) (by norm_num)
  have hp := uniform_second_deriv ((155 / 294 : ℝ) - 1 / 10000) le_rfl
  change 0 ≤ (-1 : ℝ) ^ 2 * iteratedDeriv 2 (-(G ((155 / 294 : ℝ) - 1 / 10000))) (1 / 64) at hs
  rw [iteratedDeriv_neg] at hs
  norm_num at hs
  linarith


end D5.S3.Analytic.YangChuZhangPsiCM.Refutation
