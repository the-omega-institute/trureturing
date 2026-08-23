/- GID: D5/S3/Analytic/Zeta/ZetaRenyiCriticalDivergence
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The zeta law's Renyi entropy diverges at its critical temperature. -/

import Mathlib
/- Provenance: Native proof over pinned mathlib. -/
import D5.S3.Analytic.Zeta.ZetaEntropyDivergence
import D5.S3.Analytic.Zeta.ZetaRenyiEntropy

/-!
Library-search audit (2026-08-23): the repository was searched for every occurrence of
`countableRenyiEntropy`, for zeta-Renyi `Tendsto` declarations, and for the Shannon critical
limit.  The only existing Renyi limits vary the order: `zeta_renyi_entropy_tendsto_min_entropy`
and `zeta_renyi_entropy_tendsto_entropy`.  The reusable temperature-limit hits were
`partition_log_tendsto_atTop` and its public general tool
`log_tendsto_atTop_of_pos_simple_pole` in `ZetaEntropyDivergence.lean`.

Pinned mathlib was searched for Riemann-zeta continuity and positivity, one-sided neighborhood
transport under multiplication, logarithms of quotients and real powers, and multiplication of
`atTop`/`atBot` limits by signed constants.  The proof uses
`differentiableAt_riemannZeta`, `riemannZeta_re_pos_of_one_lt`, `Real.log_div`,
`Real.log_rpow`, `tendsto_nhdsWithin_iff`, and the signed `Filter.Tendsto` limit API.  Mathlib has
no Renyi-entropy definition or theorem.

The two order regimes genuinely have different critical temperatures.  For `1 < alpha`, the
domain boundary is `s = 1`: `Z(s)` diverges while `Z(alpha * s)` stays finite, and the negative
coefficient `1 / (1 - alpha)` reverses the resulting `atBot` logarithmic bracket.  For
`0 < alpha < 1`, the boundary is `s = 1 / alpha`: now `Z(alpha * s)` diverges while `Z(s)` stays
finite, and the coefficient is positive.  Order one must be excluded: Lean's totalized division
makes `countableRenyiEntropy 1 p = 0`, so the literal function is identically zero rather than
divergent.

A numerical sanity check of the same closed form gave `H_2(1.1) = 4.319630940585011` and
`H_2(1.01) = 8.735390547079208`, and `H_0.5(2.05) = 6.936234288935405` and
`H_0.5(2.005) = 11.490952487859513`; both values grow as the applicable critical point is
approached.  Temporary `#print axioms` probes reported exactly
`[propext, Classical.choice, Quot.sound]` for both public declarations and were then removed.
-/

namespace D5.S3.Analytic.Zeta.ZetaRenyiCriticalDivergence

open Filter Set
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropyDivergence
open D5.S3.Analytic.Zeta.ZetaRenyiEntropy

noncomputable section

private lemma zeta_renyi_entropy_eq_log_sub (s alpha : ℝ) (hs : 1 < s)
    (halpha_ne_one : alpha ≠ 1) (halpha_s : 1 < alpha * s) :
    countableRenyiEntropy alpha (zetaDist s hs) =
      (1 / (1 - alpha)) *
        (Real.log (riemannZeta ((alpha * s : ℝ) : ℂ)).re -
          alpha * Real.log (riemannZeta (s : ℂ)).re) := by
  rw [zeta_renyi_entropy_eq s alpha hs halpha_ne_one halpha_s]
  have hZs : 0 < (riemannZeta (s : ℂ)).re := riemannZeta_re_pos_of_one_lt hs
  have hZas : 0 < (riemannZeta ((alpha * s : ℝ) : ℂ)).re :=
    riemannZeta_re_pos_of_one_lt halpha_s
  rw [Real.log_div hZas.ne' (Real.rpow_pos_of_pos hZs alpha).ne',
    Real.log_rpow hZs alpha]

private lemma zeta_log_continuousAt_of_one_lt (t : ℝ) (ht : 1 < t) :
    ContinuousAt (fun x : ℝ => Real.log (riemannZeta (x : ℂ)).re) t := by
  have hzeta : ContinuousAt (fun x : ℝ => (riemannZeta (x : ℂ)).re) t := by
    refine Complex.continuous_re.continuousAt.comp ?_
    refine (differentiableAt_riemannZeta ?_).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
    exact_mod_cast ht.ne'
  exact hzeta.log (riemannZeta_re_pos_of_one_lt ht).ne'

private lemma zeta_log_tendsto_atTop :
    Tendsto (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re)
      (nhdsWithin 1 (Ioi 1)) atTop := by
  apply partition_log_tendsto_atTop.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [partition_toReal_eq_zeta_re s hs]

private lemma tendsto_mul_critical_right (alpha : ℝ) (halpha : 0 < alpha) :
    Tendsto (fun s : ℝ => alpha * s)
      (nhdsWithin (1 / alpha) (Ioi (1 / alpha))) (nhdsWithin 1 (Ioi 1)) := by
  have hcont : Tendsto (fun s : ℝ => alpha * s) (nhds (1 / alpha)) (nhds 1) := by
    have hmul : ContinuousAt (fun s : ℝ => alpha * s) (1 / alpha) :=
      continuousAt_const.mul continuousAt_id
    convert hmul.tendsto using 1
    field_simp
  refine tendsto_nhdsWithin_iff.mpr
    ⟨hcont.mono_left (nhdsWithin_le_nhds :
      nhdsWithin (1 / alpha) (Ioi (1 / alpha)) ≤ nhds (1 / alpha)), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  calc
    1 = alpha * (1 / alpha) := by field_simp
    _ < alpha * s := mul_lt_mul_of_pos_left hs halpha

/-- For Renyi order strictly above one, the zeta law's Renyi entropy diverges as the inverse
temperature decreases to `1`.  Order one is excluded because totalized division makes the
literal order-one Renyi entropy identically zero. -/
theorem zeta_renyi_entropy_tendsto_atTop_of_one_lt (alpha : ℝ) (halpha : 1 < alpha) :
    Tendsto
      (fun s : ℝ => if hs : 1 < s then
        countableRenyiEntropy alpha (zetaDist s hs) else 0)
      (nhdsWithin 1 (Ioi 1)) atTop := by
  let L : ℝ → ℝ := fun t => Real.log (riemannZeta (t : ℂ)).re
  have halpha_pos : 0 < alpha := zero_lt_one.trans halpha
  have hfinite : Tendsto (fun s : ℝ => L (alpha * s))
      (nhdsWithin 1 (Ioi 1)) (nhds (L alpha)) := by
    have hscale : Tendsto (fun s : ℝ => alpha * s) (nhds 1) (nhds alpha) := by
      have hmul : ContinuousAt (fun s : ℝ => alpha * s) 1 :=
        continuousAt_const.mul continuousAt_id
      simpa using hmul.tendsto
    exact ((zeta_log_continuousAt_of_one_lt alpha halpha).tendsto.comp hscale).mono_left
      nhdsWithin_le_nhds
  have hpole : Tendsto (fun s : ℝ => L s) (nhdsWithin 1 (Ioi 1)) atTop := by
    simpa only [L] using zeta_log_tendsto_atTop
  have hscaled : Tendsto (fun s : ℝ => alpha * L s)
      (nhdsWithin 1 (Ioi 1)) atTop := hpole.const_mul_atTop halpha_pos
  have hbracket : Tendsto (fun s : ℝ => L (alpha * s) - alpha * L s)
      (nhdsWithin 1 (Ioi 1)) atBot := by
    simpa only [sub_eq_add_neg, Function.comp_apply] using
      hfinite.add_atBot (tendsto_neg_atTop_atBot.comp hscaled)
  have hcoefficient : 1 / (1 - alpha) < 0 := one_div_neg.mpr (sub_neg.mpr halpha)
  apply (hbracket.const_mul_atBot_of_neg hcoefficient).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 1 < s := hs
  have halpha_s : 1 < alpha * s := by
    have hprod : 0 < (alpha - 1) * s :=
      mul_pos (sub_pos.mpr halpha) (zero_lt_one.trans hs')
    nlinarith
  rw [show (if hs : 1 < s then countableRenyiEntropy alpha (zetaDist s hs) else 0) =
      countableRenyiEntropy alpha (zetaDist s hs') by simp [hs']]
  simpa only [L] using
    (zeta_renyi_entropy_eq_log_sub s alpha hs' halpha.ne' halpha_s).symm

/-- For Renyi order strictly between zero and one, the zeta law's Renyi entropy diverges as the
inverse temperature decreases to `1 / alpha`.  Here `Z(alpha * s)`, rather than `Z(s)`, reaches
its pole.  The conjunction in the `dite` is the closed form's full domain; order one is excluded
because its totalized Renyi entropy is identically zero. -/
theorem zeta_renyi_entropy_tendsto_atTop_of_lt_one (alpha : ℝ) (halpha : 0 < alpha)
    (halpha_one : alpha < 1) :
    Tendsto
      (fun s : ℝ => if hs : 1 < s ∧ 1 < alpha * s then
        countableRenyiEntropy alpha (zetaDist s hs.1) else 0)
      (nhdsWithin (1 / alpha) (Ioi (1 / alpha))) atTop := by
  let L : ℝ → ℝ := fun t => Real.log (riemannZeta (t : ℂ)).re
  have hcritical : 1 < 1 / alpha := (one_lt_div halpha).mpr halpha_one
  have hpole : Tendsto (fun s : ℝ => L (alpha * s))
      (nhdsWithin (1 / alpha) (Ioi (1 / alpha))) atTop := by
    exact (show Tendsto L (nhdsWithin 1 (Ioi 1)) atTop by
      simpa only [L] using zeta_log_tendsto_atTop).comp
        (tendsto_mul_critical_right alpha halpha)
  have hfinite : Tendsto (fun s : ℝ => alpha * L s)
      (nhdsWithin (1 / alpha) (Ioi (1 / alpha))) (nhds (alpha * L (1 / alpha))) := by
    exact tendsto_const_nhds.mul
      ((zeta_log_continuousAt_of_one_lt (1 / alpha) hcritical).tendsto.mono_left
        nhdsWithin_le_nhds)
  have hbracket : Tendsto (fun s : ℝ => L (alpha * s) - alpha * L s)
      (nhdsWithin (1 / alpha) (Ioi (1 / alpha))) atTop := by
    simpa only [sub_eq_add_neg] using hpole.atTop_add hfinite.neg
  have hcoefficient : 0 < 1 / (1 - alpha) := one_div_pos.mpr (sub_pos.mpr halpha_one)
  apply (hbracket.const_mul_atTop hcoefficient).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 1 < s := hcritical.trans hs
  have halpha_s : 1 < alpha * s := by
    calc
      1 = alpha * (1 / alpha) := by field_simp
      _ < alpha * s := mul_lt_mul_of_pos_left hs halpha
  rw [show (if hs : 1 < s ∧ 1 < alpha * s then
      countableRenyiEntropy alpha (zetaDist s hs.1) else 0) =
        countableRenyiEntropy alpha (zetaDist s hs') by simp [hs', halpha_s]]
  simpa only [L] using
    (zeta_renyi_entropy_eq_log_sub s alpha hs' (ne_of_lt halpha_one) halpha_s).symm

end

end D5.S3.Analytic.Zeta.ZetaRenyiCriticalDivergence
