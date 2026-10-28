/- GID: D5/S3/Arith/Robin/ActualLeastCrossingPriceRecord
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualLeastCrossingPriceRecord
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Uniform actual least crossings have positive-price predecessor records and strict inventory confinement. -/

import D5.S3.Arith.Robin.ActualLeastCrossing5040
import D5.S3.Arith.Robin.ActualTwoPriceDefect

/-! The threshold precedes eta, including eta=1/2. All positive predecessors are
compared. Only occupied layers are confined; no crossing existence or signed Robin
upper bound is asserted. -/

noncomputable section
namespace D5.S3.Arith.Robin.ActualLeastCrossingPriceRecord

open D5.S3.Arith.Robin.OriginalFirstClockTransport
open D5.S3.Arith.Robin.ActualIntegerLogEnvelope
open D5.S3.Arith.Robin.ActualIntegerHeightJump
open D5.S3.Arith.Robin.ActualLeastCrossing5040
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.GoldenLayerMarginalDecay

private theorem strict_scalar_remainder {l beta eta : ℝ} (hl : 2 ≤ l) (hb : 0 < beta)
    (heta : 0 < eta) (hetaHalf : eta ≤ 1 / 2) :
    (1 - (39 / 20 : ℝ) * eta) * beta / (l + beta) <
      Real.log (1 + beta / l) - ((39 / 20 : ℝ) / l) *
        (1 - Real.exp (-eta * beta)) := by
  let c : ℝ := 39 / 20
  let a := c * eta
  let G : ℝ → ℝ := fun u => Real.log (l + u) - Real.log l -
    (c / l) * (1 - Real.exp (-eta * u)) - (1 - a) * u / (l + u)
  have hl0 : 0 < l := by linarith
  have ha : 0 < a := mul_pos (by norm_num [c]) heta
  have ha1 : a < 1 := by dsimp [a, c]; linarith
  have hd (u : ℝ) (hu : 0 ≤ u) : HasDerivAt G
      (1 / (l + u) - (a / l) * Real.exp (-eta * u) -
        (1 - a) * l / (l + u) ^ 2) u := by
    have hlog := ((hasDerivAt_id u).const_add l).log (by linarith : l + u ≠ 0)
    have hexp := (Real.hasDerivAt_exp (-eta * u)).comp u
      ((hasDerivAt_id u).const_mul (-eta))
    have hrat := ((hasDerivAt_id u).const_mul (1 - a)).div
      ((hasDerivAt_id u).const_add l) (by linarith : l + u ≠ 0)
    convert ((hlog.sub_const (Real.log l)).sub
      (((hasDerivAt_const u 1).sub hexp).const_mul (c / l))).sub hrat using 1
    · funext x; dsimp [G]; ring
    · dsimp [a]; ring
  have hmono : StrictMonoOn G (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · intro u hu
      exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Ici, Set.mem_Ioi] at hu
      rw [(hd u hu.le).deriv]
      let t := u / l
      have ht : 0 < t := div_pos hu hl0
      have he : 1 + a * t < Real.exp (eta * u) := by
        have harg : a * t ≤ eta * u := by
          dsimp [a, t, c]
          apply (div_le_iff₀ hl0).mp ?_
          · nlinarith
        have he := Real.add_one_lt_exp (show eta * u ≠ 0 from (mul_pos heta hu).ne')
        linarith
      have hnum : 0 < Real.exp (eta * u) * (a + t) - a * (1 + t) ^ 2 := by
        have hm := mul_lt_mul_of_pos_right he (add_pos ha ht)
        have hid : (1 + a * t) * (a + t) - a * (1 + t) ^ 2 = t * (1 - a) ^ 2 := by ring
        have hp : 0 ≤ t * (1 - a) ^ 2 := mul_nonneg ht.le (sq_nonneg _)
        nlinarith
      have hid : 1 / (l + u) - (a / l) * Real.exp (-eta * u) -
          (1 - a) * l / (l + u) ^ 2 =
          (Real.exp (eta * u) * (a + t) - a * (1 + t) ^ 2) /
            (l * (1 + t) ^ 2 * Real.exp (eta * u)) := by
        rw [show -eta * u = -(eta * u) by ring, Real.exp_neg]
        dsimp [t]
        field_simp
        <;> ring
      rw [hid]
      exact div_pos hnum (by positivity)
  have hg := hmono (show (0 : ℝ) ∈ Set.Ici 0 by simp)
    (show beta ∈ Set.Ici 0 from hb.le) hb
  have hG0 : G 0 = 0 := by simp [G]
  rw [hG0] at hg
  have hid : Real.log (l + beta) - Real.log l = Real.log (1 + beta / l) := by
    rw [← Real.log_div (by linarith : l + beta ≠ 0) hl0.ne']
    congr 1
    field_simp
  dsimp [G] at hg
  rw [hid] at hg
  dsimp [a, c] at hg
  linarith

end D5.S3.Arith.Robin.ActualLeastCrossingPriceRecord
