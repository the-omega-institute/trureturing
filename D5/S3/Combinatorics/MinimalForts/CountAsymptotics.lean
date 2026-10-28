/- GID: D5/S3/Combinatorics/MinimalForts/CountAsymptotics
   generality: I
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/CountAsymptotics
   mirror-E: none(waiver:count-asymptotic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecificLimits.Normed]
   utility: none
   digest: Feasible vanishing logarithmic error implies normalization of the actual complete mixed-graph fort counts. -/

import D5.S3.Combinatorics.MinimalForts.MixedBlocks
import D5.S3.Combinatorics.MinimalForts.BlockParameters
import Mathlib.Analysis.SpecificLimits.Normed

/-! The full graph counts split into a normalized exponential term and a negligible linear term. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.CountAsymptotics

open Filter Topology
open D5.S3.Combinatorics.MinimalForts.UniversalRoot
open D5.S3.Combinatorics.MinimalForts.BlockParameters

private theorem log_identity (x y z k : ℕ) (r : Fin 6) (hsum : x + y + z = k) :
    Real.log (((r.val : ℝ) + 2) * 6 ^ x * 9 ^ y * 12 ^ z /
      rate ^ (6 * k + r.val + 3)) =
      (x : ℝ) * negativeIncrement + (z : ℝ) * positiveIncrement -
        ((k : ℝ) * slope + offset r) := by
  have hq : 0 < rate := by norm_num [rate]
  have h6 : Real.log (6 : ℝ) = Real.log 9 + negativeIncrement := by
    dsimp [negativeIncrement]
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h12 : Real.log (12 : ℝ) = Real.log 9 + positiveIncrement := by
    dsimp [positiveIncrement]
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hs : (x : ℝ) + y + z = k := by exact_mod_cast hsum
  rw [Real.log_div (by positivity) (by positivity [rate]),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, h6, h12]
  dsimp [BlockParameters.slope, offset]
  rw [← hs]
  ring

/-- The actual full fort count, including the additive root-free class, is normalized. -/
theorem mixed_count_normalization (r : Fin 6) (x y z : ℕ → ℕ)
    (hsum : ∀ k, x k + y k + z k = k)
    (hlim : Tendsto (fun k => (x k : ℝ) * negativeIncrement +
      (z k : ℝ) * positiveIncrement - ((k : ℝ) * slope + offset r)) atTop (𝓝 0)) :
    Tendsto (fun k =>
      ((minimalForts (MixedBlocks.graph (x k) (y k) (z k) r.val)).card : ℝ) /
        rate ^ (6 * k + r.val + 3)) atTop (𝓝 1) := by
  have hq : 0 < rate := by norm_num [rate]
  let P (k : ℕ) : ℝ := ((r.val : ℝ) + 2) * 6 ^ x k * 9 ^ y k * 12 ^ z k
  let R (k : ℕ) : ℝ := 15 * x k + 6 * y k + 11 * z k + (r.val + 2).choose 2
  have hP : Tendsto (fun k => P k / rate ^ (6 * k + r.val + 3)) atTop (𝓝 1) := by
    have he := Real.continuous_exp.continuousAt.tendsto.comp hlim
    simp only [Real.exp_zero] at he
    convert he using 1
    ext k
    dsimp only [Function.comp_apply]
    rw [← log_identity (x k) (y k) (z k) k r (hsum k), Real.exp_log (by positivity [P, rate])]
  have hR : Tendsto (fun k => R k / rate ^ (6 * k + r.val + 3)) atTop (𝓝 0) := by
    have hlin := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num [rate] : 1 < rate)).const_mul 15
    have hc := (tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num [rate] : 1 < rate)).const_mul
      (((r.val + 2).choose 2 : ℕ) : ℝ)
    have hb : Tendsto (fun k : ℕ => (15 * (k : ℝ) + (r.val + 2).choose 2) / rate ^ k)
        atTop (𝓝 0) := by
      convert hlin.add hc using 1 <;> simp [pow_one, pow_zero, div_eq_mul_inv, add_mul, mul_assoc]
    apply squeeze_zero (fun k => by positivity [R, rate]) (fun k => ?_) hb
    have hs : (x k : ℝ) + y k + z k = k := by exact_mod_cast hsum k
    have hnum : R k ≤ 15 * (k : ℝ) + (r.val + 2).choose 2 := by dsimp [R]; nlinarith
    exact (div_le_div_of_nonneg_right hnum (by positivity [rate])).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity [rate])
        (pow_le_pow_right₀ (by norm_num [rate]) (by omega)))
  have hcount (k : ℕ) :
      ((minimalForts (MixedBlocks.graph (x k) (y k) (z k) r.val)).card : ℝ) = P k + R k := by
    rw [(MixedBlocks.mixed_graph_count _ _ _ _).2.2]
    push_cast
    dsimp [P, R]
    ring
  convert hP.add hR using 1
  · ext k
    rw [hcount, add_div]
  · norm_num

/-- Finite residue selection preserves convergence when the block index tends to infinity. -/
theorem finite_diagonal {ι : Type*} [Finite ι] (f : ι → ℕ → ℝ) (l : ℝ)
    (hf : ∀ i, Tendsto (f i) atTop (𝓝 l)) (a : ℕ → ι) (b : ℕ → ℕ)
    (hb : Tendsto b atTop atTop) : Tendsto (fun n => f (a n) (b n)) atTop (𝓝 l) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he : ∀ᶠ k in atTop, ∀ i, dist (f i k) l < ε :=
    Filter.eventually_all.mpr (fun i => (Metric.tendsto_atTop.mp (hf i) ε hε).choose_spec
      |> fun h => Filter.eventually_atTop.mpr ⟨_, h⟩)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hb.eventually he)
  exact ⟨N, fun n hn => hN n hn (a n)⟩

end D5.S3.Combinatorics.MinimalForts.CountAsymptotics
