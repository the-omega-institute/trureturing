/- GID: D5/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/HigherLayerLogSlope
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Uniform logarithmic slope of the actual real higher-layer marginal. -/
import D5.S3.Arith.GoldenResourceOptimalInteger
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The logarithmic slope bound is uniform in the layer index. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
open Finset Real
open D5.S3.Arith.GoldenResourceOptimalInteger

def powerSum (j : ℕ) (u : ℝ) : ℝ := ∑ k ∈ range j, u ^ (k + 1)
def powerSumDerivative (j : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ range j, (k + 1 : ℝ) * u ^ k
def gain (j : ℕ) (u : ℝ) : ℝ := log (1 + 1 / powerSum j u)
def beta (j : ℕ) (u : ℝ) : ℝ := gain j u / log u

theorem powerSum_succ (j : ℕ) (u : ℝ) :
    powerSum (j + 1) u = powerSum j u + u ^ (j + 1) := by
  simp [powerSum, sum_range_succ]

theorem powerSum_nonneg {u : ℝ} (hu : 0 ≤ u) (j : ℕ) : 0 ≤ powerSum j u :=
  sum_nonneg fun _ _ => pow_nonneg hu _

theorem last_power_le_sum {u : ℝ} (hu : 0 ≤ u) {j : ℕ} (hj : 1 ≤ j) :
    u ^ j ≤ powerSum j u := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  change u ^ (k + 1) ≤ powerSum (k + 1) u
  rw [powerSum_succ]
  exact le_add_of_nonneg_left (powerSum_nonneg hu k)

theorem powerSum_pos {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 1 ≤ j) :
    0 < powerSum j u := (pow_pos hu j).trans_le (last_power_le_sum hu.le hj)

theorem powerSum_geometric (j : ℕ) (u : ℝ) :
    (u - 1) * powerSum j u = u * (u ^ j - 1) := by
  induction j with
  | zero => simp [powerSum]
  | succ j ih => rw [powerSum_succ, pow_succ]; nlinarith [ih]

theorem powerSum_le_twice {u : ℝ} (hu : 2 ≤ u) (j : ℕ) :
    powerSum j u ≤ 2 * u ^ j := by
  have hS := powerSum_nonneg (by linarith : 0 ≤ u) j
  have h := powerSum_geometric j u
  have hp := pow_nonneg (by linarith : 0 ≤ u) j
  by_contra! hbad
  have hm := mul_lt_mul_of_pos_left hbad (show 0 < u - 1 by linarith)
  nlinarith [mul_nonneg (show 0 ≤ u - 2 by linarith) hp]

theorem powerSum_hasDerivAt (j : ℕ) (u : ℝ) :
    HasDerivAt (powerSum j) (powerSumDerivative j u) u := by
  unfold powerSum powerSumDerivative
  convert HasDerivAt.fun_sum (u := range j)
    (fun k _ => (hasDerivAt_id u).pow (k + 1)) using 1 <;> simp

theorem weighted_last_le {u : ℝ} (hu : 0 ≤ u) {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) * u ^ j ≤ u * powerSumDerivative j u := by
  have hterm : (j : ℝ) * u ^ (j - 1) ≤ powerSumDerivative j u := by
    have hlast := single_le_sum (s := range j)
      (f := fun k : ℕ => ((k + 1 : ℕ) : ℝ) * u ^ k)
      (fun k _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu _))
      (mem_range.mpr (by omega : j - 1 < j))
    rw [Nat.sub_add_cancel hj] at hlast
    simpa only [powerSumDerivative, Nat.cast_add, Nat.cast_one] using hlast
  have hh := mul_le_mul_of_nonneg_left hterm hu
  have he : u * ((j : ℝ) * u ^ (j - 1)) = (j : ℝ) * u ^ j := by
    rw [← mul_assoc, mul_comm u (j : ℝ), mul_assoc, ← pow_succ']
    congr 2
    omega
  rwa [he] at hh

theorem gain_pos {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 1 ≤ j) :
    0 < gain j u := by
  apply log_pos
  have := one_div_pos.mpr (powerSum_pos hu hj)
  linarith

theorem gain_le_inv_pow {u : ℝ} (hu : 0 < u) {j : ℕ} (hj : 1 ≤ j) :
    gain j u ≤ 1 / u ^ j := by
  have hs := powerSum_pos hu hj
  have hlog := log_le_sub_one_of_pos (show 0 < 1 + 1 / powerSum j u by positivity)
  have hrec := one_div_le_one_div_of_le (pow_pos hu j) (last_power_le_sum hu.le hj)
  dsimp [gain]
  linarith

theorem beta_pos {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 1 ≤ j) :
    0 < beta j u := div_pos (gain_pos (by linarith) hj) (log_pos (by linarith))

theorem beta_le_inv_pow_log {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 1 ≤ j) :
    beta j u ≤ 1 / (u ^ j * log u) := by
  exact (div_le_div_of_nonneg_right (gain_le_inv_pow (by linarith : 0 < u) hj)
    (log_pos (by linarith : 1 < u)).le).trans_eq (by
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]; ring)

/-- Exact reconciliation with the old arithmetic marginal; no new spectrum. -/
theorem beta_nat {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) :
    beta j (p : ℝ) = goldenLayerMarginal p j := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpow : (1 : ℝ) < (p : ℝ) ^ j := one_lt_pow₀ hp1 (by omega : j ≠ 0)
  have hs := powerSum_pos hp0 hj
  have hg := powerSum_geometric j (p : ℝ)
  have hden : 1 - (p : ℝ)⁻¹ ^ j ≠ 0 := by
    rw [inv_pow]
    exact sub_ne_zero.mpr (ne_of_gt ((inv_lt_one₀ (pow_pos hp0 j)).mpr hpow))
  have heq : (1 - (p : ℝ)⁻¹ ^ (j + 1)) / (1 - (p : ℝ)⁻¹ ^ j) =
      1 + 1 / powerSum j (p : ℝ) := by
    apply (div_eq_iff hden).mpr
    rw [inv_pow, inv_pow, pow_succ]
    field_simp [hs.ne', hp0.ne', (pow_pos hp0 j).ne']
    nlinarith [hg]
  simp only [beta, gain, goldenLayerMarginal, heq]

def logarithmicSlope (j : ℕ) (u : ℝ) : ℝ :=
  (u * powerSumDerivative j u / powerSum j u) *
    ((1 / powerSum j u) /
      ((1 + 1 / powerSum j u) * gain j u)) + 1 / log u

theorem log_beta_hasDerivAt {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 1 ≤ j) :
    HasDerivAt (fun v => log (beta j v)) (-logarithmicSlope j u / u) u := by
  have hu0 : 0 < u := by linarith
  have hs := powerSum_pos hu0 hj
  have hg := gain_pos hu0 hj
  have hl := log_pos (by linarith : 1 < u)
  have hS := powerSum_hasDerivAt j u
  have hG := ((hasDerivAt_const u (1 : ℝ)).add
    ((hasDerivAt_const u (1 : ℝ)).div hS hs.ne')).log (by positivity : 1 + 1 / powerSum j u ≠ 0)
  have hB := hG.div (Real.hasDerivAt_log hu0.ne') hl.ne'
  have h := hB.log (beta_pos hu hj).ne'
  convert h using 1 <;> try rfl
  simp only [Pi.add_apply, Pi.div_apply, zero_mul, one_mul, zero_sub, zero_add]
  change -logarithmicSlope j u / u =
    ((-(powerSumDerivative j u) / powerSum j u ^ 2 / (1 + 1 / powerSum j u) *
      log u - gain j u * u⁻¹) / log u ^ 2) / (gain j u / log u)
  unfold logarithmicSlope
  field_simp [hu0.ne', hs.ne', hg.ne', hl.ne',
    (show 1 + 1 / powerSum j u ≠ 0 by positivity)]
  <;> ring

/-- Uniform for ALL j>=2 and ALL real u>=2. -/
theorem logarithmicSlope_ge {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 2 ≤ j) :
    (j : ℝ) / 3 ≤ logarithmicSlope j u := by
  have hu0 : 0 < u := by linarith
  have hj1 : 1 ≤ j := by omega
  have hs := powerSum_pos hu0 hj1
  have hSupper := powerSum_le_twice hu j
  have hDlower := weighted_last_le hu0.le hj1
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hA : (j : ℝ) / 2 ≤ u * powerSumDerivative j u / powerSum j u := by
    apply (le_div_iff₀ hs).mpr
    have hm := mul_le_mul_of_nonneg_left hSupper (show 0 ≤ (j : ℝ) / 2 by positivity)
    nlinarith
  have hp4 : (4 : ℝ) ≤ u ^ j := by
    have hp := pow_le_pow_right₀ (by linarith : 1 ≤ u) hj
    have hu2 : (4 : ℝ) ≤ u ^ 2 := by nlinarith
    exact hu2.trans hp
  have hz : 1 / powerSum j u ≤ 1 / 4 := by
    exact one_div_le_one_div_of_le (by norm_num) (hp4.trans (last_power_le_sum hu0.le hj1))
  have hg := gain_pos hu0 hj1
  have hlog : gain j u ≤ 1 / powerSum j u := by
    have hh := log_le_sub_one_of_pos (show 0 < 1 + 1 / powerSum j u by positivity)
    dsimp [gain]
    linarith
  have hB : (4 : ℝ) / 5 ≤ (1 / powerSum j u) /
      ((1 + 1 / powerSum j u) * gain j u) := by
    apply (le_div_iff₀ (mul_pos (by positivity) hg)).mpr
    have hh := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1 + 1 / powerSum j u by positivity)
    have hz0 : 0 ≤ 1 / powerSum j u := by positivity
    nlinarith [mul_nonneg hz0 (show 0 ≤ 1 / 4 - 1 / powerSum j u by linarith)]
  have hA0 : 0 ≤ u * powerSumDerivative j u / powerSum j u := by linarith
  have hmul := mul_le_mul hA hB (by norm_num : (0 : ℝ) ≤ 4 / 5) hA0
  have hl : 0 < log u := log_pos (by linarith)
  unfold logarithmicSlope
  exact (show (j : ℝ) / 3 ≤ (j : ℝ) / 2 * (4 / 5) by linarith).trans
    (hmul.trans (le_add_of_nonneg_right (one_div_pos.mpr hl).le))

theorem beta_continuousOn {j : ℕ} (hj : 1 ≤ j) :
    ContinuousOn (beta j) (Set.Ici 2) := by
  intro u hu
  change 2 ≤ u at hu
  have hS := (powerSum_hasDerivAt j u).continuousAt
  have hs := powerSum_pos (by linarith : 0 < u) hj
  have h := ((continuousAt_const.add (continuousAt_const.div hS hs.ne')).log
    (by positivity : 1 + 1 / powerSum j u ≠ 0)).div
      (continuousAt_log (by linarith : u ≠ 0)) (log_pos (by linarith : 1 < u)).ne'
  exact h.continuousWithinAt

/-- Integrated slope, including both boundary endpoints. -/
theorem log_beta_drop {j : ℕ} (hj : 2 ≤ j) {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) :
    (j : ℝ) / 3 * log (v / u) ≤ log (beta j u / beta j v) := by
  let f : ℝ → ℝ := fun t => log (beta j t) + (j : ℝ) / 3 * log t
  have hd (t : ℝ) (ht : 2 ≤ t) :
      HasDerivAt f (((j : ℝ) / 3 - logarithmicSlope j t) / t) t := by
    convert (log_beta_hasDerivAt ht (by omega : 1 ≤ j)).add
      ((Real.hasDerivAt_log (by linarith : t ≠ 0)).const_mul ((j : ℝ) / 3)) using 1 <;>
      simp only [div_eq_mul_inv] <;> ring
  have hanti : AntitoneOn f (Set.Ici 2) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 2)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (logarithmicSlope_ge (interior_subset ht) hj))
        (by have ht2 : 2 ≤ t := interior_subset ht; linarith)
  have h := hanti hu (hu.trans huv) huv
  dsimp [f] at h
  rw [log_div (by linarith : v ≠ 0) (by linarith : u ≠ 0),
    log_div (beta_pos hu (by omega)).ne' (beta_pos (hu.trans huv) (by omega)).ne']
  linarith

theorem beta_strictAntiOn {j : ℕ} (hj : 2 ≤ j) :
    StrictAntiOn (beta j) (Set.Ici 2) := by
  intro u hu v hv huv
  change 2 ≤ u at hu
  change 2 ≤ v at hv
  have h := log_beta_drop hj hu huv.le
  have hratio : 1 < v / u := (lt_div_iff₀ (by linarith : 0 < u)).mpr (by linarith)
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hpositive : 0 < (j : ℝ) / 3 * log (v / u) :=
    mul_pos (div_pos hjpos (by norm_num)) (log_pos hratio)
  have hlog : 0 < log (beta j u / beta j v) := hpositive.trans_le h
  have hq := (log_pos_iff (div_pos (beta_pos hu (by omega))
    (beta_pos hv (by omega))).le).mp hlog
  exact (one_lt_div (beta_pos hv (by omega))).mp hq

/-- A finite endpoint witnessing decay, used by the actual root construction. -/
theorem beta_small_endpoint {j : ℕ} (hj : 1 ≤ j) {η : ℝ} (hη : 0 < η) :
    ∃ v : ℝ, 2 ≤ v ∧ beta j v < η := by
  let v : ℝ := max 4 (4 / η)
  have hv : 2 ≤ v := by dsimp [v]; linarith [le_max_left (4 : ℝ) (4 / η)]
  have hv0 : 0 < v := by linarith
  have hlog : 1 / 2 < log v := by
    have h2 : (1 / 2 : ℝ) < log 2 := by
      have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)
      norm_num at h ⊢
      linarith
    exact h2.trans_le (log_le_log (by norm_num) hv)
  have hp : v ≤ v ^ j := by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ v) hj
  have hbound : beta j v ≤ 2 / v := by
    apply (beta_le_inv_pow_log hv hj).trans
    apply (div_le_div_iff₀ (mul_pos (pow_pos hv0 _) (by linarith)) hv0).mpr
    have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ log v by linarith)
    nlinarith
  have hηv : 4 ≤ η * v := by
    have hh := mul_le_mul_of_nonneg_left (le_max_right (4 : ℝ) (4 / η)) hη.le
    dsimp [v]
    field_simp [hη.ne'] at hh
    linarith
  refine ⟨v, hv, hbound.trans_lt ?_⟩
  apply (div_lt_iff₀ hv0).mpr
  linarith
end D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
