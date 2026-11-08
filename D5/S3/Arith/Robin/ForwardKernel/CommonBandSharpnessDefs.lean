/- GID: D5/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/CommonBandSharpnessDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Clipped logarithmic cusps and sparse perturbations for common-band sharpness. -/

import D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.LocallyFinite

/-! Abstract cusps, sparse spikes and comparison scales for common-band variance sharpness. -/

namespace D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness

open Set MeasureTheory Filter
open VarianceTransferDefs
open scoped Topology BigOperators

noncomputable section

/-- The logarithm clipped below at radius `h` and above at radius `k`. -/
def clippedLog (h k y : ℝ) : ℝ :=
  Real.log (min k (max h |y|) / k)

/-- The unit translation difference of the logarithm of the absolute value. -/
def logJump (z : ℝ) : ℝ :=
  Real.log |z + 1| - Real.log |z|

/-- The unit-profile average of a forward increment of a clipped logarithmic cusp. -/
def cuspAverage (h k q y : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, clippedLog h k (y + s * q) - clippedLog h k y

/-- The cross energy of the cusp averages at its inner and outer lengths. -/
def cuspCrossEnergy (h k : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..k, cuspAverage h k h y * cuspAverage h k k y

/-- The geometrically separated centers of the spikes. -/
def center (n : ℕ) : ℝ :=
  (10 : ℝ) ^ n

/-- The amplitude of the spike at the `n`th center. -/
def amplitude (n : ℕ) : ℝ :=
  Real.sqrt (center n * Real.log (center n) / Real.log (Real.log (center n)))

/-- A translated clipped logarithmic cusp with its prescribed amplitude and radii. -/
def spike (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  amplitude n * clippedLog (center n ^ a) (center n ^ b) (x - center n)

/-- A starting index beyond which every outer radius is at most a tenth of its center. -/
def AdmissibleStart (b : ℝ) (n₀ : ℕ) : Prop :=
  1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n → center n ^ b ≤ center n / 10

/-- The sparse perturbation, with its indices reparametrized starting at `n₀`. -/
def perturbation (a b : ℝ) (n₀ : ℕ) (x : ℝ) : ℝ :=
  ∑' j : ℕ, spike a b (n₀ + j) x

/-- The pointwise growth scale of the sparse perturbation. -/
def spikePointScale (x : ℝ) : ℝ :=
  Real.sqrt x * (Real.log x) ^ (3 / 2 : ℝ) / Real.sqrt (Real.log (Real.log x))

/-- The scale attained along the spike centers by the common-band cross energy. -/
def nearOptScale (b X : ℝ) : ℝ :=
  X ^ (1 - b) * (Real.log X) ^ 3 / Real.log (Real.log X)

/-- A comparison scale with the logarithmic exponent reduced by `η`. -/
def reducedLogScale (b η X : ℝ) : ℝ :=
  X ^ (1 - b) * (Real.log X) ^ (3 - η)

/-- The normalized cumulative variance tends uniformly to zero throughout the exponent band. -/
def CumulativeVarianceBandNegligibleFor (F : ℝ → ℝ) (α β : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℝ in atTop, ∀ u : ℝ,
    Y ^ α ≤ u → u ≤ Y ^ β →
      |cumulativeVariance F Y u / (Y * u * Real.log (Y / u))| ≤ ε

/-- Every spike center is positive. -/
theorem center_pos (n : ℕ) : 0 < center n := by
  exact pow_pos (by norm_num) n

/-- The spike centers are strictly increasing. -/
theorem center_strictMono : StrictMono center := by
  exact pow_right_strictMono₀ (by norm_num)

/-- The spike centers tend to positive infinity. -/
theorem center_tendsto : Tendsto center atTop atTop := by
  exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

/-- Every exponent below one admits a starting index with separated spike radii. -/
theorem exists_admissibleStart {b : ℝ} (hb : b < 1) :
    ∃ n₀ : ℕ, AdmissibleStart b n₀ := by
  have ht := (tendsto_rpow_neg_atTop (sub_pos.mpr hb)).comp center_tendsto
  have he : ∀ᶠ n : ℕ in atTop, center n ^ (b - 1) < (1 / 10 : ℝ) := by
    simpa only [neg_sub, Function.comp_def] using
      ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10))
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨max 1 N, le_max_left _ _, ?_⟩
  intro n hn
  have h := (hN n ((le_max_right _ _).trans hn)).le
  rw [Real.rpow_sub_one (center_pos n).ne'] at h
  exact (div_le_iff₀ (center_pos n)).1 h |>.trans_eq (by ring)

/-- A clipped logarithm is zero at or beyond its outer radius. -/
theorem clippedLog_eq_zero {h k y : ℝ} (hk : 0 < k) (hy : k ≤ |y|) :
    clippedLog h k y = 0 := by
  rw [clippedLog, min_eq_left (hy.trans (le_max_right _ _)), div_self hk.ne', Real.log_one]

/-- A spike vanishes outside the interval given by its outer radius. -/
theorem spike_support_subset (a b : ℝ) (n : ℕ) :
    Function.support (spike a b n) ⊆
      Icc (center n - center n ^ b) (center n + center n ^ b) := by
  intro x hx
  by_contra h
  have hy : center n ^ b ≤ |x - center n| := by
    by_contra! hy
    have hy' := abs_lt.1 hy
    exact h ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
  exact hx (by simp only [spike, clippedLog_eq_zero
    (Real.rpow_pos_of_pos (center_pos n) b) hy, mul_zero])

private lemma spike_intervals_locallyFinite {b : ℝ} {n₀ : ℕ}
    (hs : AdmissibleStart b n₀) :
    LocallyFinite (fun j : ℕ =>
      Icc (center (n₀ + j) - center (n₀ + j) ^ b)
        (center (n₀ + j) + center (n₀ + j) ^ b)) := by
  intro x
  have ht := center_tendsto.atTop_mul_const (by norm_num : (0 : ℝ) < 9 / 10)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (eventually_gt_atTop (x + 1)))
  refine ⟨Iio (x + 1), Iio_mem_nhds (by linarith), (Set.finite_Iio N).subset ?_⟩
  rintro j ⟨y, hy, hxy⟩
  by_contra! hj
  change ¬ j < N at hj
  have hn : N ≤ n₀ + j := by omega
  have hcenter := hN (n₀ + j) hn
  have hr := hs.2 (n₀ + j) (Nat.le_add_right _ _)
  change y < x + 1 at hxy
  linarith only [hy.1, hxy, hcenter, hr]

/-- Every earlier spike's outer interval ends strictly before a later one begins. -/
theorem spike_intervals_disjoint {b : ℝ} {n₀ : ℕ}
    (hs : AdmissibleStart b n₀) {i j : ℕ} (hij : i < j) :
    center (n₀ + i) + center (n₀ + i) ^ b <
      center (n₀ + j) - center (n₀ + j) ^ b := by
  have hc := center_strictMono.monotone (show n₀ + i + 1 ≤ n₀ + j by omega)
  have he : center (n₀ + i + 1) = 10 * center (n₀ + i) := by
    simp only [center, pow_succ]
    ring
  rw [he] at hc
  have hi := hs.2 (n₀ + i) (Nat.le_add_right _ _)
  have hj := hs.2 (n₀ + j) (Nat.le_add_right _ _)
  linarith [center_pos (n₀ + i)]

/-- The supports of the spikes form a locally finite family at an admissible start. -/
theorem spike_locallyFinite {a b : ℝ} {n₀ : ℕ} (hs : AdmissibleStart b n₀) :
    LocallyFinite (fun j : ℕ => Function.support (spike a b (n₀ + j))) := by
  exact (spike_intervals_locallyFinite hs).subset fun j => spike_support_subset a b (n₀ + j)

/-- Only finitely many terms of the perturbation are nonzero at any fixed point. -/
theorem perturbation_finite_support {a b : ℝ} {n₀ : ℕ}
    (hs : AdmissibleStart b n₀) (x : ℝ) :
    (Function.support (fun j : ℕ => spike a b (n₀ + j) x)).Finite := by
  exact (spike_locallyFinite hs).point_finite x

/-- Each point has a neighbourhood meeting the support of at most one spike. -/
theorem perturbation_locally_single_spike {a b : ℝ} {n₀ : ℕ}
    (hs : AdmissibleStart b n₀) (x : ℝ) :
    ∃ U ∈ 𝓝 x, ∀ i j : ℕ, ∀ y ∈ U, ∀ z ∈ U,
      spike a b (n₀ + i) y ≠ 0 → spike a b (n₀ + j) z ≠ 0 → i = j := by
  have he := (spike_intervals_locallyFinite hs).eventually_subset
    (fun _ => isClosed_Icc) x
  refine ⟨{y | ∀ i : ℕ,
      y ∈ Icc (center (n₀ + i) - center (n₀ + i) ^ b)
        (center (n₀ + i) + center (n₀ + i) ^ b) →
      x ∈ Icc (center (n₀ + i) - center (n₀ + i) ^ b)
        (center (n₀ + i) + center (n₀ + i) ^ b)}, he, ?_⟩
  intro i j y hy z hz hi hj
  have hix := hy i (spike_support_subset a b (n₀ + i) hi)
  have hjx := hz j (spike_support_subset a b (n₀ + j) hj)
  rcases lt_trichotomy i j with hij | hij | hij
  · have h := spike_intervals_disjoint hs hij
    linarith [hix.2, hjx.1]
  · exact hij
  · have h := spike_intervals_disjoint hs hij
    linarith [hjx.2, hix.1]

end

end D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness
