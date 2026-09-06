/- GID: D5/S3/Fourier/GoldenModelSetDelone
   generality: G
   mirror-B: D5/B/S3/Fourier/GoldenModelSetDelone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Integral norms and floor witnesses certify the complete golden model set as Delone. -/

import D5.S0.Carrier.Euclidean
import D5.S3.Fourier.GoldenCutProjectSchemeAdapter
import D5.S3.Fourier.DeloneModelSetCertificate
import D5.S1.Deficit.ModelSet.GoldenModelSetSelfSimilar

/-!
The complete golden window model set has packing radius 1/2 and covering
radius 3. The new geometric input is a parameter-general norm separation
bound and a floor-selected witness for every real point. The final certificate
connects the existing golden lattice, selection adapter, and Delone bundle,
supporting the paper's end-to-end geometric claim for the bi-infinite carrier.
It does not assert relative density of the natural-number digit image.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Fourier.GoldenModelSetDelone

open D5.S0.Carrier D5.S1.Scale
open D5.S1.Deficit.GoldenModelSetSelfSimilar
open GoldenCutProjectSchemeAdapter DeloneModelSetCertificate
open scoped NNReal

/-- A bound on internal displacement forces reciprocal physical separation,
uniformly in the displacement bound B. -/
theorem norm_separation (u v : GoldenInt) (hne : u ≠ v) (B : ℝ)
    (hB : |embedding (conj u) - embedding (conj v)| ≤ B) :
    1 ≤ |embedding u - embedding v| * B := by
  have hn : norm (u - v) ≠ 0 := by
    exact mt (norm_eq_zero_iff (u - v)).mp (sub_ne_zero.mpr hne)
  have hi : (1 : ℝ) ≤ |(norm (u - v) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hn
  have hc : conj (u - v) = conj u - conj v := conjEquiv.map_sub u v
  rw [← abs_embedding_mul_abs_conj, map_sub, hc, map_sub] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left hB (abs_nonneg _))

/-- The existing inverse-power window has the simpler endpoints phi-2 and phi-1. -/
theorem goldenWindow_eq :
    goldenWindow = Set.Icc (Real.goldenRatio - 2) (Real.goldenRatio - 1) := by
  have hi : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    linarith [Real.inv_goldenRatio, Real.goldenRatio_add_goldenConj]
  have hs := Real.goldenRatio_sq
  unfold goldenWindow
  rw [hi]
  congr 1
  nlinarith

/-- Distinct points of the closed golden window model set are at least one apart. -/
theorem golden_modelSet_dist_ge_one {x y : ℝ}
    (hx : x ∈ modelSet goldenWindow) (hy : y ∈ modelSet goldenWindow)
    (hne : x ≠ y) : 1 ≤ dist x y := by
  rcases hx with ⟨u, rfl, hu⟩
  rcases hy with ⟨v, rfl, hv⟩
  rw [goldenWindow_eq] at hu hv
  have huv : u ≠ v := fun h => hne (congrArg embedding h)
  have hB : |embedding (conj u) - embedding (conj v)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
  simpa only [mul_one, Real.dist_eq] using norm_separation u v huv 1 hB

/-- Two explicit integer floor choices give a golden model-set point within
distance three of every real input, including negative inputs. -/
theorem golden_modelSet_covering (x : ℝ) :
    ∃ y ∈ modelSet goldenWindow, dist x y ≤ 3 := by
  let q : ℝ := 2 * Real.goldenRatio - 1
  have hq : 0 < q := by dsimp [q]; linarith [Real.one_lt_goldenRatio]
  let b : ℤ := ⌊x / q⌋
  let a : ℤ := ⌊Real.goldenRatio - 1 - (b : ℝ) * (1 - Real.goldenRatio)⌋
  let u : GoldenInt := ⟨a, b⟩
  have hb₀ : (b : ℝ) * q ≤ x := (le_div_iff₀ hq).mp (Int.floor_le (x / q))
  have hb₁ : x < ((b : ℝ) + 1) * q :=
    (div_lt_iff₀ hq).mp (Int.lt_floor_add_one (x / q))
  have ha₀ := Int.floor_le
    (Real.goldenRatio - 1 - (b : ℝ) * (1 - Real.goldenRatio))
  have ha₁ := Int.lt_floor_add_one
    (Real.goldenRatio - 1 - (b : ℝ) * (1 - Real.goldenRatio))
  have hc : embedding (conj u) = (a : ℝ) + (b : ℝ) * (1 - Real.goldenRatio) := by
    simp [u, embedding_apply, conj]
    ring
  have hlow : Real.goldenRatio - 2 ≤ embedding (conj u) := by
    rw [hc]
    change (a : ℝ) ≤ _ at ha₀
    change _ < (a : ℝ) + 1 at ha₁
    linarith
  have hupp : embedding (conj u) ≤ Real.goldenRatio - 1 := by
    rw [hc]
    change (a : ℝ) ≤ _ at ha₀
    linarith
  have hp : embedding u = embedding (conj u) + (b : ℝ) * q := by
    rw [hc]
    simp only [embedding_apply, u, q]
    ring
  refine ⟨embedding u, ⟨u, rfl, ?_⟩, ?_⟩
  · rw [goldenWindow_eq]
    exact ⟨hlow, hupp⟩
  · rw [Real.dist_eq, hp]
    apply abs_le.mpr
    dsimp only [q] at hb₀ hb₁ ⊢
    constructor <;> nlinarith [Real.goldenRatio_lt_two]

/-- Explicit radii and metric witnesses for the existing lattice-subtype scheme. -/
def goldenModelSetCertificate : Certificate goldenScheme goldenWindow where
  packingRadius := 1 / 2
  packingRadius_pos := by norm_num
  isSeparated_packingRadius := by
    intro x hx y hy hne
    rw [goldenScheme_modelSet_eq] at hx hy
    have hd := golden_modelSet_dist_ge_one hx hy hne
    rw [edist_dist, ENNReal.coe_lt_ofReal]
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    linarith
  coveringRadius := 3
  coveringRadius_pos := by norm_num
  isCover_coveringRadius := by
    rw [Metric.isCover_iff_subset_iUnion_closedBall, goldenScheme_modelSet_eq]
    intro x _
    obtain ⟨y, hy, hd⟩ := golden_modelSet_covering x
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, by simpa using hd⟩⟩

/-- The constructed certificate has the claimed positive packing and covering radii. -/
theorem golden_modelSet_certificate_radii :
    goldenModelSetCertificate.packingRadius = (1 / 2 : ℝ≥0) ∧
      goldenModelSetCertificate.coveringRadius = (3 : ℝ≥0) := ⟨rfl, rfl⟩

/-- The complete golden model-set carrier supports a Mathlib Delone set with
the explicit packing radius 1/2 and covering radius 3. -/
theorem exists_golden_modelSet_delone :
    ∃ D : Delone.DeloneSet ℝ,
      D.carrier = modelSet goldenWindow ∧
      D.packingRadius = (1 / 2 : ℝ≥0) ∧ D.coveringRadius = (3 : ℝ≥0) := by
  refine ⟨goldenModelSetCertificate.toDeloneSet, ?_, rfl, rfl⟩
  exact goldenScheme_modelSet_eq goldenWindow

end D5.S3.Fourier.GoldenModelSetDelone
