/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/BallNet
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/BallNet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Volumetric finite nets in finite-dimensional real normed spaces. -/

import OmegaBuild.Commands
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.CoveringNumbers

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

set_option maxHeartbeats 800000

namespace D5.S3.Quantum.Entanglement.EntanglementBreaking

open MeasureTheory Metric Set
open scoped ENNReal NNReal

/-- A subset of the unit ball has an internal finite ε-net with the volumetric bound. -/
theorem exists_finset_net_unitBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hS : S ⊆ closedBall 0 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset E, (↑N : Set E) ⊆ S ∧
      (∀ x ∈ S, ∃ y ∈ N, dist x y ≤ ε) ∧
      (N.card : ℝ) ≤ (1 + 2 / ε) ^ Module.finrank ℝ E := by
  classical
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  let δ : ℝ≥0 := ⟨ε, hε.le⟩
  have hδ : 0 < δ := hε
  have hδhalf : 0 < δ / 2 := by positivity
  obtain ⟨C, -, hCfin, hCcover⟩ :=
    exists_finite_isCover_of_totallyBounded
      (ε := δ / 2) hδhalf.ne'
      ((isCompact_closedBall (0 : E) 1).totallyBounded.subset hS)
  have hpack : packingNumber δ S ≠ ⊤ := by
    have h := (packingNumber_two_mul_le_externalCoveringNumber (δ / 2) S).trans
      hCcover.externalCoveringNumber_le_encard
    have hmul : 2 * (δ / 2) = δ := by ring
    rw [hmul] at h
    exact (h.trans_lt (encard_lt_top_iff.mpr hCfin)).ne
  let P := maximalSeparatedSet δ S
  have hPS : P ⊆ S := maximalSeparatedSet_subset
  have hPsep : IsSeparated δ P := isSeparated_maximalSeparatedSet
  have hPfin : P.Finite := encard_ne_top_iff.mp
    ((encard_maximalSeparatedSet hpack).trans_ne hpack)
  let N := hPfin.toFinset
  have hNP : (↑N : Set E) = P := hPfin.coe_toFinset
  have hcover : IsCover δ S P := isCover_maximalSeparatedSet hpack
  refine ⟨N, hNP.symm ▸ hPS, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover hx
    change edist x y ≤ (δ : ℝ≥0∞) at hxy
    exact ⟨y, by simpa only [← hNP, Finset.mem_coe] using hy,
      by exact_mod_cast (ENNReal.coe_le_coe.mp (by simpa only [edist_nndist] using hxy) : nndist x y ≤ δ)⟩
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let μ := (Module.finBasis ℝ E).addHaar
  let r := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hdisj : (↑N : Set E).PairwiseDisjoint (fun y => ball y r) := by
    intro x hx y hy hne
    have hxy := hPsep (hNP ▸ hx) (hNP ▸ hy) hne
    apply ball_disjoint_ball
    have h' : ε < dist x y := by
      exact_mod_cast (ENNReal.coe_lt_coe.mp (by simpa only [edist_nndist] using hxy) : δ < nndist x y)
    dsimp [r]
    linarith
  have hsub : (⋃ y ∈ N, ball y r) ⊆ ball (0 : E) (1 + r) := by
    intro x hx
    simp only [mem_iUnion, mem_ball, exists_prop] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hy0 := mem_closedBall.mp (hS (hPS (hNP ▸ Finset.mem_coe.mpr hy)))
    exact (dist_triangle x y 0).trans_lt (by linarith)
  have hvol := measureReal_mono (μ := μ) hsub measure_ball_lt_top.ne
  rw [measureReal_biUnion_finset hdisj (fun _ _ => measurableSet_ball)
    (fun _ _ => measure_ball_lt_top.ne)] at hvol
  simp only [Measure.addHaar_real_ball_center μ, Finset.sum_const, nsmul_eq_mul] at hvol
  have hscale : (1 + 2 / ε) * r = 1 + r := by dsimp [r]; field_simp; ring
  have hbase : 0 < 1 + 2 / ε := by positivity
  have hout : μ.real (ball (0 : E) (1 + r)) =
      (1 + 2 / ε) ^ Module.finrank ℝ E * μ.real (ball 0 r) := by
    rw [← hscale]
    simp only [measureReal_def, Measure.addHaar_ball_mul_of_pos μ _ hbase,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hbase.le _)]
  rw [hout] at hvol
  have hpos : 0 < μ.real (ball (0 : E) r) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 hr).ne' measure_ball_lt_top.ne
  exact le_of_mul_le_mul_right hvol hpos

end D5.S3.Quantum.Entanglement.EntanglementBreaking
