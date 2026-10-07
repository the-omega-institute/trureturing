/- GID: D5/S3/Arith/Lattices/Klartag/Construction/Tiling
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Construction/Tiling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construction A lattices, covolumes and ellipsoid transfer. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib

open MeasureTheory
open Metric
open Set
open Finset
open scoped ENNReal

namespace D5.S3.Arith.Lattices.Klartag.Construction.Tiling

variable {n : ℕ}

/-- The embedding `ℤⁿ ↪ ℝⁿ` (Euclidean). -/
def toE (n : ℕ) (y : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (y i : ℝ))

@[simp] theorem toE_apply (y : Fin n → ℤ) (i : Fin n) : toE n y i = (y i : ℝ) := rfl

/-- The open unit cube centred at `c`. -/
def cube (c : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, x i ∈ Set.Ioo (c i - 1/2) (c i + 1/2)}

theorem preimage_cube (c : EuclideanSpace ℝ (Fin n)) :
    (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' cube c
      = Set.pi Set.univ (fun i => Set.Ioo (c i - 1/2) (c i + 1/2)) := by
  ext v
  simp only [Set.mem_preimage, cube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]

theorem measurableSet_cube (c : EuclideanSpace ℝ (Fin n)) : MeasurableSet (cube c) := by
  rw [← (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableSet_preimage,
    MeasurableEquiv.coe_toLp, preimage_cube]
  exact MeasurableSet.univ_pi (fun i => measurableSet_Ioo)

theorem volume_cube (c : EuclideanSpace ℝ (Fin n)) : volume (cube c) = 1 := by
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (measurableSet_cube c).nullMeasurableSet, preimage_cube]
  rw [volume_pi_pi]
  simp
  norm_num

theorem norm_sub_lt_of_mem_cube (hn : 0 < n) (c : EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ cube c) :
    ‖x - c‖ < Real.sqrt n / 2 := by
  have hsum : ∑ i : Fin n, (x i - c i) ^ 2 < (n : ℝ) / 4 := by
    have hlt : ∀ i : Fin n, (x i - c i) ^ 2 < 1 / 4 := by
      intro i
      obtain ⟨h1, h2⟩ := hx i
      have : |x i - c i| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
      nlinarith [abs_nonneg (x i - c i), sq_abs (x i - c i)]
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
      rw [Finset.univ_nonempty_iff]
      exact Fin.pos_iff_nonempty.1 hn
    calc ∑ i : Fin n, (x i - c i) ^ 2 < ∑ _i : Fin n, (1 / 4 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty hne (fun i _ => hlt i)
      _ = (n : ℝ) / 4 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hsq : ∑ i : Fin n, ‖(x - c) i‖ ^ 2 = ∑ i : Fin n, (x i - c i) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by
      rw [show (x - c) i = x i - c i from rfl, Real.norm_eq_abs, sq_abs])
  have h4 : Real.sqrt ((n : ℝ) / 4) = Real.sqrt n / 2 := by
    rw [Real.sqrt_div (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [EuclideanSpace.norm_eq, hsq, ← h4]
  exact Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hsum

/-- Cubes centred at distinct integer points are disjoint. -/
theorem cube_disjoint {y z : Fin n → ℤ} (h : y ≠ z) :
    Disjoint (cube (toE n y)) (cube (toE n z)) := by
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ z j := by
    by_contra hcon
    push Not at hcon
    exact h (funext hcon)
  rw [Set.disjoint_left]
  intro x hxy hxz
  obtain ⟨h1, h2⟩ := hxy j
  obtain ⟨h3, h4⟩ := hxz j
  rw [toE_apply] at h1 h2 h3 h4
  have hlt : |(y j : ℝ) - (z j : ℝ)| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have hge : (1 : ℝ) ≤ |(y j : ℝ) - (z j : ℝ)| := by
    have hz : y j - z j ≠ 0 := sub_ne_zero_of_ne hj
    have hint : (1 : ℤ) ≤ |y j - z j| := Int.one_le_abs hz
    have hcast : ((|y j - z j| : ℤ) : ℝ) = |(y j : ℝ) - (z j : ℝ)| := by
      rw [Int.cast_abs]; push_cast; ring_nf
    rw [← hcast]
    exact_mod_cast hint
  linarith

theorem pairwiseDisjoint_cube (A : Finset (Fin n → ℤ)) :
    (↑A : Set (Fin n → ℤ)).PairwiseDisjoint (fun y => cube (toE n y)) :=
  fun _ _ _ _ h => cube_disjoint h

/-- **Cube packing.**  A finite set of integer points of norm `≤ R` has cardinality at most the
volume of the ball of radius `R + √n/2`. -/
theorem card_le_volume_ball (hn : 0 < n) (R : ℝ) (A : Finset (Fin n → ℤ))
    (hA : ∀ y ∈ A, ‖toE n y‖ ≤ R) :
    (A.card : ℝ≥0∞) ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + Real.sqrt n / 2)) := by
  have hsub : (⋃ y ∈ A, cube (toE n y))
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + Real.sqrt n / 2) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [mem_ball_zero_iff]
    calc ‖x‖ = ‖(x - toE n y) + toE n y‖ := by congr 1; abel
      _ ≤ ‖x - toE n y‖ + ‖toE n y‖ := norm_add_le _ _
      _ < Real.sqrt n / 2 + R := by
          exact add_lt_add_of_lt_of_le (norm_sub_lt_of_mem_cube hn _ hxy) (hA y hy)
      _ = R + Real.sqrt n / 2 := by ring
  calc (A.card : ℝ≥0∞) = ∑ y ∈ A, volume (cube (toE n y)) := by
        rw [Finset.sum_congr rfl (fun y _ => volume_cube (toE n y))]
        simp
    _ = volume (⋃ y ∈ A, cube (toE n y)) :=
        (measure_biUnion_finset (pairwiseDisjoint_cube A)
          (fun y _ => measurableSet_cube (toE n y))).symm
    _ ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (R + Real.sqrt n / 2)) :=
        measure_mono hsub

/-- **Sum-to-integral comparison** (the cube-tiling lemma, in the form that needs no `φ↑`):
a finite lattice sum is bounded by the integral of any function dominating it on each cube. -/
theorem sum_le_lintegral (A : Finset (Fin n → ℤ)) (φ : (Fin n → ℤ) → ℝ≥0∞)
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hdom : ∀ y ∈ A, ∀ x ∈ cube (toE n y), φ y ≤ ψ x) :
    ∑ y ∈ A, φ y ≤ ∫⁻ x, ψ x := by
  calc ∑ y ∈ A, φ y = ∑ y ∈ A, ∫⁻ _x in cube (toE n y), φ y := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [setLIntegral_const, volume_cube, mul_one]
    _ ≤ ∑ y ∈ A, ∫⁻ x in cube (toE n y), ψ x := by
        refine Finset.sum_le_sum (fun y hy => ?_)
        refine lintegral_mono_ae ?_
        filter_upwards [self_mem_ae_restrict (measurableSet_cube (toE n y))] with x hx
        exact hdom y hy x hx
    _ = ∫⁻ x in ⋃ y ∈ A, cube (toE n y), ψ x :=
        (lintegral_biUnion_finset (pairwiseDisjoint_cube A)
          (fun y _ => measurableSet_cube (toE n y)) _).symm
    _ ≤ ∫⁻ x, ψ x := lintegral_mono' Measure.restrict_le_self le_rfl

/-- A coordinate is bounded by the Euclidean norm. -/
theorem abs_coord_le_norm (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) : |x j| ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have : ‖x j‖ ^ 2 ≤ ∑ i : Fin n, ‖x i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  simpa [Real.norm_eq_abs, sq_abs] using this

/-- **Set finiteness.**  A Euclidean ball contains finitely many integer points. -/
theorem finite_ball_integer (n : ℕ) (R : ℝ) :
    {y : Fin n → ℤ | ‖toE n y‖ ≤ R}.Finite := by
  refine Set.Finite.subset (Set.Finite.pi (fun _ : Fin n =>
    (Set.finite_Icc (-(⌈R⌉)) (⌈R⌉))) ) ?_
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Icc]
  intro i
  have h1 : |(y i : ℝ)| ≤ R := le_trans (by rw [← toE_apply]; exact abs_coord_le_norm _ i) hy
  have hceil : R ≤ ((⌈R⌉ : ℤ) : ℝ) := Int.le_ceil R
  have hub : ((y i : ℤ) : ℝ) ≤ ((⌈R⌉ : ℤ) : ℝ) := by
    have := le_abs_self ((y i : ℝ)); linarith
  have hlb : (((-⌈R⌉ : ℤ)) : ℝ) ≤ ((y i : ℤ) : ℝ) := by
    have := neg_abs_le ((y i : ℝ)); push_cast; linarith
  exact ⟨by exact_mod_cast hlb, by exact_mod_cast hub⟩

end D5.S3.Arith.Lattices.Klartag.Construction.Tiling
