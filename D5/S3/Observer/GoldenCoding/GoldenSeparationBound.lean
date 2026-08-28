/- GID: D5/S3/Observer/GoldenCoding/GoldenSeparationBound
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenSeparationBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite golden-slope integer windows have explicit positive separation. -/

import D5.S0.Carrier.Euclidean
import D5.S1.Scale.Embedding
import Mathlib

-- Library-search audit trail (2026-08-28):
-- * Repository searches found no theorem for the minimum spacing of the
--   golden-slope image of an integer square. The nearby theorem
--   `D5.S1.Depth.golden_hurwitz_bound` has a different rational-denominator
--   bound and does not imply this finite-window constant.
-- * Repository declarations `embedding_eq_zero_iff`, `embedding_mul_conj`,
--   `abs_embedding_mul_abs_conj`, and `norm_eq_zero_iff` exactly supply the
--   golden-integer embedding and norm steps and are reused below.
-- * Pinned Mathlib supplies `Real.goldenRatio_add_goldenConj`,
--   `Real.goldenRatio_mul_goldenConj`, both irrationality declarations,
--   `Int.one_le_abs`, and `Finset.le_min'`. No packaged theorem for the full
--   finite-window separation statement was found.
-- * Loogle confirmed the golden-ratio irrationality and finite-minimum APIs;
--   full-shape Loogle, LeanSearch, Reservoir, and GitHub ecosystem searches
--   found no exact theorem.

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.GoldenCoding.GoldenSeparationBound

open D5.S0.Carrier
open D5.S1.Scale

-- A source window size, including its stated lower bound `H >= 2`.
abbrev GoldenWindowSize := {H : ℕ // 2 ≤ H}

-- The integer square `{1, ..., H}^2` from the source.
noncomputable def goldenRootWindow (H : GoldenWindowSize) : Finset (ℤ × ℤ) :=
  (Finset.Icc 1 (H.val : ℤ)).product (Finset.Icc 1 (H.val : ℤ))

-- The golden-slope energy `E_phi(m,n) = phi*m + n`.
noncomputable def goldenSlopeEnergy (point : ℤ × ℤ) : ℝ :=
  (point.1 : ℝ) * Real.goldenRatio + point.2

-- All spectral distances between distinct points in the finite root window.
noncomputable def goldenDistanceSet (H : GoldenWindowSize) : Finset ℝ := by
  classical
  exact
    (((goldenRootWindow H).product (goldenRootWindow H)).filter
      fun pair => pair.1 ≠ pair.2).image
        fun pair => |goldenSlopeEnergy pair.1 - goldenSlopeEnergy pair.2|

private theorem golden_distance_set_nonempty (H : GoldenWindowSize) :
    (goldenDistanceSet H).Nonempty := by
  classical
  have hH1 : (1 : ℤ) ≤ (H.val : ℤ) := by exact_mod_cast (show 1 ≤ H.val by omega)
  have hH2 : (2 : ℤ) ≤ (H.val : ℤ) := by exact_mod_cast H.property
  refine ⟨|goldenSlopeEnergy (1, 1) - goldenSlopeEnergy (1, 2)|, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(((1, 1), (1, 2)) : (ℤ × ℤ) × (ℤ × ℤ)), ?_, rfl⟩
  simp [goldenRootWindow, hH1, hH2]

-- The minimum spectral spacing `delta_phi(H)` over distinct window points.
noncomputable def goldenSeparation (H : GoldenWindowSize) : ℝ :=
  (goldenDistanceSet H).min' (golden_distance_set_nonempty H)

private theorem golden_pair_separation_bound
    (H : GoldenWindowSize) (x y : ℤ × ℤ)
    (hx : x ∈ goldenRootWindow H) (hy : y ∈ goldenRootWindow H)
    (hxy : x ≠ y) :
    1 / (Real.goldenRatio * ((H.val : ℝ) - 1)) ≤
      |goldenSlopeEnergy x - goldenSlopeEnergy y| := by
  rcases Finset.mem_product.mp hx with ⟨hx1, hx2⟩
  rcases Finset.mem_product.mp hy with ⟨hy1, hy2⟩
  rcases Finset.mem_Icc.mp hx1 with ⟨hx1Lower, hx1Upper⟩
  rcases Finset.mem_Icc.mp hx2 with ⟨hx2Lower, hx2Upper⟩
  rcases Finset.mem_Icc.mp hy1 with ⟨hy1Lower, hy1Upper⟩
  rcases Finset.mem_Icc.mp hy2 with ⟨hy2Lower, hy2Upper⟩
  let a : ℤ := x.1 - y.1
  let b : ℤ := x.2 - y.2
  let B : ℝ := (H.val : ℝ) - 1
  have hBpos : 0 < B := by
    have hOneLt : (1 : ℝ) < H.val := by
      exact_mod_cast (show 1 < H.val by omega)
    simpa [B] using sub_pos.mpr hOneLt
  have hx1LowerReal : (1 : ℝ) ≤ (x.1 : ℝ) := by exact_mod_cast hx1Lower
  have hx1UpperReal : (x.1 : ℝ) ≤ (H.val : ℝ) := by exact_mod_cast hx1Upper
  have hx2LowerReal : (1 : ℝ) ≤ (x.2 : ℝ) := by exact_mod_cast hx2Lower
  have hx2UpperReal : (x.2 : ℝ) ≤ (H.val : ℝ) := by exact_mod_cast hx2Upper
  have hy1LowerReal : (1 : ℝ) ≤ (y.1 : ℝ) := by exact_mod_cast hy1Lower
  have hy1UpperReal : (y.1 : ℝ) ≤ (H.val : ℝ) := by exact_mod_cast hy1Upper
  have hy2LowerReal : (1 : ℝ) ≤ (y.2 : ℝ) := by exact_mod_cast hy2Lower
  have hy2UpperReal : (y.2 : ℝ) ≤ (H.val : ℝ) := by exact_mod_cast hy2Upper
  have haAbs : |(a : ℝ)| ≤ B := by
    rw [abs_le]
    constructor
    · dsimp [a, B]
      push_cast
      linarith
    · dsimp [a, B]
      push_cast
      linarith
  have hbAbs : |(b : ℝ)| ≤ B := by
    rw [abs_le]
    constructor
    · dsimp [b, B]
      push_cast
      linarith
    · dsimp [b, B]
      push_cast
      linarith
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_cases ha : a = 0
    · right
      intro hb
      apply hxy
      apply Prod.ext
      · exact sub_eq_zero.mp (by simpa [a] using ha)
      · exact sub_eq_zero.mp (by simpa [b] using hb)
    · exact Or.inl ha
  let g : GoldenInt := ⟨b, a⟩
  have hg : g ≠ 0 := by
    intro hgZero
    have hbZero : b = 0 := by
      simpa [g] using congrArg (fun z : GoldenInt => z.a) hgZero
    have haZero : a = 0 := by
      simpa [g] using congrArg (fun z : GoldenInt => z.b) hgZero
    rcases hab with ha | hb
    · exact ha haZero
    · exact hb hbZero
  have hnormNe : norm g ≠ 0 := mt (norm_eq_zero_iff g).mp hg
  have hnormLower : (1 : ℝ) ≤ |(norm g : ℝ)| := by
    exact_mod_cast Int.one_le_abs hnormNe
  have hnormProduct :
      |embedding g| * |embedding (conj g)| = |(norm g : ℝ)| :=
    abs_embedding_mul_abs_conj g
  have honeProduct : (1 : ℝ) ≤ |embedding g| * |embedding (conj g)| := by
    calc
      (1 : ℝ) ≤ |(norm g : ℝ)| := hnormLower
      _ = |embedding g| * |embedding (conj g)| := hnormProduct.symm
  have hEmbed : embedding g = (a : ℝ) * Real.goldenRatio + b := by
    simp [g, embedding]
    ring
  have hConjEmbed :
      embedding (conj g) = (a : ℝ) * Real.goldenConj + b := by
    simp only [embedding_apply, conj_a, conj_b]
    simp [g]
    linear_combination (a : ℝ) * Real.goldenRatio_add_goldenConj
  have hPsiAbs : |Real.goldenConj| = Real.goldenRatio - 1 := by
    rw [abs_of_neg Real.goldenConj_neg]
    linarith [Real.goldenRatio_add_goldenConj]
  have hConjBound : |embedding (conj g)| ≤ Real.goldenRatio * B := by
    rw [hConjEmbed]
    calc
      |(a : ℝ) * Real.goldenConj + b| ≤
          |(a : ℝ) * Real.goldenConj| + |(b : ℝ)| := abs_add_le _ _
      _ = |(a : ℝ)| * |Real.goldenConj| + |(b : ℝ)| := by rw [abs_mul]
      _ = |(a : ℝ)| * (Real.goldenRatio - 1) + |(b : ℝ)| := by rw [hPsiAbs]
      _ ≤ B * (Real.goldenRatio - 1) + B :=
        add_le_add
          (mul_le_mul_of_nonneg_right haAbs
            (sub_nonneg.mpr Real.one_lt_goldenRatio.le))
          hbAbs
      _ = Real.goldenRatio * B := by ring
  have honeBound : (1 : ℝ) ≤ |embedding g| * (Real.goldenRatio * B) :=
    honeProduct.trans
      (mul_le_mul_of_nonneg_left hConjBound (abs_nonneg (embedding g)))
  have hdenPos : 0 < Real.goldenRatio * B :=
    mul_pos Real.goldenRatio_pos hBpos
  have hquotient :
      1 / (Real.goldenRatio * B) ≤ |embedding g| := by
    rw [div_le_iff₀ hdenPos]
    exact honeBound
  have hEnergy :
      goldenSlopeEnergy x - goldenSlopeEnergy y =
        (a : ℝ) * Real.goldenRatio + b := by
    simp [goldenSlopeEnergy, a, b]
    ring
  rw [hEnergy, ← hEmbed]
  simpa [B] using hquotient

-- Golden separation bound: the minimum spacing in the finite integer
-- golden-slope window is at least `1 / (phi * (H - 1))`.
theorem golden_separation_bound (H : GoldenWindowSize) :
    1 / (Real.goldenRatio * ((H.val : ℝ) - 1)) ≤ goldenSeparation H := by
  classical
  unfold goldenSeparation
  apply Finset.le_min'
  intro distance hDistance
  rcases Finset.mem_image.mp hDistance with ⟨⟨x, y⟩, hPair, rfl⟩
  rcases Finset.mem_filter.mp hPair with ⟨hWindow, hxy⟩
  rcases Finset.mem_product.mp hWindow with ⟨hx, hy⟩
  exact golden_pair_separation_bound H x y hx hy hxy

-- Reverse probe: the public bound forces the source minimum spacing to be positive.
example (H : GoldenWindowSize) : 0 < goldenSeparation H := by
  have hH : (1 : ℝ) < H.val := by
    exact_mod_cast (show 1 < H.val by omega)
  have hden : 0 < Real.goldenRatio * ((H.val : ℝ) - 1) :=
    mul_pos Real.goldenRatio_pos (sub_pos.mpr hH)
  exact lt_of_lt_of_le (one_div_pos.mpr hden) (golden_separation_bound H)

-- Collapse probe: identifying the two points makes the positive lower bound impossible.
example :
    ¬(1 / Real.goldenRatio ≤
      |goldenSlopeEnergy (1, 1) - goldenSlopeEnergy (1, 1)|) := by
  simpa [goldenSlopeEnergy] using
    (not_le_of_gt (one_div_pos.mpr Real.goldenRatio_pos))

#print axioms golden_separation_bound

end D5.S3.Observer.GoldenCoding.GoldenSeparationBound
