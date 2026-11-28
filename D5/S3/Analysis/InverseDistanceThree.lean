/- GID: D5/S3/Analysis/InverseDistanceThree
   generality: G
   mirror-B: none(waiver:covered-by-penrose-hawking-singularity-bps4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate derivatives and radial decay of the inverse Euclidean distance in dimension three. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Omega original.

Coordinate derivatives and radial decay of the inverse Euclidean distance in dimension three.
-/

compile_only_with_mathlib

set_option autoImplicit false

open Filter WithLp
open scoped BigOperators Topology

namespace OmegaMath.InverseDistanceThree

abbrev Point := Fin 3 → ℝ

def squareDistance (x c : Point) : ℝ := ∑ j, (x j - c j) ^ 2

noncomputable def radius (x c : Point) : ℝ := Real.sqrt (squareDistance x c)

def axis (j : Fin 3) : Point := fun k => if k = j then 1 else 0

def line (x : Point) (j : Fin 3) (t : ℝ) : Point := x + t • axis j

noncomputable def coordinateDerivative (f : Point → ℝ) (j : Fin 3) (x : Point) : ℝ :=
  deriv (fun t => f (line x j t)) 0

noncomputable def laplacian (f : Point → ℝ) (x : Point) : ℝ :=
  ∑ j, coordinateDerivative (coordinateDerivative f j) j x

private theorem radius_norm (x c : Point) :
    radius x c = ‖(toLp 2 x : EuclideanSpace ℝ (Fin 3)) - toLp 2 c‖ := by
  rw [radius, EuclideanSpace.norm_eq]
  congr 1
  simp only [squareDistance, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]

theorem radius_pos {x c : Point} (hx : x ≠ c) : 0 < radius x c := by
  rw [radius_norm]
  exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hx (congrArg ofLp h)))

private theorem squareDistance_pos {x c : Point} (hx : x ≠ c) : 0 < squareDistance x c := by
  exact Real.sqrt_pos.mp (radius_pos hx)

@[simp] theorem line_zero (x : Point) (j : Fin 3) : line x j 0 = x := by
  simp [line]

private theorem squareDistance_line (x c : Point) (j : Fin 3) (t : ℝ) :
    squareDistance (line x j t) c =
      (x j + t - c j) ^ 2 + (squareDistance x c - (x j - c j) ^ 2) := by
  fin_cases j <;> simp [squareDistance, Fin.sum_univ_succ, line, axis] <;> ring

private theorem hasDerivAt_squareDistance (x c : Point) (j : Fin 3) (t : ℝ) :
    HasDerivAt (fun s => squareDistance (line x j s) c) (2 * (x j + t - c j)) t := by
  simp_rw [squareDistance_line]
  have hd : HasDerivAt (fun s => x j + s - c j) 1 t :=
    ((hasDerivAt_id t).const_add (x j)).sub_const (c j)
  simpa using HasDerivAt.add_const (squareDistance x c - (x j - c j) ^ 2) (hd.pow 2)

private theorem line_component (x : Point) (j : Fin 3) (t : ℝ) :
    line x j t j = x j + t := by
  simp [line, axis]

theorem eventually_line_ne {x c : Point} (hx : x ≠ c) (j : Fin 3) :
    ∀ᶠ t : ℝ in 𝓝 0, line x j t ≠ c := by
  have he : ContinuousAt (fun t => squareDistance (line x j t) c) 0 :=
    (hasDerivAt_squareDistance x c j 0).continuousAt
  have hpos : ∀ᶠ t in 𝓝 0, 0 < squareDistance (line x j t) c :=
    he.eventually (Ioi_mem_nhds (by simpa using squareDistance_pos hx))
  filter_upwards [hpos] with t ht eq
  simp [eq, squareDistance] at ht

private theorem hasDerivAt_radius {x c : Point} (j : Fin 3) (t : ℝ)
    (ht : line x j t ≠ c) :
    HasDerivAt (fun s => radius (line x j s) c)
      ((x j + t - c j) / radius (line x j t) c) t := by
  convert (hasDerivAt_squareDistance x c j t).sqrt (squareDistance_pos ht).ne' using 1
  · rfl
  · change (x j + t - c j) / radius (line x j t) c =
      (2 * (x j + t - c j)) / (2 * radius (line x j t) c)
    field_simp [(radius_pos ht).ne']

theorem hasDerivAt_inverse {x c : Point} (j : Fin 3) (t : ℝ)
    (ht : line x j t ≠ c) :
    HasDerivAt (fun s => 1 / radius (line x j s) c)
      (-(x j + t - c j) / radius (line x j t) c ^ 3) t := by
  have hn := (radius_pos ht).ne'
  convert (hasDerivAt_radius j t ht).inv hn using 1
  · funext s
    exact one_div _
  · field_simp [hn]

private theorem partial_inverse {x c : Point} (hx : x ≠ c) (j : Fin 3) :
    coordinateDerivative (fun y => 1 / radius y c) j x = -(x j - c j) / radius x c ^ 3 := by
  simpa [coordinateDerivative] using (hasDerivAt_inverse j 0 (by simpa using hx)).deriv

theorem hasDerivAt_partial_inverse {x c : Point} (hx : x ≠ c) (j : Fin 3) :
    HasDerivAt (fun t => coordinateDerivative (fun y => 1 / radius y c) j (line x j t))
      (3 * (x j - c j) ^ 2 / radius x c ^ 5 - 1 / radius x c ^ 3) 0 := by
  have hr := hasDerivAt_radius j 0 (by simpa using hx)
  have hd : HasDerivAt (fun s => x j + s - c j) 1 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add (x j)).sub_const (c j)
  have hn : HasDerivAt (fun s => -(x j + s - c j)) (-1) 0 := HasDerivAt.neg hd
  have hh := hn.div (hr.pow 3)
    (pow_ne_zero _ (radius_pos (show line x j 0 ≠ c by simpa)).ne')
  have hformula : HasDerivAt (fun s => -(x j + s - c j) / radius (line x j s) c ^ 3)
      (3 * (x j - c j) ^ 2 / radius x c ^ 5 - 1 / radius x c ^ 3) 0 := by
    convert hh using 1
    simp only [Pi.pow_apply, line_zero, add_zero, Nat.cast_ofNat]
    field_simp [(radius_pos hx).ne']
    ring
  apply hformula.congr_of_eventuallyEq
  filter_upwards [eventually_line_ne hx j] with t ht
  rw [partial_inverse ht, line_component]

theorem laplacian_inverse {x c : Point} (hx : x ≠ c) :
    laplacian (fun y => 1 / radius y c) x = 0 := by
  unfold laplacian coordinateDerivative
  change (∑ j, deriv (fun t => coordinateDerivative (fun y => 1 / radius y c) j (line x j t)) 0) = 0
  simp_rw [fun j => (hasDerivAt_partial_inverse hx j).deriv]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  have hs : radius x c ^ 2 = squareDistance x c :=
    Real.sq_sqrt (squareDistance_pos hx).le
  change 3 * squareDistance x c / radius x c ^ 5 - 3 * (1 / radius x c ^ 3) = 0
  rw [← hs]
  field_simp [(radius_pos hx).ne']
  ring

theorem tendsto_radius_atTop {u : Point} (hu : radius u 0 = 1) (c : Point) :
    Tendsto (fun R : ℝ => radius (R • u) c) atTop atTop := by
  have hu' : ‖(toLp 2 u : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa [radius_norm] using hu
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (max 0 (b + ‖(toLp 2 c : EuclideanSpace ℝ (Fin 3))‖))]
    with R hR
  rw [radius_norm]
  have hR₀ : 0 ≤ R := le_trans (le_max_left _ _) hR
  have h := norm_sub_norm_le (R • (toLp 2 u : EuclideanSpace ℝ (Fin 3))) (toLp 2 c)
  rw [norm_smul, hu', Real.norm_eq_abs, abs_of_nonneg hR₀, mul_one] at h
  exact (le_sub_iff_add_le.mpr (le_trans (le_max_right _ _) hR)).trans h

end OmegaMath.InverseDistanceThree
