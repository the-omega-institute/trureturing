/- GID: D5/S3/Topology/LowDimensionalBorsukUlam
   generality: G
   mirror-B: D5/B/S3/Topology/LowDimensionalBorsukUlam
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous maps from the unit sphere of R^(d+1) to R^d with d <= 2 meet antipodally. -/

import D5.S3.Geometry.Lorentz.ChiralEventParityMinimality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! # The Borsuk--Ulam theorem in dimensions at most two

A continuous map from the unit sphere of `ℝ^(d+1)` to `ℝ^d` with `d ≤ 2` sends some pair of
antipodal points to the same value. For `d = 0` this is immediate, for `d = 1` it follows from the
intermediate value theorem on the connected circle, and for `d = 2` it reduces to the fact that a
continuous odd map from the unit sphere of `ℝ³` to `ℂ` has a zero
(`D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.planar_odd_map_zero`). Consequently a
nonempty open subset of `ℝ^m` admits no continuous injection into `ℝ^d` when `d < m` and
`d ≤ 2`: a small sphere of dimension `d` inside the open set would be mapped injectively. -/

set_option autoImplicit false

open Metric

namespace D5.S3.Topology.LowDimensionalBorsukUlam

/-- Every map from the unit sphere of `ℝ¹` to `ℝ⁰` identifies some pair of antipodal points. -/
private theorem exists_eq_neg_zero (f : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 0)) :
    ∃ x ∈ sphere (0 : EuclideanSpace ℝ (Fin 1)) 1, f x = f (-x) :=
  ⟨EuclideanSpace.single 0 1, by simp, PiLp.ext fun i => i.elim0⟩

/-- A continuous map from the unit circle of `ℝ²` to `ℝ` identifies some pair of antipodal
points: the antipodal difference is odd, so it changes sign on the connected circle. -/
private theorem exists_eq_neg_one (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 1))
    (hf : ContinuousOn f (sphere 0 1)) :
    ∃ x ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, f x = f (-x) := by
  set S := sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 with hS
  have hneg : Set.MapsTo (fun x => -x) S S := fun x hx => by simpa [hS] using hx
  let g : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => f x 0 - f (-x) 0
  have hg : ContinuousOn g S :=
    ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp_continuousOn hf).sub
      ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp_continuousOn
        (hf.comp continuous_neg.continuousOn hneg))
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have hconn : IsPreconnected S := isPreconnected_sphere hrank 0 1
  let x₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  have hx₀ : x₀ ∈ S := by simp [hS, x₀]
  have hodd : g (-x₀) = -g x₀ := by
    simp only [g, neg_neg]
    ring
  obtain ⟨x, hx, hgx⟩ : (0 : ℝ) ∈ g '' S := by
    rcases le_total (g x₀) 0 with h | h
    · exact hconn.intermediate_value hx₀ (hneg hx₀) hg ⟨h, by rw [hodd]; linarith⟩
    · exact hconn.intermediate_value (hneg hx₀) hx₀ hg ⟨by rw [hodd]; linarith, h⟩
  refine ⟨x, hx, PiLp.ext fun i => ?_⟩
  fin_cases i
  exact sub_eq_zero.mp hgx

/-- A continuous map from the unit sphere of `ℝ³` to `ℝ²` identifies some pair of antipodal
points: the antipodal difference, read in `ℂ` through an isometric identification, is an odd map
and therefore has a zero. -/
private theorem exists_eq_neg_two (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2))
    (hf : ContinuousOn f (sphere 0 1)) :
    ∃ x ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, f x = f (-x) := by
  have hneg : Set.MapsTo (fun x => -x) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (sphere 0 1) := fun x hx => by simpa using hx
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  obtain ⟨v, hv, hz⟩ :=
    D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.planar_odd_map_zero
      (fun x => e (f x - f (-x)))
      (e.continuous.comp_continuousOn (hf.sub (hf.comp continuous_neg.continuousOn hneg)))
      (fun v _ => by simp only [neg_neg, ← map_neg, neg_sub])
  refine ⟨v, hv, sub_eq_zero.mp (e.injective ?_)⟩
  rw [hz, map_zero]

/-- The Borsuk--Ulam theorem in dimensions at most two: a map from the unit sphere of `ℝ^(d+1)`
to `ℝ^d`, continuous on the sphere, takes the same value at some pair of antipodal points. -/
theorem exists_eq_neg_of_le_two {d : ℕ} (hd : d ≤ 2)
    (f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f (Metric.sphere 0 1)) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1, f x = f (-x) := by
  interval_cases d
  · exact exists_eq_neg_zero f
  · exact exists_eq_neg_one f hf
  · exact exists_eq_neg_two f hf

/-- For `d ≤ 2` and `d < m`, no map from `ℝ^m` to `ℝ^d` is continuous and injective on a
nonempty open set: it would be injective on a small `d`-sphere inside the set. -/
theorem not_injOn_of_lt {m d : ℕ} (hd : d ≤ 2) (hdm : d < m)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU : IsOpen U) (hne : U.Nonempty)
    (f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d)) (hf : ContinuousOn f U) :
    ¬ Set.InjOn f U := by
  intro hinj
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hdm
  obtain ⟨p, hp⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU p hp
  let ι : EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (d + 1 + k)) :=
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ _ _)
  have hι : Function.Injective ι := by
    intro x y hxy
    have h := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := d + 1) (m := k)).symm.injective hxy
    exact (Prod.ext_iff.mp h).1
  set t : ℝ := r / (‖ι‖ + 1) with ht
  have htpos : 0 < t := div_pos hr (by positivity)
  let φ : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1 + k)) :=
    fun y => p + t • ι y
  have hφ : Set.MapsTo φ (sphere 0 1) U := by
    intro y hy
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [φ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have hy1 : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
    have hle : ‖ι y‖ ≤ ‖ι‖ := by
      simpa [hy1] using ι.le_opNorm y
    calc t * ‖ι y‖ ≤ t * ‖ι‖ := mul_le_mul_of_nonneg_left hle htpos.le
      _ < t * (‖ι‖ + 1) := by nlinarith
      _ = r := by rw [ht]; field_simp
  have hφc : Continuous φ := continuous_const.add (ι.continuous.const_smul t)
  obtain ⟨x, hx, hfx⟩ := exists_eq_neg_of_le_two hd (f ∘ φ) (hf.comp hφc.continuousOn hφ)
  have hx' : -x ∈ sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 := by simpa using hx
  have heq : φ x = φ (-x) := hinj (hφ hx) (hφ hx') hfx
  have h0 : ι x = 0 := by
    simp only [φ, add_right_inj, map_neg, smul_neg] at heq
    have h2 : (2 * t) • ι x = 0 := by
      rw [mul_smul, two_smul]
      exact eq_neg_iff_add_eq_zero.mp heq
    exact (smul_eq_zero.mp h2).resolve_left (by positivity)
  have hx0 : x = 0 := hι (h0.trans (map_zero ι).symm)
  have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
  rw [hx0, norm_zero] at hx1
  exact zero_ne_one hx1

end D5.S3.Topology.LowDimensionalBorsukUlam
