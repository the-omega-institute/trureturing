/- GID: D5/S3/Geometry/Lorentz/PenroseHawkingSingularityBPS4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/PenroseHawkingSingularityBPS4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Null and timelike focusing, light-sheet area, FLRW lifetime, and extremal potentials. -/

import OmegaBuild.Commands
import D5.S3.Geometry.Lorentz.SachsJacobsonEinstein4D
import D5.S3.Geometry.Lorentz.FLRWCosmologyFriedmann4D
import D5.S3.Geometry.Lorentz.BlackHoleThermodynamics4D
import D5.S3.Analysis.InverseDistanceThree
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! Finite regularity bounds for null optics and cosmological expansion in four dimensions. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D

private theorem negative_expansion_comparison {θ : ℝ → ℝ} {L c : ℝ}
    (hL : 0 ≤ L) (hc : 0 < c) (hθ : ∀ t ∈ Icc 0 L, DifferentiableAt ℝ θ t)
    (hineq : ∀ t ∈ Icc 0 L, deriv θ t ≤ -((θ t) ^ 2) / c) (h₀ : θ 0 < 0) :
    StrictAntiOn θ (Icc 0 L) ∧ (∀ t ∈ Icc 0 L, θ t < 0) ∧
      MonotoneOn (fun t => (θ t)⁻¹ - t / c) (Icc 0 L) ∧ L < c / |θ 0| := by
  have hI : Convex ℝ (Icc 0 L) := convex_Icc 0 L
  have hzero : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL⟩
  have hcont : ContinuousOn θ (Icc 0 L) :=
    fun t ht => (hθ t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ θ (interior (Icc 0 L)) :=
    fun t ht => (hθ t (interior_subset ht)).differentiableWithinAt
  have hanti : AntitoneOn θ (Icc 0 L) := by
    apply antitoneOn_of_deriv_nonpos hI hcont hdiff
    intro t ht
    exact (hineq t (interior_subset ht)).trans
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hc.le)
  have hneg (t : ℝ) (ht : t ∈ Icc 0 L) : θ t < 0 :=
    (hanti hzero ht ht.1).trans_lt h₀
  have hstrict : StrictAntiOn θ (Icc 0 L) := by
    apply strictAntiOn_of_deriv_neg hI
    · exact hcont
    · intro t ht
      exact (hineq t (interior_subset ht)).trans_lt
        (div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_ne_zero (hneg t (interior_subset ht)).ne)) hc)
  let f := fun t => (θ t)⁻¹ - t / c
  have hd (t : ℝ) (ht : t ∈ Icc 0 L) :
      HasDerivAt f (-deriv θ t / (θ t) ^ 2 - 1 / c) t :=
    (((hθ t ht).hasDerivAt.inv (hneg t ht).ne).sub ((hasDerivAt_id t).div_const c))
  have hmono : MonotoneOn f (Icc 0 L) := by
    apply monotoneOn_of_deriv_nonneg hI
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    have ht' := interior_subset ht
    rw [(hd t ht').deriv, sub_nonneg]
    apply (le_div_iff₀ (sq_pos_of_ne_zero (hneg t ht').ne)).2
    rw [show 1 / c * (θ t) ^ 2 = (θ t) ^ 2 / c by ring]
    simpa only [neg_div, neg_neg] using (neg_le_neg (hineq t ht'))
  have hend : L ∈ Icc 0 L := ⟨hL, le_rfl⟩
  have hf := hmono hzero hend hL
  change (θ 0)⁻¹ - 0 / c ≤ (θ L)⁻¹ - L / c at hf
  simp only [zero_div, sub_zero] at hf
  have hinv : (θ L)⁻¹ < 0 := inv_lt_zero'.mpr (hneg L hend)
  have hrec : L / c < -(θ 0)⁻¹ := by linarith
  have hrec' : L / c < 1 / |θ 0| := by
    rwa [abs_of_neg h₀, one_div, inv_neg]
  have hprod := (div_lt_iff₀ hc).mp hrec'
  refine ⟨hstrict, hneg, hmono, ?_⟩
  linarith only [hprod, show 1 / |θ 0| * c = c / |θ 0| by ring]

private theorem null_deriv_bound {θ σSq Rkk : ℝ → ℝ} {L : ℝ}
    (hθ : ∀ t ∈ Icc 0 L, HasDerivAt θ (-((θ t) ^ 2) / 2 - σSq t - Rkk t) t)
    (hσ : ∀ t ∈ Icc 0 L, 0 ≤ σSq t) (hR : ∀ t ∈ Icc 0 L, 0 ≤ Rkk t)
    {t : ℝ} (ht : t ∈ Icc 0 L) :
    deriv θ t ≤ -((θ t) ^ 2) / 2 := by
  rw [(hθ t ht).deriv]
  linarith [hσ t ht, hR t ht]

/-- Negative null expansion has a finite upper bound on its regular affine interval. -/
theorem penrose_trapped_surface_caustic_bound {θ σSq Rkk : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L)
    (hθ : ∀ t ∈ Icc 0 L, HasDerivAt θ (-((θ t) ^ 2) / 2 - σSq t - Rkk t) t)
    (hσ : ∀ t ∈ Icc 0 L, 0 ≤ σSq t) (hR : ∀ t ∈ Icc 0 L, 0 ≤ Rkk t)
    (h₀ : θ 0 < 0) :
    StrictAntiOn θ (Icc 0 L) ∧
      (∀ t ∈ Icc 0 L, θ t < 0 ∧ 1 / θ 0 + t / 2 ≤ 1 / θ t) ∧ L < 2 / |θ 0| := by
  obtain ⟨hanti, hneg, hmono, hlength⟩ := negative_expansion_comparison hL (by norm_num : (0 : ℝ) < 2)
    (fun t ht => (hθ t ht).differentiableAt) (fun _ ht => null_deriv_bound hθ hσ hR ht) h₀
  refine ⟨hanti, fun t ht => ⟨hneg t ht, ?_⟩, hlength⟩
  have h := hmono (left_mem_Icc.mpr hL) ht ht.1
  simp only [zero_div, sub_zero, one_div] at h ⊢
  linarith only [h]

/-- Initial positive focusing gives a strictly improved reciprocal estimate at every later point. -/
theorem penrose_shear_strictly_accelerates_focusing {θ σSq Rkk : ℝ → ℝ} {L : ℝ}
    (hθ : ∀ t ∈ Icc 0 L, HasDerivAt θ (-((θ t) ^ 2) / 2 - σSq t - Rkk t) t)
    (hσ : ∀ t ∈ Icc 0 L, 0 ≤ σSq t) (hR : ∀ t ∈ Icc 0 L, 0 ≤ Rkk t)
    (h₀ : θ 0 < 0) (hstrict : 0 < σSq 0 ∨ 0 < Rkk 0) :
    ∀ t ∈ Ioc 0 L, 1 / θ 0 + t / 2 < 1 / θ t := by
  intro t ht
  have hL := (ht.1.trans_le ht.2).le
  have hzero := left_mem_Icc.mpr hL
  obtain ⟨_, _, hmono, _⟩ := negative_expansion_comparison hL (by norm_num : (0 : ℝ) < 2)
    (fun x hx => (hθ x hx).differentiableAt) (fun _ hx => null_deriv_bound hθ hσ hR hx) h₀
  let f := fun x => (θ x)⁻¹ - x / 2
  have hd : HasDerivAt f ((σSq 0 + Rkk 0) / (θ 0) ^ 2) 0 := by
    apply (((hθ 0 hzero).inv h₀.ne).sub ((hasDerivAt_id (0 : ℝ)).div_const 2)).congr_deriv
    field_simp [h₀.ne]
    ring
  have hpos : 0 < (σSq 0 + Rkk 0) / (θ 0) ^ 2 := by
    apply div_pos _ (sq_pos_of_ne_zero h₀.ne)
    rcases hstrict with hs | hr
    · exact add_pos_of_pos_of_nonneg hs (hR 0 hzero)
    · exact add_pos_of_nonneg_of_pos (hσ 0 hzero) hr
  have hlt : f 0 < f t := by
    by_contra! hle
    have hconst (x : ℝ) (hx : x ∈ Icc 0 t) : f x = f 0 := by
      have hxs : x ∈ Icc 0 L := ⟨hx.1, hx.2.trans ht.2⟩
      exact le_antisymm ((hmono hxs ⟨ht.1.le, ht.2⟩ hx.2).trans hle)
        (hmono hzero hxs hx.1)
    have hdz : HasDerivWithinAt f 0 (Icc 0 t) 0 :=
      (hasDerivAt_const (0 : ℝ) (f 0)).hasDerivWithinAt.congr hconst rfl
    have hu := uniqueDiffOn_Icc ht.1 0 (left_mem_Icc.mpr ht.1.le)
    exact hpos.ne' ((hd.hasDerivWithinAt.derivWithin hu).symm.trans (hdz.derivWithin hu))
  change (θ 0)⁻¹ - 0 / 2 < (θ t)⁻¹ - t / 2 at hlt
  simp only [zero_div, sub_zero, one_div] at hlt ⊢
  linarith only [hlt]

open SachsJacobsonEinstein4D (OpticalData SolvesOn area optical_nec_bounds hasDerivAt_area
  tangent_delay_nonneg tangentDelay radiusSlope)

/-- The positive optical radius is concave and the area of a light-sheet is antitone. -/
theorem bousso_lightsheet_area_monotonicity {o : OpticalData} {L : ℝ}
    (hL : 0 ≤ L) (ho : SolvesOn o (Icc 0 L)) (hR : ∀ t ∈ Icc 0 L, 0 ≤ o.ricciTerm t)
    (hr : ∀ t ∈ Icc 0 L, 0 < o.radius t) (h₀ : o.expansion 0 ≤ 0) :
    ConcaveOn ℝ (Icc 0 L) (fun t => Real.sqrt (area o t)) ∧
      (∀ t ∈ Icc 0 L, o.expansion t ≤ 0) ∧ AntitoneOn (area o) (Icc 0 L) ∧
      (o.expansion 0 < 0 →
        (∀ t ∈ Icc 0 L, Real.sqrt (area o t) ≤
          Real.sqrt (area o 0) * (1 + (o.expansion 0 / 2) * t)) ∧
        L < 2 / |o.expansion 0|) := by
  have hzero := left_mem_Icc.mpr hL
  obtain ⟨_, hanti, _, hconc⟩ :=
    optical_nec_bounds ho (convex_Icc _ _) hR (fun t ht => (hr t ht).le)
  have hsqrt (t : ℝ) (ht : t ∈ Icc 0 L) : o.radius t = Real.sqrt (area o t) := by
    rw [area, Real.sqrt_sq (hr t ht).le]
  have hnonpos (t : ℝ) (ht : t ∈ Icc 0 L) : o.expansion t ≤ 0 :=
    (hanti hzero ht ht.1).trans h₀
  refine ⟨hconc.congr hsqrt, hnonpos, ?_, ?_⟩
  · apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun t ht => (hasDerivAt_area ho ht).continuousAt.continuousWithinAt)
      (fun t ht => (hasDerivAt_area ho (interior_subset ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hasDerivAt_area ho (interior_subset ht)).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (hnonpos t (interior_subset ht)) (sq_nonneg _)
  · intro hneg
    have htangent (t : ℝ) (ht : t ∈ Icc 0 L) :
        o.radius t ≤ o.radius 0 * (1 + (o.expansion 0 / 2) * t) := by
      have hs : Icc (0 : ℝ) t ⊆ Icc 0 L := Icc_subset_Icc_right ht.2
      have ho' : SolvesOn o (Icc 0 t) := ⟨
        fun x hx => ho.expansion' x (hs hx),
        fun x hx => ho.shear' x (hs hx),
        fun x hx => ho.radius' x (hs hx)⟩
      have hd := tangent_delay_nonneg ht.1 ho' (fun x hx => hR x (hs hx))
        (fun x hx => (hr x (hs hx)).le)
      unfold tangentDelay radiusSlope at hd
      nlinarith only [hd]
    refine ⟨fun t ht => ?_, ?_⟩
    · rw [← hsqrt t ht, ← hsqrt 0 hzero]
      exact htangent t ht
    · have hbound := (hr L (right_mem_Icc.mpr hL)).trans_le (htangent L (right_mem_Icc.mpr hL))
      have hlin := pos_of_mul_pos_right hbound (hr 0 hzero).le
      rw [abs_of_neg hneg, lt_div_iff₀ (neg_pos.mpr hneg)]
      linarith only [hlin]

open FLRWCosmologyFriedmann4D

/-- A positive FLRW scale factor with antitone velocity has finite past lifetime. -/
theorem hawking_past_big_bang_bound {a : ℝ → ℝ} {t₀ T : ℝ}
    (hT : 0 < T) (ha : ∀ t ∈ Icc (t₀ - T) t₀, DifferentiableAt ℝ a t)
    (hsec : AntitoneOn (deriv a) (Icc (t₀ - T) t₀))
    (ha₀ : 0 < a t₀) (hv₀ : 0 < deriv a t₀) :
    0 < hubble a t₀ ∧
      (∀ t ∈ Icc (t₀ - T) t₀, a t ≤ a t₀ * (1 + hubble a t₀ * (t - t₀))) ∧
      ((∀ t ∈ Icc (t₀ - T) t₀, 0 < a t) → T < 1 / hubble a t₀) := by
  have ht₀ : t₀ ∈ Icc (t₀ - T) t₀ := ⟨by linarith, le_rfl⟩
  have hH : 0 < hubble a t₀ := div_pos hv₀ ha₀
  have htangent (t : ℝ) (ht : t ∈ Icc (t₀ - T) t₀) :
      a t ≤ a t₀ + deriv a t₀ * (t - t₀) := by
    by_cases hsame : t = t₀
    · simp [hsame]
    have hlt := lt_of_le_of_ne ht.2 hsame
    have hs : Icc t t₀ ⊆ Icc (t₀ - T) t₀ := Icc_subset_Icc_left ht.1
    obtain ⟨x, hx, hdx⟩ := exists_deriv_eq_slope a hlt
      (fun x hx => (ha x (hs hx)).continuousAt.continuousWithinAt)
      (fun x hx => (ha x (hs (Ioo_subset_Icc_self hx))).differentiableWithinAt)
    have hvel := hsec (hs (Ioo_subset_Icc_self hx)) ht₀ hx.2.le
    rw [hdx, le_div_iff₀ (sub_pos.mpr hlt)] at hvel
    linarith only [hvel]
  have hscaled (t : ℝ) (ht : t ∈ Icc (t₀ - T) t₀) :
      a t ≤ a t₀ * (1 + hubble a t₀ * (t - t₀)) := by
    convert htangent t ht using 1
    unfold hubble
    field_simp [ha₀.ne']
  refine ⟨hH, hscaled, fun hpos => ?_⟩
  have hleft : t₀ - T ∈ Icc (t₀ - T) t₀ := ⟨le_rfl, by linarith⟩
  have hpositive := pos_of_mul_pos_right ((hpos _ hleft).trans_le (hscaled _ hleft)) ha₀.le
  exact (lt_div_iff₀ hH).2 (by linarith only [hpositive])

/-- The timelike four-dimensional Raychaudhuri coefficient gives its affine ceiling. -/
theorem hawking_timelike_congruence_raychaudhuri {θ : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hθ : ∀ t ∈ Icc 0 L, DifferentiableAt ℝ θ t)
    (hsec : ∀ t ∈ Icc 0 L, deriv θ t ≤ -((θ t) ^ 2) / 3) (h₀ : θ 0 < 0) :
    L < 3 / |θ 0| :=
  (negative_expansion_comparison hL (by norm_num) hθ hsec h₀).2.2.2

/-- Pairwise inward gravitational force for positive masses. -/
def gravitationalForce (m₁ m₂ r : ℝ) : ℝ := m₁ * m₂ / r ^ 2

/-- Magnitude of the Coulomb force. -/
def coulombForceMagnitude (q₁ q₂ r : ℝ) : ℝ := |q₁ * q₂| / r ^ 2

/-- Outward radial force, with attraction represented by negative values. -/
def netBPSForce (m₁ q₁ m₂ q₂ r : ℝ) : ℝ := (q₁ * q₂ - m₁ * m₂) / r ^ 2

theorem bps_extremal_force_cancellation {m₁ q₁ m₂ q₂ r : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hr : 0 < r)
    (h : (q₁ = m₁ ∧ q₂ = m₂) ∨ (q₁ = -m₁ ∧ q₂ = -m₂)) :
    netBPSForce m₁ q₁ m₂ q₂ r = 0 ∧
      coulombForceMagnitude q₁ q₂ r = gravitationalForce m₁ m₂ r ∧
      0 < gravitationalForce m₁ m₂ r ∧
      BlackHoleThermodynamics4D.surfaceGravity m₁ 0 q₁ = 0 ∧
      BlackHoleThermodynamics4D.surfaceGravity m₂ 0 q₂ = 0 := by
  have extremal {m q : ℝ} (hq : q = m ∨ q = -m) :
      BlackHoleThermodynamics4D.surfaceGravity m 0 q = 0 := by
    apply BlackHoleThermodynamics4D.surfaceGravity_zero_of_extremal
    rcases hq with rfl | rfl <;> simp [BlackHoleThermodynamics4D.spin]
  have hprod : q₁ * q₂ = m₁ * m₂ := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  refine ⟨by simp [netBPSForce, hprod], ?_, div_pos (mul_pos hm₁ hm₂) (pow_pos hr 2), ?_, ?_⟩
  · simp [coulombForceMagnitude, gravitationalForce, hprod,
      abs_of_pos (mul_pos hm₁ hm₂)]
  · exact extremal (h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  · exact extremal (h.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))

theorem bps_superposition_charge_bound {N : ℕ} {m q : Fin N → ℝ}
    (hext : ∀ i, q i = m i) :
    (∑ i, m i) = ∑ i, q i := by
  exact Finset.sum_congr rfl fun i _ => (hext i).symm

theorem bps_subextremal_attraction {m₁ q₁ m₂ q₂ r : ℝ}
    (h₁ : |q₁| < m₁) (h₂ : |q₂| ≤ m₂) (hm₂ : 0 < m₂) (hr : 0 < r) :
    netBPSForce m₁ q₁ m₂ q₂ r < 0 := by
  have hprod : q₁ * q₂ < m₁ * m₂ := calc
    q₁ * q₂ ≤ |q₁ * q₂| := le_abs_self _
    _ = |q₁| * |q₂| := abs_mul _ _
    _ ≤ |q₁| * m₂ := mul_le_mul_of_nonneg_left h₂ (abs_nonneg _)
    _ < m₁ * m₂ := mul_lt_mul_of_pos_right h₁ hm₂
  exact div_neg_of_neg_of_pos (sub_neg.mpr hprod) (pow_pos hr 2)

open OmegaMath.InverseDistanceThree

abbrev r3 (x y : Point) : ℝ := radius x y

/-- Potential with one inverse-distance term for each center. -/
def mpPotential {N : ℕ} (m : Fin N → ℝ) (c : Fin N → Point) (x : Point) : ℝ :=
  1 + ∑ i, m i / r3 x (c i)

theorem inv_r3_harmonic_3d {x c : Point} (hx : x ≠ c) :
    (∀ j : Fin 3,
      HasDerivAt (fun t => 1 / r3 (line x j t) c) (-(x j - c j) / r3 x c ^ 3) 0 ∧
      HasDerivAt (fun t => coordinateDerivative (fun y => 1 / r3 y c) j (line x j t))
        (3 * (x j - c j) ^ 2 / r3 x c ^ 5 - 1 / r3 x c ^ 3) 0) ∧
    laplacian (fun y => 1 / r3 y c) x = 0 := by
  refine ⟨fun j => ⟨?_, hasDerivAt_partial_inverse hx j⟩, laplacian_inverse hx⟩
  simpa using hasDerivAt_inverse j 0 (by simpa using hx)

/-- First derivatives are summed on the common domain avoiding the centers. -/
private theorem coordinateDerivative_mpPotential {N : ℕ} (m : Fin N → ℝ)
    (c : Fin N → Point) {x : Point} (hx : ∀ i, x ≠ c i) (j : Fin 3) :
    coordinateDerivative (mpPotential m c) j x =
      ∑ i, m i * coordinateDerivative (fun y => 1 / r3 y (c i)) j x := by
  have hs : ∀ i : Fin N, HasDerivAt
      (fun t => m i / r3 (line x j t) (c i))
      (m i * coordinateDerivative (fun y => 1 / r3 y (c i)) j x) 0 := by
    intro i
    have hi := ((inv_r3_harmonic_3d (hx i)).1 j).1
    rw [coordinateDerivative, hi.deriv]
    simpa only [mul_one_div] using hi.const_mul (m i)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hs i
  exact (HasDerivAt.const_add 1 hsum).deriv

private theorem secondDerivative_mpPotential {N : ℕ} (m : Fin N → ℝ)
    (c : Fin N → Point) {x : Point} (hx : ∀ i, x ≠ c i) (j : Fin 3) :
    coordinateDerivative (coordinateDerivative (mpPotential m c) j) j x =
      ∑ i, m i * coordinateDerivative (coordinateDerivative (fun y => 1 / r3 y (c i)) j) j x := by
  have hs : ∀ i : Fin N, HasDerivAt
      (fun t => m i * coordinateDerivative (fun y => 1 / r3 y (c i)) j (line x j t))
      (m i * coordinateDerivative (coordinateDerivative (fun y => 1 / r3 y (c i)) j) j x)
      0 := by
    intro i
    have hi := ((inv_r3_harmonic_3d (hx i)).1 j).2
    rw [coordinateDerivative, hi.deriv]
    exact hi.const_mul (m i)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hs i
  refine (hsum.congr_of_eventuallyEq ?_).deriv
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, line x j t ≠ c i :=
    Filter.eventually_all.mpr fun i => eventually_line_ne (hx i) j
  filter_upwards [hnear] with t ht
  exact coordinateDerivative_mpPotential m c ht j

theorem majumdar_papapetrou_harmonic {N : ℕ} (m : Fin N → ℝ) (c : Fin N → Point) :
    (∀ x, (∀ i, x ≠ c i) → laplacian (mpPotential m c) x = 0) ∧
    (∀ x, (∀ i, x ≠ c i) → (∀ i, 0 ≤ m i) → (∃ i, 0 < m i) → 1 < mpPotential m c x) ∧
    (∀ u, r3 u 0 = 1 → Tendsto (fun R : ℝ => mpPotential m c (R • u)) atTop (𝓝 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    unfold laplacian
    simp_rw [secondDerivative_mpPotential m c hx]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.mul_sum]
    change m i * laplacian (fun y => 1 / r3 y (c i)) x = 0
    rw [(inv_r3_harmonic_3d (hx i)).2, mul_zero]
  · rintro x hx hm ⟨i, hi⟩
    unfold mpPotential
    have hsum : 0 < ∑ k, m k / r3 x (c k) :=
      Finset.sum_pos' (fun k _ => div_nonneg (hm k) (radius_pos (hx k)).le)
        ⟨i, Finset.mem_univ _, div_pos hi (radius_pos (hx i))⟩
    linarith
  · intro u hu
    have ht (i : Fin N) :
        Tendsto (fun R : ℝ => m i / r3 (R • u) (c i)) atTop (𝓝 0) :=
      by
        simpa [div_eq_mul_inv] using
          ((tendsto_inv_atTop_zero.comp (tendsto_radius_atTop hu (c i))).const_mul (m i))
    have hs := tendsto_finsetSum (s := Finset.univ) fun i _ => ht i
    have hs₀ : Tendsto (fun R : ℝ => ∑ i, m i / r3 (R • u) (c i)) atTop (𝓝 0) := by
      simpa using hs
    simpa [mpPotential] using hs₀.const_add (1 : ℝ)

end D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D
