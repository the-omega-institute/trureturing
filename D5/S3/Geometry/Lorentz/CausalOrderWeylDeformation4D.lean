/- GID: D5/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/CausalOrderWeylDeformation4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Null-cone deformation and curvature reconstruction from volume and five null tides. -/

import D5.S3.Geometry.Lorentz.WeylNullScreen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.LinearCombination
import Batteries.Tactic.OpenPrivate

/-! Pointwise Lorentzian curvature from Alexandrov volume and transverse null tides. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Lorentz.CausalOrderWeylDeformation4D

open Matrix
open WeylNullScreen
open private ricci_symm lorentzTrace diagSum tidal_symm wedge pairBilinear
  fromEM emBlock pairLeft pairRight electric contractions
  from D5.S3.Geometry.Lorentz.WeylNullScreen

/-- The metric matrix in the same sign convention as the null screens. -/
def eta {K : Type*} [Ring K] : Matrix (Fin 4) (Fin 4) K :=
  diagonal ![-1, 1, 1, 1]

/-- Contraction with the inverse Minkowski metric. -/
def minkowskiTrace {K : Type*} [Ring K] (h : Matrix (Fin 4) (Fin 4) K) : K :=
  ∑ i, eta i i * h i i

/-- The metric perturbation with its conformal component removed. -/
def traceFree {K : Type*} [Field K] (h : Matrix (Fin 4) (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K :=
  h - (minkowskiTrace h / 4) • eta

private theorem eta_transpose {K : Type*} [Ring K] : (eta (K := K))ᵀ = eta :=
  diagonal_transpose _

private theorem q_eta_smul {K : Type*} [Field K] (a : K) (x : Fin 4 → K) :
    x ⬝ᵥ (a • eta) *ᵥ x = a * minkowski x x := by
  simp [dotProduct, mulVec, eta, diagonal_apply, Fin.sum_univ_succ, minkowski]
  ring

private theorem q_sub {K : Type*} [Field K] (g h : Matrix (Fin 4) (Fin 4) K)
    (x : Fin 4 → K) :
    x ⬝ᵥ (g - h) *ᵥ x = x ⬝ᵥ g *ᵥ x - x ⬝ᵥ h *ᵥ x := by
  simp [dotProduct, mulVec, sub_mul, mul_sub, Finset.sum_sub_distrib]

private theorem q_entries {K : Type*} [Field K] (g : Matrix (Fin 4) (Fin 4) K)
    (hg : gᵀ = g) (a b c d : K) :
    ![a, b, c, d] ⬝ᵥ g *ᵥ ![a, b, c, d] =
      g 0 0 * a^2 + g 1 1 * b^2 + g 2 2 * c^2 + g 3 3 * d^2 +
      2 * (g 0 1 * a*b + g 0 2 * a*c + g 0 3 * a*d +
           g 1 2 * b*c + g 1 3 * b*d + g 2 3 * c*d) := by
  have h (i j : Fin 4) : g j i = g i j := congrFun (congrFun hg i) j
  simp [dotProduct, mulVec, Fin.sum_univ_succ,
    h 0 1, h 0 2, h 0 3, h 1 2, h 1 3, h 2 3]
  ring

/-- Containment of null cones already forces proportionality, even over fields
without square roots. Six axial null vectors and three Pythagorean vectors suffice. -/
theorem conformal_metric_same_null_cone_iff {K : Type*} [Field K] [CharZero K]
    (g : Matrix (Fin 4) (Fin 4) K) (hg : gᵀ = g) :
    (∀ k : Fin 4 → K, (∑ i, eta i i * k i * k i) = 0 → k ⬝ᵥ g *ᵥ k = 0) ↔
      ∃ Ω : K, g = Ω • eta := by
  have hn (k : Fin 4 → K) : (∑ i, eta i i * k i * k i) = minkowski k k := by
    simp [eta, Fin.sum_univ_succ, minkowski, mul_assoc, add_assoc]
  simp only [hn]
  constructor
  · intro h
    have eval (a b c d : K) (hnull : -(a*a) + b*b + c*c + d*d = 0) :=
      (q_entries g hg a b c d).symm.trans
        (h ![a, b, c, d] (by simpa [minkowski] using hnull))
    have h1p := eval 1 1 0 0 (by norm_num)
    have h1m := eval 1 (-1) 0 0 (by norm_num)
    have h2p := eval 1 0 1 0 (by norm_num)
    have h2m := eval 1 0 (-1) 0 (by norm_num)
    have h3p := eval 1 0 0 1 (by norm_num)
    have h3m := eval 1 0 0 (-1) (by norm_num)
    have d1 : g 1 1 = -g 0 0 := by linear_combination (h1p + h1m) / 2
    have d2 : g 2 2 = -g 0 0 := by linear_combination (h2p + h2m) / 2
    have d3 : g 3 3 = -g 0 0 := by linear_combination (h3p + h3m) / 2
    have o1 : g 0 1 = 0 := by linear_combination (h1p - h1m) / 4
    have o2 : g 0 2 = 0 := by linear_combination (h2p - h2m) / 4
    have o3 : g 0 3 = 0 := by linear_combination (h3p - h3m) / 4
    have h12 := eval 5 3 4 0 (by norm_num)
    have h13 := eval 5 3 0 4 (by norm_num)
    have h23 := eval 5 0 3 4 (by norm_num)
    rw [d1, d2, o1, o2, o3] at h12
    rw [d1, d3, o1, o2, o3] at h13
    rw [d2, d3, o1, o2, o3] at h23
    have o12 : g 1 2 = 0 := by linear_combination h12 / 24
    have o13 : g 1 3 = 0 := by linear_combination h13 / 24
    have o23 : g 2 3 = 0 := by linear_combination h23 / 24
    have hs (i j : Fin 4) : g j i = g i j := congrFun (congrFun hg i) j
    refine ⟨-g 0 0, Matrix.ext fun i j => ?_⟩
    fin_cases i <;> fin_cases j <;>
      simp [eta, d1, d2, d3, o1, o2, o3, o12, o13, o23,
        hs 0 1, hs 0 2, hs 0 3, hs 1 2, hs 1 3, hs 2 3]
  · rintro ⟨a, rfl⟩ k hk
    rw [q_eta_smul, hk, mul_zero]

private theorem trace_sub_smul_eta {K : Type*} [Field K]
    (h : Matrix (Fin 4) (Fin 4) K) (a : K) :
    minkowskiTrace (h - a • eta) = minkowskiTrace h - 4 * a := by
  simp [minkowskiTrace, eta, Fin.sum_univ_succ]
  ring

/-- The complete kernel of the first-order null-cone readings is the conformal
line. The canonical representative of each reading is trace-free. -/
theorem null_cone_perturbation_trace_free_split {K : Type*} [Field K] [CharZero K]
    (h : Matrix (Fin 4) (Fin 4) K) (hs : hᵀ = h) :
    h = (minkowskiTrace h / 4) • eta + traceFree h ∧
    minkowskiTrace (traceFree h) = 0 ∧
    (∀ k : Fin 4 → K, minkowski k k = 0 → k ⬝ᵥ h *ᵥ k = k ⬝ᵥ traceFree h *ᵥ k) ∧
    ((∀ k : Fin 4 → K, minkowski k k = 0 → k ⬝ᵥ h *ᵥ k = 0) ↔ traceFree h = 0) := by
  have ht : minkowskiTrace (traceFree h) = 0 := by
    rw [traceFree, trace_sub_smul_eta]
    ring
  have hq (k : Fin 4 → K) (hk : minkowski k k = 0) :
      k ⬝ᵥ h *ᵥ k = k ⬝ᵥ traceFree h *ᵥ k := by
    rw [traceFree, q_sub, q_eta_smul, hk, mul_zero, sub_zero]
  refine ⟨(by unfold traceFree; abel), ht, hq, ?_⟩
  constructor
  · intro hz
    have hsym : (traceFree h)ᵀ = traceFree h := by
      simp [traceFree, transpose_sub, transpose_smul, hs, eta_transpose]
    obtain ⟨a, ha⟩ := (conformal_metric_same_null_cone_iff _ hsym).mp (fun k hk => by
      have hk' : minkowski k k = 0 := by
        simpa [eta, Fin.sum_univ_succ, minkowski, mul_assoc, add_assoc] using hk
      rw [← hq k hk', hz k hk'])
    have hzero : 4 * a = 0 := by
      rw [ha] at ht
      simp [minkowskiTrace, eta, Fin.sum_univ_succ] at ht
      linear_combination ht
    rw [ha, (mul_eq_zero.mp hzero).resolve_left (by norm_num), zero_smul]
  · intro hz k hk
    rw [hq k hk, hz]
    simp [dotProduct, mulVec]

section Integrals

open intervalIntegral

private theorem integral_even_radius (f : ℝ → ℝ) (hf : Continuous f)
    (a : ℝ) (ha : 0 ≤ a) :
    (∫ t in -a..a, f |t|) = 2 * ∫ t in 0..a, f t := by
  have hc : Continuous fun t => f |t| := hf.comp continuous_abs
  have hpos : (∫ t in 0..a, f |t|) = ∫ t in 0..a, f t :=
    integral_congr fun t ht => by
      rw [Set.uIcc_of_le ha] at ht
      rw [abs_of_nonneg ht.1]
  have hneg : (∫ t in -a..0, f |t|) = ∫ t in 0..a, f |t| := by
    simpa only [neg_zero, abs_neg] using
      (integral_comp_neg (fun t => f |t|) (a := 0) (b := a)).symm
  rw [← integral_add_adjacent_intervals (hc.intervalIntegrable (-a) 0)
      (hc.intervalIntegrable 0 a), hneg, hpos, two_mul]

private theorem integral_radius_power (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (∫ t in -a..a, (a - |t|)^n) = 2 * a^(n+1) / (n+1) := by
  have hi : (∫ t in 0..a, (a - t)^n) = a^(n+1) / (n+1) := by
    let F (x : ℝ) := -(a - x)^(n+1) / (n+1)
    have hF (x : ℝ) : HasDerivAt F ((a-x)^n) x := by
      have h := (((hasDerivAt_const x a).sub (hasDerivAt_id x)).pow (n+1)).neg.div_const
        ((n : ℝ) + 1)
      apply h.congr_deriv
      simp
      field_simp
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
      ((show Continuous (fun t : ℝ => (a - t)^n) by fun_prop).intervalIntegrable _ _)]
    simp [F, neg_div]
  rw [integral_even_radius (fun t => (a - t)^n) (by fun_prop) a ha, hi]
  ring

/-- Cross-sectional integration of the flat four-dimensional Alexandrov volume. -/
theorem alexandrov_diamond_flat_volume (τ : ℝ) (hτ : 0 ≤ τ) :
    (∫ t in (-τ / 2)..(τ / 2), (4 * Real.pi / 3) * (τ / 2 - |t|)^3) =
      (Real.pi / 24) * τ^4 := by
  rw [integral_const_mul, show -τ / 2 = -(τ / 2) by ring,
    integral_radius_power _ (by positivity)]
  norm_num
  ring

/-- The time moment and the moment of any one spatial coordinate, integrated
from their Euclidean ball cross sections. -/
theorem alexandrov_diamond_quadratic_moments (τ : ℝ) (hτ : 0 ≤ τ) :
    (∫ t in (-τ / 2)..(τ / 2), t^2 * ((4 * Real.pi / 3) * (τ / 2 - |t|)^3)) =
        (τ^2 / 60) * ((Real.pi / 24) * τ^4) ∧
    (∫ t in (-τ / 2)..(τ / 2), (4 * Real.pi / 15) * (τ / 2 - |t|)^5) =
        (τ^2 / 30) * ((Real.pi / 24) * τ^4) := by
  rw [show -τ / 2 = -(τ / 2) by ring]
  constructor
  · let a := τ / 2
    change (∫ t in -a..a, t^2 * ((4 * Real.pi / 3) * (a - |t|)^3)) = _
    have he : (∫ t in -a..a, t^2 * ((4 * Real.pi / 3) * (a - |t|)^3)) =
        ∫ t in -a..a, |t|^2 * ((4 * Real.pi / 3) * (a - |t|)^3) :=
      integral_congr fun t _ => by rw [sq_abs]
    rw [he]
    rw [integral_even_radius (fun t => t^2 * ((4 * Real.pi / 3) * (a - t)^3))
      (by fun_prop) a (by positivity)]
    let F (t : ℝ) := (4 * Real.pi / 3) *
      (a^3*t^3/3 - 3*a^2*t^4/4 + 3*a*t^5/5 - t^6/6)
    have hF (x : ℝ) : HasDerivAt F (x^2 * ((4 * Real.pi / 3) * (a-x)^3)) x := by
      convert ((((hasDerivAt_pow 3 x).const_mul (a^3)).div_const 3).sub
          (((hasDerivAt_pow 4 x).const_mul (3*a^2)).div_const 4) |>.add
          (((hasDerivAt_pow 5 x).const_mul (3*a)).div_const 5) |>.sub
          ((hasDerivAt_pow 6 x).div_const 6) |>.const_mul (4 * Real.pi / 3)) using 1
      ring
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
      ((show Continuous (fun t : ℝ => t^2 * ((4 * Real.pi / 3) * (a-t)^3)) by
        fun_prop).intervalIntegrable _ _)]
    dsimp [F, a]
    ring
  · rw [integral_const_mul, integral_radius_power _ (by positivity)]
    norm_num
    ring

/-- The quadratic Riemann-normal-coordinate density term on the fixed flat
diamond, after spatial cross-section integration. Mixed terms vanish by
reflection. This term alone is the bulk, before displacement of the boundary. -/
theorem alexandrov_diamond_bulk_ricci (τ : ℝ) (hτ : 0 ≤ τ)
    (A : Matrix (Fin 4) (Fin 4) ℝ) :
    (-(1/6 : ℝ)) * (∫ t in (-τ / 2)..(τ / 2),
      A 0 0 * (t^2 * ((4 * Real.pi / 3) * (τ / 2 - |t|)^3)) +
      (A 1 1 + A 2 2 + A 3 3) * ((4 * Real.pi / 15) * (τ / 2 - |t|)^5)) =
    ((Real.pi / 24) * τ^4) * τ^2 * (-A 0 0 / 120 - minkowskiTrace A / 180) := by
  have h₁ : Continuous fun t : ℝ => A 0 0 * (t^2 * ((4 * Real.pi / 3) * (τ / 2 - |t|)^3)) := by
    fun_prop
  have h₂ : Continuous fun t : ℝ =>
      (A 1 1 + A 2 2 + A 3 3) * ((4 * Real.pi / 15) * (τ / 2 - |t|)^5) := by
    fun_prop
  rw [integral_add (h₁.intervalIntegrable _ _) (h₂.intervalIntegrable _ _),
    integral_const_mul, integral_const_mul,
    (alexandrov_diamond_quadratic_moments τ hτ).1,
    (alexandrov_diamond_quadratic_moments τ hτ).2]
  simp [minkowskiTrace, eta, Fin.sum_univ_succ]
  ring

/-- The first-order radial response of the truncated midpoint-RNC null
equation. Here `E` is the sectional reading in a unit spatial direction and
`r > 0` is the radius before curvature is applied. -/
theorem alexandrov_diamond_boundary_radius (τ r E v : ℝ) (hr : 0 < r) :
    HasDerivAt (fun ε : ℝ => (r + ε * v)^2 * (1 - ε * (τ^2 * E / 12)) - r^2) 0 0 ↔
      v = τ^2 * E * r / 24 := by
  have h := ((((hasDerivAt_id (0 : ℝ)).mul_const v).const_add r).pow 2).mul
    ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub ((hasDerivAt_id (0 : ℝ)).mul_const (τ^2 * E / 12)))
  have hd : HasDerivAt (fun ε : ℝ => (r + ε * v)^2 * (1 - ε * (τ^2 * E / 12)) - r^2)
      (2 * r * v - r^2 * τ^2 * E / 12) 0 := by
    apply (h.sub_const (r^2)).congr_deriv
    norm_num
    ring
  constructor
  · intro hv
    have hz := hd.unique hv
    have hf : r * (v - τ^2 * E * r / 24) = 0 := by linear_combination hz / 2
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hr.ne')
  · intro hv
    rwa [show 2 * r * v - r^2 * τ^2 * E / 12 = 0 by rw [hv]; ring] at hd

/-- First variation of the flat-density cross-sectional volume as the null
radius moves. The three spatial axis readings integrate a quadratic angular
first variation exactly, since the spherical mean of `nᵢ nⱼ` is `δᵢⱼ / 3`. -/
theorem alexandrov_diamond_boundary_volume (τ : ℝ) (hτ : 0 ≤ τ)
    (E : Fin 3 → ℝ) :
    HasDerivAt (fun ε : ℝ => ∫ t in (-τ / 2)..(τ / 2),
        ∑ i : Fin 3, (4 * Real.pi / 9) *
          ((τ / 2 - |t|) * (1 + ε * (τ^2 * E i / 24)))^3)
      (((Real.pi / 24) * τ^4) * τ^2 * (∑ i, E i) / 24) 0 := by
  let c (ε : ℝ) (i : Fin 3) := (1 + ε * (τ^2 * E i / 24))^3 / 3
  have hc (i : Fin 3) :
      HasDerivAt (fun ε => c ε i) (τ^2 * E i / 24) 0 := by
    apply ((((hasDerivAt_id (0 : ℝ)).mul_const (τ^2 * E i / 24)).const_add 1).pow 3
      |>.div_const 3).congr_deriv
    norm_num
  have he (ε : ℝ) : (∫ t in (-τ / 2)..(τ / 2), ∑ i : Fin 3, (4 * Real.pi / 9) *
          ((τ / 2 - |t|) * (1 + ε * (τ^2 * E i / 24)))^3) =
      ((∑ i, c ε i) * ((Real.pi / 24) * τ^4)) := by
    rw [← alexandrov_diamond_flat_volume τ hτ, ← integral_const_mul]
    apply integral_congr
    intro t _
    simp only [Fin.sum_univ_three, c]
    ring
  simp_rw [he]
  have hd := ((hc 0).add (hc 1)).add (hc 2) |>.mul_const ((Real.pi / 24) * τ^4)
  simp only [Fin.sum_univ_three]
  apply hd.congr_deriv
  ring

end Integrals

/-- Trace-free Ricci projection of the 20-component algebraic tensor. -/
abbrev ricciPart (R : AlgebraicCurvature4) : TracelessRicci4 :=
  (curvature_ricci_split R).2.1

/-- Scalar contraction of the Ricci tensor. -/
abbrev scalarPart (R : AlgebraicCurvature4) : ℝ :=
  (curvature_ricci_split R).2.2

/-- Signed coefficient of the relative volume change per squared proper time
when the direction has Minkowski norm squared minus one. This is the sum of
the density and moving-boundary contributions. -/
def alexandrovO2Deficit (R : AlgebraicCurvature4) (u : Fin 4 → ℝ) : ℝ :=
  (u ⬝ᵥ ricci R *ᵥ u) / 30 + scalarPart R * minkowski u u / 180

/-- Bulk and moving-boundary contributions to the signed relative
second-order coefficient in the midpoint rest frame. The result concerns
the first variation of the truncated Riemann-normal-coordinate model. -/
theorem alexandrov_diamond_rnc_volume_coefficient (R : AlgebraicCurvature4)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    HasDerivAt (fun ε : ℝ =>
      (∫ t in (-τ / 2)..(τ / 2),
        ∑ i : Fin 3, (4 * Real.pi / 9) *
          ((τ / 2 - |t|) * (1 + ε * (τ^2 * R.val (.inl i) (.inl i) / 24)))^3) +
      ε * (-(1/6 : ℝ) * (∫ t in (-τ / 2)..(τ / 2),
        ricci R 0 0 * (t^2 * ((4 * Real.pi / 3) * (τ / 2 - |t|)^3)) +
        (ricci R 1 1 + ricci R 2 2 + ricci R 3 3) *
          ((4 * Real.pi / 15) * (τ / 2 - |t|)^5))))
      (((Real.pi / 24) * τ^4) * τ^2 * alexandrovO2Deficit R ![1, 0, 0, 0]) 0 := by
  have hb := alexandrov_diamond_boundary_volume τ hτ (fun i => R.val (.inl i) (.inl i))
  let bulk := -(1/6 : ℝ) * (∫ t in (-τ / 2)..(τ / 2),
    ricci R 0 0 * (t^2 * ((4 * Real.pi / 3) * (τ / 2 - |t|)^3)) +
    (ricci R 1 1 + ricci R 2 2 + ricci R 3 3) * ((4 * Real.pi / 15) * (τ / 2 - |t|)^5))
  have hd := hb.add ((hasDerivAt_id (0 : ℝ)).mul_const bulk)
  have hsum : (∑ i : Fin 3, R.val (.inl i) (.inl i)) = ricci R 0 0 := by
    simp [Fin.sum_univ_three, ricci, contractions, electric]
  have hscalar : minkowskiTrace (ricci R) = scalarPart R := rfl
  apply hd.congr_deriv
  dsimp only [bulk]
  rw [alexandrov_diamond_bulk_ricci τ hτ, hsum, hscalar]
  simp [alexandrovO2Deficit, minkowski, dotProduct, mulVec, Fin.sum_univ_succ]
  ring

private theorem ricci_parts (R : AlgebraicCurvature4) :
    ricci R = (ricciPart R).val + (scalarPart R / 4) • eta :=
  (sub_add_cancel _ _).symm

private theorem timelike_quadratic_zero (Q : Matrix (Fin 4) (Fin 4) ℝ) (hs : Qᵀ = Q)
    (h : ∀ u : Fin 4 → ℝ, minkowski u u = -1 → u ⬝ᵥ Q *ᵥ u = 0) : Q = 0 := by
  have eval (a b c d : ℝ) (ht : -(a*a) + b*b + c*c + d*d = -1) :=
    (q_entries Q hs a b c d).symm.trans (h ![a,b,c,d] (by simpa [minkowski] using ht))
  have h0 := eval 1 0 0 0 (by norm_num)
  have h1p := eval (5/3) (4/3) 0 0 (by norm_num)
  have h1m := eval (5/3) (-4/3) 0 0 (by norm_num)
  have h2p := eval (5/3) 0 (4/3) 0 (by norm_num)
  have h2m := eval (5/3) 0 (-4/3) 0 (by norm_num)
  have h3p := eval (5/3) 0 0 (4/3) (by norm_num)
  have h3m := eval (5/3) 0 0 (-4/3) (by norm_num)
  have d0 : Q 0 0 = 0 := by simpa using h0
  have d1 : Q 1 1 = 0 := by linear_combination (h1p+h1m)* (9/32) - d0*(25/16)
  have d2 : Q 2 2 = 0 := by linear_combination (h2p+h2m)* (9/32) - d0*(25/16)
  have d3 : Q 3 3 = 0 := by linear_combination (h3p+h3m)* (9/32) - d0*(25/16)
  have o1 : Q 0 1 = 0 := by linear_combination (h1p-h1m)*(9/80)
  have o2 : Q 0 2 = 0 := by linear_combination (h2p-h2m)*(9/80)
  have o3 : Q 0 3 = 0 := by linear_combination (h3p-h3m)*(9/80)
  have h12 := eval 3 2 2 0 (by norm_num)
  have h13 := eval 3 2 0 2 (by norm_num)
  have h23 := eval 3 0 2 2 (by norm_num)
  rw [d0, d1, d2, d3, o1, o2, o3] at h12 h13 h23
  have o12 : Q 1 2 = 0 := by linear_combination h12 / 8
  have o13 : Q 1 3 = 0 := by linear_combination h13 / 8
  have o23 : Q 2 3 = 0 := by linear_combination h23 / 8
  have ht (i j : Fin 4) : Q j i = Q i j := congrFun (congrFun hs i) j
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d0, d1, d2, d3, o1, o2, o3, o12, o13, o23,
      ht 0 1, ht 0 2, ht 0 3, ht 1 2, ht 1 3, ht 2 3]

/-- Every Ricci-flat algebraic curvature tensor gives zero volume coefficient
in all directions. -/
theorem alexandrov_o2_weyl_blind (W : Weyl4) (u : Fin 4 → ℝ) :
    alexandrovO2Deficit W.val u = 0 := by
  have h := LinearMap.mem_ker.mp W.property
  have hs : scalarPart W.val = 0 := by
    change lorentzTrace (ricci W.val) = 0
    rw [h, map_zero]
  simp [alexandrovO2Deficit, h, hs, dotProduct, mulVec]

/-- Timelike volume coefficients separate all nine trace-free Ricci components
and the scalar curvature. -/
theorem alexandrov_o2_reconstructs_ricci_iff (R : AlgebraicCurvature4) :
    (∀ u : Fin 4 → ℝ, minkowski u u = -1 → alexandrovO2Deficit R u = 0) ↔
      ricciPart R = 0 ∧ scalarPart R = 0 := by
  constructor
  · intro h
    let Q := ricci R - (-(scalarPart R / 6)) • eta
    have hs : Qᵀ = Q := by
      simp [Q, transpose_smul, eta_transpose,
        show (ricci R)ᵀ = ricci R from Matrix.ext fun i j => ricci_symm R j i]
    have hQ : Q = 0 := timelike_quadratic_zero Q hs fun u hu => by
      have he := h u hu
      unfold alexandrovO2Deficit at he
      dsimp [Q]
      rw [q_sub, q_eta_smul]
      linarith
    have hr : ricci R = (-(scalarPart R / 6)) • eta := sub_eq_zero.mp hQ
    have ht : scalarPart R = 0 := by
      have he : minkowskiTrace (ricci R) = scalarPart R := rfl
      rw [hr] at he
      simp [minkowskiTrace, eta, Fin.sum_univ_succ] at he
      linarith
    refine ⟨Subtype.ext ?_, ht⟩
    have he := ricci_parts R
    rw [hr, ht] at he
    simpa using he.symm
  · rintro ⟨hS, hr⟩ u _
    have hzero : ricci R = 0 := by simp [ricci_parts R, hS, hr]
    simp [alexandrovO2Deficit, hzero, hr, dotProduct, mulVec]

private theorem complexTide_entries (R : AlgebraicCurvature4) (r : FutureNullRay) :
    let T := fun a b => tidal R (nullGenerator r) (screenFrame r a) (screenFrame r b)
    complexTide R r = (T 0 0 : ℂ) - T 1 1 + (2 : ℂ) * Complex.I * T 0 1 := by
  dsimp only
  have hs := tidal_symm R (nullGenerator r) (screenFrame r 1) (screenFrame r 0)
  simp only [tidal, pairBilinear, wedge, screenFrame, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hs
  apply Complex.ext <;>
    simp only [tidal, complexTide, pairBilinear, wedge, screenFrame, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.re_sum, Complex.im_sum, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith

private theorem complexTide_split (R : AlgebraicCurvature4) (r : FutureNullRay) :
    complexTide R r = complexTide (curvature_ricci_split R).1.val r := by
  have h := null_tidal_ricci_invariance R r
  rw [complexTide_entries, complexTide_entries]
  dsimp only at h ⊢
  rw [(h 0 0).1, (h 1 1).1, (h 0 1).1]
  simp only [Fin.zero_ne_one, ite_false, zero_mul, zero_div, add_zero,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div]
  ring

/-- Unit timelike volume readings and the complex tides at five distinct null
rays jointly have trivial kernel on algebraic curvature. -/
theorem complete_curvature_reconstruction_volume_and_five_rays
    (rays : Fin 5 → FutureNullRay) (hr : Function.Injective rays) (R : AlgebraicCurvature4) :
    ((∀ u : Fin 4 → ℝ, minkowski u u = -1 → alexandrovO2Deficit R u = 0) ∧
      (∀ i : Fin 5, complexTide R (rays i) = 0)) ↔ R = 0 := by
  constructor
  · rintro ⟨hv, ht⟩
    obtain ⟨hs, hc⟩ := (alexandrov_o2_reconstructs_ricci_iff R).mp hv
    have hw := (weyl_null_screen_zero rays hr (curvature_ricci_split R).1).mp (by
      funext i
      exact (weylQuarticEquiv_eval _ _).trans ((complexTide_split R _).symm.trans (ht i)))
    apply curvature_ricci_split.injective
    rw [map_zero]
    exact Prod.ext hw (Prod.ext hs hc)
  · rintro rfl
    exact ⟨(alexandrov_o2_reconstructs_ricci_iff 0).mpr (by simp [ricciPart, scalarPart]),
      fun i => by simp [complexTide, pairBilinear]⟩

private def waveElectric : STF3 ℝ := ⟨!![1,0,0; 0,-1,0; 0,0,0], by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · norm_num [diagSum, Fin.sum_univ_three]⟩

private def waveMagnetic : STF3 ℝ := ⟨!![0,1,0; 1,0,0; 0,0,0], by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · norm_num [diagSum, Fin.sum_univ_three]⟩

/-- Polarized Weyl wave with electric entries (1,−1,0) and magnetic
entries M₀₁ = M₁₀ = 1 in the transverse plane. -/
def volumeBlindWave : Weyl4 :=
  weyl_electric_magnetic_equiv.symm (waveElectric, waveMagnetic)

/-- The polarized Ricci-flat wave has zero volume coefficient in every
direction and a nonzero complex tide at the finite ray 1. -/
theorem volume_blind_nonzero_weyl_witness :
    volumeBlindWave.val ≠ 0 ∧ (∀ u, alexandrovO2Deficit volumeBlindWave.val u = 0) ∧
      complexTide volumeBlindWave.val (some 1) ≠ 0 := by
  have ht : complexTide volumeBlindWave.val (some 1) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [complexTide, pairBilinear, wedge, pairLeft, pairRight, screenVector, nullGenerator,
      volumeBlindWave, waveElectric, waveMagnetic, weyl_electric_magnetic_equiv, fromEM,
      emBlock, Fintype.sum_sum_type, Fin.sum_univ_three, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im] at hr
  exact ⟨fun hz => ht (by simp [hz, complexTide, pairBilinear]),
    alexandrov_o2_weyl_blind volumeBlindWave, ht⟩

/-- The scalar curvature one tensor, with zero Weyl and trace-free Ricci parts. -/
def screenBlindScalar : AlgebraicCurvature4 :=
  curvature_ricci_split.symm (0, 0, 1)

/-- Scalar curvature contributes to the timelike volume coefficient while
leaving every trace-free null tide zero. -/
theorem screen_blind_nonzero_ricci_witness :
    screenBlindScalar ≠ 0 ∧ (curvature_ricci_split screenBlindScalar).1 = 0 ∧
    (∀ r : FutureNullRay, complexTide screenBlindScalar r = 0) ∧
      alexandrovO2Deficit screenBlindScalar ![1, 0, 0, 0] = -(1/72 : ℝ) := by
  have hs := curvature_ricci_split.apply_symm_apply (0, 0, 1)
  have hw : (curvature_ricci_split screenBlindScalar).1 = 0 := congrArg Prod.fst hs
  have hS : ricciPart screenBlindScalar = 0 := congrArg (fun x => x.2.1) hs
  have hr : scalarPart screenBlindScalar = 1 := congrArg (fun x => x.2.2) hs
  refine ⟨fun hz => (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa [scalarPart, hz] using hr.symm), hw, fun r => ?_, ?_⟩
  · rw [complexTide_split, hw]
    simp [complexTide, pairBilinear]
  · have h := ricci_parts screenBlindScalar
    rw [hS, hr, ZeroMemClass.coe_zero, zero_add] at h
    rw [alexandrovO2Deficit, h, q_eta_smul, hr]
    norm_num [minkowski]

/-- The volume coefficient at rest and the five complex screen readings can
be prescribed independently, even with the trace-free Ricci part fixed to zero. -/
theorem rest_volume_and_five_tides_surjective
    (rays : Fin 5 → FutureNullRay) (hr : Function.Injective rays)
    (v : ℝ) (tides : Fin 5 → ℂ) :
    ∃ R : AlgebraicCurvature4, ricciPart R = 0 ∧
      alexandrovO2Deficit R ![1, 0, 0, 0] = v ∧
      ∀ i, complexTide R (rays i) = tides i := by
  let W := (weyl_null_screen_five rays hr).symm tides
  let a := -72 * v
  let R := curvature_ricci_split.symm (W, 0, a)
  have hR : curvature_ricci_split R = (W, 0, a) := LinearEquiv.apply_symm_apply _ _
  have hS : ricciPart R = 0 := congrArg (fun x => x.2.1) hR
  have hscalar : scalarPart R = a := congrArg (fun x => x.2.2) hR
  have hs : curvature_ricci_split screenBlindScalar = (0, 0, 1) :=
    LinearEquiv.apply_symm_apply _ _
  have hRic : ricci R = (a / 4) • eta := by
    rw [ricci_parts R, hS, hscalar, ZeroMemClass.coe_zero, zero_add]
  have hRicScalar : ricci screenBlindScalar = (1 / 4 : ℝ) • eta := by
    rw [ricci_parts screenBlindScalar, show ricciPart screenBlindScalar = 0 from
      congrArg (fun x => x.2.1) hs, show scalarPart screenBlindScalar = 1 from
      congrArg (fun x => x.2.2) hs, ZeroMemClass.coe_zero, zero_add]
  refine ⟨R, hS, ?_, ?_⟩
  · have hvol := screen_blind_nonzero_ricci_witness.2.2.2
    have he : alexandrovO2Deficit R ![1, 0, 0, 0] =
        a * alexandrovO2Deficit screenBlindScalar ![1, 0, 0, 0] := by
      simp only [alexandrovO2Deficit, hRic, hRicScalar, hscalar,
        show scalarPart screenBlindScalar = 1 from congrArg (fun x => x.2.2) hs,
        q_eta_smul]
      ring
    rw [he, hvol]
    dsimp [a]
    ring
  · intro i
    rw [complexTide_split, congrArg Prod.fst hR]
    exact (weylQuarticEquiv_eval _ _).symm.trans
      (congrFun ((weyl_null_screen_five rays hr).apply_symm_apply tides) i)

end D5.S3.Geometry.Lorentz.CausalOrderWeylDeformation4D
