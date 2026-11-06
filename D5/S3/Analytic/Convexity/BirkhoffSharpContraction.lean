/- GID: D5/S3/Analytic/Convexity/BirkhoffSharpContraction
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/BirkhoffSharpContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The sharp projective diameter and contraction coefficient of a positive rectangular matrix. -/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Lattice
import Mathlib.Topology.Order.IsLUB
import Mathlib.Tactic

/-!
# Sharp finite rectangular Birkhoff contraction

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors of the adapted upper estimates: The Tau Ceti contributors.
Released under Apache 2.0; full license: docs/reports/licenses/tauceti-birkhoff/LICENSE.txt.

The consumed scalar and residual-vector upper estimates are adapted from
TauCetiProject/TauCeti at afa08a3ed16fb167e35de371afb1eb03fbc5913a,
TauCeti/Analysis/SpecialFunctions/Log/BirkhoffCrossRatio.lean and
TauCeti/Data/Matrix/BirkhoffContraction.lean.
Modifications: independent finite universes, direct maximal cross ratio and square-root
coefficient, finite max/min distance, and strictly positive sharpness constructions.
Retire adapted estimates when equivalent statements enter the pinned host library.

The sharp lower constructions approximate boundary columns by positive vectors and
embed a balanced two-column minor into the positive orthant. Sharpness is a supremum
and least-coefficient statement; positive-pair attainment is not asserted.
-/

open Real Matrix Filter Set Topology

namespace D5.S3.Analytic.Convexity.BirkhoffSharpContraction

universe u v w

/-- Strict positivity in every coordinate. -/
def Positive {K : Type w} (x : K → ℝ) : Prop := ∀ k, 0 < x k

/-- Hilbert distance, written with the finite maximum and minimum of coordinate ratios. -/
noncomputable def distance {K : Type w} [Fintype K] (x y : K → ℝ) : ℝ :=
  log ((⨆ k, x k / y k) / (⨅ k, x k / y k))

/-- Maximal rectangular cross ratio. -/
noncomputable def theta {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (A : Matrix I J ℝ) : ℝ :=
  ⨆ p : I × I × J × J, A p.1 p.2.2.1 * A p.2.1 p.2.2.2 /
    (A p.1 p.2.2.2 * A p.2.1 p.2.2.1)

/-- The sharp nonnegative contraction coefficient. -/
noncomputable def kappa {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (A : Matrix I J ℝ) : ℝ := (sqrt (theta A) - 1) / (sqrt (theta A) + 1)

/-- All distances between images of strictly positive vectors. -/
def imageDistances {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (A : Matrix I J ℝ) : Set ℝ :=
  {r | ∃ x y : J → ℝ, Positive x ∧ Positive y ∧ distance (A *ᵥ x) (A *ᵥ y) = r}

/-- All nonnegative global Lipschitz coefficients on the intrinsic positive domain. -/
def coefficients {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (A : Matrix I J ℝ) : Set ℝ :=
  {c | 0 ≤ c ∧ ∀ x y : J → ℝ, Positive x → Positive y →
    distance (A *ᵥ x) (A *ᵥ y) ≤ c * distance x y}

private theorem distance_extrema {K : Type w} [Fintype K] [Nonempty K]
    (x y : K → ℝ) : ∃ a b : K,
    (∀ k, x k / y k ≤ x a / y a) ∧ (∀ k, x b / y b ≤ x k / y k) ∧
    distance x y = log ((x a / y a) / (x b / y b)) := by
  obtain ⟨a, ha⟩ := Finite.exists_max (fun k => x k / y k)
  obtain ⟨b, hb⟩ := Finite.exists_min (fun k => x k / y k)
  refine ⟨a, b, ha, hb, ?_⟩
  unfold distance
  congr 2
  · exact le_antisymm (ciSup_le ha) (le_ciSup (f := fun k => x k / y k) (Set.finite_range _).bddAbove a)
  · exact le_antisymm (ciInf_le (f := fun k => x k / y k) (Set.finite_range _).bddBelow b) (le_ciInf hb)

private theorem distance_nonneg {K : Type w} [Fintype K] [Nonempty K]
    {x y : K → ℝ} (hx : Positive x) (hy : Positive y) : 0 ≤ distance x y := by
  obtain ⟨a,b,ha,hb,hd⟩ := distance_extrema x y
  rw [hd]
  exact log_nonneg ((one_le_div (div_pos (hx b) (hy b))).2 (hb a))

private theorem cross_le_distance {K : Type w} [Fintype K] [Nonempty K]
    {x y : K → ℝ} (hx : Positive x) (hy : Positive y) (i k : K) :
    log (x i * y k / (y i * x k)) ≤ distance x y := by
  obtain ⟨a,b,ha,hb,hd⟩ := distance_extrema x y
  rw [hd, ← div_div_div_eq]
  exact log_le_log (div_pos (div_pos (hx i) (hy i)) (div_pos (hx k) (hy k)))
    (div_le_div₀ (div_pos (hx a) (hy a)).le (ha i) (div_pos (hx b) (hy b)) (hb k))

private theorem distance_le {K : Type w} [Fintype K] [Nonempty K]
    {x y : K → ℝ} {C : ℝ} (h : ∀ i k, log (x i * y k / (y i * x k)) ≤ C) :
    distance x y ≤ C := by
  obtain ⟨a,b,ha,hb,hd⟩ := distance_extrema x y
  rw [hd, div_div_div_eq]
  exact h a b

private theorem output_positive {I : Type u} {J : Type v} [Fintype J] [Nonempty J]
    {A : Matrix I J ℝ} (hA : ∀ i j, 0 < A i j) {x : J → ℝ} (hx : Positive x) :
    Positive (A *ᵥ x) := by
  intro i
  exact Finset.sum_pos (fun j _ => mul_pos (hA i j) (hx j)) Finset.univ_nonempty

private theorem theta_attained {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (A : Matrix I J ℝ) :
    ∃ i k j l, theta A = A i j * A k l / (A i l * A k j) := by
  obtain ⟨p,hp⟩ := Finite.exists_max (fun p : I × I × J × J =>
    A p.1 p.2.2.1 * A p.2.1 p.2.2.2 / (A p.1 p.2.2.2 * A p.2.1 p.2.2.1))
  exact ⟨p.1,p.2.1,p.2.2.1,p.2.2.2,
    le_antisymm (ciSup_le hp) (le_ciSup (f := fun p : I × I × J × J => A p.1 p.2.2.1 * A p.2.1 p.2.2.2 / (A p.1 p.2.2.2 * A p.2.1 p.2.2.1)) (Set.finite_range _).bddAbove p)⟩

private theorem entry_cross_le {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (A : Matrix I J ℝ) (i k : I) (j l : J) :
    A i j * A k l / (A i l * A k j) ≤ theta A :=
  le_ciSup (f := fun p : I × I × J × J => A p.1 p.2.2.1 * A p.2.1 p.2.2.2 / (A p.1 p.2.2.2 * A p.2.1 p.2.2.1)) (Set.finite_range _).bddAbove (i,k,j,l)

private theorem theta_one_le {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] {A : Matrix I J ℝ} (hA : ∀ i j, 0 < A i j) :
    1 ≤ theta A := by
  let i := Classical.choice (inferInstance : Nonempty I)
  let j := Classical.choice (inferInstance : Nonempty J)
  simpa [div_self (mul_pos (hA i j) (hA i j)).ne'] using entry_cross_le A i i j j

private theorem kappa_range {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] {A : Matrix I J ℝ} (hA : ∀ i j, 0 < A i j) :
    0 ≤ kappa A ∧ kappa A < 1 := by
  have hL : 1 ≤ sqrt (theta A) := Real.one_le_sqrt.mpr (theta_one_le hA)
  unfold kappa
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · exact (div_lt_one (by linarith)).2 (by linarith)


/-- For `1 ≤ l` and `0 ≤ σ`, `log ((1 + l * exp σ) / (l + exp σ)) ≤ (l - 1) / (l + 1) * σ`.
Both sides vanish at `σ = 0`, and the derivative of the left side is at most `(l - 1) / (l + 1)`. -/
private theorem log_one_add_mul_exp_div_add_exp_le {l σ : ℝ} (hl : 1 ≤ l) (hσ : 0 ≤ σ) :
    log ((1 + l * exp σ) / (l + exp σ)) ≤ (l - 1) / (l + 1) * σ := by
  have hpos₁ : ∀ t, 0 < 1 + l * exp t := fun t ↦ by positivity
  have hpos₂ : ∀ t, 0 < l + exp t := fun t ↦ by positivity
  have hderiv : ∀ t, HasDerivAt
      (fun t ↦ (l - 1) / (l + 1) * t - (log (1 + l * exp t) - log (l + exp t)))
      ((l - 1) / (l + 1) - (l * exp t / (1 + l * exp t) - exp t / (l + exp t))) t := fun t ↦ by
    have := ((hasDerivAt_id t).const_mul ((l - 1) / (l + 1))).sub
      ((((hasDerivAt_exp t).const_mul l).const_add 1).log (hpos₁ t).ne' |>.sub
        (((hasDerivAt_exp t).const_add l).log (hpos₂ t).ne'))
    exact this.congr_deriv (by ring)
  have hmono := monotone_of_hasDerivAt_nonneg hderiv fun t ↦ by
    rw [Pi.zero_apply, sub_nonneg, div_sub_div _ _ (hpos₁ t).ne' (hpos₂ t).ne',
      div_le_div_iff₀ (mul_pos (hpos₁ t) (hpos₂ t)) (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hl) (zero_le_one.trans hl))
      (sq_nonneg (exp t - 1))]
  have := hmono hσ
  simp only [mul_zero, exp_zero, mul_one, add_comm (1 : ℝ) l, sub_self] at this
  rw [log_div (hpos₁ σ).ne' (hpos₂ σ).ne']
  linarith

/-- The two-dimensional polynomial inequality behind Birkhoff's theorem. Let `1 ≤ s` and
`1 ≤ l`, and let `α, β, α', β'` be positive with `α * β' ≤ l ^ 2 * (β * α')`. Then the cross ratio
of `(s ^ 2 * α + β, α + β)` and `(s ^ 2 * α' + β', α' + β')` is at most
`((1 + l * s) / (l + s)) ^ 2`. -/
private theorem birkhoff_cross_ratio_le {α β α' β' s l : ℝ} (hα : 0 < α) (hβ : 0 < β) (hα' : 0 < α')
    (hβ' : 0 < β') (hs : 1 ≤ s) (hl : 1 ≤ l) (h : α * β' ≤ l ^ 2 * (β * α')) :
    (s ^ 2 * α + β) * (α' + β') * (l + s) ^ 2 ≤
      (1 + l * s) ^ 2 * ((α + β) * (s ^ 2 * α' + β')) := by
  have hs2 : 0 ≤ s ^ 2 - 1 := by nlinarith
  have hl2 : 0 ≤ l ^ 2 - 1 := by nlinarith
  -- increasing the ratio `α / β` up to `l ^ 2 * α' / β'` only increases the left side
  have h₁ : (s ^ 2 * α + β) * (l ^ 2 * α' + β') ≤ (s ^ 2 * (l ^ 2 * α') + β') * (α + β) := by
    nlinarith [mul_le_mul_of_nonneg_left h hs2]
  -- at the extreme ratio the difference is `(l ^ 2 - 1) * (s ^ 2 - 1) * (l * s * α' - β') ^ 2`
  have h₂ : (s ^ 2 * (l ^ 2 * α') + β') * (α' + β') * (l + s) ^ 2 ≤
      (1 + l * s) ^ 2 * ((l ^ 2 * α' + β') * (s ^ 2 * α' + β')) := by
    nlinarith [mul_nonneg (mul_nonneg hl2 hs2) (sq_nonneg (l * s * α' - β'))]
  refine le_of_mul_le_mul_right ?_ (by positivity : 0 < l ^ 2 * α' + β')
  nlinarith [mul_le_mul_of_nonneg_right h₁ (by positivity : 0 ≤ (α' + β') * (l + s) ^ 2),
    mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ α + β)]

/-- The two-dimensional form of Birkhoff's theorem: for `R ≥ 1`, `l ≥ 1` and positive
`α, β, α', β'` with `α * β' ≤ l ^ 2 * (β * α')`, the logarithmic cross ratio of
`(R * α + β, α + β)` and `(R * α' + β', α' + β')` is at most `(l - 1) / (l + 1) * log R`. -/
private theorem log_birkhoff_cross_ratio_le {α β α' β' R l : ℝ} (hα : 0 < α) (hβ : 0 < β) (hα' : 0 < α')
    (hβ' : 0 < β') (hR : 1 ≤ R) (hl : 1 ≤ l) (h : α * β' ≤ l ^ 2 * (β * α')) :
    log ((R * α + β) * (α' + β') / ((α + β) * (R * α' + β'))) ≤
      (l - 1) / (l + 1) * log R := by
  set s := exp (log R / 2)
  have hs : 1 ≤ s := one_le_exp (by linarith [log_nonneg hR])
  have hsR : s ^ 2 = R := by
    rw [sq, ← exp_add, add_halves, exp_log (by linarith)]
  have hden : 0 < (α + β) * (R * α' + β') := by
    have : 0 < R := by linarith
    positivity
  have hnum : 0 < (R * α + β) * (α' + β') := by
    have : 0 < R := by linarith
    positivity
  have _hls : 0 < l + s := by linarith
  have hle : (R * α + β) * (α' + β') / ((α + β) * (R * α' + β')) ≤
      ((1 + l * s) / (l + s)) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ hden (by positivity), ← hsR]
    nlinarith [birkhoff_cross_ratio_le hα hβ hα' hβ' hs hl h]
  calc log ((R * α + β) * (α' + β') / ((α + β) * (R * α' + β')))
      ≤ log (((1 + l * s) / (l + s)) ^ 2) := log_le_log (div_pos hnum hden) hle
    _ = 2 * log ((1 + l * s) / (l + s)) := by rw [log_pow]; norm_num
    _ ≤ 2 * ((l - 1) / (l + 1) * (log R / 2)) := by
        gcongr
        exact log_one_add_mul_exp_div_add_exp_le hl (by linarith [log_nonneg hR])
    _ = (l - 1) / (l + 1) * log R := by ring



section MatrixBounds
variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]
  [Nonempty I] [Nonempty J] {A : Matrix I J ℝ}

private theorem mulVec_cross_le (hA : ∀ i j, 0 < A i j) {u v : J → ℝ}
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) (i k : I) :
    (A *ᵥ u) i * (A *ᵥ v) k ≤ theta A * ((A *ᵥ v) i * (A *ᵥ u) k) := by
  have hcross : ∀ j l, A i j * A k l ≤ theta A * (A i l * A k j) :=
    fun j l => (div_le_iff₀ (mul_pos (hA i l) (hA k j))).1 (entry_cross_le A i k j l)
  simp only [mulVec, dotProduct]
  calc (∑ j, A i j * u j) * ∑ l, A k l * v l
      = ∑ j, ∑ l, (A i j * A k l) * (u j * v l) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ j, ∑ l, theta A * (A i l * A k j) * (u j * v l) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_right (hcross j l) (mul_nonneg (hu j) (hv l))
    _ = theta A * ((∑ l, A i l * v l) * ∑ j, A k j * u j) := by
        rw [Finset.sum_mul_sum, Finset.sum_comm, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring

private theorem image_upper (hA : ∀ i j, 0 < A i j) {x y : J → ℝ}
    (hx : Positive x) (hy : Positive y) :
    distance (A *ᵥ x) (A *ᵥ y) ≤ log (theta A) := by
  refine distance_le fun i k => ?_
  apply log_le_log
    (div_pos (mul_pos (output_positive hA hx i) (output_positive hA hy k))
      (mul_pos (output_positive hA hy i) (output_positive hA hx k)))
  exact (div_le_iff₀ (mul_pos (output_positive hA hy i) (output_positive hA hx k))).2
    (mulVec_cross_le hA (fun j => (hx j).le) (fun j => (hy j).le) i k)

private theorem log_cross_mulVec_le (hA : ∀ i j, 0 < A i j) {x y : J → ℝ}
    (hy : Positive y) {m M : ℝ} (hm : 0 < m) (hmx : ∀ j, m * y j ≤ x j)
    (hxM : ∀ j, x j ≤ M * y j) {j₁ j₂ : J} (hj₁ : m * y j₁ < x j₁)
    (hj₂ : x j₂ < M * y j₂) (i k : I) :
    log ((A *ᵥ x) i * (A *ᵥ y) k / ((A *ᵥ y) i * (A *ᵥ x) k)) ≤
      kappa A * log (M / m) := by
  have hmM : m < M := lt_of_mul_lt_mul_right (hj₁.trans_le (hxM j₁)) (hy j₁).le
  have hu : ∀ j, 0 ≤ (x - m • y) j := fun j => by simpa using hmx j
  have hv : ∀ j, 0 ≤ (M • y - x) j := fun j => by simpa using hxM j
  have hpos : ∀ {w : J → ℝ}, (∀ j, 0 ≤ w j) → ∀ {j₀}, 0 < w j₀ →
      ∀ i, 0 < (A *ᵥ w) i :=
    fun hw j₀ hj₀ i => Finset.sum_pos' (fun j _ => mul_nonneg (hA i j).le (hw j))
      ⟨j₀, Finset.mem_univ j₀, mul_pos (hA i j₀) hj₀⟩
  have hα := hpos hu (j₀ := j₁) (by simpa using hj₁)
  have hβ := hpos hv (j₀ := j₂) (by simpa using hj₂)
  have hcross := mulVec_cross_le hA hu hv i k
  have hΘ : 0 ≤ theta A := le_trans zero_le_one (theta_one_le hA)
  rw [← Real.sq_sqrt hΘ] at hcross
  have key := log_birkhoff_cross_ratio_le (R := M / m) (hα i) (hβ i) (hα k) (hβ k)
    ((one_le_div hm).2 hmM.le) (Real.one_le_sqrt.mpr (theta_one_le hA)) hcross
  have hcongr : ∀ i, M / m * (A *ᵥ (x - m • y)) i + (A *ᵥ (M • y - x)) i =
      (M - m) / m * (A *ᵥ x) i ∧
      (A *ᵥ (x - m • y)) i + (A *ᵥ (M • y - x)) i = (M - m) * (A *ᵥ y) i :=
    fun i => by
      simp only [mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      constructor
      · field_simp
        ring
      · ring
  rw [(hcongr i).1, (hcongr i).2, (hcongr k).1, (hcongr k).2] at key
  have hc : (M - m) / m * (M - m) ≠ 0 := by
    have := sub_pos.2 hmM
    positivity
  unfold kappa
  convert key using 2
  rw [← mul_div_mul_left ((A *ᵥ x) i * (A *ᵥ y) k)
    ((A *ᵥ y) i * (A *ᵥ x) k) hc]
  ring

private theorem contraction_upper (hA : ∀ i j, 0 < A i j) {x y : J → ℝ}
    (hx : Positive x) (hy : Positive y) :
    distance (A *ᵥ x) (A *ᵥ y) ≤ kappa A * distance x y := by
  obtain ⟨a,b,ha,hb,hd⟩ := distance_extrema x y
  let M := x a / y a
  let m := x b / y b
  have hm : 0 < m := div_pos (hx b) (hy b)
  have hmM : m ≤ M := hb a
  rcases hmM.eq_or_lt with heq | hlt
  · have hxy : x = m • y := funext fun j => by
      have hr := le_antisymm ((ha j).trans heq.ge) (hb j)
      rw [Pi.smul_apply, smul_eq_mul, ← hr, div_mul_cancel₀ _ (hy j).ne']
    apply distance_le
    intro i k
    rw [hxy, mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    have he : m * (A *ᵥ y) i * (A *ᵥ y) k /
        ((A *ᵥ y) i * (m * (A *ᵥ y) k)) = 1 := by
      field_simp [(output_positive hA hy i).ne', (output_positive hA hy k).ne', hm.ne']
      <;> ring
    rw [he, log_one]
    simpa only [hxy] using mul_nonneg (kappa_range hA).1 (distance_nonneg hx hy)
  · rw [hd]
    exact distance_le fun i k => log_cross_mulVec_le hA hy hm
      (fun j => (le_div_iff₀ (hy j)).1 (hb j))
      (fun j => (div_le_iff₀ (hy j)).1 (ha j))
      ((lt_div_iff₀ (hy a)).1 hlt) ((div_lt_iff₀ (hy b)).1 hlt) i k

end MatrixBounds

private theorem positive_parameter {f : ℝ → ℝ} (hf : ContinuousAt f 0)
    {b : ℝ} (hb : b < f 0) : ∃ η : ℝ, 0 < η ∧ b < f η := by
  have he : ∀ᶠ η in 𝓝[>] (0 : ℝ), b < f η :=
    (hf.tendsto.eventually (eventually_gt_nhds hb)).filter_mono nhdsWithin_le_nhds
  have hp : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η := self_mem_nhdsWithin
  exact (hp.and he).exists

section Sharpness
variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]
  [Nonempty I] [Nonempty J] {A : Matrix I J ℝ}

/-- Strictly positive images approach the maximal minor's logarithm. -/
private theorem lower_diameter (hA : ∀ i j, 0 < A i j) {ε : ℝ} (hε : 0 < ε) :
    ∃ x y : J → ℝ, Positive x ∧ Positive y ∧
      log (theta A) - ε < distance (A *ᵥ x) (A *ᵥ y) := by
  classical
  obtain ⟨i,k,j,l,hm⟩ := theta_attained A
  let R : I → ℝ := fun p => ∑ s, A p s
  let H : ℝ → ℝ := fun η =>
    log (((A i j + η * R i) * (A k l + η * R k)) /
      ((A i l + η * R i) * (A k j + η * R k)))
  have hij := hA i j
  have hil := hA i l
  have hkj := hA k j
  have hkl := hA k l
  have hcont : ContinuousAt H 0 := by
    dsimp [H]
    fun_prop (disch := (simp only [zero_mul, add_zero]; positivity))
  have hzero : H 0 = log (theta A) := by simp [H,hm]
  obtain ⟨η,hη,hH⟩ := positive_parameter hcont (b := log (theta A) - ε)
    (by rw [hzero]; linarith)
  let x : J → ℝ := fun s => (if s = j then 1 else 0) + η
  let y : J → ℝ := fun s => (if s = l then 1 else 0) + η
  have hx : Positive x := fun s => by dsimp [x]; split_ifs <;> linarith
  have hy : Positive y := fun s => by dsimp [y]; split_ifs <;> linarith
  have hact (p : I) (r : J) :
      (A *ᵥ (fun s => (if s = r then 1 else 0) + η)) p = A p r + η * R p := by
    simp [mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum, R, mul_comm]
  refine ⟨x,y,hx,hy,hH.trans_le ?_⟩
  have hc := cross_le_distance (output_positive hA hx) (output_positive hA hy) i k
  simpa only [x,y,hact,H] using hc

end Sharpness

private noncomputable def phi (L t : ℝ) : ℝ := log ((1 + L * exp t) / (L + exp t))

private theorem phi_deriv {L : ℝ} (hL : 0 < L) :
    HasDerivAt (phi L) ((L - 1) / (L + 1)) 0 := by
  have h1 (t : ℝ) : 0 < 1 + L * exp t := by positivity
  have h2 (t : ℝ) : 0 < L + exp t := by positivity
  have he : phi L = fun t => log (1 + L * exp t) - log (L + exp t) := by
    funext t
    exact log_div (h1 t).ne' (h2 t).ne'
  rw [he]
  have hd := ((((hasDerivAt_exp (0 : ℝ)).const_mul L).const_add 1).log (h1 0).ne').sub
    (((hasDerivAt_exp (0 : ℝ)).const_add L).log (h2 0).ne')
  convert hd using 1 <;> simp only [exp_zero,mul_one] <;> ring

private theorem phi_secant {L c : ℝ} (hL : 0 < L) (hc : c < (L - 1) / (L + 1)) :
    ∃ t : ℝ, 0 < t ∧ c * t < phi L t := by
  have hzero : phi L 0 = 0 := by simp [phi, add_comm, hL.ne']
  have ht := (phi_deriv hL).tendsto_slope_zero_right
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), c < t⁻¹ * phi L t := by
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul] using
      ht.eventually (eventually_gt_nhds hc)
  have hp : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,hct⟩ := (hp.and he).exists
  refine ⟨t,ht,?_⟩
  have hh := (mul_lt_mul_iff_left₀ ht).2 hct
  simpa [mul_assoc, ht.ne', mul_comm, mul_left_comm] using hh


section CoefficientSharpness
variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]
  [Nonempty I] [Nonempty J] {A : Matrix I J ℝ}

/-- Every smaller nonnegative coefficient is defeated by genuine positive inputs. -/
private theorem lower_coefficient (hA : ∀ i j, 0 < A i j) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : c < kappa A) :
    ∃ x y : J → ℝ, Positive x ∧ Positive y ∧
      c * distance x y < distance (A *ᵥ x) (A *ᵥ y) := by
  classical
  obtain ⟨i,k,j,l,hm⟩ := theta_attained A
  have hΘ : 1 < theta A := by
    by_contra! hh
    have he : theta A = 1 := le_antisymm hh (theta_one_le hA)
    have hz : kappa A = 0 := by simp [kappa,he]
    linarith
  have hjl : j ≠ l := by
    intro he
    have heq : theta A = 1 := by rw [hm,he]; exact div_self (mul_pos (hA i l) (hA k l)).ne'
    linarith
  let L := sqrt (theta A)
  have hL1 : 1 ≤ L := Real.one_le_sqrt.mpr (theta_one_le hA)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLsq : L ^ 2 = theta A := Real.sq_sqrt (by linarith)
  let q := A i l * L / A i j
  have hq : 0 < q := div_pos (mul_pos (hA i l) hL) (hA i j)
  have hbal₁ : A i j * q = A i l * L := by
    dsimp [q]
    field_simp [(hA i j).ne']
  have hminor : A i j * A k l = L ^ 2 * (A i l * A k j) := by
    rw [hLsq]
    exact (div_eq_iff (mul_pos (hA i l) (hA k j)).ne').1 hm.symm
  have hbal₂ : A k j * q * L = A k l := by
    apply mul_left_cancel₀ (hA i j).ne'
    calc A i j * (A k j * q * L) = (A i j * q) * (A k j * L) := by ring
      _ = (A i l * L) * (A k j * L) := by rw [hbal₁]
      _ = L ^ 2 * (A i l * A k j) := by ring
      _ = A i j * A k l := hminor.symm
  obtain ⟨t,ht,hct⟩ := phi_secant hL (show c < (L - 1) / (L + 1) from hc)
  let w : ℝ → ℝ → J → ℝ := fun η t s =>
    if s = j then q * exp t else if s = l then 1 else η
  have hw (η t : ℝ) (hη : 0 < η) : Positive (w η t) := by
    intro s
    dsimp [w]
    split_ifs <;> positivity
  have hratio (η : ℝ) (hη : 0 < η) (s : J) :
      w η t s / w η 0 s = if s = j then exp t else 1 := by
    by_cases hs : s = j
    · simp [w,hs,hq.ne']
    · by_cases hs' : s = l <;> simp [w,hs,hs',hη.ne',hjl.symm]
  have hdist (η : ℝ) (hη : 0 < η) : distance (w η t) (w η 0) = t := by
    have hmax : (⨆ s, w η t s / w η 0 s) = exp t := by
      apply le_antisymm
      · apply ciSup_le
        intro s
        rw [hratio η hη s]
        split_ifs
        · exact le_rfl
        · exact one_le_exp ht.le
      · have hh := le_ciSup (f := fun s => w η t s / w η 0 s)
          (Set.finite_range _).bddAbove j
        simpa [hratio η hη] using hh
    have hmin : (⨅ s, w η t s / w η 0 s) = 1 := by
      apply le_antisymm
      · have hh := ciInf_le (f := fun s => w η t s / w η 0 s)
          (Set.finite_range _).bddBelow l
        simpa [hratio η hη,hjl.symm] using hh
      · apply le_ciInf
        intro s
        rw [hratio η hη s]
        split_ifs
        · exact one_le_exp ht.le
        · exact le_rfl
    simp only [distance,hmax,hmin,div_one,log_exp]
  let Z : I → ℝ → ℝ → ℝ := fun p η t => (A *ᵥ w η t) p
  have hZzero (p : I) (t : ℝ) : Z p 0 t = A p j * q * exp t + A p l := by
    change (∑ s, A p s * w 0 t s) = _
    calc (∑ s, A p s * w 0 t s)
        = ∑ s, ((if s = j then A p j * q * exp t else 0) +
          (if s = l then A p l else 0)) := by
            apply Finset.sum_congr rfl
            intro s hs
            by_cases hs' : s = j
            · subst s; simp [w,hjl,mul_assoc]
            · by_cases hs'' : s = l
              · subst s; simp [w,hjl.symm]
              · simp [w,hs',hs'']
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hZcont (p : I) (s : ℝ) : ContinuousAt (fun η => Z p η s) 0 := by
    change ContinuousAt (fun η => ∑ r, A p r * w η s r) 0
    apply Continuous.continuousAt
    apply continuous_finsetSum
    intro r hr
    dsimp [w]
    split_ifs <;> fun_prop
  have hZpos (p : I) (s : ℝ) : 0 < Z p 0 s := by
    rw [hZzero]
    exact add_pos (mul_pos (mul_pos (hA p j) hq) (exp_pos s)) (hA p l)
  let G : ℝ → ℝ := fun η => log (Z i η t * Z k η 0 / (Z i η 0 * Z k η t))
  have hGc : ContinuousAt G 0 := by
    exact (((hZcont i t).mul (hZcont k 0)).div
      ((hZcont i 0).mul (hZcont k t)) (mul_pos (hZpos i 0) (hZpos k t)).ne').log
      (div_pos (mul_pos (hZpos i t) (hZpos k 0))
        (mul_pos (hZpos i 0) (hZpos k t))).ne'
  have hGzero : G 0 = phi L t := by
    dsimp only [G,phi]
    simp only [hZzero,exp_zero,mul_one]
    rw [hbal₁, ← hbal₂]
    apply congrArg log
    have hb := (hA i l).ne'
    have hgq := (mul_pos (hA k j) hq).ne'
    have hLp : L + 1 ≠ 0 := by positivity
    have hLe : L + exp t ≠ 0 := by positivity
    field_simp [(hA i j).ne', (hA i l).ne', (hA k j).ne', (hA k l).ne',
      hL.ne', hq.ne',hLp,hLe]
    <;> ring
  obtain ⟨η,hη,hηG⟩ := positive_parameter hGc (b := c * t) (by rw [hGzero]; exact hct)
  refine ⟨w η t,w η 0,hw η t hη,hw η 0 hη,?_⟩
  rw [hdist η hη]
  exact hηG.trans_le (cross_le_distance (output_positive hA (hw η t hη))
    (output_positive hA (hw η 0 hη)) i k)

/-- The image diameter and nonnegative global contraction coefficient are sharp,
for any finite nonempty rectangular positive real matrix. -/
theorem sharp_contraction (hA : ∀ i j, 0 < A i j) :
    (∀ x : J → ℝ, Positive x → Positive (A *ᵥ x)) ∧
    IsLUB (imageDistances A) (log (theta A)) ∧
    sSup (imageDistances A) = log (theta A) ∧
    IsLeast (coefficients A) (kappa A) ∧ 0 ≤ kappa A ∧ kappa A < 1 := by
  have hlu : IsLUB (imageDistances A) (log (theta A)) := by
    constructor
    · rintro r ⟨x,y,hx,hy,rfl⟩
      exact image_upper hA hx hy
    · intro b hb
      by_contra! hh
      obtain ⟨x,y,hx,hy,hxy⟩ := lower_diameter hA (sub_pos.mpr hh)
      have hup := hb (show distance (A *ᵥ x) (A *ᵥ y) ∈ imageDistances A from
        ⟨x,y,hx,hy,rfl⟩)
      linarith
  have hne : (imageDistances A).Nonempty := by
    exact ⟨distance (A *ᵥ (fun _ => 1)) (A *ᵥ (fun _ => 1)),
      (fun _ => 1),(fun _ => 1),(fun _ => zero_lt_one),(fun _ => zero_lt_one),rfl⟩
  refine ⟨fun x hx => output_positive hA hx,hlu,hlu.csSup_eq hne,?_,kappa_range hA⟩
  constructor
  · exact ⟨(kappa_range hA).1, fun x y hx hy => contraction_upper hA hx hy⟩
  · intro c hc
    by_contra! hh
    obtain ⟨x,y,hx,hy,hxy⟩ := lower_coefficient hA hc.1 hh
    exact (not_lt_of_ge (hc.2 x y hx hy)) hxy

end CoefficientSharpness
end D5.S3.Analytic.Convexity.BirkhoffSharpContraction
