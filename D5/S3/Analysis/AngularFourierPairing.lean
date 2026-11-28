/- GID: D5/S3/Analysis/AngularFourierPairing
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-weak-boundary4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed Fourier pairings over an additional pair of angular variables. -/

import OmegaBuild.Commands
import D5.S3.Analysis.MixedFourierKernel
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
Omega original.

Mixed Fourier pairings over an additional pair of angular variables.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped FourierTransform

namespace Omega

/-- Group the first and second coordinates of a pair of ordered pairs. -/
def pairInterleave {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] :
    (X × A) × (X × A) ≃ᵐ (X × X) × (A × A) where
  toFun z := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  invFun z := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable (fun z : (X × A) × (X × A) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : (X × X) × (A × A) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
    fun_prop

theorem pairInterleave_apply {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (z : (X × A) × (X × A)) :
    pairInterleave z = ((z.1.1, z.2.1), (z.1.2, z.2.2)) := rfl

theorem pairInterleave_symm_apply {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (z : (X × X) × (A × A)) :
    pairInterleave.symm z = ((z.1.1, z.2.1), (z.1.2, z.2.2)) := rfl

theorem measurePreserving_pairInterleave {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (μ : Measure X) (σ : Measure A) [SFinite μ] [SFinite σ] :
    MeasurePreserving (pairInterleave (X := X) (A := A))
      ((μ.prod σ).prod (μ.prod σ)) ((μ.prod μ).prod (σ.prod σ)) := by
  have hswap : MeasurePreserving (MeasurableEquiv.prodComm : A × X ≃ᵐ X × A)
    (σ.prod μ) (μ.prod σ) := measurePreserving_swap
  have hfirst := measurePreserving_prodAssoc μ σ (μ.prod σ)
  have hsecond := (measurePreserving_prodAssoc σ μ σ).symm MeasurableEquiv.prodAssoc
  have hthird := hswap.prod (MeasurePreserving.id σ)
  have hfourth := measurePreserving_prodAssoc μ σ σ
  have hfifth := (measurePreserving_prodAssoc μ μ (σ.prod σ)).symm MeasurableEquiv.prodAssoc
  exact hfifth.comp (((MeasurePreserving.id μ).prod
    (hfourth.comp (hthird.comp hsecond))).comp hfirst)

/-- Fubini groups both angular variables outside both radial variables. -/
theorem integral_pairInterleave {X A V : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Measure X) (σ : Measure A)
    [SFinite μ] [SFinite σ] (H : (X × A) × (X × A) → V)
    (hH : Integrable H ((μ.prod σ).prod (μ.prod σ))) :
    (∫ z, H z ∂((μ.prod σ).prod (μ.prod σ))) =
      ∫ n : A × A, ∫ p : X × X, H ((p.1, n.1), (p.2, n.2)) ∂(μ.prod μ) ∂(σ.prod σ) := by
  let e : (X × A) × (X × A) ≃ᵐ (X × X) × (A × A) := pairInterleave
  have hmp := (measurePreserving_pairInterleave μ σ).symm e
  rw [← hmp.integral_comp e.symm.measurableEmbedding H]
  exact integral_prod_symm (H ∘ e.symm) (hmp.integrable_comp_of_integrable hH)

/-- The mixed transform in angular-frequency form, before the unitary normalization. -/
theorem mixedFourier_eq_iterated_exp (K : ℝ × ℝ → ℂ)
    (hK : Integrable K ((volume : Measure ℝ).prod volume)) (ξ η : ℝ) :
    mixedFourier K (ξ, η) =
      ∫ r : ℝ, ∫ s : ℝ,
        Complex.exp (-Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ) * r +
          Complex.I * ((2 * Real.pi * η : ℝ) : ℂ) * s) * K (r, s) := by
  let E : ℝ × ℝ → ℂ := fun p => Complex.exp
    (-Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ) * p.1 +
      Complex.I * ((2 * Real.pi * η : ℝ) : ℂ) * p.2)
  have hi : Integrable (fun p => E p * K p) (volume.prod volume) := by
    refine hK.norm.mono' (Continuous.aestronglyMeasurable (f := E) (by dsimp [E]; fun_prop)
      |>.mul hK.aestronglyMeasurable) ?_
    filter_upwards with p
    simp [E, Complex.norm_exp, Complex.mul_re, Complex.mul_im, Complex.add_re]
  rw [← integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards with p
  change star (Complex.exp (((2 * Real.pi * p.1 * ξ : ℝ) : ℂ) * Complex.I)) *
    Complex.exp (((2 * Real.pi * p.2 * η : ℝ) : ℂ) * Complex.I) * K p = E p * K p
  simp only [E, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

/-- An affine factor in the sum of two absolute coordinates can be absorbed
by half of an exponential decay rate. -/
theorem exp_sum_linear_le_separated {b c L : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (r s : ℝ) :
    c * Real.exp (-2 * b * (|r| + |s|)) * (1 + |r| + |s| + L) ≤
      c * (1 + L + b⁻¹) * Real.exp (-(b * |r|)) * Real.exp (-(b * |s|)) := by
  let u := |r| + |s|
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hE : 1 ≤ Real.exp (b * u) := Real.one_le_exp_iff.mpr (mul_nonneg hb.le hu)
  have hU : u ≤ b⁻¹ * Real.exp (b * u) := by
    rw [inv_mul_eq_div, le_div_iff₀ hb]
    linarith [Real.add_one_le_exp (b * u)]
  have hpoly : 1 + u + L ≤ (1 + L + b⁻¹) * Real.exp (b * u) := by
    rw [add_mul]
    linarith [mul_le_mul_of_nonneg_left hE (show 0 ≤ 1 + L by positivity)]
  calc
    _ = c * Real.exp (-2 * b * u) * (1 + u + L) := by dsimp [u]; ring
    _ ≤ c * Real.exp (-2 * b * u) * ((1 + L + b⁻¹) * Real.exp (b * u)) :=
      mul_le_mul_of_nonneg_left hpoly (mul_nonneg hc (Real.exp_pos _).le)
    _ = c * (1 + L + b⁻¹) * Real.exp (-2 * b * u + b * u) := by rw [Real.exp_add]; ring
    _ = _ := by
      rw [show -2 * b * u + b * u = -(b * |r|) + -(b * |s|) by dsimp [u]; ring,
        Real.exp_add]
      ring

/-- Integrability of pair kernels with an exponential bound and an affine factor in
the sum of the absolute radial coordinates. -/
theorem integrable_of_exponential_pair_bound {V : Type*} [NormedAddCommGroup V]
    {K : ℝ × ℝ → V} (hK : AEStronglyMeasurable K ((volume : Measure ℝ).prod volume))
    {c L b : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L) (hb : 0 < b)
    (he : Integrable (fun r : ℝ => Real.exp (-(b * |r|))))
    (h : ∀ p : ℝ × ℝ, ‖K p‖ ≤ c * Real.exp (-2 * b * (|p.1| + |p.2|)) *
      (1 + |p.1| + |p.2| + L)) :
    Integrable K ((volume : Measure ℝ).prod volume) :=
  ((he.const_mul (c * (1 + L + b⁻¹))).mul_prod he).mono' hK
    (.of_forall fun p => (h p).trans (exp_sum_linear_le_separated hb hc hL p.1 p.2))

/-- A continuously varying angular coefficient preserves boundedness and continuity
of a dilated Schwartz Fourier profile. -/
theorem bounded_continuous_separated_fourier {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (g : SchwartzMap ℝ ℂ) (a : A → ℂ) (ha : Continuous a) (k : ℂ) (b : ℝ) :
    Continuous (fun p : ℝ × A => k * (𝓕 g : SchwartzMap ℝ ℂ) (b * p.1) * a p.2) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℝ × A, ‖k * (𝓕 g : SchwartzMap ℝ ℂ) (b * p.1) * a p.2‖ ≤ B := by
  refine ⟨(continuous_const.mul ((𝓕 g : SchwartzMap ℝ ℂ).continuous.comp
    (continuous_const.mul continuous_fst))).mul (ha.comp continuous_snd), ?_⟩
  obtain ⟨A', hA'⟩ := (isCompact_univ.image ha).isBounded.exists_norm_le
  refine ⟨‖k‖ * SchwartzMap.seminorm ℝ 0 0 (𝓕 g) * max 0 A', by positivity, fun p => ?_⟩
  have hap : ‖a p.2‖ ≤ max 0 A' := (hA' _ ⟨p.2, trivial, rfl⟩).trans (le_max_right _ _)
  simp only [norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left
    ((𝓕 g : SchwartzMap ℝ ℂ).norm_le_seminorm (𝕜 := ℝ) (b * p.1)) (norm_nonneg _))
    hap (norm_nonneg _) (by positivity)

/-- Finite sums of continuous functions with uniform norm bounds retain both properties. -/
theorem continuous_bounded_listSum {X T : Type*} [TopologicalSpace X]
    (F : List T) (f : T → X → ℂ)
    (h : ∀ t, Continuous (f t) ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖f t x‖ ≤ B) :
    Continuous (fun x => (F.map fun t => f t x).sum) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖(F.map fun t => f t x).sum‖ ≤ B := by
  induction F with
  | nil => exact ⟨continuous_const, 0, le_rfl, fun x => by simp⟩
  | cons t F ih =>
    obtain ⟨ht, A, hA, ha⟩ := h t
    obtain ⟨hf, B, hB, hb⟩ := ih
    exact ⟨ht.add hf, A + B, add_nonneg hA hB,
      fun x => (norm_add_le _ _).trans (add_le_add (ha x) (hb x))⟩

/-- A square-integrable scalar function on a finite measure space has an
integrable absolute value with a constant term. -/
theorem integrable_one_add_abs_of_sq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : AEStronglyMeasurable f μ)
    (h : Integrable (fun x => (f x) ^ 2) μ) :
    Integrable (fun x => 1 + |f x|) μ := by
  apply ((integrable_const (2 : ℝ)).add h).mono' (aestronglyMeasurable_const.add hf.norm)
  filter_upwards with x
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ 1 + |f x| by positivity)]
  nlinarith [sq_nonneg (|f x| - 1 / 2), sq_abs (f x)]

/-- A bounded test on each spatial variable preserves integrability against a
kernel dominated by separate radial and angular envelopes. -/
theorem integrable_pairing_of_product_bound {A : Type*} [MeasurableSpace A]
    (σ : Measure A) [SFinite σ] (F : ℝ × A → ℂ)
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B) (hFb : ∀ p, ‖F p‖ ≤ B)
    (L : (ℝ × A) × (ℝ × A) → ℂ) (hL : Measurable L)
    (e : ℝ → ℝ) (he : Integrable e) (he₀ : ∀ r, 0 ≤ e r)
    (a : A × A → ℝ) (ha : Integrable a (σ.prod σ)) (ha₀ : ∀ n, 0 ≤ a n)
    {C : ℝ} (hC : 0 ≤ C)
    (hLb : ∀ᵐ p ∂(((volume : Measure ℝ).prod σ).prod (volume.prod σ)),
      ‖L p‖ ≤ C * (e p.1.1 * e p.2.1) * a (p.1.2, p.2.2)) :
    Integrable (fun p : (ℝ × A) × (ℝ × A) => star (F p.1) * L p * F p.2)
      (((volume : Measure ℝ).prod σ).prod (volume.prod σ)) := by
  have hg := ((he.mul_prod he).mul_prod ha).const_mul (B ^ 2 * C)
  have hmp := measurePreserving_pairInterleave (volume : Measure ℝ) σ
  apply (hmp.integrable_comp_of_integrable hg).mono'
  · exact ((Complex.continuous_conj.measurable.comp (hF.comp measurable_fst)).mul hL |>.mul
      (hF.comp measurable_snd)).aestronglyMeasurable
  · filter_upwards [hLb] with p hp
    change ‖star (F p.1) * L p * F p.2‖ ≤
      B ^ 2 * C * ((e p.1.1 * e p.2.1) * a (p.1.2, p.2.2))
    rw [norm_mul, norm_mul, norm_star]
    calc
      _ ≤ B * (C * (e p.1.1 * e p.2.1) * a (p.1.2, p.2.2)) * B :=
        mul_le_mul (mul_le_mul (hFb p.1) hp (norm_nonneg _) hB)
          (hFb p.2) (norm_nonneg _)
          (by positivity [he₀ p.1.1, he₀ p.2.1, ha₀ (p.1.2, p.2.2)])
      _ = _ := by ring

private theorem mixedFourier_pairing_scaled (K L : ℝ × ℝ → ℂ)
    (hK : Integrable K ((volume : Measure ℝ).prod volume))
    (f g : SchwartzMap ℝ ℂ) (F G : ℝ → ℂ) {b : ℝ} (hb : 0 < b)
    (hL : ∀ ξ η : ℝ, L (b * ξ, b * η) = (b : ℂ)⁻¹ * mixedFourier K (ξ, η))
    (hF : ∀ ξ : ℝ, F (b * ξ) = (Real.sqrt b : ℂ)⁻¹ * 𝓕 f ξ)
    (hG : ∀ η : ℝ, G (b * η) = (Real.sqrt b : ℂ)⁻¹ * 𝓕 g η) :
    (∫ p : ℝ × ℝ, star (F p.1) * L p * G p.2 ∂((volume : Measure ℝ).prod volume)) =
      ∫ p : ℝ × ℝ, star (f p.1) * K p * g p.2 ∂((volume : Measure ℝ).prod volume) := by
  let W : ℝ × ℝ → ℂ := fun p => star (F p.1) * L p * G p.2
  have hs : ((Real.sqrt b : ℝ) : ℂ) ^ 2 = (b : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hb.le]
  have hb₀ : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hscale : (b : ℂ) ^ 2 * (∫ p : ℝ × ℝ, W (b • p) ∂(volume.prod volume)) =
      ∫ p : ℝ × ℝ, W p ∂(volume.prod volume) := by
    have hd := Measure.integral_comp_smul_of_nonneg (volume : Measure (ℝ × ℝ))
      W b (hR := hb.le)
    simp only [Module.finrank_prod, Module.finrank_self] at hd
    rw [← Measure.volume_eq_prod, hd, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hb₀), one_mul]
  change (∫ p, W p ∂(volume.prod volume)) = _
  rw [← hscale, ← integral_const_mul, ← mixedFourier_pairing K hK f g]
  apply integral_congr_ae
  filter_upwards with p
  change (b : ℂ) ^ 2 * (star (F (b * p.1)) * L (b * p.1, b * p.2) * G (b * p.2)) = _
  rw [hF, hG, hL, star_mul]
  simp only [Complex.star_def, map_inv₀, Complex.conj_ofReal]
  have hc : (b : ℂ) ^ 2 * ((Real.sqrt b : ℂ)⁻¹ * (b : ℂ)⁻¹ * (Real.sqrt b : ℂ)⁻¹) = 1 := by
    rw [mul_right_comm ((Real.sqrt b : ℂ)⁻¹), ← pow_two, inv_pow, hs]
    field_simp
  calc
    _ = ((b : ℂ) ^ 2 * ((Real.sqrt b : ℂ)⁻¹ * (b : ℂ)⁻¹ * (Real.sqrt b : ℂ)⁻¹)) *
        ((starRingEnd ℂ) (𝓕 f p.1) * mixedFourier K p * 𝓕 g p.2) := by ring
    _ = _ := by rw [hc, one_mul]

/-- Two Schwartz tests preserve integrability of a kernel under multiplication. -/
theorem integrable_schwartz_kernel_pairing (K : ℝ × ℝ → ℂ)
    (hK : Integrable K ((volume : Measure ℝ).prod volume)) (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun p : ℝ × ℝ => star (f p.1) * K p * g p.2)
      ((volume : Measure ℝ).prod volume) := by
  let B := SchwartzMap.seminorm ℝ 0 0 f
  let C := SchwartzMap.seminorm ℝ 0 0 g
  refine (hK.norm.const_mul (B * C)).mono'
    ((((f.continuous.comp continuous_fst).star.aestronglyMeasurable).mul
      hK.aestronglyMeasurable).mul (g.continuous.comp continuous_snd).aestronglyMeasurable) ?_
  filter_upwards with p
  rw [norm_mul, norm_mul, norm_star]
  calc
    _ ≤ (B * ‖K p‖) * C :=
      mul_le_mul (mul_le_mul_of_nonneg_right (f.norm_le_seminorm (𝕜 := ℝ) p.1) (norm_nonneg _))
        (g.norm_le_seminorm (𝕜 := ℝ) p.2) (norm_nonneg _) (by dsimp [B]; positivity)
    _ = _ := by ring

/-- The pairing on two copies of frequency and angle space is the corresponding
position pairing after angular Fubini and mixed Fourier inversion. -/
theorem angular_mixedFourier_pairing {A : Type*} [MeasurableSpace A]
    (σ : Measure A) [SFinite σ] (f : A → SchwartzMap ℝ ℂ)
    (K L : A × A → ℝ × ℝ → ℂ) (F : ℝ × A → ℂ) {b : ℝ} (hb : 0 < b)
    (hK : ∀ᵐ n ∂σ.prod σ, Integrable (K n) ((volume : Measure ℝ).prod volume))
    (hL : ∀ n ξ η, L n (b * ξ, b * η) = (b : ℂ)⁻¹ * mixedFourier (K n) (ξ, η))
    (hF : ∀ n ξ, F (b * ξ, n) = (Real.sqrt b : ℂ)⁻¹ * 𝓕 (f n) ξ)
    (hi : Integrable (fun p : (ℝ × A) × (ℝ × A) =>
      star (F p.1) * L (p.1.2, p.2.2) (p.1.1, p.2.1) * F p.2)
      (((volume : Measure ℝ).prod σ).prod (volume.prod σ))) :
    (∫ p : (ℝ × A) × (ℝ × A), star (F p.1) * L (p.1.2, p.2.2) (p.1.1, p.2.1) * F p.2
       ∂(((volume : Measure ℝ).prod σ).prod (volume.prod σ))) =
      ∫ n : A × A, ∫ p : ℝ × ℝ, star (f n.1 p.1) * K n p * f n.2 p.2
        ∂((volume : Measure ℝ).prod volume) ∂(σ.prod σ) := by
  rw [integral_pairInterleave volume σ _ hi]
  apply integral_congr_ae
  filter_upwards [hK] with n hk
  exact mixedFourier_pairing_scaled (K n) (L n) hk (f n.1) (f n.2)
    (fun ξ => F (ξ, n.1)) (fun η => F (η, n.2)) hb (hL n) (hF n.1) (hF n.2)

end Omega
