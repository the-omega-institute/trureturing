/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelDyadicCoercivity
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelDyadicCoercivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dyadic conditioning of finite local Gram matrices of the complete arithmetic kernel. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
import D5.S3.Analytic.Interpolation.AveragedBoxEnergy
import D5.S3.Analytic.Interpolation.WideTentCoercivity
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ComplexOrder

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelDyadicCoercivity

open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity

private def quadratic {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ) (c : Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, (star (c i) * c j).re * f (x i - x j)

private lemma re_sum {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    (∑ i, f i).re = ∑ i, (f i).re :=
  map_sum Complex.reAddGroupHom f Finset.univ

private lemma quadratic_eq_re {n : ℕ} (f : ℝ → ℝ)
    (x : Fin n → ℝ) (c : Fin n → ℂ) :
    quadratic f x c =
      (star c ⬝ᵥ ((fun i j => (f (x i - x j) : ℂ)) *ᵥ c)).re := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum,
    re_sum, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private def tentEnergy {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (s : ℝ) : ℝ :=
  quadratic (fun t => max (s - |t|) 0) x c

private lemma tentEnergy_continuous {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) :
    Continuous (tentEnergy x c) := by
  unfold tentEnergy quadratic
  fun_prop

private lemma tentEnergy_eq_integral {n : ℕ} (x : Fin n → ℝ)
    (c : Fin n → ℂ) (s : ℝ) :
    tentEnergy x c s = ∫ u : ℝ,
      Complex.normSq (D5.S3.Analytic.Interpolation.AveragedBoxEnergy.boxSum x c s u) := by
  classical
  have hterm (i : Fin n) :
      (Ico (x i) (x i + s)).indicator (fun _ => c i) =ᵐ[volume]
        fun u => intervalVector s (x i) u * c i := by
    have he : (Ico (x i) (x i + s)).indicator (fun _ : ℝ => c i) =ᵐ[volume]
        (Icc (x i) (x i + s)).indicator (fun _ : ℝ => c i) :=
      indicator_ae_eq_of_ae_eq_set Ico_ae_eq_Icc
    filter_upwards [he] with u hu
    rw [hu]
    by_cases hi : u ∈ Icc (x i) (x i + s) <;> simp [intervalVector, hi]
  have hsum : D5.S3.Analytic.Interpolation.AveragedBoxEnergy.boxSum x c s =ᵐ[volume]
      fun u => ∑ i, intervalVector s (x i) u * c i := by
    filter_upwards [ae_all_iff.mpr hterm] with u hu
    exact Finset.sum_congr rfl (fun i _ => hu i)
  rw [tentEnergy, quadratic_eq_re, ← (triangle_quadratic s x c).2,
    integral_complex_ofReal]
  simp only [Complex.ofReal_re]
  exact integral_congr_ae (hsum.mono (fun u hu => congrArg Complex.normSq hu.symm))

private lemma tentEnergy_nonneg {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (s : ℝ) :
    0 ≤ tentEnergy x c s := by
  rw [tentEnergy_eq_integral]
  exact integral_nonneg (fun _ => Complex.normSq_nonneg _)

private lemma tentEnergy_average {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ)
    {g a : ℝ} (hg : 0 < g) (hga : g ≤ a)
    (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|) :
    a * g / 16 * (∑ i, Complex.normSq (c i)) ≤
      ∫ s : ℝ in Ioc a (2 * a), tentEnergy x c s := by
  have h := D5.S3.Analytic.Interpolation.AveragedBoxEnergy.averaged_box_energy_lower_bound
    x c hg hga hsep
  rw [integral_Icc_eq_integral_Ioc] at h
  simpa only [← tentEnergy_eq_integral] using h

/-- The original density is bounded below on a smaller window; the representer window
and its positive wide atom are retained. -/
private lemma density_lower_window {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧
      ∀ s ∈ Ioc 0 η, 1 / (4 * s) ≤ D2 s := by
  have he : ∀ᶠ s in 𝓝[>] (0 : ℝ), (1 / 4 : ℝ) < s * D2 s :=
    weighted_D2_limit.eventually (Ioi_mem_nhds (by norm_num))
  obtain ⟨ε, hε, hall⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp he
  refine ⟨min δ ε, lt_min hδ hε, min_le_left _ _, ?_⟩
  intro s hs
  have hquarter := (hall ⟨hs.1, hs.2.trans (min_le_right _ _)⟩).le
  apply (div_le_iff₀ (show (0 : ℝ) < 4 * s by positivity)).mpr
  nlinarith

/-- Each contained dyadic band uses only the lower density inherited from the
original representer. -/
private lemma density_lower_band {η g a : ℝ}
    (hη : ∀ s ∈ Ioc 0 η, 1 / (4 * s) ≤ D2 s)
    (hg : 0 < g) (hga : g ≤ a) (haη : 2 * a ≤ η)
    {s : ℝ} (hs : s ∈ Icc a (2 * a)) :
    1 / (8 * a) ≤ D2 s := by
  have ha : 0 < a := hg.trans_le hga
  have hs0 : 0 < s := ha.trans_le hs.1
  calc
    1 / (8 * a) ≤ 1 / (4 * s) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [hs.2]
    _ ≤ D2 s := hη s ⟨hs0, hs.2.trans haη⟩

/-- Half-open bands are disjoint at their shared dyadic endpoints. -/
private lemma dyadic_mixture_lower_bound
    (E : ℝ → ℝ) (hE : Continuous E) {δ η g C : ℝ}
    (hηδ : η ≤ δ) (hg : 0 < g)
    (hpos : ∀ s ∈ Ioc 0 δ, 0 < D2 s)
    (hEpos : ∀ s : ℝ, 0 ≤ E s)
    (hi : IntegrableOn (fun s => E s * D2 s) (Ioc 0 δ))
    (hη : ∀ s ∈ Ioc 0 η, 1 / (4 * s) ≤ D2 s)
    (haverage : ∀ a : ℝ, g ≤ a → 2 * a ≤ η →
      a * g / 16 * C ≤ ∫ s : ℝ in Ioc a (2 * a), E s)
    (J : ℕ) (hJ : (2 : ℝ) ^ J * g ≤ η) :
    (J : ℝ) * g / 128 * C ≤ ∫ s : ℝ in Ioc 0 δ, E s * D2 s := by
  have hband (a : ℝ) (hga : g ≤ a) (haη : 2 * a ≤ η) :
      g / 128 * C ≤ ∫ s : ℝ in Ioc a (2 * a), E s * D2 s := by
    have ha : 0 < a := hg.trans_le hga
    have hiE : IntegrableOn E (Ioc a (2 * a)) :=
      hE.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hiED : IntegrableOn (fun s => E s * D2 s) (Ioc a (2 * a)) :=
      hi.mono_set (fun s hs => ⟨ha.trans hs.1, hs.2.trans (haη.trans hηδ)⟩)
    have hmono : (1 / (8 * a)) * (∫ s : ℝ in Ioc a (2 * a), E s) ≤
        ∫ s : ℝ in Ioc a (2 * a), E s * D2 s := by
      rw [← integral_const_mul]
      apply setIntegral_mono_on (hiE.const_mul _) hiED measurableSet_Ioc
      intro s hs
      have hd := density_lower_band hη hg hga haη ⟨hs.1.le, hs.2⟩
      nlinarith [mul_le_mul_of_nonneg_left hd (hEpos s)]
    have hscaled := mul_le_mul_of_nonneg_left (haverage a hga haη)
      (show 0 ≤ 1 / (8 * a) by positivity)
    have heq : (1 / (8 * a)) * (a * g / 16 * C) = g / 128 * C := by
      field_simp [ha.ne']
      <;> ring
    exact heq ▸ hscaled.trans hmono
  have hrun : ∀ j : ℕ, (2 : ℝ) ^ j * g ≤ η →
      (j : ℝ) * g / 128 * C ≤
        ∫ s : ℝ in Ioc g ((2 : ℝ) ^ j * g), E s * D2 s := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hpow : (2 : ℝ) ^ (j + 1) * g = 2 * ((2 : ℝ) ^ j * g) := by
        rw [pow_succ]
        ring
      have ha : 0 < (2 : ℝ) ^ j * g := by positivity
      have hga : g ≤ (2 : ℝ) ^ j * g := by
        nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := j)]
      have haj : (2 : ℝ) ^ j * g ≤ η := by rw [hpow] at hj; linarith
      have hjband : 2 * ((2 : ℝ) ^ j * g) ≤ η := by rwa [← hpow]
      have hinc : (2 : ℝ) ^ j * g ≤ (2 : ℝ) ^ (j + 1) * g := by
        rw [hpow]; linarith
      have hi₁ : IntegrableOn (fun s => E s * D2 s)
          (Ioc g ((2 : ℝ) ^ j * g)) :=
        hi.mono_set (fun s hs => ⟨hg.trans hs.1, hs.2.trans (haj.trans hηδ)⟩)
      have hi₂ : IntegrableOn (fun s => E s * D2 s)
          (Ioc ((2 : ℝ) ^ j * g) ((2 : ℝ) ^ (j + 1) * g)) :=
        hi.mono_set (fun s hs => ⟨ha.trans hs.1, hs.2.trans (hj.trans hηδ)⟩)
      have hunion := setIntegral_union (Ioc_disjoint_Ioc_of_le (le_refl _))
        measurableSet_Ioc hi₁ hi₂
      rw [Ioc_union_Ioc_eq_Ioc hga hinc] at hunion
      have hb := hband ((2 : ℝ) ^ j * g) hga hjband
      rw [← hpow] at hb
      rw [hunion]
      push_cast
      nlinarith [ih haj, hb]
  have hmono : (∫ s : ℝ in Ioc g ((2 : ℝ) ^ J * g), E s * D2 s) ≤
      ∫ s : ℝ in Ioc 0 δ, E s * D2 s := by
    apply setIntegral_mono_set hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact mul_nonneg (hEpos s) (hpos s hs).le
    · exact ae_of_all _ (fun s hs => ⟨hg.trans hs.1, hs.2.trans (hJ.trans hηδ)⟩)
  exact (hrun J hJ).trans hmono

private lemma quadratic_representation {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ)
    {δ r L : ℝ}
    (hrep : ∀ t : ℝ, |t| ≤ δ →
      IntegrableOn (fun s : ℝ => max (s - |t|) 0 * D2 s) (Ioc 0 δ) ∧
      K t = (∫ s : ℝ in Ioc 0 δ, max (s - |t|) 0 * D2 s) + r * max (L - |t|) 0)
    (hdiam : ∀ i j, |x i - x j| ≤ δ) :
    IntegrableOn (fun s => tentEnergy x c s * D2 s) (Ioc 0 δ) ∧
    quadratic K x c = (∫ s : ℝ in Ioc 0 δ, tentEnergy x c s * D2 s) +
      r * tentEnergy x c L := by
  have hi (i j : Fin n) : IntegrableOn (fun s : ℝ =>
      (star (c i) * c j).re * (max (s - |x i - x j|) 0 * D2 s)) (Ioc 0 δ) :=
    ((hrep (x i - x j) (hdiam i j)).1).const_mul _
  have he : (fun s => tentEnergy x c s * D2 s) = fun s =>
      ∑ i, ∑ j, (star (c i) * c j).re * (max (s - |x i - x j|) 0 * D2 s) := by
    funext s
    simp only [tentEnergy, quadratic, Finset.sum_mul, mul_assoc]
  have his : IntegrableOn (fun s => tentEnergy x c s * D2 s) (Ioc 0 δ) := by
    rw [he]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))
  have hint : (∫ s : ℝ in Ioc 0 δ, tentEnergy x c s * D2 s) =
      ∑ i, ∑ j, (star (c i) * c j).re *
        (∫ s : ℝ in Ioc 0 δ, max (s - |x i - x j|) 0 * D2 s) := by
    rw [he, integral_finsetSum _
      (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul]
  refine ⟨his, ?_⟩
  rw [hint]
  simp only [tentEnergy, quadratic]
  simp_rw [(hrep _ (hdiam _ _)).2]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma inverse_entry_bound {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) {λ : ℝ}
    (hλ : 0 < λ)
    (hcoercive : ∀ v : Fin n → ℝ,
      λ * (∑ k, (v k) ^ 2) ≤ v ⬝ᵥ (H *ᵥ v))
    (i j : Fin n) : |H⁻¹ i j| ≤ 1 / λ := by
  classical
  let e : Fin n → ℝ := Pi.single j 1
  let v : Fin n → ℝ := H⁻¹ *ᵥ e
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hHv : H *ᵥ v = e := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv H hdet, Matrix.one_mulVec]
  have hv (k : Fin n) : v k = H⁻¹ k j := by
    simp only [v, e, Matrix.mulVec_single_one, Matrix.col_apply]
  have hquad : λ * (∑ k, (v k) ^ 2) ≤ v j := by
    simpa only [hHv, e, dotProduct_single, mul_one] using hcoercive v
  have hcoord (k : Fin n) : (v k) ^ 2 ≤ ∑ l, (v l) ^ 2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (v l)) (Finset.mem_univ k)
  have hdiag : v j ≤ 1 / λ := by
    have hj : λ * (v j) ^ 2 ≤ v j :=
      (mul_le_mul_of_nonneg_left (hcoord j) hλ.le).trans hquad
    by_contra h
    have hvj : 1 / λ < v j := lt_of_not_ge h
    have hvj0 : 0 < v j := (one_div_pos.mpr hλ).trans hvj
    have hprod : 1 < λ * v j := by
      have := (div_lt_iff₀ hλ).mp hvj
      nlinarith
    have hstrict := mul_pos (sub_pos.mpr hprod) hvj0
    nlinarith
  have hi : λ * (v i) ^ 2 ≤ 1 / λ :=
    ((mul_le_mul_of_nonneg_left (hcoord i) hλ.le).trans hquad).trans hdiag
  have hisq : (v i) ^ 2 ≤ (1 / λ) ^ 2 := by
    calc
      (v i) ^ 2 ≤ (1 / λ) / λ := (le_div_iff₀ hλ).mpr (by nlinarith [hi])
      _ = (1 / λ) ^ 2 := by ring
  rw [← hv i]
  apply (sq_le_sq₀ (abs_nonneg _) (one_div_pos.mpr hλ).le).mp
  simpa only [sq_abs] using hisq

private lemma inverse_budget_bound {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) {λ : ℝ}
    (hλ : 0 < λ)
    (hcoercive : ∀ v : Fin n → ℝ,
      λ * (∑ k, (v k) ^ 2) ≤ v ⬝ᵥ (H *ᵥ v)) :
    1 + ∑ i, ∑ j, |H⁻¹ i j| ≤ 1 + (n : ℝ) ^ 2 / λ := by
  have hsum : (∑ i, ∑ j, |H⁻¹ i j|) ≤ ∑ _i : Fin n, ∑ _j : Fin n, 1 / λ :=
    Finset.sum_le_sum (fun i _ =>
      Finset.sum_le_sum (fun j _ => inverse_entry_bound H hH hλ hcoercive i j))
  have hconstant : (∑ _i : Fin n, ∑ _j : Fin n, 1 / λ) = (n : ℝ) ^ 2 / λ := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  linarith [hsum.trans_eq hconstant]

/-- One fixed arithmetic window has a dyadically improving coercivity margin and
the corresponding entrywise inverse budget for every finite separated family. -/
theorem exists_window_dyadic_conditioning : ∃ δ η r : ℝ,
    0 < δ ∧ δ < Real.log 2 ∧ 0 < η ∧ η ≤ δ ∧ 0 < r ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ (x : Fin n → ℝ) (g : ℝ), 0 < g →
      (∀ i j, i ≠ j → g ≤ |x i - x j|) →
      (∀ i j, |x i - x j| ≤ δ) →
      ∀ (J : ℕ), (2 : ℝ) ^ J * g ≤ η →
      let λ := g * (r / 2 + (J : ℝ) / 128)
      let H : Matrix (Fin n) (Fin n) ℝ := fun i j => K (x i - x j)
      (∀ c : Fin n → ℂ, λ * (∑ i, Complex.normSq (c i)) ≤
        (star c ⬝ᵥ ((fun i j => (K (x i - x j) : ℂ)) *ᵥ c)).re) ∧
      (∀ i j : Fin n, |H⁻¹ i j| ≤ 1 / λ) ∧
      1 + (∑ i, ∑ j, |H⁻¹ i j|) ≤ 1 + (n : ℝ) ^ 2 / λ := by
  classical
  obtain ⟨δ, r, L, hδ, hδ2, hr, hL, hpos, _hi, hrep⟩ := actual_positive_representer
  obtain ⟨η, hη, hηδ, hdensity⟩ := density_lower_window hδ
  refine ⟨δ, η, r, hδ, hδ2, hη, hηδ, hr, ?_⟩
  intro n hn x g hg hsep hdiam J hJ
  let λ := g * (r / 2 + (J : ℝ) / 128)
  let H : Matrix (Fin n) (Fin n) ℝ := fun i j => K (x i - x j)
  have hλ : 0 < λ := by
    dsimp [λ]
    exact mul_pos hg (add_pos_of_pos_of_nonneg (by positivity) (by positivity))
  have hcomplex (c : Fin n → ℂ) :
      λ * (∑ i, Complex.normSq (c i)) ≤
        (star c ⬝ᵥ ((fun i j => (K (x i - x j) : ℂ)) *ᵥ c)).re := by
    obtain ⟨hmi, hqrep⟩ := quadratic_representation x c hrep hdiam
    have hmix := dyadic_mixture_lower_bound (tentEnergy x c)
      (tentEnergy_continuous x c) hηδ hg hpos (tentEnergy_nonneg x c) hmi hdensity
      (fun a hga _haη => tentEnergy_average x c hg hga hsep) J hJ
    have hwide : g / 2 * (∑ i, Complex.normSq (c i)) ≤ tentEnergy x c L := by
      rw [tentEnergy, quadratic_eq_re]
      exact D5.S3.Analytic.Interpolation.WideTentCoercivity.wide_tent_lower_bound
        hn x c hg hsep (fun i j => (hdiam i j).trans hL.le)
    calc
      λ * (∑ i, Complex.normSq (c i)) =
          (J : ℝ) * g / 128 * (∑ i, Complex.normSq (c i)) +
            r * (g / 2 * (∑ i, Complex.normSq (c i))) := by dsimp [λ]; ring
      _ ≤ (∫ s : ℝ in Ioc 0 δ, tentEnergy x c s * D2 s) +
            r * tentEnergy x c L :=
        add_le_add hmix (mul_le_mul_of_nonneg_left hwide hr.le)
      _ = quadratic K x c := hqrep.symm
      _ = _ := quadratic_eq_re K x c
  have hreal (v : Fin n → ℝ) : λ * (∑ k, (v k) ^ 2) ≤ v ⬝ᵥ (H *ᵥ v) := by
    have hc := hcomplex (fun k => (v k : ℂ))
    rw [← quadratic_eq_re] at hc
    have hnorm : (∑ k, Complex.normSq ((v k : ℝ) : ℂ)) = ∑ k, (v k) ^ 2 := by
      simp only [Complex.normSq_ofReal, pow_two]
    rw [hnorm] at hc
    convert hc using 1
    simp only [H, quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hHermitian : H.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [H, star_trivial, K, abs_sub_comm]
  have hH : H.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hHermitian
    intro v hv
    have hsum : 0 < ∑ k, (v k) ^ 2 := by
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
      exact Finset.sum_pos' (fun l _ => sq_nonneg (v l))
        ⟨k, Finset.mem_univ _, sq_pos_of_ne_zero hk⟩
    simpa only [star_trivial] using (mul_pos hλ hsum).trans_le (hreal v)
  exact ⟨hcomplex, inverse_entry_bound H hH hλ hreal,
    inverse_budget_bound H hH hλ hreal⟩

#print axioms exists_window_dyadic_conditioning

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelDyadicCoercivity
