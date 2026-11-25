/- GID: D5/S3/Fourier/Asymptotics/CyclicActivationShift
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicActivationShift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Displacement of a front support boundary under the two cyclic cosine constraints. -/

import D5.S3.Fourier.Asymptotics.CyclicEventualSupport

/-! The zero of the outermost weight locates the change of the front support. -/

open Finset Filter Matrix
open scoped Topology
open D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open D5.S3.Fourier.Asymptotics.CyclicEventualSupport
open D5.S3.Fourier.Asymptotics.CyclicSupportCertificate
open D5.S3.Fourier.Asymptotics.CyclicParityLimit
open D5.S3.Fourier.Asymptotics.CyclicParityCorrection
open D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison

namespace D5.S3.Fourier.Asymptotics.CyclicActivationShift

set_option autoImplicit false

private theorem boundary_moment_elimination {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (T a b g : ℝ)
    (hmass : ∑ i, (a + b * x i + g * x i ^ 2) = 0) :
    let n : ℝ := Fintype.card ι
    let s₁ := ∑ i, x i
    let s₂ := ∑ i, x i ^ 2
    let s₃ := ∑ i, x i ^ 3
    let K := ∑ i, x i * (a + b * x i + g * x i ^ 2)
    (n * s₂ - s₁ ^ 2) * (a + b * T + g * T ^ 2) =
      (n * T - s₁) * K +
        g * ((n * T - s₁) * (s₂ * T - s₃) - (s₁ * T - s₂) ^ 2) := by
  intro n s₁ s₂ s₃ K
  have hs₀ : n * a + s₁ * b + s₂ * g = 0 := by
    simpa [n, s₁, s₂, sum_add_distrib, ← mul_sum, mul_comm] using hmass
  have hs₁ : s₁ * a + s₂ * b + s₃ * g = K := by
    have term (i : ι) : x i * (a + b * x i + g * x i ^ 2) =
        x i * a + x i ^ 2 * b + x i ^ 3 * g := by ring
    simp [K, term, sum_add_distrib, ← sum_mul, s₁, s₂, s₃]
  rw [← hs₁]
  linear_combination (s₂ - s₁ * T) * hs₀

private theorem switch_coefficient {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (T a b a' b' m m₄ K : ℝ)
    (hZ : 0 < ∑ i, (T - x i))
    (hslope : 0 < a' + b' * T)
    (hM : ∑ i, x i * (T - x i) = (∑ i, (T - x i)) * m)
    (hM₄ : ∑ i, x i ^ 2 * (T - x i) = (∑ i, (T - x i)) * m₄)
    (hmass : ∑ i, (a + b * x i + (1 / (3 * ∑ j, (T - x j))) * x i ^ 2) = 0)
    (hmoment : ∑ i, x i * (a + b * x i + (1 / (3 * ∑ j, (T - x j))) * x i ^ 2) = K)
    (hmass' : ∑ i, (a' + b' * x i) = 0)
    (hmoment' : ∑ i, x i * (a' + b' * x i) = 1) :
    let Z := ∑ i, (T - x i)
    0 < a' + b' * T ∧
      (a + b * T + (1 / (3 * Z)) * T ^ 2) / (a' + b' * T) = K + (m₄ - m ^ 2) / 3 := by
  let n : ℝ := Fintype.card ι
  let s₁ := ∑ i, x i
  let s₂ := ∑ i, x i ^ 2
  let s₃ := ∑ i, x i ^ 3
  let Z := ∑ i, (T - x i)
  let g := 1 / (3 * Z)
  have h₀ : n * T - s₁ = Z := by simp [n, s₁, Z, sum_sub_distrib, mul_comm]
  have h₁ : s₁ * T - s₂ = Z * m := by
    rw [← hM]
    simp_rw [mul_sub, ← pow_two, sum_sub_distrib, ← sum_mul]
    rfl
  have h₂ : s₂ * T - s₃ = Z * m₄ := by
    rw [← hM₄]
    simp_rw [mul_sub, ← pow_succ, sum_sub_distrib, ← sum_mul]
    rfl
  have hf := boundary_moment_elimination x T a b g hmass
  dsimp only at hf
  change (n * s₂ - s₁ ^ 2) * _ = (n * T - s₁) * _ +
    g * ((n * T - s₁) * (s₂ * T - s₃) - (s₁ * T - s₂) ^ 2) at hf
  rw [h₀, h₁, h₂, hmoment] at hf
  have hmasslin : ∑ i, (a' + b' * x i + 0 * x i ^ 2) = 0 := by simpa using hmass'
  have hfl := boundary_moment_elimination x T a' b' 0 hmasslin
  dsimp only at hfl
  simp only [zero_mul, add_zero, hmoment', mul_one] at hfl
  change (n * s₂ - s₁ ^ 2) * (a' + b' * T) = n * T - s₁ at hfl
  rw [h₀] at hfl
  have hdet : n * s₂ - s₁ ^ 2 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hfl
    exact hZ.ne' hfl.symm
  refine ⟨hslope, (div_eq_iff hslope.ne').mpr ?_⟩
  apply (mul_right_inj' hdet).mp
  change (n * s₂ - s₁ ^ 2) * (a + b * T + g * T ^ 2) =
    (n * s₂ - s₁ ^ 2) * ((K + (m₄ - m ^ 2) / 3) * (a' + b' * T))
  calc
    _ = Z * K + g * (Z * (Z * m₄) - (Z * m) ^ 2) := hf
    _ = Z * (K + (m₄ - m ^ 2) / 3) := by
      dsimp only [g]
      field_simp [hZ.ne']
    _ = _ := by rw [← hfl]; ring

private theorem sum_sixth_rat (n : ℕ) :
    (∑ j ∈ range (n + 1), (j : ℚ) ^ 6) =
      (n : ℚ) * (n + 1) * (2 * n + 1) *
        (3 * (n : ℚ) ^ 4 + 6 * (n : ℚ) ^ 3 - 3 * n + 1) / 42 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sum_centered_sixth (n : ℕ) :
    (∑ k ∈ Icc (-(n : ℤ)) (n : ℤ), (k : ℝ) ^ 6) =
      (n : ℝ) * (n + 1) * (2 * n + 1) *
        (3 * (n : ℝ) ^ 4 + 6 * (n : ℝ) ^ 3 - 3 * n + 1) / 21 := by
  have heven : Function.Even (fun k : ℤ => (k : ℝ) ^ 6) := by
    intro k
    dsimp only
    push_cast
    ring
  rw [Finset.sum_Icc_of_even_eq_range heven]
  push_cast
  have h := congrArg (fun q : ℚ => (q : ℝ)) (sum_sixth_rat n)
  push_cast at h
  rw [h]
  norm_num
  ring


private theorem threshold_lattice_fourth_moment (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ latticeInterval n, (k : ℝ) ^ 4 *
      (((n : ℝ) ^ 2 - (k : ℝ) ^ 2) / normalizer n ((n : ℝ) ^ 2))) =
      ((n : ℝ) ^ 2 - 1) * (3 * (n : ℝ) ^ 2 - 5) / 35 := by
  have hz := (normalizer_pos n hn le_rfl).ne'
  simp_rw [← mul_div_assoc, mul_sub, ← pow_add]
  norm_num
  rw [← sum_div, sum_sub_distrib, ← sum_mul, sum_lattice_fourth]
  change (_ - (∑ k ∈ Icc (-(n : ℤ)) (n : ℤ), (k : ℝ) ^ 6)) /
      normalizer n ((n : ℝ) ^ 2) = _
  rw [sum_centered_sixth, div_eq_iff hz, normalizer_formula]
  ring

private theorem affine_switch {κ : Type*} {l : Filter κ}
    {s r b : κ → ℝ} {r₀ b₀ : ℝ}
    (hs : ∀ᶠ k in l, 0 < s k) (hr : Tendsto r l (𝓝 r₀))
    (hb : Tendsto b l (𝓝 b₀)) (hb₀ : 0 < b₀) (m₀ : ℝ) :
    ∃ m : κ → ℝ, Tendsto (fun k => (m k - m₀) / s k) l (𝓝 (-r₀ / b₀)) ∧
      ∀ᶠ k in l, ∀ z : ℝ,
        ((s k * r k + (z - m₀) * b k = 0) ↔ z = m k) ∧
        ((0 < s k * r k + (z - m₀) * b k) ↔ m k < z) := by
  let m := fun k => m₀ - s k * (r k / b k)
  have hbpos : ∀ᶠ k in l, 0 < b k := hb.eventually (lt_mem_nhds hb₀)
  refine ⟨m, ?_, ?_⟩
  · apply ((hr.neg).div hb hb₀.ne').congr'
    filter_upwards [hs] with k hk
    dsimp [m]
    field_simp [hk.ne']
    ring
  · filter_upwards [hbpos] with k hk z
    have factor : s k * r k + (z - m₀) * b k = (z - m k) * b k := by
      dsimp [m]
      field_simp [hk.ne']
      ring
    rw [factor, mul_eq_zero, or_iff_left hk.ne', sub_eq_zero,
      mul_pos_iff_of_pos_right hk, sub_pos]
    exact ⟨Iff.rfl, Iff.rfl⟩


private theorem gram_slope {ι κ : Type*} [Fintype ι] {l : Filter κ}
    {F : κ → Matrix ι (Fin 3) ℝ} {F₀ : Matrix ι (Fin 3) ℝ}
    (hFt : Tendsto F l (𝓝 F₀)) (hF : Function.Injective F₀.mulVec)
    {y : κ → Fin 3 → ℝ} {y₀ : Fin 3 → ℝ} (hy : Tendsto y l (𝓝 y₀)) :
    let u₀ := (F₀ᵀ * F₀)⁻¹ *ᵥ y₀
    ∃ u : κ → Fin 3 → ℝ, Tendsto u l (𝓝 u₀) ∧ F₀ᵀ *ᵥ (F₀ *ᵥ u₀) = y₀ ∧
      ∀ᶠ k in l, (F k)ᵀ *ᵥ (F k *ᵥ u k) = y k := by
  intro u₀
  let M := fun A : Matrix ι (Fin 3) ℝ => Aᵀ * A
  let u := fun k => (M (F k))⁻¹ *ᵥ y k
  have hM : Tendsto (fun k => M (F k)) l (𝓝 (M F₀)) :=
    (continuous_id.matrix_transpose.matrix_mul continuous_id).continuousAt.tendsto.comp hFt
  have hdet : (M F₀).det ≠ 0 := gram_det_ne_zero F₀ hF
  have hinv : Tendsto (fun k => (M (F k))⁻¹) l (𝓝 ((M F₀)⁻¹)) := by
    apply (continuousAt_matrix_inv (M F₀) ?_).tendsto.comp hM
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  have hmul : Continuous (fun p : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ) =>
      p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  refine ⟨u, hmul.continuousAt.tendsto.comp (hinv.prodMk_nhds hy), ?_, ?_⟩
  · dsimp only [u₀]
    rw [mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]
  · have hdetF := (continuous_id.matrix_det.continuousAt (x := M F₀)).tendsto.comp hM
    filter_upwards [hdetF.eventually_ne hdet] with k hk
    change (M (F k)).det ≠ 0 at hk
    dsimp only [u]
    rw [mulVec_mulVec, mulVec_mulVec]
    change (M (F k) * (M (F k))⁻¹) *ᵥ y k = y k
    rw [mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hk), one_mulVec]


private theorem gram_boundary_switch {ι κ : Type*} [Fintype ι] {l : Filter κ}
    {s : κ → ℝ} (hs : Tendsto s l (𝓝 0)) (hspos : ∀ᶠ k in l, 0 < s k)
    {E : κ → Matrix ι (Fin 3) ℝ} {E₀ : Matrix ι (Fin 3) ℝ} (hE : Tendsto E l (𝓝 E₀))
    (F₀ : Matrix ι (Fin 3) ℝ) (hF : Function.Injective F₀.mulVec)
    {y : κ → Fin 3 → ℝ} {y₀ : Fin 3 → ℝ} (hy : Tendsto y l (𝓝 y₀))
    (a₀ b₁ : Fin 3 → ℝ) (j : ι) (m₀ : ℝ) (hzero : (F₀ *ᵥ a₀) j = 0)
    (hslope : 0 < (F₀ *ᵥ ((F₀ᵀ * F₀)⁻¹ *ᵥ y₀)) j) :
    let F := fun k => F₀ + s k • E k
    let w₀ := F₀ *ᵥ a₀
    ∃ (m : κ → ℝ) (u₀ : Fin 3 → ℝ) (v : κ → Fin 3 → ℝ),
      let r₀ := E₀ *ᵥ a₀ + F₀ *ᵥ u₀
      let b₀ := (F₀ᵀ * F₀)⁻¹ *ᵥ y₀
      F₀ᵀ *ᵥ r₀ = b₁ - E₀ᵀ *ᵥ w₀ ∧
      Tendsto (fun k => (m k - m₀) / s k) l
        (𝓝 (-r₀ j / (F₀ *ᵥ b₀) j)) ∧
      Tendsto v l (𝓝 a₀) ∧
      Tendsto (fun k => (s k)⁻¹ • (F k *ᵥ v k - w₀)) l
        (𝓝 (r₀ + (-r₀ j / (F₀ *ᵥ b₀) j) • (F₀ *ᵥ b₀))) ∧
      ∀ᶠ k in l, (F k)ᵀ *ᵥ (F k *ᵥ v k) =
        F₀ᵀ *ᵥ w₀ + s k • b₁ + (m k - m₀) • y k ∧ (F k *ᵥ v k) j = 0 := by
  intro F w₀
  obtain ⟨u, u₀, hu, hnorm, huEq⟩ := gram_variation hs hE F₀ hF a₀ b₁
  have hFt : Tendsto F l (𝓝 F₀) := by
    simpa only [zero_smul, add_zero] using tendsto_const_nhds.add (hs.smul hE)
  obtain ⟨b, hb, _, hbEq⟩ := gram_slope hFt hF hy
  let b₀ := (F₀ᵀ * F₀)⁻¹ *ᵥ y₀
  let r₀ := E₀ *ᵥ a₀ + F₀ *ᵥ u₀
  let rAt := fun k => E k *ᵥ a₀ + F k *ᵥ u k
  let slopeAt := fun k => F k *ᵥ b k
  have hmul : Continuous (fun p : Matrix ι (Fin 3) ℝ × (Fin 3 → ℝ) =>
      p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hr : Tendsto rAt l (𝓝 r₀) :=
    (hmul.continuousAt.tendsto.comp (hE.prodMk_nhds tendsto_const_nhds)).add
      (hmul.continuousAt.tendsto.comp (hFt.prodMk_nhds hu))
  have hB : Tendsto slopeAt l (𝓝 (F₀ *ᵥ b₀)) :=
    hmul.continuousAt.tendsto.comp (hFt.prodMk_nhds hb)
  obtain ⟨m, hm, hmEq⟩ := affine_switch hspos (tendsto_pi_nhds.mp hr j)
    (tendsto_pi_nhds.mp hB j) hslope m₀
  let v := fun k => a₀ + s k • u k + (m k - m₀) • b k
  have hmSmall : Tendsto (fun k => m k - m₀) l (𝓝 0) := by
    have hmProduct := hs.mul hm
    have heq := hmProduct.congr' (show
        (fun k => s k * ((m k - m₀) / s k)) =ᶠ[l] (fun k => m k - m₀) from by
      filter_upwards [hspos] with k hk
      field_simp [hk.ne'])
    simpa only [zero_mul] using heq
  have hv : Tendsto v l (𝓝 a₀) := by
    simpa only [zero_smul, add_zero] using
      (tendsto_const_nhds.add (hs.smul hu)).add (hmSmall.smul hb)
  have hbase (k) : F k *ᵥ a₀ = w₀ + s k • (E k *ᵥ a₀) := by
    simp only [F, w₀, add_mulVec, smul_mulVec]
  have hvar : Tendsto (fun k => (s k)⁻¹ • (F k *ᵥ v k - w₀)) l
      (𝓝 (r₀ + (-r₀ j / (F₀ *ᵥ b₀) j) • (F₀ *ᵥ b₀))) := by
    apply (hr.add (hm.smul hB)).congr'
    filter_upwards [hspos] with k hk
    funext i
    simp only [v, mulVec_add, mulVec_smul, hbase, rAt, slopeAt, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    field_simp [hk.ne']
    ring
  refine ⟨m, u₀, v, hnorm, hm, hv, hvar, ?_⟩
  filter_upwards [huEq, hbEq, hmEq] with k hk₁ hk₂ hk₃
  change (F k)ᵀ *ᵥ (F k *ᵥ (a₀ + s k • u k)) = F₀ᵀ *ᵥ w₀ + s k • b₁ at hk₁
  have hmJ := (hk₃ (m k)).1.mpr rfl
  constructor
  · rw [show v k = (a₀ + s k • u k) + (m k - m₀) • b k from rfl]
    rw [mulVec_add, mulVec_smul, mulVec_add, mulVec_smul, hk₁, hk₂]
  · change (F k *ᵥ (a₀ + s k • u k + (m k - m₀) • b k)) j = 0
    simp only [mulVec_add, mulVec_smul, hbase, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      show w₀ j = 0 from hzero, zero_add]
    change s k * (E k *ᵥ a₀) j + s k * (F k *ᵥ u k) j + (m k - m₀) * slopeAt k j = 0
    rw [← mul_add]
    exact hmJ


private theorem phase_budget_derivative {ι η : Type*} [Fintype ι] [Fintype η] [Nonempty η]
    (x : ι → ℝ) (d : ℝ) (i₀ i₁ : ι) (h₀ : x i₀ = 0) (h₁ : x i₁ = 1) :
    let F₀ := phaseRow (η := η) x d baseRow
    let b := (F₀ᵀ * F₀)⁻¹ *ᵥ ![0, 0, 1]
    (∀ i : ι, (F₀ *ᵥ b) (Sum.inl i) = b 0 + b 2 * x i ^ 2) ∧
    (∀ i : η, (F₀ *ᵥ b) (Sum.inr i) = 0) ∧
    (∑ i, (b 0 + b 2 * x i ^ 2)) = 0 ∧
    (∑ i, x i ^ 2 * (b 0 + b 2 * x i ^ 2)) = 1 := by
  intro F₀ b
  have hdet : IsUnit (F₀ᵀ * F₀).det :=
    isUnit_iff_ne_zero.mpr (gram_det_ne_zero F₀ (phase_injective x d i₀ i₁ h₀ h₁))
  have heq : F₀ᵀ *ᵥ (F₀ *ᵥ b) = ![0, 0, 1] := by
    dsimp only [b]
    rw [mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hfront (i : ι) : (F₀ *ᵥ b) (Sum.inl i) = b 0 + b 2 * x i ^ 2 := by
    change ![1, 0, x i ^ 2] ⬝ᵥ b = _
    rw [dot_three]
    ring
  have hback (i : η) : (F₀ *ᵥ b) (Sum.inr i) = 0 := by
    have h := congrFun heq (1 : Fin 3)
    change ((phaseRow x d baseRow)ᵀ *ᵥ (F₀ *ᵥ b)) 1 = 0 at h
    rw [phase_moment] at h
    change (∑ j : ι, 0 * (F₀ *ᵥ b) (Sum.inl j)) +
      (∑ j : η, 2 * (F₀ *ᵥ b) (Sum.inr j)) = 0 at h
    have row_eq_const (j : η) : (F₀ *ᵥ b) (Sum.inr j) = (F₀ *ᵥ b) (Sum.inr i) := rfl
    simp only [zero_mul, sum_const_zero, zero_add, row_eq_const, sum_const, nsmul_eq_mul] at h
    have hc : 0 < (Fintype.card η : ℝ) := by exact_mod_cast Fintype.card_pos
    exact (mul_eq_zero.mp h).resolve_left hc.ne' |> fun he =>
      (mul_eq_zero.mp he).resolve_left (by norm_num)
  refine ⟨hfront, hback, ?_, ?_⟩
  · have h := congrFun heq (0 : Fin 3)
    change ((phaseRow x d baseRow)ᵀ *ᵥ (F₀ *ᵥ b)) 0 = 0 at h
    rw [phase_moment] at h
    change (∑ i : ι, 1 * (F₀ *ᵥ b) (Sum.inl i)) +
      (∑ i : η, 1 * (F₀ *ᵥ b) (Sum.inr i)) = 0 at h
    simpa only [one_mul, hfront, hback, sum_const_zero, add_zero] using h
  · have h := congrFun heq (2 : Fin 3)
    change ((phaseRow x d baseRow)ᵀ *ᵥ (F₀ *ᵥ b)) 2 = 1 at h
    rw [phase_moment] at h
    change (∑ i : ι, x i ^ 2 * (F₀ *ᵥ b) (Sum.inl i)) +
      (∑ i : η, d ^ 2 * (F₀ *ᵥ b) (Sum.inr i)) = 1 at h
    simpa only [hfront, hback, mul_zero, sum_const_zero, add_zero] using h

private theorem phase_root {ι η κ : Type*} [Fintype ι] [Fintype η] [Nonempty η]
    {l : Filter κ} {h : κ → ℝ} (ht : Tendsto h l (𝓝 0)) (hp : ∀ᶠ k in l, 0 < h k)
    (x : ι → ℝ) (d t m : ℝ) (hm : 0 < m)
    (i₀ i₁ j : ι) (h₀ : x i₀ = 0) (h₁ : x i₁ = 1)
    (hx : ∀ i, x i ^ 2 ≤ t) (hj : x j ^ 2 = t) :
    let Z := ∑ i, (t - x i ^ 2)
    let W := fun i => (t - x i ^ 2) / Z
    let M₄ := ∑ i, (x i ^ 2) ^ 2 * W i
    0 < Z → (∑ i, W i) = 1 → (∑ i, x i ^ 2 * W i) = m →
    let F := fun k => phaseRow (η := η) x d fun back z =>
      ![1, 1 - signedCos back z (h k), (1 - signedCos back z (h k) ^ 2) / h k ^ 2]
    ∃ (root : κ → ℝ) (a : κ → Fin 3 → ℝ),
      Tendsto (fun k => (root k - m) / h k ^ 2) l
        (𝓝 ((m ^ 2 - 2 * M₄) / 3 - (m - d ^ 2) * (3 * m / 4))) ∧
      Tendsto a l (𝓝 (leading t Z d)) ∧
      ∀ᶠ k in l,
        (F k)ᵀ *ᵥ (F k *ᵥ a k) = ![1, 2 * root k * h k ^ 2, root k] ∧
        (∀ i : ι, x i ^ 2 = t → (F k *ᵥ a k) (Sum.inl i) = 0) ∧
        (∀ i : ι, x i ^ 2 < t → 0 < (F k *ᵥ a k) (Sum.inl i)) ∧
        (∀ i : η, 0 < (F k *ᵥ a k) (Sum.inr i)) := by
  intro Z W M₄ hZ hW hX F
  let F₀ := phaseRow (η := η) x d baseRow
  let E := fun k => phaseRow (η := η) x d fun back z => variationRow back z (h k)
  let E₀ := phaseRow (η := η) x d limitRow
  let a₀ := leading t Z d
  let w := F₀ *ᵥ a₀
  let s := fun k => h k ^ 2
  let y := fun k => (![0, 2 * s k, 1] : Fin 3 → ℝ)
  let b₀ := (F₀ᵀ * F₀)⁻¹ *ᵥ (![0, 0, 1] : Fin 3 → ℝ)
  let P := fun k => F₀ + s k • E k
  have hs : Tendsto s l (𝓝 0) := by simpa [s] using ht.pow 2
  have hspos : ∀ᶠ k in l, 0 < s k := hp.mono fun _ hk => sq_pos_of_pos hk
  have hn := hp.mono fun _ hk => hk.ne'
  have hE : Tendsto E l (𝓝 E₀) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    cases i with
    | inl i => exact variationRow_tendsto ht hn false (x i)
    | inr i => exact variationRow_tendsto ht hn true d
  have hy : Tendsto y l (𝓝 (![0, 0, 1] : Fin 3 → ℝ)) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    fin_cases i
    · exact tendsto_const_nhds
    · simpa [y] using hs.const_mul 2
    · exact tendsto_const_nhds
  obtain ⟨hwf, hwb, hbase⟩ := phase_leading_moments (η := η) x d t Z m hZ hW hX
  change ∀ i : ι, w (Sum.inl i) = W i at hwf
  change ∀ i : η, w (Sum.inr i) = 0 at hwb
  change F₀ᵀ *ᵥ w = ![1, 0, m] at hbase
  have hzero : w (Sum.inl j) = 0 := by simp [hwf, W, hj]
  obtain ⟨hbfront, hbback, hbm, hbx⟩ :=
    phase_budget_derivative (η := η) x d i₀ i₁ h₀ h₁
  change ∀ i : ι, (F₀ *ᵥ b₀) (Sum.inl i) = b₀ 0 + b₀ 2 * x i ^ 2 at hbfront
  change ∀ i : η, (F₀ *ᵥ b₀) (Sum.inr i) = 0 at hbback
  change (∑ i, (b₀ 0 + b₀ 2 * x i ^ 2)) = 0 at hbm
  change (∑ i, x i ^ 2 * (b₀ 0 + b₀ 2 * x i ^ 2)) = 1 at hbx
  have hbelow : x i₀ ^ 2 < x j ^ 2 := by
    have hh := hx i₁
    rw [h₀, hj, h₁] at *
    norm_num at *
    linarith only [hh]
  have hSlope : 0 < b₀ 0 + b₀ 2 * t := by
    have hh := boundary_variation_pos (fun i => x i ^ 2) j (hj ▸ hx) ⟨i₀, hbelow⟩
      (b₀ 0) (b₀ 2) 0 le_rfl
      (by simpa only [zero_mul, add_zero] using hbm)
      (by simpa only [zero_mul, add_zero, hbx] using (zero_lt_one : (0 : ℝ) < 1))
    simpa only [lt_max_iff, lt_irrefl, false_or, hj, zero_mul, add_zero] using hh
  have hB : 0 < (F₀ *ᵥ b₀) (Sum.inl j) := by rwa [hbfront, hj]
  obtain ⟨root, u₀, a, hl, hlim, ha, hvarLim, heq⟩ :=
    gram_boundary_switch hs hspos hE F₀ (phase_injective x d i₀ i₁ h₀ h₁) hy
      a₀ ![0, 2 * m, 0] (Sum.inl j) m hzero hB
  let r := E₀ *ᵥ a₀ + F₀ *ᵥ u₀
  let μ := 3 * m / 4
  let A := u₀ 0 + μ * t / Z
  let B := u₀ 2 + a₀ 1 / 2 - μ / Z
  let G := 1 / (3 * Z)
  obtain ⟨hrf, _, hrmass, hrx, hrback⟩ :=
    phase_first_variation_moments (η := η) x d t Z m hZ.ne' hX u₀ hl
  change ∀ i : ι, r (Sum.inl i) =
    u₀ 0 + (u₀ 2 + a₀ 1 / 2) * x i ^ 2 + G * (x i ^ 2) ^ 2 at hrf
  change (∑ i : ι, r (Sum.inl i)) = -μ at hrmass
  change (∑ i : ι, x i ^ 2 * r (Sum.inl i)) = M₄ / 3 - d ^ 2 * μ at hrx
  change ∀ i : η, (Fintype.card η : ℝ) * r (Sum.inr i) = μ at hrback
  have hvar (i : ι) : A + B * x i ^ 2 + G * (x i ^ 2) ^ 2 =
      r (Sum.inl i) + μ * W i := by
    rw [hrf]
    dsimp [A, B, W]
    ring
  have hM : (∑ i, x i ^ 2 * (t - x i ^ 2)) = Z * m := by
    rw [← hX, mul_comm]
    simp_rw [W, ← mul_div_assoc, ← sum_div, div_mul_cancel₀ _ hZ.ne']
  have hM₄ : (∑ i, (x i ^ 2) ^ 2 * (t - x i ^ 2)) = Z * M₄ := by
    rw [mul_comm]
    simp_rw [M₄, W, ← mul_div_assoc, ← sum_div, div_mul_cancel₀ _ hZ.ne']
  have hMass : (∑ i, (A + B * x i ^ 2 + G * (x i ^ 2) ^ 2)) = 0 := by
    simp_rw [hvar, sum_add_distrib, ← mul_sum, hrmass, hW]
    ring
  have hMoment : (∑ i, x i ^ 2 * (A + B * x i ^ 2 + G * (x i ^ 2) ^ 2)) =
      M₄ / 3 + (m - d ^ 2) * μ := by
    simp_rw [hvar, mul_add, mul_left_comm (x _ ^ 2) μ, sum_add_distrib, ← mul_sum, hrx, hX]
    ring
  have hRead := (switch_coefficient (fun i => x i ^ 2) t A B (b₀ 0) (b₀ 2)
      m M₄ (M₄ / 3 + (m - d ^ 2) * μ) hZ hSlope hM hM₄ hMass hMoment hbm hbx).2
  have hAt : A + B * t + G * t ^ 2 = r (Sum.inl j) := by
    simpa only [hj, W, sub_self, zero_div, mul_zero, add_zero] using hvar j
  have hCoefficient : -r (Sum.inl j) / (F₀ *ᵥ b₀) (Sum.inl j) =
      (m ^ 2 - 2 * M₄) / 3 - (m - d ^ 2) * μ := by
    rw [neg_div, hbfront, hj, ← hAt]
    change -((A + B * t + (1 / (3 * Z)) * t ^ 2) / (b₀ 0 + b₀ 2 * t)) = _
    rw [hRead]
    ring
  refine ⟨root, a, ?_, ha, ?_⟩
  · change Tendsto (fun k => (root k - m) / s k) l
      (𝓝 ((m ^ 2 - 2 * M₄) / 3 - (m - d ^ 2) * μ))
    rw [← hCoefficient]
    exact hlim
  have hrows : ∀ᶠ k in l, P k = F k := by
    filter_upwards [hn] with k hk
    funext i
    cases i with
    | inl i => exact row_eq false (x i) hk
    | inr i => exact row_eq true d hk
  have hPt : Tendsto P l (𝓝 F₀) := by
    simpa only [zero_smul, add_zero] using tendsto_const_nhds.add (hs.smul hE)
  have hmul : Continuous (fun p : Matrix (ι ⊕ η) (Fin 3) ℝ × (Fin 3 → ℝ) =>
      p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hweights : Tendsto (fun k => P k *ᵥ a k) l (𝓝 w) :=
    hmul.continuousAt.tendsto.comp (hPt.prodMk_nhds ha)
  have hfront : ∀ᶠ k in l, ∀ i : ι, x i ^ 2 < t → 0 < (P k *ᵥ a k) (Sum.inl i) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : x i ^ 2 < t
    · have hiw : 0 < w (Sum.inl i) := by rw [hwf]; exact div_pos (sub_pos.mpr hi) hZ
      filter_upwards [(tendsto_pi_nhds.mp hweights (Sum.inl i)).eventually
        (eventually_gt_nhds hiw)] with k hk _
      exact hk
    · exact Eventually.of_forall fun _ hlt => (hi hlt).elim
  have hback : ∀ᶠ k in l, ∀ i : η, 0 < (P k *ᵥ a k) (Sum.inr i) := by
    rw [Filter.eventually_all]
    intro i
    have hpos : 0 < r (Sum.inr i) := by
      have hh : 0 < (Fintype.card η : ℝ) * r (Sum.inr i) := by
        rw [hrback]
        dsimp [μ]
        positivity
      exact pos_of_mul_pos_right hh (Nat.cast_nonneg _)
    have hv := tendsto_pi_nhds.mp hvarLim (Sum.inr i)
    change Tendsto (fun k => ((s k)⁻¹ • (P k *ᵥ a k - w)) (Sum.inr i)) l
      (𝓝 ((r + (-r (Sum.inl j) / (F₀ *ᵥ b₀) (Sum.inl j)) • (F₀ *ᵥ b₀)) (Sum.inr i))) at hv
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, hwb, hbback, sub_zero,
      mul_zero, add_zero] at hv
    filter_upwards [hspos, hv.eventually (eventually_gt_nhds hpos)] with k hk hkp
    exact pos_of_mul_pos_right hkp (inv_nonneg.mpr hk.le)
  filter_upwards [hrows, heq, hfront, hback] with k hk hke hkp hkb
  rw [← hk]
  change ((P k)ᵀ *ᵥ (P k *ᵥ a k) =
    F₀ᵀ *ᵥ w + s k • ![0, 2 * m, 0] + (root k - m) • y k) ∧ _ at hke
  refine ⟨hke.1.trans ?_, ?_, hkp, hkb⟩
  · rw [hbase]
    funext i
    fin_cases i <;> simp [y, s]
    ring
  · intro i hi
    have hsquare : x i ^ 2 = x j ^ 2 := hi.trans hj.symm
    have habs : |x i| = |x j| :=
      (sq_eq_sq_iff_abs_eq_abs _ _).mp hsquare
    have hcos : Real.cos (x i * h k) = Real.cos (x j * h k) := by
      rw [← Real.cos_abs, ← Real.cos_abs (x j * h k), abs_mul, abs_mul, habs]
    have hr : F k (Sum.inl i) = F k (Sum.inl j) := by
      simp only [F, phaseRow, Sum.elim_inl, signedCos, Bool.false_eq_true, ite_false, hcos]
    have hjzero : (P k *ᵥ a k) (Sum.inl j) = 0 := hke.2
    rw [hk]
    change F k (Sum.inl i) ⬝ᵥ a k = 0
    rw [hr]
    exact hk ▸ hjzero

private theorem grid_root_certificate {n k : ℕ} (odd : Bool) (hk : n < k)
    (a : Fin 3 → ℝ) (m : ℝ) (hb : a 1 ≤ 0) (hg : a 2 ≤ 0) :
    let q := parityModulus odd k
    let h := mesh q
    let d := parityOffset odd
    let threshold := 1 - 2 * m * h ^ 2
    let x := fun i : Front n => (i.1 : ℝ)
    let p := fun c : ℝ => a 0 + a 1 * (1 - c) + a 2 * ((1 - c ^ 2) / h ^ 2)
    let F := phaseRow (η := Back odd) x d fun back z =>
      ![1, 1 - signedCos back z h, (1 - signedCos back z h ^ 2) / h ^ 2]
    p (signedCos true (d + 1) h) < 0 →
    p (signedCos false ((n : ℝ) + 1) h) < 0 →
    Fᵀ *ᵥ (F *ᵥ a) = ![1, 2 * m * h ^ 2, m] →
    (∀ i : Front n, x i ^ 2 = (n : ℝ) ^ 2 → (F *ᵥ a) (Sum.inl i) = 0) →
    (∀ i : Front n, x i ^ 2 < (n : ℝ) ^ 2 → 0 < (F *ᵥ a) (Sum.inl i)) →
    (∀ i : Back odd, 0 < (F *ᵥ a) (Sum.inr i)) →
    let v := fun i : ZMod q => max 0 (p (sample i))
    v ∈ feasible q threshold ∧
    cosineMoment 1 v = threshold ∧ cosineMoment 2 v = threshold ∧
    (∀ w ∈ feasible q threshold, w ≠ v → energy v < energy w) ∧
    (∀ i : ZMod q, 0 < v i ↔
      i.valMinAbs.natAbs < n ∨ sample i = sample ((↑(q / 2) : ℤ) : ZMod q)) ∧
    ∀ i : ZMod q, (i.valMinAbs.natAbs ≤ n ∨
      sample i = sample ((↑(q / 2) : ℤ) : ZMod q)) → 0 ≤ p (sample i) := by
  intro q h d threshold x p F hlo hhi hnormal hz hp hback v
  let emb := gridEmbedding (odd := odd) hk
  let wide := (univ : Finset (Front n ⊕ Back odd)).map emb
  let narrow := wide.filter fun i => 0 < p (sample i)
  let w := fun i : ZMod q => if i ∈ wide then p (sample i) else 0
  obtain ⟨hrow, hmass, hM₁, hM₂⟩ := grid_fit_moments (odd := odd) hk a m hnormal
  change ∀ j, (F *ᵥ a) j = p (sample (emb j)) at hrow
  change ∑ i, w i = 1 at hmass
  change cosineMoment 1 w = threshold at hM₁
  change cosineMoment 2 w = threshold at hM₂
  have hs : 0 < h ^ 2 := sq_pos_of_pos mesh_pos
  have hoff (i : ZMod q) (hi : i ∉ wide) : p (sample i) ≤ 0 := by
    obtain ⟨hlo', hhi'⟩ := sample_between (odd := odd) hk i hi
    exact (dualValue_negative_of_between hs hg hlo' hhi' hlo hhi).le
  have hnonneg (i : ZMod q) (hi : i ∈ wide) : 0 ≤ p (sample i) := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    rw [← hrow]
    cases j with
    | inr j => exact (hback j).le
    | inl j =>
        have hbound : x j ^ 2 ≤ (n : ℝ) ^ 2 := by
          change (j.1 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2
          have hj := mem_Icc.mp j.2
          have ha : |(j.1 : ℝ)| ≤ (n : ℝ) :=
            abs_le.mpr ⟨by exact_mod_cast hj.1, by exact_mod_cast hj.2⟩
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg n)).mpr ha
        rcases hbound.eq_or_lt with hj | hj
        · exact (hz j hj).ge
        · exact (hp j hj).le
  have hw : w = v := by
    funext i
    by_cases hi : i ∈ wide
    · simp [w, v, hi, max_eq_right (hnonneg i hi)]
    · simp [w, v, hi, max_eq_left (hoff i hi)]
  let u := fun i : ZMod q => if i ∈ narrow then p (sample i) else 0
  have hu : u = v := by
    funext i
    by_cases hi : i ∈ narrow
    · have hpos := (mem_filter.mp hi).2
      simp [u, v, hi, max_eq_right hpos.le]
    · have hn : p (sample i) ≤ 0 := by
        by_cases hw : i ∈ wide
        · exact le_of_not_gt fun hh => hi (mem_filter.mpr ⟨hw, hh⟩)
        · exact hoff i hw
      simp [u, v, hi, max_eq_left hn]
  have hnarrow (i : ZMod q) (hi : i ∉ narrow) : p (sample i) ≤ 0 := by
    by_cases hi' : i ∈ wide
    · exact le_of_not_gt fun h => hi (mem_filter.mpr ⟨hi', h⟩)
    · exact hoff i hi'
  rw [hw] at hmass hM₁ hM₂
  obtain ⟨hv, hstrict, _⟩ := exact_support_of_dual_nonpos (sites := narrow)
    (threshold := threshold) hs hb hg (fun i hi => (mem_filter.mp hi).2) hnarrow
    (show ∑ i, u i = 1 by simpa only [hu] using hmass)
    (show cosineMoment 1 u = threshold by simpa only [hu] using hM₁)
    (show cosineMoment 2 u = threshold by simpa only [hu] using hM₂)
  change u ∈ feasible q threshold at hv
  change ∀ w ∈ feasible q threshold, w ≠ u → energy u < energy w at hstrict
  rw [hu] at hv hstrict
  refine ⟨hv, hM₁, hM₂, hstrict, ?_, ?_⟩
  swap
  · intro i hi
    exact hnonneg i ((grid_mem (odd := odd) hk i).mpr hi)
  intro i
  have hgrid := grid_mem (odd := odd) hk i
  change i ∈ wide ↔ i.valMinAbs.natAbs ≤ n ∨
    sample i = sample ((↑(q / 2) : ℤ) : ZMod q) at hgrid
  have hjcast (j : Front n) : ((emb (Sum.inl j)).valMinAbs : ℝ) = x j := by
    have hj := gridRep_centered (odd := odd) hk (Sum.inl j)
    change (emb (Sum.inl j)).valMinAbs = j.1 at hj
    exact congrArg (fun j : ℤ => (j : ℝ)) hj
  have hsquare (j : Front n) :
      (emb (Sum.inl j)).valMinAbs.natAbs < n ↔ x j ^ 2 < (n : ℝ) ^ 2 := by
    rw [← hjcast, ← sq_abs, sq_lt_sq₀ (abs_nonneg _) (Nat.cast_nonneg _),
      ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    exact_mod_cast Iff.rfl
  have hq : n < q / 2 := by
    unfold q parityModulus
    split <;> omega
  constructor
  · intro hv'
    have hpos : 0 < p (sample i) := by
      simpa only [v, lt_max_iff, lt_irrefl, false_or] using hv'
    have hiw : i ∈ wide := by
      by_contra h
      exact (not_lt_of_ge (hoff i h)) hpos
    rcases (hgrid.mp hiw) with hfront | hanti
    · refine Or.inl (lt_of_le_of_ne hfront ?_)
      intro hj
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hiw
      rw [← hrow] at hpos
      cases j with
      | inr j =>
          have hrep' : (emb (Sum.inr j)).valMinAbs.natAbs = q / 2 := by
            exact back_grid_natAbs (odd := odd) hk j
          exact (ne_of_gt hq) (hrep'.symm.trans hj)
      | inl j =>
          have hxeq : |x j| = (n : ℝ) := by
            rw [← hjcast, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast, hj]
          have hxeq' : x j ^ 2 = (n : ℝ) ^ 2 := by rw [← sq_abs (x j), hxeq]
          exact (ne_of_gt hpos) (hz j hxeq')
    · exact Or.inr hanti
  · intro hi
    have hiw : i ∈ wide := hgrid.mpr (hi.imp Nat.le_of_lt id)
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hiw
    simp only [v, lt_max_iff, lt_irrefl, false_or, ← hrow]
    cases j with
    | inr j => exact hback j
    | inl j =>
        apply hp j
        apply (hsquare j).mp
        rcases hi with hj | hj
        · exact hj
        · have hjmin := (sample_antipode_iff _).mp hj
          have hb : (emb (Sum.inl j)).valMinAbs.natAbs ≤ n := by
            have hcenter := gridRep_centered (odd := odd) hk (Sum.inl j)
            change (emb (Sum.inl j)).valMinAbs = j.1 at hcenter
            rw [hcenter]
            have hJ := mem_Icc.mp j.2
            omega
          exact (not_lt_of_ge (hjmin ▸ hb) hq).elim

private theorem cyclic_root_on_parity (n : ℕ) (hn : 2 ≤ n) (odd : Bool) :
    let d := parityOffset odd
    let t := (n : ℝ) ^ 2
    let m₀ := (t - 1) / 5
    let q := parityModulus odd
    let h := fun k => mesh (q k)
    ∃ (root : ℕ → ℝ) (a : ℕ → Fin 3 → ℝ),
      Tendsto (fun k => (root k - m₀) / h k ^ 2) atTop
        (𝓝 ((t - 1) * (63 * d ^ 2 + 47 - 31 * t) / 420)) ∧
      ∀ᶠ k in atTop, ∃ _hk : n < k,
        let threshold := 1 - 2 * root k * h k ^ 2
        let v := fun i : ZMod (q k) => max 0
          (a k 0 + a k 1 * (1 - sample i) + a k 2 * ((1 - sample i ^ 2) / h k ^ 2))
        v ∈ feasible (q k) threshold ∧
        cosineMoment 1 v = threshold ∧ cosineMoment 2 v = threshold ∧
        (∀ w ∈ feasible (q k) threshold, w ≠ v → energy v < energy w) ∧
        (∀ i : ZMod (q k), 0 < v i ↔ i.valMinAbs.natAbs < n ∨
          sample i = sample ((↑(q k / 2) : ℤ) : ZMod (q k))) ∧
        a k 1 ≤ 0 ∧ a k 2 ≤ 0 ∧
        ∀ i : ZMod (q k), (i.valMinAbs.natAbs ≤ n ∨
          sample i = sample ((↑(q k / 2) : ℤ) : ZMod (q k))) →
          0 ≤ a k 0 + a k 1 * (1 - sample i) + a k 2 * ((1 - sample i ^ 2) / h k ^ 2) := by
  intro d t m₀ q h
  have hnpos : 0 < n := by omega
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnn := Nat.cast_nonneg (α := ℝ) n
  have hm : 0 < m₀ := by dsimp [m₀, t]; nlinarith
  have hmhi : m₀ ≤ (n : ℝ) * (n + 2) / 5 := by dsimp [m₀, t]; nlinarith
  obtain ⟨⟨radius, norm, weight⟩, act, _⟩ :=
    (exists_lattice_square_moment_minimizer_on_interval n hnpos m₀).mp ⟨le_rfl, hmhi⟩
  have hradius : radius = t := act.lower_endpoint.mp rfl
  subst radius
  have hhi : t < ((n : ℝ) + 1) ^ 2 := by dsimp [t]; nlinarith
  have hnormal : norm = normalizer n t := act.normalizer_eq
  subst norm
  let Z := normalizer n t
  let x := fun i : Front n => (i.1 : ℝ)
  let i₀ : Front n := ⟨0, mem_Icc.mpr (by omega)⟩
  let i₁ : Front n := ⟨1, mem_Icc.mpr (by omega)⟩
  let j : Front n := ⟨(n : ℤ), mem_Icc.mpr (by omega)⟩
  have hx (i : Front n) : x i ^ 2 ≤ t := by
    have hi := mem_Icc.mp i.2
    have hcast : |x i| ≤ (n : ℝ) := by
      change |(i.1 : ℝ)| ≤ (n : ℝ)
      exact abs_le.mpr ⟨by exact_mod_cast hi.1, by exact_mod_cast hi.2⟩
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hnn).mpr hcast
  obtain ⟨hW, hX⟩ := lattice_window_sums act hhi
  have hZ : 0 < Z := act.normalizer_pos
  have hZsum : (∑ i : Front n, (t - x i ^ 2)) = Z := by
    have hW' : (∑ i : Front n, (t - x i ^ 2) / Z) = 1 := hW
    rwa [← sum_div, div_eq_iff hZ.ne', one_mul] at hW'
  have ht := mesh_tendsto odd
  have hp : ∀ᶠ k in atTop, 0 < h k := Eventually.of_forall fun _ => mesh_pos
  have hj : x j ^ 2 = t := by simp [x, j, t]
  have hroot := phase_root (η := Back odd) ht hp x d t m₀ hm i₀ i₁ j
    (by simp [x, i₀]) (by simp [x, i₁]) hx hj
  dsimp only at hroot
  rw [hZsum] at hroot
  obtain ⟨root, a, hshift, ha, heq⟩ := hroot hZ hW hX
  have hM₄ : (∑ i : Front n, (x i ^ 2) ^ 2 * ((t - x i ^ 2) / Z)) =
      ((n : ℝ) ^ 2 - 1) * (3 * (n : ℝ) ^ 2 - 5) / 35 := by
    dsimp only [x]
    simp_rw [← pow_mul]
    have heq := threshold_lattice_fourth_moment n hnpos
    rw [← Finset.sum_attach] at heq
    exact heq
  rw [hM₄] at hshift
  have hformula :
      (m₀ ^ 2 - 2 * (((n : ℝ) ^ 2 - 1) * (3 * (n : ℝ) ^ 2 - 5) / 35)) / 3 -
        (m₀ - d ^ 2) * (3 * m₀ / 4) = (t - 1) * (63 * d ^ 2 + 47 - 31 * t) / 420 := by
    dsimp [m₀, t]
    ring
  rw [hformula] at hshift
  have hd : 0 ≤ d ∧ d ^ 2 ≤ 1 / 4 := by cases odd <;> norm_num [d, parityOffset]
  have hbneg : ∀ᶠ k in atTop, a k 1 < 0 := by
    refine (tendsto_pi_nhds.mp ha 1).eventually (eventually_lt_nhds ?_)
    change -(t - d ^ 2) / (2 * Z) < 0
    apply div_neg_of_neg_of_pos _ (by positivity)
    dsimp [t]
    nlinarith only [hn2, hd.2]
  have hgneg : ∀ᶠ k in atTop, a k 2 < 0 := by
    refine (tendsto_pi_nhds.mp ha 2).eventually (eventually_lt_nhds ?_)
    change -1 / Z < 0
    exact div_neg_of_neg_of_pos (by norm_num) hZ
  have hnmesh := hp.mono fun _ hk => hk.ne'
  have hlo := polynomial_tendsto ht hnmesh ha true (d + 1)
  have hhi' := polynomial_tendsto ht hnmesh ha false ((n : ℝ) + 1)
  have e₁ := base_dot t Z d (d + 1) hZ.ne' true
  have e₂ := base_dot t Z d ((n : ℝ) + 1) hZ.ne' false
  change baseRow true (d + 1) ⬝ᵥ leading t Z d = (d ^ 2 - (d + 1) ^ 2) / Z at e₁
  change baseRow false ((n : ℝ) + 1) ⬝ᵥ leading t Z d = (t - ((n : ℝ) + 1) ^ 2) / Z at e₂
  rw [e₁] at hlo
  rw [e₂] at hhi'
  have hex₁ := hlo.eventually (eventually_lt_nhds
    (div_neg_of_neg_of_pos (by nlinarith only [hd.1]) hZ))
  have hex₂ := hhi'.eventually (eventually_lt_nhds (div_neg_of_neg_of_pos (sub_neg.mpr hhi) hZ))
  refine ⟨root, a, hshift, ?_⟩
  filter_upwards [eventually_gt_atTop n, heq, hbneg, hgneg, hex₁, hex₂] with k hk he hb hg hlo hhi'
  obtain ⟨hf, h₁, h₂, hopt, hsup, hweak⟩ :=
    grid_root_certificate odd hk (a k) (root k) hb.le hg.le hlo hhi' he.1
      he.2.1 he.2.2.1 he.2.2.2
  exact ⟨hk, hf, h₁, h₂, hopt, hsup, hb.le, hg.le, hweak⟩

private noncomputable def fitValue {q : ℕ} (s : ℝ) (a : Fin 3 → ℝ) (i : ZMod q) : ℝ :=
  a 0 + a 1 * (1 - sample i) + a 2 * ((1 - sample i ^ 2) / s)

private noncomputable def clippedFit {q : ℕ} (s : ℝ) (a : Fin 3 → ℝ) (i : ZMod q) : ℝ :=
  max 0 (fitValue s a i)

private theorem interpolate_fit {q : ℕ} [NeZero q] {s : ℝ}
    {S : Finset (ZMod q)} (hs : 0 < s)
    (a b : Fin 3 → ℝ) (A B t : ℝ) (ht : 0 < t) (ht₁ : t ≤ 1)
    (ha₁ : a 1 ≤ 0) (ha₂ : a 2 ≤ 0) (hb₁ : b 1 ≤ 0) (hb₂ : b 2 ≤ 0)
    (ha_pos : ∀ i ∈ S, 0 ≤ fitValue s a i) (hb_pos : ∀ i ∈ S, 0 < fitValue s b i)
    (ha_off : ∀ i ∉ S, fitValue s a i ≤ 0) (hb_off : ∀ i ∉ S, fitValue s b i ≤ 0)
    (ha_mass : ∑ i : ZMod q, clippedFit s a i = 1) (hb_mass : ∑ i : ZMod q, clippedFit s b i = 1)
    (haM : ∀ r ∈ ({1, 2} : Finset ℕ), cosineMoment r (clippedFit (q := q) s a) = A)
    (hbM : ∀ r ∈ ({1, 2} : Finset ℕ), cosineMoment r (clippedFit (q := q) s b) = B) :
    let θ := (1 - t) * A + t * B
    let c := (1 - t) • a + t • b
    let w := clippedFit s c
    w ∈ feasible q θ ∧ cosineMoment 1 w = θ ∧ cosineMoment 2 w = θ ∧
    (∀ u ∈ feasible q θ, u ≠ w → energy w < energy u) ∧
    (∀ i, 0 < w i ↔ i ∈ S) := by
  intro θ c w
  have hτ : 0 ≤ 1 - t := sub_nonneg.mpr ht₁
  have hc₁ : c 1 ≤ 0 := add_nonpos (mul_nonpos_of_nonneg_of_nonpos hτ ha₁)
    (mul_nonpos_of_nonneg_of_nonpos ht.le hb₁)
  have hc₂ : c 2 ≤ 0 := add_nonpos (mul_nonpos_of_nonneg_of_nonpos hτ ha₂)
    (mul_nonpos_of_nonneg_of_nonpos ht.le hb₂)
  have hlin (i : ZMod q) :
      fitValue s c i = (1 - t) * fitValue s a i + t * fitValue s b i := by
    simp only [fitValue, c, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hp (i : ZMod q) (hi : i ∈ S) : 0 < fitValue s c i := by
    rw [hlin]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hτ (ha_pos i hi)) (mul_pos ht (hb_pos i hi))
  have hn (i : ZMod q) (hi : i ∉ S) : fitValue s c i ≤ 0 := by
    rw [hlin]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hτ (ha_off i hi))
      (mul_nonpos_of_nonneg_of_nonpos ht.le (hb_off i hi))
  have hw (i : ZMod q) : w i = (1 - t) * clippedFit s a i + t * clippedFit s b i := by
    change max 0 (fitValue s c i) = _
    by_cases hi : i ∈ S
    · rw [max_eq_right (hp i hi).le, hlin]
      simp only [clippedFit, max_eq_right (ha_pos i hi), max_eq_right (hb_pos i hi).le]
    · simp only [max_eq_left (hn i hi), clippedFit, max_eq_left (ha_off i hi),
        max_eq_left (hb_off i hi), mul_zero, add_zero]
  have hmass : ∑ i, w i = 1 := by
    simp_rw [hw, sum_add_distrib, ← mul_sum, ha_mass, hb_mass]
    ring
  have hmoment (r : ℕ) (hr : r ∈ ({1, 2} : Finset ℕ)) : cosineMoment r w = θ := by
    change (∑ i : ZMod q, w i * _) = θ
    simp_rw [hw, add_mul, mul_assoc, sum_add_distrib, ← mul_sum]
    change (1 - t) * cosineMoment r (clippedFit (q := q) s a) +
      t * cosineMoment r (clippedFit (q := q) s b) = θ
    rw [haM r hr, hbM r hr]
  have hM₁ := hmoment 1 (by simp)
  have hM₂ := hmoment 2 (by simp)
  let u := fun i => if i ∈ S then fitValue s c i else 0
  have hu : u = w := by
    funext i
    by_cases hi : i ∈ S
    · simp [u, hi, w, clippedFit, max_eq_right (hp i hi).le]
    · simp [u, hi, w, clippedFit, max_eq_left (hn i hi)]
  obtain ⟨hfeas, hstrict, _⟩ := exact_support_of_dual_nonpos (sites := S)
    (threshold := θ) hs hc₁ hc₂ hp hn
    (show ∑ i, u i = 1 by simpa only [hu] using hmass)
    (show cosineMoment 1 u = θ by simpa only [hu] using hM₁)
    (show cosineMoment 2 u = θ by simpa only [hu] using hM₂)
  change u ∈ feasible q θ at hfeas
  change ∀ v ∈ feasible q θ, v ≠ u → energy u < energy v at hstrict
  rw [hu] at hfeas hstrict
  refine ⟨hfeas, hM₁, hM₂, hstrict, fun i => ?_⟩
  change 0 < max 0 (fitValue s c i) ↔ i ∈ S
  simp only [lt_max_iff, lt_irrefl, false_or]
  exact ⟨fun h => by_contra fun hi => (not_lt_of_ge (hn i hi)) h, hp i⟩

private theorem fixed_budget_fit (odd : Bool) (n : ℕ) (hn : 0 < n) {m : ℝ}
    (hm : 0 < m) (hlo : ((n : ℝ) ^ 2 - 1) / 5 ≤ m)
    (hhi : m < (n : ℝ) * (n + 2) / 5) :
    ∀ᶠ k in atTop, ∃ hk : n < k, ∃ a : Fin 3 → ℝ,
      let q := parityModulus odd k
      let s := mesh q ^ 2
      let θ := 1 - 2 * m * s
      let S := (univ : Finset (Front n ⊕ Back odd)).map (gridEmbedding hk)
      a 1 ≤ 0 ∧ a 2 ≤ 0 ∧ (∀ i ∈ S, 0 < fitValue s a i) ∧
      (∀ i ∉ S, fitValue s a i ≤ 0) ∧
      (∑ i : ZMod q, clippedFit s a i) = 1 ∧
      ∀ r ∈ ({1, 2} : Finset ℕ), cosineMoment r (clippedFit (q := q) s a) = θ := by
  obtain ⟨⟨t, Z, w⟩, act, _⟩ :=
    (exists_lattice_square_moment_minimizer_on_interval n hn m).mp ⟨hlo, hhi.le⟩
  have ht : t < ((n : ℝ) + 1) ^ 2 := by
    refine act.radius_upper.lt_of_ne ?_
    intro he
    exact hhi.ne (act.upper_endpoint.mpr he)
  filter_upwards [grid_fit_on_parity m hm hn act ht odd] with k ha
  obtain ⟨hk, a, hb, hg, hLeft, hRight, hpos, hmass, hM₁, hM₂⟩ := ha
  let q := parityModulus odd k
  let s := mesh q ^ 2
  let S := (univ : Finset (Front n ⊕ Back odd)).map (gridEmbedding hk)
  let u := fun i : ZMod q => if i ∈ S then fitValue s a i else 0
  have hneg (i : ZMod q) (hi : i ∉ S) : fitValue s a i ≤ 0 := by
    obtain ⟨hl, hh⟩ := sample_between (odd := odd) hk i hi
    exact (dualValue_negative_of_between (sq_pos_of_pos mesh_pos) hg.le hl hh hLeft hRight).le
  change ∀ i ∈ S, 0 < fitValue s a i at hpos
  have he : u = clippedFit s a := by
    funext i
    by_cases hi : i ∈ S
    · simp [u, hi, clippedFit, max_eq_right (hpos i hi).le]
    · simp [u, hi, clippedFit, max_eq_left (hneg i hi)]
  change ∑ i, u i = 1 at hmass
  change cosineMoment 1 u = 1 - 2 * m * s at hM₁
  change cosineMoment 2 u = 1 - 2 * m * s at hM₂
  rw [he] at hmass hM₁ hM₂
  refine ⟨hk, a, hb.le, hg.le, hpos, hneg, hmass, ?_⟩
  intro r hr
  simp only [mem_insert, mem_singleton] at hr
  rcases hr with rfl | rfl
  · exact hM₁
  · exact hM₂

/-- At a fixed lattice activation index, each parity of sufficiently fine cycles has a
single change of front support in a fixed neighborhood of the lattice budget. The
boundary pair is absent at equality. The limit gives the displacement in mesh squared. -/
theorem cyclic_activation_shift (n : ℕ) (hn : 2 ≤ n) (odd : Bool) :
    let clip := fun x : ℝ => max 0 x
    let d := parityOffset odd
    let m₀ := ((n : ℝ) ^ 2 - 1) / 5
    let q := parityModulus odd
    let h := fun k => mesh (q k)
    ∃ (ε : ℝ) (root : ℕ → ℝ), 0 < ε ∧
      Tendsto (fun k => (root k - m₀) / h k ^ 2) atTop
        (𝓝 (((n : ℝ) ^ 2 - 1) * (63 * d ^ 2 + 47 - 31 * (n : ℝ) ^ 2) / 420)) ∧
      ∀ᶠ k in atTop, root k ∈ Set.Ioo (m₀ - ε) (m₀ + ε) ∧
        ∀ m ∈ Set.Icc (m₀ - ε) (m₀ + ε),
          let θ := 1 - 2 * m * h k ^ 2
          ∃ v ∈ feasible (q k) θ, cosineMoment 1 v = θ ∧ cosineMoment 2 v = θ ∧
            (∀ w ∈ feasible (q k) θ, w ≠ v → energy v < energy w) ∧
            ∀ i : ZMod (q k), 0 < clip (v i) ↔ |(i.valMinAbs : ℝ)| < n ∨
              (root k < m ∧ |(i.valMinAbs : ℝ)| = n) ∨
              sample i = sample ((↑(q k / 2) : ℤ) : ZMod (q k)) := by
  intro clip d m₀ q h
  let ε : ℝ := (2 * (n : ℝ) - 1) / 10
  let low := m₀ - ε
  let high := m₀ + ε
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hlow : 0 < low := by dsimp [low, m₀, ε]; nlinarith
  have hhigh : 0 < high := by dsimp [high]; linarith
  have hpred : (↑(n - 1) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hl₁ : (((n - 1 : ℕ) : ℝ) ^ 2 - 1) / 5 ≤ low := by
    rw [hpred]; dsimp [low, m₀, ε]; nlinarith
  have hl₂ : low < ((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ) + 2) / 5 := by
    rw [hpred]; dsimp [low, m₀, ε]; nlinarith
  have hh₁ : ((n : ℝ) ^ 2 - 1) / 5 ≤ high := by change m₀ ≤ m₀ + ε; linarith
  have hh₂ : high < (n : ℝ) * (n + 2) / 5 := by dsimp [high, m₀, ε]; nlinarith
  obtain ⟨root, a, hr, ha⟩ := cyclic_root_on_parity n hn odd
  have hmesh : Tendsto h atTop (𝓝 0) := mesh_tendsto odd
  have hs : Tendsto (fun k => h k ^ 2) atTop (𝓝 0) := by simpa using hmesh.pow 2
  have hsmall := (hs.mul hr).congr' (show
      (fun k => h k ^ 2 * ((root k - m₀) / h k ^ 2)) =ᶠ[atTop]
        (fun k => root k - m₀) from by
    filter_upwards with k
    have hk : h k ≠ 0 := (mesh_pos (q := q k)).ne'
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 hk)])
  have hroot : Tendsto root atTop (𝓝 m₀) := by
    simpa only [zero_mul, zero_add, sub_add_cancel] using hsmall.add_const m₀
  have hint : ∀ᶠ k in atTop, root k ∈ Set.Ioo low high :=
    hroot.eventually (Ioo_mem_nhds (by dsimp [low]; linarith) (by dsimp [high]; linarith))
  refine ⟨ε, root, hε, hr, ?_⟩
  filter_upwards [hint, ha, fixed_budget_fit odd (n - 1) (by omega) hlow hl₁ hl₂,
      fixed_budget_fit odd n (by omega) hhigh hh₁ hh₂] with k hkI hk hl hh
  obtain ⟨_, hf, hM₁, hM₂, ho, hsupport, ha₁, ha₂, hnonneg⟩ := hk
  obtain ⟨hkL, bL, hL₁, hL₂, hLpos, hLoff, hLmass, hLM⟩ := hl
  obtain ⟨hkH, bH, hH₁, hH₂, hHpos, hHoff, hHmass, hHM⟩ := hh
  let s := h k ^ 2
  let θ := fun m : ℝ => 1 - 2 * m * s
  let A := a k
  let Sₗ := (univ : Finset (Front (n - 1) ⊕ Back odd)).map (gridEmbedding hkL)
  let Sₕ := (univ : Finset (Front n ⊕ Back odd)).map (gridEmbedding hkH)
  let anti := fun i : ZMod (q k) => sample i = sample ((↑(q k / 2) : ℤ) : ZMod (q k))
  have hSl (i : ZMod (q k)) : i ∈ Sₗ ↔ i.valMinAbs.natAbs < n ∨ anti i := by
    rw [show i ∈ Sₗ ↔ _ from grid_mem hkL i]
    exact or_congr (by omega) Iff.rfl
  have hSh (i : ZMod (q k)) : i ∈ Sₕ ↔ i.valMinAbs.natAbs ≤ n ∨ anti i :=
    grid_mem hkH i
  have hsub : Sₗ ⊆ Sₕ := fun i hi => (hSh i).mpr (((hSl i).mp hi).imp Nat.le_of_lt id)
  have hpos₀ (i : ZMod (q k)) : 0 < fitValue s A i ↔ i ∈ Sₗ := by
    rw [hSl, ← hsupport]
    simp only [lt_max_iff, lt_irrefl, false_or]
    rfl
  have hoff₀ (S : Finset (ZMod (q k))) (hS : Sₗ ⊆ S)
      (i : ZMod (q k)) (hi : i ∉ S) : fitValue s A i ≤ 0 :=
    le_of_not_gt fun h => hi (hS ((hpos₀ i).mp h))
  have haₘ : ∀ r ∈ ({1, 2} : Finset ℕ), cosineMoment r (clippedFit (q := q k) s A) = θ (root k) := by
    intro r hr
    simp only [mem_insert, mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hM₁
    · exact hM₂
  refine ⟨hkI, fun m hm => ?_⟩
  have abs_index (i : ZMod (q k)) : |(i.valMinAbs : ℝ)| = (i.valMinAbs.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  simp only [abs_index, Nat.cast_lt, Nat.cast_inj]
  rcases lt_trichotomy m (root k) with hlt | rfl | hgt
  · let z := (root k - m) / (root k - low)
    have hd : 0 < root k - low := sub_pos.mpr hkI.1
    have hz : 0 < z := div_pos (sub_pos.mpr hlt) hd
    have hz₁ : z ≤ 1 := (div_le_one (by exact hd)).mpr (sub_le_sub_left hm.1 _)
    have hθ : (1 - z) * θ (root k) + z * θ low = θ m := by
      dsimp [z, θ]
      field_simp [hd.ne']
      ring
    obtain ⟨hf', hM₁', hM₂', hopt, hsup⟩ :=
      interpolate_fit (S := Sₗ) (sq_pos_of_pos (mesh_pos (q := q k)))
        A bL (θ (root k)) (θ low) z hz hz₁ ha₁ ha₂ hL₁ hL₂
        (fun i hi => ((hpos₀ i).mpr hi).le) hLpos (hoff₀ Sₗ Subset.rfl) hLoff
        hf.2.1 hLmass haₘ hLM
    rw [hθ] at hf' hM₁' hM₂' hopt
    refine ⟨_, hf', hM₁', hM₂', hopt, fun i => ?_⟩
    simp only [clip, lt_max_iff, lt_irrefl, false_or, hsup, hSl]
    simp only [(not_lt_of_ge hlt.le), false_and, false_or, anti]
  · refine ⟨_, hf, hM₁, hM₂, ho, fun i => ?_⟩
    simp only [clip, lt_max_iff, lt_irrefl, false_or, hsupport]
    simp only [lt_irrefl, false_and, false_or, q]
  · let z := (m - root k) / (high - root k)
    have hd : 0 < high - root k := sub_pos.mpr hkI.2
    have hz : 0 < z := div_pos (sub_pos.mpr hgt) hd
    have hz₁ : z ≤ 1 := (div_le_one (by exact hd)).mpr (sub_le_sub_right hm.2 _)
    have hθ : (1 - z) * θ (root k) + z * θ high = θ m := by
      dsimp [z, θ]
      field_simp [hd.ne']
      ring
    obtain ⟨hf', hM₁', hM₂', hopt, hsup⟩ :=
      interpolate_fit (S := Sₕ) (sq_pos_of_pos (mesh_pos (q := q k)))
        A bH (θ (root k)) (θ high) z hz hz₁ ha₁ ha₂ hH₁ hH₂
        (fun i hi => hnonneg i ((hSh i).mp hi)) hHpos (hoff₀ Sₕ hsub) hHoff
        hf.2.1 hHmass haₘ hHM
    rw [hθ] at hf' hM₁' hM₂' hopt
    refine ⟨_, hf', hM₁', hM₂', hopt, fun i => ?_⟩
    simp only [clip, lt_max_iff, lt_irrefl, false_or, hsup, hSh, hgt, true_and, anti, ← or_assoc]
    exact or_congr (show i.valMinAbs.natAbs ≤ n ↔ i.valMinAbs.natAbs < n ∨
      i.valMinAbs.natAbs = n by omega) Iff.rfl

end D5.S3.Fourier.Asymptotics.CyclicActivationShift
