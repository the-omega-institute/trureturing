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

private theorem shared_gram_at_zero {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ)
    (row a : ι → ℝ) (k : ℝ) (hzero : row ⬝ᵥ a = 0) :
    (G + k • vecMulVec row row) *ᵥ a = G *ᵥ a := by
  rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, hzero]
  simp

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


private theorem repeated_row_boundary {ι : Type*} [Fintype ι]
    (F : Matrix ι (Fin 3) ℝ) (hF : Function.Injective F.mulVec)
    (row narrow wide : Fin 3 → ℝ) {copies : ℝ} (hc : 0 ≤ copies)
    (heq : (Fᵀ * F) *ᵥ narrow = (Fᵀ * F + copies • vecMulVec row row) *ᵥ wide) :
    ∃ factor : ℝ, 0 < factor ∧ row ⬝ᵥ narrow = factor * (row ⬝ᵥ wide) ∧
      (row ⬝ᵥ wide = 0 → narrow = wide) := by
  let G := Fᵀ * F
  have hdet : IsUnit G.det := isUnit_iff_ne_zero.mpr (gram_det_ne_zero F hF)
  have hinj : Function.Injective G.mulVec :=
    mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hdet)
  let z := G⁻¹ *ᵥ row
  have hz : G *ᵥ z = row := by
    dsimp only [z]
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hpos : 0 ≤ row ⬝ᵥ z := by
    rw [dotProduct_comm, ← hz, ← mulVec_mulVec, dotProduct_transpose_mulVec]
    exact sum_nonneg fun i _ => mul_self_nonneg _
  have hn : narrow = wide + (copies * (row ⬝ᵥ wide)) • z := by
    apply hinj
    rw [heq, add_mulVec, mulVec_add, mulVec_smul, hz, smul_mulVec, vecMulVec_mulVec]
    congr 1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring
  refine ⟨1 + copies * (row ⬝ᵥ z), by positivity, ?_, ?_⟩
  · rw [hn, dotProduct_add, dotProduct_smul]
    ring
  · intro hzero
    exact hinj (heq.trans (shared_gram_at_zero G row wide copies hzero))


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
    fin_cases i <;> simp [y, s] <;> ring
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

end D5.S3.Fourier.Asymptotics.CyclicActivationShift
