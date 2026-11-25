/- GID: D5/S3/Fourier/Asymptotics/CyclicEventualSupport
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicEventualSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Eventual exact support of the squared-mass minimizer with two cosine constraints. -/

import D5.S3.Fourier.Asymptotics.CyclicParityLimit
import D5.S3.Fourier.Asymptotics.CyclicSupportCertificate
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix

/-! The joint cosine constraints determine a Gram solve on the front window
together with the nearest antipodal residues. The rescaled variation determines the
signs at the front activation boundary. -/

open Finset Filter Matrix
open scoped Topology
open D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open D5.S3.Fourier.Asymptotics.CyclicParityCorrection
open D5.S3.Fourier.Asymptotics.CyclicParityLimit
open D5.S3.Fourier.Asymptotics.CyclicSupportCertificate

noncomputable section

namespace D5.S3.Fourier.Asymptotics.CyclicEventualSupport

set_option autoImplicit false

private theorem gram_det_ne_zero {ι : Type*} [Fintype ι] (F : Matrix ι (Fin 3) ℝ)
    (hF : Function.Injective F.mulVec) : (Fᵀ * F).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (isUnit_iff_isUnit_det _).mp
  apply mulVec_injective_iff_isUnit.mp
  change Function.Injective (Fᵀ * F).mulVecLin
  rw [← LinearMap.ker_eq_bot, ker_mulVecLin_transpose_mul_self, LinearMap.ker_eq_bot]
  exact hF

private theorem gram_variation {ι : Type*} [Fintype ι] {κ : Type*} {l : Filter κ}
    {s : κ → ℝ} (hs : Tendsto s l (𝓝 0))
    {E : κ → Matrix ι (Fin 3) ℝ} {E₀ : Matrix ι (Fin 3) ℝ} (hE : Tendsto E l (𝓝 E₀))
    (F₀ : Matrix ι (Fin 3) ℝ) (hF : Function.Injective F₀.mulVec)
    (a₀ b₁ : Fin 3 → ℝ) :
    let F := fun h => F₀ + s h • E h
    let w := F₀ *ᵥ a₀
    ∃ (u : κ → Fin 3 → ℝ) (u₀ : Fin 3 → ℝ),
      Tendsto u l (𝓝 u₀) ∧
      F₀ᵀ *ᵥ (E₀ *ᵥ a₀ + F₀ *ᵥ u₀) = b₁ - E₀ᵀ *ᵥ w ∧
      ∀ᶠ h in l, (F h)ᵀ *ᵥ (F h *ᵥ (a₀ + s h • u h)) = F₀ᵀ *ᵥ w + s h • b₁ := by
  intro F w
  let M := fun A : Matrix ι (Fin 3) ℝ => Aᵀ * A
  let rhs := fun A B : Matrix ι (Fin 3) ℝ => b₁ - Bᵀ *ᵥ w - Aᵀ *ᵥ (B *ᵥ a₀)
  let u := fun h => (M (F h))⁻¹ *ᵥ rhs (F h) (E h)
  let u₀ := (M F₀)⁻¹ *ᵥ rhs F₀ E₀
  have hFt : Tendsto F l (𝓝 F₀) := by
    simpa only [zero_smul, add_zero] using tendsto_const_nhds.add (hs.smul hE)
  have hMc : Continuous M := continuous_id.matrix_transpose.matrix_mul continuous_id
  have hMt := hMc.continuousAt.tendsto.comp hFt
  have hdet : (M F₀).det ≠ 0 := gram_det_ne_zero F₀ hF
  have hMi : Tendsto (fun h => (M (F h))⁻¹) l (𝓝 ((M F₀)⁻¹)) := by
    apply (continuousAt_matrix_inv (M F₀) ?_).tendsto.comp hMt
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  have hrhs : Continuous (fun p : Matrix ι (Fin 3) ℝ × Matrix ι (Fin 3) ℝ =>
      rhs p.1 p.2) :=
    (continuous_const.sub (continuous_snd.matrix_transpose.matrix_mulVec continuous_const)).sub
      (continuous_fst.matrix_transpose.matrix_mulVec
        (continuous_snd.matrix_mulVec continuous_const))
  have hmul : Continuous (fun p : Matrix (Fin 3) (Fin 3) ℝ × (Fin 3 → ℝ) =>
      p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  refine ⟨u, u₀, hmul.continuousAt.tendsto.comp
    (hMi.prodMk_nhds (hrhs.continuousAt.tendsto.comp (hFt.prodMk_nhds hE))), ?_, ?_⟩
  · have hu : M F₀ *ᵥ u₀ = rhs F₀ E₀ := by
      dsimp only [u₀]
      rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]
    rw [mulVec_add, mulVec_mulVec (v := u₀) F₀ᵀ F₀]
    change _ + M F₀ *ᵥ u₀ = _
    rw [hu]
    dsimp only [rhs]
    abel
  · have hdet_t := (continuous_id.matrix_det.continuousAt (x := M F₀)).tendsto.comp hMt
    filter_upwards [hdet_t.eventually_ne hdet] with h hh
    change (M (F h)).det ≠ 0 at hh
    have hu : M (F h) *ᵥ u h = rhs (F h) (E h) := by
      dsimp only [u]
      rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hh), one_mulVec]
    have hbase : F h *ᵥ a₀ = w + s h • (E h *ᵥ a₀) := by
      simp only [F, w, add_mulVec, smul_mulVec]
    have htranspose : (F h)ᵀ *ᵥ w = F₀ᵀ *ᵥ w + s h • ((E h)ᵀ *ᵥ w) := by
      simp only [F, transpose_add, transpose_smul, add_mulVec, smul_mulVec]
    have hstep : (F h)ᵀ *ᵥ (F h *ᵥ u h) = rhs (F h) (E h) := by
      rw [mulVec_mulVec]
      exact hu
    simp only [mulVec_add, mulVec_smul, hbase, htranspose, hstep]
    dsimp only [rhs]
    rw [smul_sub, smul_sub]
    abel

private def signedCos (back : Bool) (z h : ℝ) : ℝ :=
  if back then -Real.cos (z * h) else Real.cos (z * h)

private def baseRow (back : Bool) (z : ℝ) : Fin 3 → ℝ :=
  ![1, if back then 2 else 0, z ^ 2]

private def variationRow (back : Bool) (z h : ℝ) : Fin 3 → ℝ :=
  ![0, if back then -cosineSecond z h else cosineSecond z h,
    -2 * cosineFourth z h - cosineSecond z h ^ 2]

private def limitRow (back : Bool) (z : ℝ) : Fin 3 → ℝ :=
  ![0, if back then -z ^ 2 / 2 else z ^ 2 / 2, -z ^ 4 / 3]

private theorem variationRow_tendsto {κ : Type*} {l : Filter κ} {h : κ → ℝ}
    (ht : Tendsto h l (𝓝 0)) (hn : ∀ᶠ k in l, h k ≠ 0) (back : Bool) (z : ℝ) :
    Tendsto (fun k => variationRow back z (h k)) l (𝓝 (limitRow back z)) := by
  have hc := cosineSecond_tendsto ht hn z
  have hq := cosineFourth_tendsto ht hn z
  have hlast : Tendsto (fun k => -2 * cosineFourth z (h k) - cosineSecond z (h k) ^ 2)
      l (𝓝 (-z ^ 4 / 3)) := by
    convert (hq.const_mul (-2)).sub (hc.pow 2) using 1
    congr 1
    ring
  refine tendsto_pi_nhds.mpr fun i => ?_
  fin_cases i
  · exact tendsto_const_nhds
  · cases back
    · simpa [variationRow, limitRow] using hc
    · simpa [variationRow, limitRow, neg_div] using hc.neg
  · simpa [variationRow, limitRow] using hlast

private theorem row_eq (back : Bool) (z : ℝ) {h : ℝ} (hn : h ≠ 0) :
    baseRow back z + (h ^ 2) • variationRow back z h =
      ![1, 1 - signedCos back z h, (1 - signedCos back z h ^ 2) / h ^ 2] := by
  have hd := cosineSecond_eq z hn
  have he : Real.cos (z * h) = 1 - h ^ 2 * cosineSecond z h := by linarith only [hd]
  have hx : cosineSecond z h = z ^ 2 / 2 - h ^ 2 * cosineFourth z h := rfl
  funext i
  fin_cases i
  · simp [baseRow, variationRow]
  · cases back
    · simp [baseRow, variationRow, signedCos, he]
    · simp [baseRow, variationRow, signedCos, he]
      ring
  · cases back <;> simp [baseRow, variationRow, signedCos, he] <;>
      field_simp [hn] <;> linear_combination -2 * h ^ 2 * hx

private theorem dot_three (a b c : ℝ) (v : Fin 3 → ℝ) :
    ![a, b, c] ⬝ᵥ v = a * v 0 + b * v 1 + c * v 2 := by
  simp [dotProduct, Fin.sum_univ_succ, add_assoc]

private def leading (t Z d : ℝ) : Fin 3 → ℝ := ![t / Z, -(t - d ^ 2) / (2 * Z), -1 / Z]

private theorem base_dot (t Z d z : ℝ) (hZ : Z ≠ 0) (back : Bool) :
    baseRow back z ⬝ᵥ leading t Z d = if back then (d ^ 2 - z ^ 2) / Z else (t - z ^ 2) / Z := by
  cases back <;> simp [baseRow, leading] <;> field_simp [hZ] <;> ring

private theorem polynomial_eq (back : Bool) (z : ℝ) {h : ℝ} (hn : h ≠ 0) (v : Fin 3 → ℝ) :
    (baseRow back z + (h ^ 2) • variationRow back z h) ⬝ᵥ v =
      v 0 + v 1 * (1 - signedCos back z h) + v 2 * ((1 - signedCos back z h ^ 2) / h ^ 2) := by
  rw [row_eq back z hn, dot_three]
  ring

private theorem polynomial_tendsto {κ : Type*} {l : Filter κ} {h : κ → ℝ}
    (ht : Tendsto h l (𝓝 0)) (hn : ∀ᶠ k in l, h k ≠ 0)
    {v : κ → Fin 3 → ℝ} {v₀ : Fin 3 → ℝ} (hv : Tendsto v l (𝓝 v₀)) (back : Bool) (z : ℝ) :
    Tendsto (fun k => v k 0 + v k 1 * (1 - signedCos back z (h k)) +
      v k 2 * ((1 - signedCos back z (h k) ^ 2) / h k ^ 2)) l (𝓝 (baseRow back z ⬝ᵥ v₀)) := by
  have hr : Tendsto (fun k => baseRow back z + (h k ^ 2) • variationRow back z (h k))
      l (𝓝 (baseRow back z)) := by
    simpa using tendsto_const_nhds.add ((ht.pow 2).smul (variationRow_tendsto ht hn back z))
  have hp : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 ⬝ᵥ p.2) :=
    continuous_fst.dotProduct continuous_snd
  apply (hp.continuousAt.tendsto.comp (hr.prodMk_nhds hv)).congr'
  filter_upwards [hn] with k hk
  exact polynomial_eq back z hk (v k)

private def phaseRow {ι η : Type*} (x : ι → ℝ) (d : ℝ)
    (f : Bool → ℝ → Fin 3 → ℝ) : Matrix (ι ⊕ η) (Fin 3) ℝ :=
  fun i => i.elim (fun j => f false (x j)) (fun _ => f true d)

private theorem phase_injective {ι η : Type*} [Nonempty η] (x : ι → ℝ) (d : ℝ)
    (i₀ i₁ : ι) (h₀ : x i₀ = 0) (h₁ : x i₁ = 1) :
    Function.Injective (phaseRow (η := η) x d baseRow).mulVec := by
  intro a b hab
  obtain ⟨j⟩ := ‹Nonempty η›
  have eqAt (i : ι ⊕ η) :=
    congrFun hab i
  have e₀ : a 0 = b 0 := by
    have h := eqAt (Sum.inl i₀)
    change baseRow false (x i₀) ⬝ᵥ a = baseRow false (x i₀) ⬝ᵥ b at h
    rw [h₀] at h
    change ![1, 0, (0 : ℝ) ^ 2] ⬝ᵥ a = ![1, 0, (0 : ℝ) ^ 2] ⬝ᵥ b at h
    simpa only [dot_three, one_mul, zero_pow two_ne_zero, zero_mul, add_zero] using h
  have e₂ : a 2 = b 2 := by
    have h := eqAt (Sum.inl i₁)
    change baseRow false (x i₁) ⬝ᵥ a = baseRow false (x i₁) ⬝ᵥ b at h
    rw [h₁] at h
    change ![1, 0, (1 : ℝ) ^ 2] ⬝ᵥ a = ![1, 0, (1 : ℝ) ^ 2] ⬝ᵥ b at h
    simp only [dot_three, one_pow, one_mul, zero_mul, add_zero, e₀, add_right_inj] at h
    exact h
  have e₁ : a 1 = b 1 := by
    have h := eqAt (Sum.inr j)
    change ![1, 2, d ^ 2] ⬝ᵥ a = ![1, 2, d ^ 2] ⬝ᵥ b at h
    simp only [dot_three, one_mul, e₀, e₂] at h
    linarith only [h]
  funext i
  fin_cases i
  · exact e₀
  · exact e₁
  · exact e₂

private theorem phase_moment {ι η : Type*} [Fintype ι] [Fintype η]
    (x : ι → ℝ) (d : ℝ) (f : Bool → ℝ → Fin 3 → ℝ) (v : ι ⊕ η → ℝ) (j : Fin 3) :
    ((phaseRow x d f)ᵀ *ᵥ v) j =
      (∑ i : ι, f false (x i) j * v (Sum.inl i)) + ∑ i : η, f true d j * v (Sum.inr i) := by
  change (∑ i : ι ⊕ η, phaseRow x d f i j * v i) = _
  rw [Fintype.sum_sum_type]
  rfl

private theorem phase_solution {ι η κ : Type*} [Fintype ι] [Fintype η] [Nonempty η]
    {l : Filter κ} {h : κ → ℝ} (ht : Tendsto h l (𝓝 0)) (hp : ∀ᶠ k in l, 0 < h k)
    (x : ι → ℝ) (d t Z m : ℝ) (hZ : 0 < Z) (hm : 0 < m)
    (i₀ i₁ : ι) (h₀ : x i₀ = 0) (h₁ : x i₁ = 1)
    (hx : ∀ i, x i ^ 2 ≤ t) (hboundary : (∃ i, x i ^ 2 = t) → d ^ 2 < m)
    (hW : ∑ i, (t - x i ^ 2) / Z = 1)
    (hX : ∑ i, x i ^ 2 * ((t - x i ^ 2) / Z) = m) :
    let F := fun k => phaseRow (η := η) x d fun back z =>
      ![1, 1 - signedCos back z (h k), (1 - signedCos back z (h k) ^ 2) / h k ^ 2]
    ∃ a : κ → Fin 3 → ℝ, Tendsto a l (𝓝 (leading t Z d)) ∧
      ∀ᶠ k in l, (F k)ᵀ *ᵥ (F k *ᵥ a k) = ![1, 2 * m * h k ^ 2, m] ∧
        ∀ i, 0 < (F k *ᵥ a k) i := by
  intro F
  let F₀ := phaseRow (η := η) x d baseRow
  let E := fun k => phaseRow (η := η) x d fun back z => variationRow back z (h k)
  let E₀ := phaseRow (η := η) x d limitRow
  let a₀ := leading t Z d
  let w := F₀ *ᵥ a₀
  let s := fun k => h k ^ 2
  let b₁ : Fin 3 → ℝ := ![0, 2 * m, 0]
  let W := fun i => (t - x i ^ 2) / Z
  have hn := hp.mono fun _ hk => hk.ne'
  have hE : Tendsto E l (𝓝 E₀) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    cases i with
    | inl i => exact variationRow_tendsto ht hn false (x i)
    | inr i => exact variationRow_tendsto ht hn true d
  have hwf (i : ι) : w (Sum.inl i) = W i := by
    simpa only [w, Matrix.mulVec, F₀, phaseRow, Sum.elim_inl, a₀, W, Bool.false_eq_true,
      ite_false] using base_dot t Z d (x i) hZ.ne' false
  have hwb (i : η) : w (Sum.inr i) = 0 := by
    simpa only [w, Matrix.mulVec, F₀, phaseRow, Sum.elim_inr, a₀, ite_true, sub_self, zero_div]
      using base_dot t Z d d hZ.ne' true
  have hbase : F₀ᵀ *ᵥ w = ![1, 0, m] := by
    funext j
    fin_cases j
    · simpa [Matrix.mulVec, dotProduct, transpose_apply, Fintype.sum_sum_type,
        F₀, phaseRow, baseRow, hwf, hwb, W] using hW
    · simp [Matrix.mulVec, dotProduct, transpose_apply, Fintype.sum_sum_type,
        F₀, phaseRow, baseRow, hwb]
    · simpa [Matrix.mulVec, dotProduct, transpose_apply, Fintype.sum_sum_type,
        F₀, phaseRow, baseRow, hwf, hwb, W] using hX
  obtain ⟨u, u₀, hu, hlimit, heq⟩ :=
    gram_variation (ht.pow 2 |>.congr' (Eventually.of_forall fun _ => rfl) |>.trans
      (by simp)) hE F₀ (phase_injective x d i₀ i₁ h₀ h₁) a₀ b₁
  let a := fun k => a₀ + s k • u k
  let r := E₀ *ᵥ a₀ + F₀ *ᵥ u₀
  have ha : Tendsto a l (𝓝 a₀) := by
    simpa [s] using tendsto_const_nhds.add ((ht.pow 2).smul hu)
  have hrf (i : ι) : r (Sum.inl i) =
      u₀ 0 + (u₀ 2 + a₀ 1 / 2) * x i ^ 2 + (1 / (3 * Z)) * (x i ^ 2) ^ 2 := by
    change (![0, x i ^ 2 / 2, -x i ^ 4 / 3] ⬝ᵥ a₀) +
      (![1, 0, x i ^ 2] ⬝ᵥ u₀) = _
    rw [dot_three, dot_three]
    have ha₂ : a₀ 2 = -1 / Z := rfl
    rw [ha₂]
    field_simp [hZ.ne']
    ring
  let μ := ∑ i : η, r (Sum.inr i)
  let m₄ := ∑ i : ι, (x i ^ 2) ^ 2 * W i
  have hm₄ : 0 ≤ m₄ :=
    sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (div_nonneg (sub_nonneg.mpr (hx i)) hZ.le)
  have hl : F₀ᵀ *ᵥ r = b₁ - E₀ᵀ *ᵥ w := hlimit
  have hμ : μ = 3 * m / 4 := by
    have h := congrFun hl (1 : Fin 3)
    change ((phaseRow x d baseRow)ᵀ *ᵥ r) 1 =
      2 * m - ((phaseRow x d limitRow)ᵀ *ᵥ w) 1 at h
    rw [phase_moment, phase_moment] at h
    change (∑ i : ι, 0 * r (Sum.inl i)) + (∑ i : η, 2 * r (Sum.inr i)) =
      2 * m - ((∑ i : ι, x i ^ 2 / 2 * w (Sum.inl i)) +
        (∑ i : η, (-d ^ 2 / 2) * w (Sum.inr i))) at h
    simp only [hwf, hwb, zero_mul, mul_zero, sum_const_zero, zero_add, add_zero, ← mul_sum] at h
    have hdiv : (∑ i, x i ^ 2 / 2 * W i) = m / 2 := by
      simp_rw [show ∀ (a b : ℝ), a / 2 * b = (a * b) / 2 by intros; ring, ← sum_div]
      rw [show (∑ i, x i ^ 2 * W i) = m from hX]
    rw [hdiv] at h
    change 2 * μ = 2 * m - m / 2 at h
    linarith only [h]
  have hsum_r : ∑ i : ι, r (Sum.inl i) = -μ := by
    have he := congrFun hl (0 : Fin 3)
    change ((phaseRow x d baseRow)ᵀ *ᵥ r) 0 =
      0 - ((phaseRow x d limitRow)ᵀ *ᵥ w) 0 at he
    rw [phase_moment, phase_moment] at he
    change (∑ i : ι, 1 * r (Sum.inl i)) + (∑ i : η, 1 * r (Sum.inr i)) =
      0 - ((∑ i : ι, 0 * w (Sum.inl i)) + ∑ i : η, 0 * w (Sum.inr i)) at he
    simp only [one_mul, zero_mul, sum_const_zero, add_zero, sub_zero] at he
    exact eq_neg_of_add_eq_zero_left he
  have hmoment_r : ∑ i : ι, x i ^ 2 * r (Sum.inl i) = m₄ / 3 - d ^ 2 * μ := by
    have h := congrFun hl (2 : Fin 3)
    change ((phaseRow x d baseRow)ᵀ *ᵥ r) 2 =
      0 - ((phaseRow x d limitRow)ᵀ *ᵥ w) 2 at h
    rw [phase_moment, phase_moment] at h
    change (∑ i : ι, x i ^ 2 * r (Sum.inl i)) + (∑ i : η, d ^ 2 * r (Sum.inr i)) =
      0 - ((∑ i : ι, -(x i ^ 4) / 3 * w (Sum.inl i)) +
        ∑ i : η, (-d ^ 4 / 3) * w (Sum.inr i)) at h
    simp only [hwf, hwb, mul_zero, sum_const_zero, add_zero, zero_sub, ← mul_sum] at h
    have he : (∑ i, -(x i ^ 4) / 3 * W i) = -(m₄ / 3) := by
      simp_rw [show ∀ (y w : ℝ), -(y ^ 4) / 3 * w = -(((y ^ 2) ^ 2 * w) / 3) by
        intros; ring, sum_neg_distrib, ← sum_div]
      rfl
    rw [he, neg_neg] at h
    exact eq_sub_of_add_eq h
  have hrb (i : η) : 0 < r (Sum.inr i) := by
    have hconst (j : η) : r (Sum.inr j) = r (Sum.inr i) := rfl
    have h : μ = (Fintype.card η : ℝ) * r (Sum.inr i) := by simp [μ, hconst]
    have hm' : 0 < μ := by rw [hμ]; positivity
    exact pos_of_mul_pos_right (h ▸ hm') (Nat.cast_nonneg _)
  have hrFront (i : ι) (hi : x i ^ 2 = t) : 0 < r (Sum.inl i) := by
    have hmax (j : ι) : x j ^ 2 ≤ x i ^ 2 := hi ▸ hx j
    have htpos : 0 < t := by have he := hx i₁; rw [h₁] at he; norm_num at he; linarith
    let A := u₀ 0 + μ * t / Z
    let B := u₀ 2 + a₀ 1 / 2 - μ / Z
    let G := 1 / (3 * Z)
    have hvar (j : ι) : A + B * x j ^ 2 + G * (x j ^ 2) ^ 2 = r (Sum.inl j) + μ * W j := by
      rw [hrf]
      dsimp [A, B, G, W]
      ring
    have hzero : ∑ j, (A + B * x j ^ 2 + G * (x j ^ 2) ^ 2) = 0 := by
      simp_rw [hvar, sum_add_distrib, ← mul_sum, hsum_r, show (∑ j, W j) = 1 from hW]
      ring
    have hmoment : 0 < ∑ j, x j ^ 2 * (A + B * x j ^ 2 + G * (x j ^ 2) ^ 2) := by
      simp_rw [hvar, mul_add, mul_left_comm (x _ ^ 2) μ, sum_add_distrib, ← mul_sum,
        hmoment_r, show (∑ j, x j ^ 2 * W j) = m from hX]
      have hμ' : 0 < μ := by rw [hμ]; positivity
      have hk := mul_pos hμ' (sub_pos.mpr (hboundary ⟨i, hi⟩))
      linarith only [hm₄, hk]
    have hsign := boundary_variation_pos (fun j => x j ^ 2) i hmax A B G
      (by dsimp [G]; positivity) hzero hmoment
    rw [hvar, show W i = 0 by simp [W, hi], mul_zero, add_zero] at hsign
    simpa only [lt_max_iff, lt_irrefl, false_or] using hsign
  let Ft := fun k => F₀ + s k • E k
  let rAt := fun k => E k *ᵥ a₀ + Ft k *ᵥ u k
  have hFt : Tendsto Ft l (𝓝 F₀) := by
    simpa [s] using tendsto_const_nhds.add ((ht.pow 2).smul hE)
  have hMv : Continuous (fun p : Matrix (ι ⊕ η) (Fin 3) ℝ × (Fin 3 → ℝ) => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hrt : Tendsto rAt l (𝓝 r) :=
    (hMv.continuousAt.tendsto.comp (hE.prodMk_nhds tendsto_const_nhds)).add
      (hMv.continuousAt.tendsto.comp (hFt.prodMk_nhds hu))
  have hposAll : ∀ᶠ k in l, ∀ i : ι ⊕ η, 0 < (Ft k *ᵥ a k) i := by
    rw [Filter.eventually_all]
    intro i
    have hri := tendsto_pi_nhds.mp hrt i
    have hsplit (k) : (Ft k *ᵥ a k) i = w i + s k * rAt k i := by
      dsimp only [a, rAt]
      rw [mulVec_add, mulVec_smul, show Ft k *ᵥ a₀ = w + s k • (E k *ᵥ a₀) by
        simp only [Ft, w, add_mulVec, smul_mulVec]]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h_nonneg : 0 ≤ w i := by
      cases i with
      | inl j => rw [hwf]; exact div_nonneg (sub_nonneg.mpr (hx j)) hZ.le
      | inr j => rw [hwb]
    rcases h_nonneg.eq_or_lt with hz | hz
    · have hrpos : 0 < r i := by
        cases i with
        | inl j =>
          apply hrFront
          rw [hwf] at hz
          have he := (div_eq_zero_iff.mp hz.symm).resolve_right hZ.ne'
          linarith only [he]
        | inr j => exact hrb j
      filter_upwards [hp, hri.eventually (eventually_gt_nhds hrpos)] with k hk hh
      rw [hsplit, ← hz, zero_add]
      exact mul_pos (sq_pos_of_pos hk) hh
    · have hl : Tendsto (fun k => w i + s k * rAt k i) l (𝓝 (w i)) := by
        simpa [s] using tendsto_const_nhds.add ((ht.pow 2).mul hri)
      filter_upwards [hl.eventually (eventually_gt_nhds hz)] with k hk
      rwa [hsplit]
  refine ⟨a, ha, ?_⟩
  filter_upwards [hn, heq, hposAll] with k hk hke hkp
  have hrows : Ft k = F k := by
    funext i
    cases i with
    | inl i => exact row_eq false (x i) hk
    | inr i => exact row_eq true d hk
  rw [← hrows]
  refine ⟨hke.trans ?_, hkp⟩
  rw [hbase]
  funext j
  fin_cases j <;> simp [b₁, mul_comm, mul_left_comm]

private abbrev Front (n : ℕ) := ↥(Icc (-(n : ℤ)) (n : ℤ))

private abbrev Back (odd : Bool) := Fin (if odd then 2 else 1)

private instance back_nonempty (odd : Bool) : Nonempty (Back odd) :=
  ⟨⟨0, by cases odd <;> decide⟩⟩

private def backRep (odd : Bool) (k : ℕ) (i : Back odd) : ℤ :=
  if i.val = 0 then (parityModulus odd k / 2 : ℕ) else -(k : ℤ)

private theorem backRep_bounds (odd : Bool) (k : ℕ) (i : Back odd) :
    -(parityModulus odd k : ℤ) < backRep odd k i * 2 ∧
      backRep odd k i * 2 ≤ parityModulus odd k := by
  cases odd <;> simp only [backRep, parityModulus, Bool.false_eq_true, ite_false, ite_true] <;>
    split <;> omega

private theorem natAbs_backRep (odd : Bool) (k : ℕ) (i : Back odd) :
    (backRep odd k i).natAbs = parityModulus odd k / 2 := by
  unfold backRep
  split
  · exact Int.natAbs_natCast _
  · cases odd
    · have := i.isLt
      simp only [Bool.false_eq_true, ite_false] at this
      omega
    · simp only [Int.natAbs_neg, Int.natAbs_natCast, parityModulus, ite_true]
      omega

private theorem backRep_inj {odd : Bool} {k : ℕ} (hk : 0 < k) :
    Function.Injective (backRep odd k) := by
  intro i j h
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  cases odd <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hi hj
  · omega
  · simp only [backRep, parityModulus, ite_true] at h
    split at h <;> split at h <;> omega

private def gridRep (n : ℕ) (odd : Bool) (k : ℕ) : Front n ⊕ Back odd → ℤ :=
  Sum.elim Subtype.val (backRep odd k)

private theorem gridRep_centered {n : ℕ} {odd : Bool} {k : ℕ} (hk : n < k)
    (i : Front n ⊕ Back odd) :
    ((gridRep n odd k i : ℤ) : ZMod (parityModulus odd k)).valMinAbs = gridRep n odd k i := by
  cases i with
  | inl i =>
    apply valMinAbs_of_window (K := n)
    · unfold parityModulus
      omega
    · exact i.2
  | inr i =>
    exact (ZMod.valMinAbs_spec _ _).2 ⟨rfl, backRep_bounds odd k i⟩

private def gridEmbedding {n : ℕ} {odd : Bool} {k : ℕ} (hk : n < k) :
    (Front n ⊕ Back odd) ↪ ZMod (parityModulus odd k) where
  toFun i := (gridRep n odd k i : ZMod (parityModulus odd k))
  inj' := by
    intro i j he
    have h : gridRep n odd k i = gridRep n odd k j := by
      simpa only [gridRep_centered hk] using congrArg ZMod.valMinAbs he
    have upper : n < parityModulus odd k / 2 := by unfold parityModulus; omega
    have abs_le (i : Front n) : i.1.natAbs ≤ n := by
      have := mem_Icc.mp i.2
      omega
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Subtype.ext h)
      | inr j =>
        have e := congrArg Int.natAbs h
        change i.1.natAbs = (backRep odd k j).natAbs at e
        rw [natAbs_backRep] at e
        have := abs_le i
        omega
    | inr i =>
      cases j with
      | inl j =>
        have e := congrArg Int.natAbs h
        change (backRep odd k i).natAbs = j.1.natAbs at e
        rw [natAbs_backRep] at e
        have := abs_le j
        omega
      | inr j => exact congrArg Sum.inr (backRep_inj (by omega) h)

private theorem sample_eq_abs {q : ℕ} [NeZero q] (i : ZMod q) :
    sample i = Real.cos ((i.valMinAbs.natAbs : ℝ) * mesh q) := by
  rw [sample, centeredAngle_eq_mesh, ← Real.cos_abs ((i.valMinAbs : ℝ) * mesh q), abs_mul,
    abs_of_pos mesh_pos, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

private theorem sample_antipode_iff {q : ℕ} [NeZero q] (i : ZMod q) :
    sample i = sample ((↑(q / 2) : ℤ) : ZMod q) ↔ i.valMinAbs.natAbs = q / 2 := by
  have hj := (ZMod.valMinAbs_spec (((q / 2 : ℕ) : ℤ) : ZMod q) ((q / 2 : ℕ) : ℤ)).mpr
    ⟨rfl, by have := NeZero.pos q; omega, by omega⟩
  rw [sample_eq_abs i, sample_eq_abs, hj, Int.natAbs_natCast]
  have hm (j : ℕ) (h : j ≤ q / 2) : (j : ℝ) * mesh q ∈ Set.Icc 0 Real.pi :=
    ⟨mul_nonneg (Nat.cast_nonneg _) mesh_pos.le,
      (mul_le_mul_of_nonneg_right (by exact_mod_cast h) mesh_pos.le).trans
      half_mesh_le_pi⟩
  constructor
  · intro h
    have he := Real.strictAntiOn_cos.injOn (hm _ (ZMod.natAbs_valMinAbs_le i)) (hm _ le_rfl) h
    exact_mod_cast (mul_right_cancel₀ mesh_pos.ne' he)
  · intro h
    rw [h]

private theorem grid_mem {n : ℕ} {odd : Bool} {k : ℕ} (hk : n < k)
    (i : ZMod (parityModulus odd k)) :
    i ∈ (univ : Finset (Front n ⊕ Back odd)).map (gridEmbedding hk) ↔
      i.valMinAbs.natAbs ≤ n ∨
        sample i = sample ((↑(parityModulus odd k / 2) : ℤ) : ZMod (parityModulus odd k)) := by
  rw [sample_antipode_iff]
  constructor
  · intro h
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp h
    have hj := gridRep_centered hk j
    change (gridEmbedding hk j).valMinAbs = gridRep n odd k j at hj
    rw [hj]
    cases j with
    | inl j =>
      left
      have := mem_Icc.mp j.2
      change j.1.natAbs ≤ n
      omega
    | inr j => exact Or.inr (natAbs_backRep odd k j)
  · intro h
    apply Finset.mem_map.mpr
    have spec := (ZMod.valMinAbs_spec i i.valMinAbs).mp rfl
    rcases h with hf | hb
    · let j : Front n := ⟨i.valMinAbs, mem_Icc.mpr (by omega)⟩
      exact ⟨Sum.inl j, mem_univ _, ZMod.coe_valMinAbs i⟩
    · by_cases hpos : 0 ≤ i.valMinAbs
      · let j : Back odd := ⟨0, by cases odd <;> decide⟩
        have hj : backRep odd k j = i.valMinAbs := by
          simp only [backRep, j, ite_true]
          omega
        refine ⟨Sum.inr j, mem_univ _, ?_⟩
        change ((backRep odd k j : ℤ) : ZMod _) = i
        rw [hj, ZMod.coe_valMinAbs]
      · have hneg : i.valMinAbs = -((parityModulus odd k / 2 : ℕ) : ℤ) := by omega
        have hstrict : -(parityModulus odd k : ℤ) <
            -((parityModulus odd k / 2 : ℕ) : ℤ) * 2 := by rw [← hneg]; exact spec.2.1
        cases odd
        · simp only [parityModulus, Bool.false_eq_true, ite_false] at hstrict
          omega
        · let j : Back true := ⟨1, by decide⟩
          have hj : backRep true k j = i.valMinAbs := by
            rw [hneg]
            simp only [backRep, j, Nat.one_ne_zero, ite_false, parityModulus, ite_true]
            omega
          refine ⟨Sum.inr j, mem_univ _, ?_⟩
          change ((backRep true k j : ℤ) : ZMod _) = i
          rw [hj, ZMod.coe_valMinAbs]

private theorem grid_sample {n : ℕ} {odd : Bool} {k : ℕ} (hk : n < k)
    (i : Front n ⊕ Back odd) :
    sample (gridEmbedding hk i) = i.elim
      (fun j : Front n => signedCos false (j.1 : ℝ) (mesh (parityModulus odd k)))
      (fun _ : Back odd => signedCos true (parityOffset odd) (mesh (parityModulus odd k))) := by
  cases i with
  | inl j =>
    have hj := gridRep_centered (odd := odd) hk (Sum.inl j)
    change (gridEmbedding hk (Sum.inl j)).valMinAbs = j.1 at hj
    rw [sample, centeredAngle_eq_mesh, hj]
    rfl
  | inr j =>
    have h : (gridEmbedding hk (.inr j)).valMinAbs.natAbs = parityModulus odd k / 2 := by
      have hj := gridRep_centered (n := n) hk (Sum.inr j)
      change (gridEmbedding hk (Sum.inr j)).valMinAbs = backRep odd k j at hj
      rw [hj, natAbs_backRep]
    rw [(sample_antipode_iff _).mpr h, sample_antipode, parity_offset]
    rfl

private theorem sample_between {n : ℕ} {odd : Bool} {k : ℕ} (hk : n < k)
    (i : ZMod (parityModulus odd k))
    (hi : i ∉ (univ : Finset (Front n ⊕ Back odd)).map (gridEmbedding hk)) :
    let h := mesh (parityModulus odd k)
    signedCos true (parityOffset odd + 1) h ≤ sample i ∧
      sample i ≤ signedCos false (n + 1 : ℝ) h := by
  intro h
  let q := parityModulus odd k
  have hq : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  obtain ⟨hfront, hback⟩ := not_or.mp (fun h => hi ((grid_mem hk i).mpr h))
  have hno : i.valMinAbs.natAbs ≤ q / 2 - 1 := by
    have hle := ZMod.natAbs_valMinAbs_le i
    have hne := mt (sample_antipode_iff i).mpr hback
    omega
  have hhalf : (q / 2 : ℕ) ≥ 1 := by dsimp [q, parityModulus]; omega
  have hr : ((q / 2 - 1 : ℕ) : ℝ) * h = Real.pi - (parityOffset odd + 1) * h := by
    rw [← parity_offset odd k, Nat.cast_sub hhalf, Nat.cast_one]
    change ((↑(q / 2) : ℝ) - 1) * mesh q = Real.pi - (↑(q % 2) / 2 + 1) * mesh q
    have he : (2 : ℝ) * (↑(q / 2) : ℝ) + (↑(q % 2) : ℝ) = q := by
      exact_mod_cast (show 2 * (q / 2) + q % 2 = q by omega)
    unfold mesh
    field_simp [hq.ne']
    linear_combination he
  change -Real.cos ((parityOffset odd + 1) * h) ≤ sample i ∧
    sample i ≤ Real.cos ((n + 1 : ℝ) * h)
  rw [← Real.cos_pi_sub, ← hr, sample_eq_abs]
  have hle : (↑i.valMinAbs.natAbs : ℝ) * h ≤ Real.pi :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast ZMod.natAbs_valMinAbs_le i) mesh_pos.le).trans
      half_mesh_le_pi
  constructor
  · apply Real.cos_le_cos_of_nonneg_of_le_pi (mul_nonneg (Nat.cast_nonneg _) mesh_pos.le) ?_
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hno) mesh_pos.le)
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le (q / 2) 1) mesh_pos.le).trans
      half_mesh_le_pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi
      (mul_nonneg (by positivity) mesh_pos.le) hle
      (mul_le_mul_of_nonneg_right (by exact_mod_cast (show n + 1 ≤ i.valMinAbs.natAbs by omega))
        mesh_pos.le)

private theorem window_iff {n : ℕ} {t : ℝ} (hlo : (n : ℝ) ^ 2 ≤ t)
    (hhi : t < ((n : ℝ) + 1) ^ 2) (j : ℤ) :
    (j : ℝ) ^ 2 ≤ t ↔ j.natAbs ≤ n := by
  have habs : |(j : ℝ)| = (j.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  rw [← sq_abs (j : ℝ), habs]
  constructor
  · intro hj
    by_contra! hn
    have h : (↑(n + 1) : ℝ) ≤ (j.natAbs : ℝ) := by
      exact_mod_cast (show n + 1 ≤ j.natAbs by omega)
    have he := (sq_le_sq₀ (by positivity) (Nat.cast_nonneg j.natAbs)).2 h
    push_cast at he
    linarith only [he, hj, hhi]
  · intro hj
    have h : (j.natAbs : ℝ) ≤ n := by exact_mod_cast hj
    exact ((sq_le_sq₀ (Nat.cast_nonneg j.natAbs) (Nat.cast_nonneg n)).2 h).trans hlo

private theorem lattice_window_sums {n : ℕ} {t Z m : ℝ} {w : ℤ → ℝ}
    (act : Activation m n t Z w) (hhi : t < ((n : ℝ) + 1) ^ 2) :
    (∑ i : Front n, (t - (i.1 : ℝ) ^ 2) / Z) = 1 ∧
      (∑ i : Front n, (i.1 : ℝ) ^ 2 * ((t - (i.1 : ℝ) ^ 2) / Z)) = m := by
  have hin (i : Front n) : w i.1 = (t - (i.1 : ℝ) ^ 2) / Z := by
    rw [act.law, max_eq_right]
    apply sub_nonneg.mpr ((window_iff act.radius_lower hhi _).2 ?_)
    have := mem_Icc.mp i.2
    omega
  have hout (j : ℤ) (hj : j ∉ Icc (-(n : ℤ)) (n : ℤ)) : w j = 0 := by
    apply activation_zero_outside act
    intro h
    have hrad : latticeSupportRadius n m ≤ n := by
      unfold latticeSupportRadius
      split <;> omega
    have hs := mem_Icc.mp h
    exact hj (mem_Icc.mpr (by omega))
  have hsum (f : ℤ → ℝ) : (∑ i : Front n, f i.1 * w i.1) = ∑' j : ℤ, f j * w j := by
    rw [Finset.sum_coe_sort (Icc (-(n : ℤ)) (n : ℤ)) (fun j => f j * w j)]
    exact (hasSum_sum_of_ne_finset_zero (s := Icc (-(n : ℤ)) (n : ℤ))
      (fun j hj => by rw [hout j hj, mul_zero])).tsum_eq.symm
  constructor
  · simpa only [hin, one_mul, act.mass.tsum_eq] using hsum (fun _ => 1)
  · have hm : (∑' j : ℤ, (j : ℝ) ^ 2 * w j) = m := act.second_moment.tsum_eq
    have hs := hsum (fun j => (j : ℝ) ^ 2)
    change (∑ i : Front n, (i.1 : ℝ) ^ 2 * w i.1) = (∑' j : ℤ, (j : ℝ) ^ 2 * w j) at hs
    simpa only [hin, hm] using hs

private def supportStatement (q : ℕ) [NeZero q] (a t : ℝ) : Prop :=
  (∃ v ∈ feasible q a, IsMinOn energy (feasible q a) v ∧
    cosineMoment 1 v = a ∧ cosineMoment 2 v = a ∧
    (∀ u ∈ feasible q a, u ≠ v → energy v < energy u) ∧
    (∀ u ∈ feasible q a, energy v + (∑ i, (u i - v i) ^ 2) ≤ energy u)) ∧
  ∀ v ∈ feasible q a, IsMinOn energy (feasible q a) v → ∀ i : ZMod q,
    0 < v i ↔ (i.valMinAbs : ℝ) ^ 2 ≤ t ∨ ∀ j : ZMod q, sample i ≤ sample j

private theorem solve_on_parity (lam : ℝ) (hlam : 0 < lam) {n : ℕ} (hn : 0 < n)
    {t Z : ℝ} {w : ℤ → ℝ}
    (act : Activation (lam / (8 * Real.pi ^ 2)) n t Z w)
    (hhi : t < ((n : ℝ) + 1) ^ 2) (odd : Bool) :
    ∀ᶠ k in atTop, supportStatement (parityModulus odd k)
      (1 - lam / (parityModulus odd k : ℝ) ^ 2) t := by
  let m := lam / (8 * Real.pi ^ 2)
  let d := parityOffset odd
  let h := fun k => mesh (parityModulus odd k)
  let x := fun i : Front n => (i.1 : ℝ)
  have hm : 0 < m := div_pos hlam (by positivity)
  let i₀ : Front n := ⟨0, mem_Icc.mpr (by omega)⟩
  let i₁ : Front n := ⟨1, mem_Icc.mpr (by omega)⟩
  have hx (i : Front n) : x i ^ 2 ≤ t := by
    apply (window_iff act.radius_lower hhi _).2
    have := mem_Icc.mp i.2
    omega
  have htpos : 1 ≤ t := by simpa [x, i₁] using hx i₁
  have hd : d ^ 2 ≤ 1 / 4 := by cases odd <;> norm_num [d, parityOffset]
  have hboundary : (∃ i : Front n, x i ^ 2 = t) → d ^ 2 < m := by
    rintro ⟨i, hi⟩
    have he : t = (n : ℝ) ^ 2 := le_antisymm
      (hi ▸ (show x i ^ 2 ≤ (n : ℝ) ^ 2 from
        (window_iff (le_refl _) (by
          have := Nat.cast_nonneg (α := ℝ) n
          nlinarith) i.1).2 (by have := mem_Icc.mp i.2; omega))) act.radius_lower
    have hbudget := act.lower_endpoint.mpr he
    have hn' : 2 ≤ n := by
      by_contra! h
      have he' : n = 1 := by omega
      apply hm.ne'
      simpa only [he', Nat.cast_one, one_pow, sub_self, zero_div] using hbudget
    have hn'' : (2 : ℝ) ≤ n := by exact_mod_cast hn'
    have hs := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n)).mpr hn''
    linarith only [hbudget, hs, hd]
  have hpos : ∀ᶠ k in atTop, 0 < h k := Eventually.of_forall fun _ => mesh_pos
  have ht := mesh_tendsto odd
  obtain ⟨hW, hX⟩ := lattice_window_sums act hhi
  obtain ⟨a, ha, he⟩ := phase_solution (η := Back odd) ht hpos x d t Z m act.normalizer_pos hm
    i₀ i₁ (by simp [x, i₀]) (by simp [x, i₁]) hx hboundary hW hX
  have hb : ∀ᶠ k in atTop, a k 1 < 0 :=
    (tendsto_pi_nhds.mp ha 1).eventually (eventually_lt_nhds (by
      change -(t - d ^ 2) / (2 * Z) < 0
      exact div_neg_of_neg_of_pos (by linarith only [htpos, hd])
        (mul_pos (by norm_num) act.normalizer_pos)))
  have hg : ∀ᶠ k in atTop, a k 2 < 0 :=
    (tendsto_pi_nhds.mp ha 2).eventually (eventually_lt_nhds
      (div_neg_of_neg_of_pos (by norm_num) act.normalizer_pos))
  have hnmesh := hpos.mono fun _ hk => hk.ne'
  have hlo := polynomial_tendsto ht hnmesh ha true (d + 1)
  have hhi' := polynomial_tendsto ht hnmesh ha false ((n : ℝ) + 1)
  have e₁ := base_dot t Z d (d + 1) act.normalizer_pos.ne' true
  have e₂ := base_dot t Z d ((n : ℝ) + 1) act.normalizer_pos.ne' false
  change baseRow true (d + 1) ⬝ᵥ leading t Z d = (d ^ 2 - (d + 1) ^ 2) / Z at e₁
  change baseRow false ((n : ℝ) + 1) ⬝ᵥ leading t Z d = (t - ((n : ℝ) + 1) ^ 2) / Z at e₂
  rw [e₁] at hlo
  rw [e₂] at hhi'
  have hd₀ : 0 ≤ d := by cases odd <;> norm_num [d, parityOffset]
  have hex₁ := hlo.eventually (eventually_lt_nhds
    (div_neg_of_neg_of_pos (by nlinarith only [hd₀]) act.normalizer_pos))
  have hex₂ := hhi'.eventually (eventually_lt_nhds
    (div_neg_of_neg_of_pos (sub_neg.mpr hhi) act.normalizer_pos))
  filter_upwards [eventually_gt_atTop n, he, hb, hg, hex₁, hex₂] with k hk heq hkB hkG hLo hHi
  let q := parityModulus odd k
  let threshold := 1 - lam / (q : ℝ) ^ 2
  let emb := gridEmbedding (odd := odd) hk
  let sites := (univ : Finset (Front n ⊕ Back odd)).map emb
  let F := phaseRow (η := Back odd) x d fun back z =>
    ![1, 1 - signedCos back z (h k), (1 - signedCos back z (h k) ^ 2) / h k ^ 2]
  let p : ZMod q → ℝ := fun i =>
    a k 0 + a k 1 * (1 - sample i) + a k 2 * ((1 - sample i ^ 2) / h k ^ 2)
  let v : ZMod q → ℝ := fun i => if i ∈ sites then p i else 0
  have hsite (j : Front n ⊕ Back odd) : emb j ∈ sites := mem_map_of_mem _ (mem_univ _)
  have hsample (j : Front n ⊕ Back odd) :
      F j = ![1, 1 - sample (emb j), (1 - sample (emb j) ^ 2) / h k ^ 2] := by
    rw [grid_sample hk j]
    cases j <;> rfl
  have hrow (j : Front n ⊕ Back odd) : (F *ᵥ a k) j = p (emb j) := by
    change F j ⬝ᵥ a k = p (emb j)
    rw [hsample, dot_three]
    dsimp only [p]
    ring
  have hposSite (i : ZMod q) (hi : i ∈ sites) : 0 < p i := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    rw [← hrow]
    exact heq.2 j
  have hsum (f : ZMod q → ℝ) :
      (∑ i, f i * v i) = ∑ j, f (emb j) * (F *ᵥ a k) j := by
    rw [← sum_subset (subset_univ sites) (by
      intro i _ hi
      simp [v, hi])]
    rw [sum_map]
    apply sum_congr rfl
    intro j _
    simp only [v, hsite, ite_true, hrow]
  have hmoment (j : Fin 3) :
      (∑ i : ZMod q, ![1, 1 - sample i, (1 - sample i ^ 2) / h k ^ 2] j * v i) =
        ![1, 2 * m * h k ^ 2, m] j := by
    rw [hsum]
    exact (sum_congr rfl fun i _ => by rw [← hsample]; rfl).trans (congrFun heq.1 j)
  have hvMass : ∑ i, v i = 1 := by
    have hmass := hmoment 0
    change (∑ i, 1 * v i) = 1 at hmass
    simpa only [one_mul] using hmass
  have hd₁ : ∑ i, v i * (1 - sample i) = 2 * m * h k ^ 2 := by
    have he₁ := hmoment 1
    change (∑ i, (1 - sample i) * v i) = 2 * m * h k ^ 2 at he₁
    simpa only [mul_comm] using he₁
  have hd₂ : ∑ i, v i * (1 - sample i ^ 2) = m * h k ^ 2 := by
    have he₂ := hmoment 2
    change (∑ i, ((1 - sample i ^ 2) / h k ^ 2) * v i) = m at he₂
    simp_rw [div_mul_eq_mul_div, mul_comm (1 - sample _ ^ 2), ← sum_div] at he₂
    exact (div_eq_iff (pow_ne_zero _ (mesh_pos (q := q)).ne')).mp he₂
  have hscale : 2 * m * h k ^ 2 = lam / (q : ℝ) ^ 2 := by
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
    change 2 * (lam / (8 * Real.pi ^ 2)) * mesh q ^ 2 = _
    unfold mesh
    field_simp [hq, Real.pi_ne_zero]
    ring
  obtain ⟨hD₁, hD₂⟩ := sum_sample_deficits hvMass
  have hv₁ : cosineMoment 1 v = threshold := by
    dsimp only [threshold]
    linarith only [hd₁, hD₁, hscale]
  have hv₂ : cosineMoment 2 v = threshold := by
    dsimp only [threshold]
    linarith only [hd₂, hD₂, hscale]
  have hbet : ∀ i ∉ sites, signedCos true (d + 1) (h k) ≤ sample i ∧
      sample i ≤ signedCos false ((n : ℝ) + 1) (h k) := fun i hi => sample_between hk i hi
  obtain ⟨hv, hopt, hdist, hsupp⟩ := exact_support_of_dual
    (threshold := threshold) (sq_pos_of_pos (mesh_pos (q := q)))
    hkB.le hkG.le hLo.le hHi.le hbet hposSite hvMass hv₁ hv₂
  refine ⟨⟨v, hv, ?_, hv₁, hv₂, hopt, hdist⟩, ?_⟩
  · intro u hu
    by_cases heq' : u = v
    · subst u
      change energy v ≤ energy v
      exact le_rfl
    · exact (hopt u hu heq').le
  · intro u hu hmin i
    have hsupport : 0 < u i ↔ i ∈ sites := by
      simpa only [lt_max_iff, lt_irrefl, false_or] using hsupp u hu hmin i
    rw [hsupport, grid_mem hk i, ← window_iff act.radius_lower hhi]
    refine or_congr Iff.rfl ?_
    constructor
    · intro hsame j
      rw [hsame]
      exact sample_antipode_le j
    · intro hleast
      exact le_antisymm (hleast _) (sample_antipode_le i)

/-- At every positive budget, for all sufficiently large moduli of either parity, the
positive sites of every minimizer are exactly the closed lattice front window and all
residues attaining the least first cosine. Both moment constraints are attained. -/
theorem cyclic_eventual_exact_support (lam : ℝ) (hlam : 0 < lam) :
    let clip := fun x : ℝ => max 0 x
    let m := lam / (8 * Real.pi ^ 2)
    ∃ (n : ℕ) (t Z : ℝ) (w : ℤ → ℝ), 0 < n ∧
      ((n : ℝ) ^ 2 - 1) / 5 ≤ m ∧ m < (n : ℝ) * (n + 2) / 5 ∧
      Activation m n t Z w ∧
      ∃ Q : ℕ, ∀ q ≥ Q, ∀ [NeZero q],
        (∃ v ∈ feasible q (1 - lam / (q : ℝ) ^ 2),
          IsMinOn energy (feasible q (1 - lam / (q : ℝ) ^ 2)) v ∧
          cosineMoment 1 v = 1 - lam / (q : ℝ) ^ 2 ∧
          cosineMoment 2 v = 1 - lam / (q : ℝ) ^ 2 ∧
          (∀ u ∈ feasible q (1 - lam / (q : ℝ) ^ 2), u ≠ v → energy v < energy u) ∧
          (∀ u ∈ feasible q (1 - lam / (q : ℝ) ^ 2),
            energy v + (∑ i, (u i - v i) ^ 2) ≤ energy u)) ∧
        ∀ v ∈ feasible q (1 - lam / (q : ℝ) ^ 2),
          IsMinOn energy (feasible q (1 - lam / (q : ℝ) ^ 2)) v → ∀ i : ZMod q,
            0 < clip (v i) ↔ (i.valMinAbs : ℝ) ^ 2 ≤ t ∨ ∀ j : ZMod q, sample i ≤ sample j := by
  dsimp only
  let m := lam / (8 * Real.pi ^ 2)
  have hm : 0 ≤ m := (div_pos hlam (by positivity)).le
  obtain ⟨⟨n, t, Z, w⟩, ⟨hn, hi, act⟩, _⟩ :=
    (exists_lattice_square_moment_minimizer m).mp hm
  have hhi : t < ((n : ℝ) + 1) ^ 2 :=
    lt_of_le_of_ne act.radius_upper (fun he => hi.2.ne (act.upper_endpoint.mpr he))
  obtain ⟨K₀, h₀⟩ := eventually_atTop.mp (solve_on_parity lam hlam hn act hhi false)
  obtain ⟨K₁, h₁⟩ := eventually_atTop.mp (solve_on_parity lam hlam hn act hhi true)
  refine ⟨n, t, Z, w, hn, hi.1, hi.2, act, 2 * (K₀ + K₁) + 2, ?_⟩
  intro q hq _
  simp only [lt_max_iff, lt_irrefl, false_or]
  change supportStatement q (1 - lam / (q : ℝ) ^ 2) t
  by_cases he : q % 2 = 0
  · have hq' : q = parityModulus false (q / 2 - 1) := by simp [parityModulus]; omega
    have hK : K₀ ≤ q / 2 - 1 := by omega
    simpa only [← hq'] using h₀ (q / 2 - 1) hK
  · have hq' : q = parityModulus true (q / 2) := by simp [parityModulus]; omega
    have hK : K₁ ≤ q / 2 := by omega
    simpa only [← hq'] using h₁ (q / 2) hK

end D5.S3.Fourier.Asymptotics.CyclicEventualSupport
