/- GID: D5/S3/Quantum/Divergence/UmegakiRareFlagBKM
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiRareFlagBKM
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rectangular rare-flag logarithmic-derivative asymptotic. -/

import D5.S3.Divergence.LogDerivTrace
import D5.S3.Quantum.Subentropy.UniformIntegrals

/-! The actual Bochner logarithmic derivative at a rectangular rare flag. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix MeasureTheory Filter
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Divergence.LogDerivTrace

namespace D5.S3.Quantum.Divergence.UmegakiRareFlagBKM

lemma block_diag_posDef {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (Z : Matrix iota iota ℂ) (C : Matrix kappa kappa ℂ)
    (hZ : Z.PosDef) (hC : C.PosDef) {δ : ℝ} (hδ : 0 < δ) :
    (Matrix.fromBlocks Z 0 0 (δ • C)).PosDef := by
  let D : Matrix kappa kappa ℂ := δ • C
  have hD : D.PosDef := by
    dsimp [D]
    exact hC.smul hδ
  letI := hZ.isUnit.invertible
  letI := hD.isUnit.invertible
  have hps : (Matrix.fromBlocks Z 0 0 D).PosSemidef := by
    simpa using ((Matrix.PosDef.fromBlocks₁₁ (0 : Matrix iota kappa ℂ) D hZ).mpr
      (by simpa [D] using hD.posSemidef))
  exact (Matrix.PosSemidef.posDef_iff_isUnit hps).2 (by
    rw [Matrix.isUnit_fromBlocks_zero₂₁]
    exact ⟨hZ.isUnit, hD.isUnit⟩)

lemma pair_kernel_eval (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Set.Ioi (0 : ℝ), 1 / ((a + t) * (b + t))) =
      if a = b then 1 / a else (Real.log a - Real.log b) / (a - b) := by
  classical
  by_cases hab : a = b
  · subst b
    obtain ⟨hi, hv⟩ := D5.S3.Quantum.Subentropy.UniformIntegrals.inverse_power a ha 0
    convert hv using 1
    · apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp [pow_two, mul_comm, add_comm]
    · norm_num
  · by_cases h : a ≤ b
    · obtain ⟨hi, hv⟩ := D5.S3.Quantum.Subentropy.UniformIntegrals.reciprocal_difference a b ha h
      have heq : (fun t : ℝ => 1 / ((a + t) * (b + t))) =ᵐ[volume.restrict (Set.Ioi 0)]
          (fun t : ℝ => (1 / (a + t) - 1 / (b + t)) / (b - a)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hat : a + t ≠ 0 := (add_pos ha ht).ne'
        have hbt : b + t ≠ 0 := (add_pos hb ht).ne'
        field_simp [hat, hbt, sub_ne_zero.mpr (Ne.symm hab)]
        ring

      have hscale : (fun t : ℝ => (1 / (a + t) - 1 / (b + t)) / (b - a)) =
          (fun t : ℝ => (b - a)⁻¹ * (1 / (a + t) - 1 / (b + t))) := by
        funext t
        ring
      rw [integral_congr_ae heq]
      rw [hscale, integral_const_mul]
      have hv' : (∫ t in Set.Ioi (0 : ℝ), 1 / (a + t) - 1 / (b + t)) =
          Real.log b - Real.log a := by simpa [add_comm] using hv
      rw [hv']
      simp [hab]
      field_simp
      ring

    · have hba : b ≤ a := le_of_not_ge h
      obtain ⟨hi, hv⟩ := D5.S3.Quantum.Subentropy.UniformIntegrals.reciprocal_difference b a hb hba
      have heq : (fun t : ℝ => 1 / ((a + t) * (b + t))) =ᵐ[volume.restrict (Set.Ioi 0)]
          (fun t : ℝ => (1 / (b + t) - 1 / (a + t)) / (a - b)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hat : a + t ≠ 0 := (add_pos ha ht).ne'
        have hbt : b + t ≠ 0 := (add_pos hb ht).ne'
        field_simp [hat, hbt, sub_ne_zero.mpr hab]
        ring
      have hscale : (fun t : ℝ => (1 / (b + t) - 1 / (a + t)) / (a - b)) =
          (fun t : ℝ => (a - b)⁻¹ * (1 / (b + t) - 1 / (a + t))) := by
        funext t
        ring
      rw [integral_congr_ae heq]
      rw [hscale, integral_const_mul]
      have hv' : (∫ t in Set.Ioi (0 : ℝ), 1 / (b + t) - 1 / (a + t)) =
          Real.log a - Real.log b := by simpa [add_comm] using hv
      rw [hv']
      simp [hab]
      field_simp

private lemma pair_kernel_normalized_limit (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    Tendsto
      (fun δ : ℝ =>
        (∫ t in Set.Ioi (0 : ℝ), 1 / ((a + t) * (δ * c + t))) /
          Real.log (1 / δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / a)) := by
  have hδ0 : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun δ : ℝ => Real.log (1 / δ)) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div, Real.log_inv] using
      (tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero)
  have hnum : Tendsto
      (fun δ : ℝ => 1 + (Real.log a - Real.log c) / Real.log (1 / δ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop hlog)
  have hden : Tendsto (fun δ : ℝ => a - δ * c) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    simpa using tendsto_const_nhds.sub (hδ0.mul tendsto_const_nhds)
  have hden_inv : Tendsto (fun δ : ℝ => (a - δ * c)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (a⁻¹)) := by
    exact (continuousAt_inv₀ ha.ne').tendsto.comp hden
  have hmain : Tendsto
      (fun δ : ℝ =>
        (1 + (Real.log a - Real.log c) / Real.log (1 / δ)) *
          (a - δ * c)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / a)) := by
    convert hnum.mul hden_inv using 1 <;> simp [one_div]
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      0 < δ ∧ δ * c < a := by
    filter_upwards [self_mem_nhdsWithin,
      hδ0.eventually (gt_mem_nhds (div_pos ha hc))] with δ hδ hδsmall
    exact ⟨hδ, (lt_div_iff₀ hc).mp hδsmall⟩
  refine hmain.congr' ?_
  filter_upwards [hsmall, hlog.eventually (eventually_gt_atTop 0)] with δ ⟨hδ, hδsmall⟩ hl
  have hbc : 0 < δ * c := mul_pos hδ hc
  have hne : a ≠ δ * c := ne_of_gt hδsmall
  have heval := pair_kernel_eval a (δ * c) ha hbc
  rw [if_neg hne] at heval
  rw [Real.log_mul hδ.ne' hc.ne'] at heval
  have hlogδ : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  rw [heval, hlogδ]
  have hlne : Real.log δ ≠ 0 := by
    rw [hlogδ] at hl
    linarith
  field_simp [hlne]
  <;> ring

private lemma block_integrand_trace
    {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (V : Matrix iota kappa ℂ) (RZ : Matrix iota iota ℂ) (RC : Matrix kappa kappa ℂ) :
    let H : Matrix (iota ⊕ kappa) (iota ⊕ kappa) ℂ :=
      Matrix.fromBlocks 0 V Vᴴ 0
    let R : Matrix (iota ⊕ kappa) (iota ⊕ kappa) ℂ :=
      Matrix.fromBlocks RZ 0 0 RC
    (Hᴴ * R * H * R).trace =
      (V * RC * Vᴴ * RZ).trace + (Vᴴ * RZ * V * RC).trace := by
  dsimp
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.trace, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂]

private lemma shift_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    (M + t • 1).PosDef := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa using hM
  · exact hM.add_posSemidef ((Matrix.PosDef.one.smul ht).posSemidef)

private lemma block_trace_integral
    {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (Z : Matrix iota iota ℂ) (C : Matrix kappa kappa ℂ) (V : Matrix iota kappa ℂ)
    (hZ : Z.PosDef) (hC : C.PosDef) {δ : ℝ} (hδ : 0 < δ) :
    let H : Matrix (iota ⊕ kappa) (iota ⊕ kappa) ℂ := Matrix.fromBlocks 0 V Vᴴ 0
    let B : Matrix (iota ⊕ kappa) (iota ⊕ kappa) ℂ := Matrix.fromBlocks Z 0 0 (δ • C)
    (Hᴴ * D5.S3.Divergence.LogDerivTrace.logDeriv B H).trace =
      ∫ t in Set.Ioi (0 : ℝ),
        ((V * ((δ • C) + t • 1)⁻¹ * Vᴴ * (Z + t • 1)⁻¹).trace +
          (Vᴴ * (Z + t • 1)⁻¹ * V * ((δ • C) + t • 1)⁻¹).trace) := by
  dsimp
  let H : Matrix (iota ⊕ kappa) (iota ⊕ kappa) ℂ := Matrix.fromBlocks 0 V Vᴴ 0
  let B : Matrix (iota ⊕ kappa) (iota ⊕ kappa) ℂ := Matrix.fromBlocks Z 0 0 (δ • C)
  let f : ℝ → Matrix (iota ⊕ kappa) (iota ⊕ kappa) ℂ := fun t =>
    (B + t • 1)⁻¹ * H * (B + t • 1)⁻¹
  let L : Matrix (iota ⊕ kappa) (iota ⊕ kappa) ℂ →L[ℂ] ℂ :=
    (Matrix.traceLinearMap (iota ⊕ kappa) ℂ ℂ).toContinuousLinearMap.comp
      (mulLeftLinearMap (iota ⊕ kappa) ℂ Hᴴ).toContinuousLinearMap
  have hf : Integrable f (volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa only [f, IntegrableOn] using
      (D5.S3.Divergence.LogDerivTrace.logDeriv_integrable B H
        (block_diag_posDef Z C hZ hC hδ))
  have hL := L.integral_comp_comm hf
  have hpoint (t : ℝ) (ht : 0 ≤ t) :
      L (f t) =
        (V * ((δ • C) + t • 1)⁻¹ * Vᴴ * (Z + t • 1)⁻¹).trace +
          (Vᴴ * (Z + t • 1)⁻¹ * V * ((δ • C) + t • 1)⁻¹).trace := by
    have hZt : (Z + t • 1).PosDef := shift_posDef Z hZ t ht
    have hCt : ((δ • C) + t • 1).PosDef := by
      have hδC : (δ • C).PosDef := hC.smul hδ
      exact shift_posDef (δ • C) hδC t ht
    have hinv : (B + t • 1)⁻¹ =
        Matrix.fromBlocks (Z + t • 1)⁻¹ 0 0 ((δ • C) + t • 1)⁻¹ := by
      have he : B + t • 1 = Matrix.fromBlocks (Z + t • 1) 0 0 ((δ • C) + t • 1) := by
        ext i j
        rcases i with i | i <;> rcases j with j | j <;>
          simp [B, Matrix.one_apply, Matrix.fromBlocks_apply₁₁,
            Matrix.fromBlocks_apply₂₂]
      rw [he, Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff]
      · simp
      · exact (by
        constructor
        · intro _; exact hCt.isUnit
        · intro _; exact hZt.isUnit)
    change (Hᴴ * ((B + t • 1)⁻¹ * H * (B + t • 1)⁻¹)).trace = _
    rw [hinv]
    simpa only [H, ← Matrix.mul_assoc] using
      block_integrand_trace V (Z + t • 1)⁻¹ ((δ • C) + t • 1)⁻¹
  change (Hᴴ * (∫ t in Set.Ioi (0 : ℝ), f t)).trace = _
  calc
    (Hᴴ * (∫ t in Set.Ioi (0 : ℝ), f t)).trace =
        ∫ t in Set.Ioi (0 : ℝ), L (f t) := by simpa [L] using hL.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hpoint t ht.le

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 100000 in
lemma trace_cross_spectral
    {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (V : Matrix iota kappa ℂ) (UZ : Matrix iota iota ℂ) (UC : Matrix kappa kappa ℂ)
    (da : iota → ℂ) (db : kappa → ℂ) :
    (V * (UC * Matrix.diagonal db * UCᴴ) * Vᴴ *
        (UZ * Matrix.diagonal da * UZᴴ)).trace =
      ∑ i, ∑ j, da i * db j * Complex.normSq ((UZᴴ * V * UC) i j) := by
  let A := V * (UC * Matrix.diagonal db * UCᴴ) * Vᴴ
  let D := Matrix.diagonal da
  let W := UZᴴ * V * UC
  have hcyc : (A * (UZ * D * UZᴴ)).trace = ((UZᴴ * A * UZ) * D).trace := by
    calc
      (A * (UZ * D * UZᴴ)).trace = ((A * UZ * D) * UZᴴ).trace := by
        simp only [Matrix.mul_assoc]
      _ = (UZᴴ * (A * UZ * D)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  change (A * (UZ * D * UZᴴ)).trace = _
  rw [hcyc]
  have hprod : (UZᴴ * A * UZ) * D = W * Matrix.diagonal db * Wᴴ * Matrix.diagonal da := by
    simp [A, D, W, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [hprod]
  change (W * Matrix.diagonal db * Wᴴ * Matrix.diagonal da).trace =
    ∑ i, ∑ j, da i * db j * Complex.normSq (W i j)
  simp only [Matrix.trace, Matrix.diag_apply]
  simp only [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_eq_single j]
  · simp only [Matrix.diagonal_apply]
    change W i j * db j * star (W i j) * da i =
      da i * db j * (Complex.normSq (W i j) : ℂ)
    calc
      W i j * db j * star (W i j) * da i =
          da i * db j * (W i j * star (W i j)) := by ring
      _ = da i * db j * (Complex.normSq (W i j) : ℂ) := by
        simpa only [starRingEnd_apply] using congrArg (fun x : ℂ => da i * db j * x)
          (Complex.mul_conj (W i j))
  · intro b hb hbj
    simp [Matrix.diagonal, hbj]
  · intro hnot
    exact (hnot hj).elim

private lemma scaled_resolvent_spectral
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℂ) (hC : C.PosDef) (δ t : ℝ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    (δ • C + t • 1)⁻¹ =
      (hC.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) *
        Matrix.diagonal
          (fun j => ((δ * hC.isHermitian.eigenvalues j + t : ℝ) : ℂ)⁻¹) *
        star (hC.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) := by
  let U : Matrix ι ι ℂ := hC.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal
    (fun j => ((δ * hC.isHermitian.eigenvalues j + t : ℝ) : ℂ))
  let R : Matrix ι ι ℂ := Matrix.diagonal
    (fun j => ((δ * hC.isHermitian.eigenvalues j + t : ℝ) : ℂ)⁻¹)
  have hspec : δ • C + t • 1 = U * D * star U := by
    have hspecC : C = U * Matrix.diagonal (RCLike.ofReal ∘ hC.isHermitian.eigenvalues) * star U := by
      simpa [U] using hC.isHermitian.spectral_theorem
    rw [hspecC]
    have hunit : U * star U = 1 := by
      exact Unitary.coe_mul_star_self (hC.isHermitian.eigenvectorUnitary)
    have hδfactor :
        δ • (U * Matrix.diagonal (RCLike.ofReal ∘ hC.isHermitian.eigenvalues) * star U) =
          U * (δ • Matrix.diagonal (RCLike.ofReal ∘ hC.isHermitian.eigenvalues)) * star U := by
      simp [Matrix.smul_mul, Matrix.mul_smul]
    have htunit : t • (1 : Matrix ι ι ℂ) = U * (t • (1 : Matrix ι ι ℂ)) * star U := by
      calc
        t • (1 : Matrix ι ι ℂ) = t • (U * star U) := by rw [hunit]
        _ = U * (t • (1 : Matrix ι ι ℂ)) * star U := by
          simp [Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hunit]
    rw [hδfactor, htunit, ← Matrix.add_mul, ← Matrix.mul_add]
    congr 2
    ext i j
    by_cases hij : i = j <;> simp [D, hij]
  rw [hspec]
  apply Matrix.inv_eq_right_inv
  have hdiag : D * R = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    apply mul_inv_cancel₀
    exact_mod_cast (add_pos_of_pos_of_nonneg (mul_pos hδ (hC.eigenvalues_pos j)) ht).ne'
  calc
    (U * D * star U) * (U * R * star U) = U * (D * R) * star U := by
      have hstar : star U * U = 1 := by
        change (star (hC.isHermitian.eigenvectorUnitary) : Matrix ι ι ℂ) *
          (hC.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) = 1
        exact Unitary.coe_star_mul_self _
      calc
        (U * D * star U) * (U * R * star U) =
            U * (D * ((star U * U) * (R * star U))) := by
              simp only [Matrix.mul_assoc]
        _ = U * (D * (R * star U)) := by rw [hstar]; simp
        _ = U * (D * R) * star U := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hdiag, Matrix.mul_one]; exact Unitary.coe_mul_star_self _

private lemma trace_logDeriv_formula
    {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (Z : Matrix iota iota ℂ) (C : Matrix kappa kappa ℂ) (V : Matrix iota kappa ℂ)
    (hZ : Z.PosDef) (hC : C.PosDef) {δ : ℝ} (hδ : 0 < δ) :
    (Matrix.trace
      ((Matrix.fromBlocks (0 : Matrix iota iota ℂ) V Vᴴ
          (0 : Matrix kappa kappa ℂ)).conjTranspose *
        D5.S3.Divergence.LogDerivTrace.logDeriv
          (Matrix.fromBlocks Z 0 0 (δ • C))
          (Matrix.fromBlocks (0 : Matrix iota iota ℂ) V Vᴴ
            (0 : Matrix kappa kappa ℂ)))).re =
      2 * ∑ i, ∑ j,
        Complex.normSq (((hZ.isHermitian.eigenvectorUnitary : Matrix iota iota ℂ)ᴴ * V *
          (hC.isHermitian.eigenvectorUnitary : Matrix kappa kappa ℂ)) i j) *
          (∫ t in Set.Ioi (0 : ℝ),
            1 / ((hZ.isHermitian.eigenvalues i + t) *
              (δ * hC.isHermitian.eigenvalues j + t))) := by
  classical
  let UZ : Matrix iota iota ℂ := hZ.isHermitian.eigenvectorUnitary
  let UC : Matrix kappa kappa ℂ := hC.isHermitian.eigenvectorUnitary
  let W : Matrix iota kappa ℂ := UZᴴ * V * UC
  have hblock := block_trace_integral Z C V hZ hC hδ
  rw [hblock]
  have hpoint : ∀ t : ℝ, 0 ≤ t →
      ((V * ((δ • C) + t • 1)⁻¹ * Vᴴ * (Z + t • 1)⁻¹).trace +
        (Vᴴ * (Z + t • 1)⁻¹ * V * ((δ • C) + t • 1)⁻¹).trace) =
        ((2 * ∑ i, ∑ j,
          Complex.normSq (W i j) *
            ((hZ.isHermitian.eigenvalues i + t)⁻¹ *
              (δ * hC.isHermitian.eigenvalues j + t)⁻¹) : ℝ) : ℂ) := by
    intro t ht
    have hresZ := resolvent_eq_spectral Z hZ t ht
    have hresC := scaled_resolvent_spectral C hC δ t hδ ht
    rw [hresZ, hresC]
    have hfirst := trace_cross_spectral V UZ UC
      (fun i => ((hZ.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹)
      (fun j => ((δ * hC.isHermitian.eigenvalues j + t : ℝ) : ℂ)⁻¹)
    have hsecond :
        (Vᴴ * (UZ * Matrix.diagonal
            (fun i => ((hZ.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹) * UZᴴ) * V *
          (UC * Matrix.diagonal
            (fun j => ((δ * hC.isHermitian.eigenvalues j + t : ℝ) : ℂ)⁻¹) * UCᴴ)).trace =
          (V * (UC * Matrix.diagonal
            (fun j => ((δ * hC.isHermitian.eigenvalues j + t : ℝ) : ℂ)⁻¹) * UCᴴ) * Vᴴ *
            (UZ * Matrix.diagonal
              (fun i => ((hZ.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹) * UZᴴ)).trace := by
      rw [show Vᴴ * (UZ * Matrix.diagonal
            (fun i => ((hZ.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹) * UZᴴ) * V *
          (UC * Matrix.diagonal
            (fun j => ((δ * hC.isHermitian.eigenvalues j + t : ℝ) : ℂ)⁻¹) * UCᴴ) =
          (Vᴴ * (UZ * Matrix.diagonal
            (fun i => ((hZ.isHermitian.eigenvalues i + t : ℝ) : ℂ)⁻¹) * UZᴴ)) *
            (V * (UC * Matrix.diagonal
              (fun j => ((δ * hC.isHermitian.eigenvalues j + t : ℝ) : ℂ)⁻¹) * UCᴴ)) by
        simp only [Matrix.mul_assoc]]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    have hfirst' := hfirst
    simp only [UZ, UC, W, Unitary.coe_star, Matrix.star_eq_conjTranspose] at hfirst'
    have hsecond' := hsecond
    simp only [UZ, UC, Unitary.coe_star, Matrix.star_eq_conjTranspose] at hsecond'
    simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose]
    rw [hsecond', hfirst', ← two_mul]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [W, UZ, UC]
    ring
  let s : ℝ → ℝ := fun t =>
    2 * ∑ i, ∑ j,
      Complex.normSq (W i j) *
        ((hZ.isHermitian.eigenvalues i + t)⁻¹ *
          (δ * hC.isHermitian.eigenvalues j + t)⁻¹)
  have hcomplex :
      (∫ t in Set.Ioi (0 : ℝ),
        ((V * ((δ • C) + t • 1)⁻¹ * Vᴴ * (Z + t • 1)⁻¹).trace +
          (Vᴴ * (Z + t • 1)⁻¹ * V * ((δ • C) + t • 1)⁻¹).trace)) =
        (∫ t in Set.Ioi (0 : ℝ), (s t : ℂ)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa [s] using hpoint t ht.le
  have hint (i : iota) (j : kappa) :
      Integrable (fun t : ℝ => Complex.normSq (W i j) *
        ((hZ.isHermitian.eigenvalues i + t)⁻¹ *
          (δ * hC.isHermitian.eigenvalues j + t)⁻¹))
        (volume.restrict (Set.Ioi 0)) := by
    simpa [one_div, _root_.mul_inv_rev, mul_comm] using
      (pairKernel_integrable (hZ.isHermitian.eigenvalues i)
        (δ * hC.isHermitian.eigenvalues j) (hZ.eigenvalues_pos i)
        (mul_pos hδ (hC.eigenvalues_pos j))).const_mul (Complex.normSq (W i j))
  have hs_integrable : Integrable s (volume.restrict (Set.Ioi (0 : ℝ))) := by
    dsimp [s]
    exact (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hint i j))).const_mul 2
  have hreal :
      (∫ t in Set.Ioi (0 : ℝ), (s t : ℂ)).re =
        ∫ t in Set.Ioi (0 : ℝ), s t := by
    simpa using
      (integral_re (𝕜 := ℂ) (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (f := fun t : ℝ => (s t : ℂ)) hs_integrable.ofReal).symm
  rw [hcomplex, hreal]
  dsimp [s]
  rw [integral_const_mul]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hint i j))]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Finset.univ (fun j _ => hint i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp [one_div, _root_.mul_inv_rev, mul_comm]

theorem rare_flag_logDeriv_limit {iota kappa : Type*}
    [Fintype iota] [DecidableEq iota] [Fintype kappa] [DecidableEq kappa]
    (Z : Matrix iota iota ℂ) (C : Matrix kappa kappa ℂ) (V : Matrix iota kappa ℂ)
    (hZ : Z.PosDef) (hC : C.PosDef) :
    Filter.Tendsto
      (fun delta : ℝ =>
        (Matrix.trace
          ((Matrix.fromBlocks (0 : Matrix iota iota ℂ) V Vᴴ
              (0 : Matrix kappa kappa ℂ)).conjTranspose *
            D5.S3.Divergence.LogDerivTrace.logDeriv
              (Matrix.fromBlocks Z 0 0 (delta • C))
              (Matrix.fromBlocks (0 : Matrix iota iota ℂ) V Vᴴ
                (0 : Matrix kappa kappa ℂ)))).re /
          (2 * Real.log (1 / delta)))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((Matrix.trace (Vᴴ * Z⁻¹ * V)).re)) := by
  classical
  let UZ : Matrix iota iota ℂ := hZ.isHermitian.eigenvectorUnitary
  let UC : Matrix kappa kappa ℂ := hC.isHermitian.eigenvectorUnitary
  let W : Matrix iota kappa ℂ := UZᴴ * V * UC
  have hterm (i : iota) (j : kappa) :
      Tendsto
        (fun δ : ℝ => Complex.normSq (W i j) *
          ((∫ t in Set.Ioi (0 : ℝ),
            1 / ((hZ.isHermitian.eigenvalues i + t) *
              (δ * hC.isHermitian.eigenvalues j + t))) /
            Real.log (1 / δ)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.normSq (W i j) / hZ.isHermitian.eigenvalues i)) := by
    have hp := pair_kernel_normalized_limit
      (hZ.isHermitian.eigenvalues i) (hC.isHermitian.eigenvalues j)
      (hZ.eigenvalues_pos i) (hC.eigenvalues_pos j)
    have hc :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => Complex.normSq (W i j))
        (𝓝[>] (0 : ℝ)) (𝓝 (Complex.normSq (W i j)))).mul hp
    convert hc using 1 <;> simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hsum :
      Tendsto
        (fun δ : ℝ => ∑ i, ∑ j, Complex.normSq (W i j) *
          ((∫ t in Set.Ioi (0 : ℝ),
            1 / ((hZ.isHermitian.eigenvalues i + t) *
              (δ * hC.isHermitian.eigenvalues j + t))) /
            Real.log (1 / δ)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ i, ∑ j, Complex.normSq (W i j) /
          hZ.isHermitian.eigenvalues i)) := by
    refine tendsto_finsetSum Finset.univ (fun i hi => ?_)
    refine tendsto_finsetSum Finset.univ (fun j hj => hterm i j)
  have htrace_sum :
      (Matrix.trace (Vᴴ * Z⁻¹ * V)).re =
        ∑ i, ∑ j, Complex.normSq (W i j) /
          hZ.isHermitian.eigenvalues i := by
    have hinv := resolvent_eq_spectral Z hZ 0 (by norm_num)
    have hcross := trace_cross_spectral V UZ UC
      (fun i => ((hZ.isHermitian.eigenvalues i : ℝ) : ℂ)⁻¹)
      (fun _ => (1 : ℂ))
    have hunitC : UC * UCᴴ = 1 := by
      exact Unitary.coe_mul_star_self (hC.isHermitian.eigenvectorUnitary)
    have hinv0 : Z⁻¹ = UZ * Matrix.diagonal
        (fun i => ((hZ.isHermitian.eigenvalues i : ℝ) : ℂ)⁻¹) * UZᴴ := by
      simpa [UZ, Matrix.star_eq_conjTranspose] using hinv
    rw [hinv0]
    have hleft :
        (Vᴴ * (UZ * Matrix.diagonal
          (fun i => ((hZ.isHermitian.eigenvalues i : ℝ) : ℂ)⁻¹) * UZᴴ) * V).trace =
          (V * (UC * Matrix.diagonal (fun _ : kappa => (1 : ℂ)) * UCᴴ) * Vᴴ *
            (UZ * Matrix.diagonal
              (fun i => ((hZ.isHermitian.eigenvalues i : ℝ) : ℂ)⁻¹) * UZᴴ)).trace := by
      have hdiagone : UC * Matrix.diagonal (fun _ : kappa => (1 : ℂ)) * UCᴴ = 1 := by
        simpa [Matrix.diagonal_one] using hunitC
      rw [hdiagone]
      rw [show Vᴴ * (UZ * Matrix.diagonal
          (fun i => ((hZ.isHermitian.eigenvalues i : ℝ) : ℂ)⁻¹) * UZᴴ) * V =
          (Vᴴ * UZ * Matrix.diagonal
            (fun i => ((hZ.isHermitian.eigenvalues i : ℝ) : ℂ)⁻¹) * UZᴴ) * V by
        simp only [Matrix.mul_assoc]]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc, Matrix.one_mul]
    rw [hleft, hcross]
    simp only [UZ, UC, W, Matrix.diagonal_one]
    push_cast
    simp only [one_mul, mul_one, div_eq_mul_inv]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.inv_re, Complex.inv_im, div_eq_mul_inv, mul_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    field_simp [ne_of_gt (hZ.eigenvalues_pos i)]
  have hsum' : Tendsto
      (fun δ : ℝ => ∑ i, ∑ j, Complex.normSq (W i j) *
        ((∫ t in Set.Ioi (0 : ℝ),
          1 / ((hZ.isHermitian.eigenvalues i + t) *
            (δ * hC.isHermitian.eigenvalues j + t))) /
          Real.log (1 / δ)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((Matrix.trace (Vᴴ * Z⁻¹ * V)).re)) := by
    simpa [htrace_sum] using hsum
  refine hsum'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : 0 < δ := hδ
  rw [trace_logDeriv_formula Z C V hZ hC hδ']
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, UZ, UC, W,
    add_comm, add_left_comm, Finset.mul_sum]

end D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
