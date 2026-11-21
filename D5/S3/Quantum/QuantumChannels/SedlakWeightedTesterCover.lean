/- GID: D5/S3/Quantum/QuantumChannels/SedlakWeightedTesterCover
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SedlakWeightedTesterCover
   mirror-E: none(waiver:effect-weighted-consequence-of-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sums of effect operator norms control one-step tester robustness and are invariant under proportional refinement. -/

import D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality

/-! Effect-weighted positive joint covers for finite one-step testers. -/

namespace Trureturing.OpenProblems.SedlakWeightedTesterCover

open scoped MatrixOrder ComplexOrder BigOperators
open Matrix
open SedlakMaximalTesterOrthogonality (coverEntry IsJointCover compatibleAt_of_jointCover)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality (testerRobustness)

open private coverEntry_psd contraction_square_le self_sandwich density_le_one
  liftInput lift_one lift_mul lift_le lift_psd lift_injective HasNormalization
  robustness_le_of_cover reTrace_pair_nonneg reTrace_pair_mono from
  D5.S3.Quantum.QuantumChannels.SedlakMaximalTesterOrthogonality

set_option autoImplicit false

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
private theorem eq_zero_of_weight_zero {X : Matrix n n ℂ}
    (hX : X.PosSemidef) (h : X ≤ (0 : Matrix n n ℂ)) : X = 0 :=
  le_antisymm h hX.nonneg

omit [Fintype n] in
private theorem normalize_effect {a : ℝ} (ha : 0 < a)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) (hbound : X ≤ a • (1 : Matrix n n ℂ)) :
    (a⁻¹ • X).PosSemidef ∧ a⁻¹ • X ≤ (1 : Matrix n n ℂ) := by
  refine ⟨hX.smul (inv_nonneg.mpr ha.le), Matrix.le_iff.mpr ?_⟩
  have hs := (Matrix.le_iff.mp hbound).smul (inv_nonneg.mpr ha.le)
  simpa only [smul_sub, smul_smul, inv_mul_cancel₀ ha.ne', one_smul] using hs

/-- The weights bound the effects in the positive operator order. -/
def weightedEntry (a b α β ε : ℝ) (X Y : Matrix n n ℂ) : Matrix n n ℂ :=
  ((1 + a * ε^2) * (β / b)) • X +
    ((1 + b * ε^2) * (α / a)) • Y - ε • (X * Y + Y * X)

omit [DecidableEq n] in
private theorem weightedEntry_swap (a b α β ε : ℝ) (X Y : Matrix n n ℂ) :
    weightedEntry a b α β ε X Y = weightedEntry b a β α ε Y X := by
  simp only [weightedEntry, add_comm]

private theorem weightedEntry_psd {a b α β ε : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (he : 0 ≤ ε) (hea : ε ≤ a⁻¹) (heb : ε ≤ b⁻¹)
    {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hXw : X ≤ α • (1 : Matrix n n ℂ)) (hYw : Y ≤ β • (1 : Matrix n n ℂ)) :
    (weightedEntry a b α β ε X Y).PosSemidef := by
  rcases hα.eq_or_lt with hα | hα
  · have hX0 := eq_zero_of_weight_zero hX (by simpa [← hα] using hXw)
    simpa [weightedEntry, ← hα, hX0] using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
  rcases hβ.eq_or_lt with hβ | hβ
  · have hY0 := eq_zero_of_weight_zero hY (by simpa [← hβ] using hYw)
    simpa [weightedEntry, ← hβ, hY0] using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
  let U := α⁻¹ • X
  let V := β⁻¹ • Y
  have hU : U.PosSemidef ∧ U ≤ 1 := normalize_effect hα hX hXw
  have hV : V.PosSemidef ∧ V ≤ 1 := normalize_effect hβ hY hYw
  have hXu : α • U = X := by simp [U, smul_smul, hα.ne']
  have hYv : β • V = Y := by simp [V, smul_smul, hβ.ne']
  have h := ((coverEntry_psd ha hb he hea heb (le_refl (0 : ℝ)) hU.1 hV.1 hU.2 hV.2).add
    (hU.1.smul (show 0 ≤ a * ε^2 / b by positivity))).add
    (hV.1.smul (show 0 ≤ b * ε^2 / a by positivity))
  have hscaled := h.smul (show 0 ≤ α * β by positivity)
  rw [← hXu, ← hYv]
  convert hscaled using 1
  simp only [weightedEntry, coverEntry, zero_mul, zero_div, zero_smul, add_zero,
    smul_add, smul_sub, smul_smul, Matrix.smul_mul, Matrix.mul_smul]
  module

private theorem normalized_row_psd {a b ε : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    {U S : Matrix n n ℂ} (hU : U.PosSemidef) (hS : S.PosSemidef)
    (hU₁ : U ≤ 1) (hS₁ : S ≤ 1) :
    (a⁻¹ • S - ε • (U * S + S * U) + (a * ε^2) • U +
      (b * ε^2 / a) • S).PosSemidef := by
  have hUS : U * S * U ≤ U := by
    refine le_trans (Matrix.le_iff.mpr ?_) (contraction_square_le hU hU₁)
    simpa only [mul_sub, sub_mul, mul_one] using
      self_sandwich hU.isHermitian (Matrix.le_iff.mp hS₁)
  have hfactor : (1 - (a * ε) • U).IsHermitian :=
    Matrix.isHermitian_one.sub (hU.isHermitian.smul (by simp [IsSelfAdjoint]))
  have h := (((self_sandwich hfactor hS).smul (inv_nonneg.mpr ha.le)).add
    ((Matrix.le_iff.mp hUS).smul (show 0 ≤ a * ε^2 by positivity))).add
    (hS.smul (show 0 ≤ b * ε^2 / a by positivity))
  convert h using 1
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
    smul_add, smul_sub, smul_smul]
  have hlin : a⁻¹ * (a * ε) = ε := by field_simp
  have hquad : a⁻¹ * (a * ε * (a * ε)) = a * ε^2 := by field_simp
  rw [hlin, hquad]
  abel

private theorem weighted_row_psd {a b α ε : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 0 ≤ α)
    {X S : Matrix n n ℂ} (hX : X.PosSemidef) (hS : S.PosSemidef)
    (hXw : X ≤ α • (1 : Matrix n n ℂ)) (hS₁ : S ≤ 1) :
    ((a * ε^2) • X + ((1 + b * ε^2) * (α / a)) • S -
      ε • (X * S + S * X)).PosSemidef := by
  rcases hα.eq_or_lt with hα | hα
  · have hX0 := eq_zero_of_weight_zero hX (by simpa [← hα] using hXw)
    simpa [← hα, hX0] using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
  let U := α⁻¹ • X
  have hU : U.PosSemidef ∧ U ≤ 1 := normalize_effect hα hX hXw
  have hXu : α • U = X := by simp [U, smul_smul, hα.ne']
  have hs := (normalized_row_psd (ε := ε) ha hb hU.1 hS hU.2 hS₁).smul hα.le
  rw [← hXu]
  convert hs using 1
  simp only [smul_add, smul_sub, smul_smul, Matrix.smul_mul, Matrix.mul_smul]
  module

private theorem sum_ratio {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hb : (∑ k, b k) ≠ 0) : ∑ k, b k / (∑ l, b l) = 1 := by
  rw [← Finset.sum_div, div_self hb]

omit [DecidableEq n] in
private theorem sum_weightedEntry {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (hb : (∑ k, b k) ≠ 0) (a α ε : ℝ) (X : Matrix n n ℂ)
    (Y : ι → Matrix n n ℂ) :
    ∑ k, weightedEntry a (∑ l, b l) α (b k) ε X (Y k) =
      (1 + a * ε^2) • X + ((1 + (∑ l, b l) * ε^2) * (α / a)) • (∑ k, Y k) -
        ε • (X * (∑ k, Y k) + (∑ k, Y k) * X) := by
  simp only [weightedEntry, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_smul, ← Finset.mul_sum, sum_ratio b hb, mul_one]
  simp only [← Finset.smul_sum, Finset.sum_add_distrib, ← Matrix.mul_sum, ← Matrix.sum_mul]

variable {d0 d1 p q : ℕ}
variable {A : Fin p → Matrix (Fin d1 × Fin d0) (Fin d1 × Fin d0) ℂ}
variable {B : Fin q → Matrix (Fin d1 × Fin d0) (Fin d1 × Fin d0) ℂ}
variable {ρ σ : Matrix (Fin d0) (Fin d0) ℂ}

/-- A positive joint cover with effect-dependent weights and quadratic cost
in the input normalizations rather than in the input dimension. -/
theorem weightedJointCover (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hA : HasNormalization A ρ) (hB : HasNormalization B σ)
    (α : Fin p → ℝ) (β : Fin q → ℝ)
    (hα : ∀ j, 0 ≤ α j) (hβ : ∀ k, 0 ≤ β k)
    (ha : 0 < ∑ j, α j) (hb : 0 < ∑ k, β k)
    (hAw : ∀ j, A j ≤ α j • 1) (hBw : ∀ k, B k ≤ β k • 1)
    {ε : ℝ} (he : 0 ≤ ε) (hea : ε ≤ (∑ j, α j)⁻¹) (heb : ε ≤ (∑ k, β k)⁻¹) :
    let a := ∑ j, α j
    let b := ∑ k, β k
    IsJointCover A B
      (fun jk => weightedEntry a b (α jk.1) (β jk.2) ε (A jk.1) (B jk.2))
      ((1 + a * ε^2) • ρ + (1 + b * ε^2) • σ - ε • (ρ * σ + σ * ρ)) := by
  dsimp only
  have hR := lift_psd (d1 := d1) hρ.1
  have hS := lift_psd (d1 := d1) hσ.1
  have hR₁ := lift_le (d1 := d1) ρ 1 (density_le_one hρ)
  have hS₁ := lift_le (d1 := d1) σ 1 (density_le_one hσ)
  rw [lift_one] at hR₁ hS₁
  refine ⟨fun jk => weightedEntry_psd ha hb (hα _) (hβ _) he hea heb
    (hA.1 _) (hB.1 _) (hAw _) (hBw _), ?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    simp_rw [sum_weightedEntry β hb.ne', hB.2]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum,
      ← Matrix.mul_sum, ← Matrix.sum_mul]
    rw [← Finset.sum_smul, ← Finset.mul_sum, sum_ratio α ha.ne', mul_one, hA.2]
    simp only [map_smul, map_add, map_sub, lift_mul]
  · intro j
    simp only
    rw [sum_weightedEntry β hb.ne', hB.2, Matrix.le_iff]
    have hh := weighted_row_psd (ε := ε) ha hb (hα j) (hA.1 j) hS (hAw j) hS₁
    convert hh using 1
    module
  · intro k
    simp_rw [weightedEntry_swap (∑ j, α j) (∑ k, β k)]
    rw [sum_weightedEntry α ha.ne', hA.2, Matrix.le_iff]
    have hh := weighted_row_psd (ε := ε) hb ha (hβ k) (hB.1 k) hR (hBw k) hR₁
    convert hh using 1
    module

private theorem trace_weightedNormalization (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (a b ε : ℝ) :
    ((1 + a * ε^2) • ρ + (1 + b * ε^2) • σ -
      ε • (ρ * σ + σ * ρ)).trace.re =
        2 - 2 * ε * (ρ * σ).trace.re + (a + b) * ε^2 := by
  have hcomm : (σ * ρ).trace = (ρ * σ).trace := Matrix.trace_mul_comm _ _
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, hρ.2, hσ.2,
    hcomm, Complex.add_re, Complex.sub_re, Complex.smul_re, Complex.one_re, smul_eq_mul]
  ring

/-- The upper bound depends only on the normalization overlap and the effect
weight totals. The totals are preserved by proportional effect refinement. -/
theorem weightedRobustnessBound (h1 : 0 < d1) (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hA : HasNormalization A ρ) (hB : HasNormalization B σ)
    (α : Fin p → ℝ) (β : Fin q → ℝ)
    (hα : ∀ j, 0 ≤ α j) (hβ : ∀ k, 0 ≤ β k)
    (ha : 0 < ∑ j, α j) (hb : 0 < ∑ k, β k)
    (hAw : ∀ j, A j ≤ α j • 1) (hBw : ∀ k, B k ≤ β k • 1) :
    testerRobustness A B ≤
      1 - (2 - (ρ * σ).trace.re^2 / ((∑ j, α j) + ∑ k, β k))⁻¹ := by
  let a := ∑ j, α j
  let b := ∑ k, β k
  let δ := (ρ * σ).trace.re
  let ε := δ / (a + b)
  have hδ : 0 ≤ δ := reTrace_pair_nonneg hρ.1 hσ.1
  have hδ₁ : δ ≤ 1 := by
    simpa only [mul_one, hρ.2, Complex.one_re] using reTrace_pair_mono hρ.1 (density_le_one hσ)
  have hab : 0 < a + b := add_pos ha hb
  have he : ε ≤ (a + b)⁻¹ := by
    rw [← one_div]
    exact div_le_div_of_nonneg_right hδ₁ hab.le
  have hc := weightedJointCover hρ hσ hA hB α β hα hβ ha hb hAw hBw
    (ε := ε) (div_nonneg hδ hab.le)
    (he.trans (inv_anti₀ ha (le_add_of_nonneg_right hb.le)))
    (he.trans (inv_anti₀ hb (le_add_of_nonneg_left ha.le)))
  have hr := robustness_le_of_cover h1 hρ hσ hA hB hc
  rw [trace_weightedNormalization hρ hσ] at hr
  have ht : 2 - 2 * ε * δ + (a + b) * ε^2 = 2 - δ^2 / (a + b) := by
    dsimp only [ε]
    field_simp
    ring
  rwa [ht] at hr


open scoped Matrix.Norms.L2Operator

private theorem posSemidef_le_norm_smul_one {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    X ≤ ‖X‖ • (1 : Matrix n n ℂ) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  exact (isHermitian_iff_isSelfAdjoint.mp hX.isHermitian).le_algebraMap_norm_self X

private theorem sum_effect_norm_pos (h1 : 0 < d1) (hρ : IsDensity ρ)
    (hA : HasNormalization A ρ) : 0 < ∑ j, ‖A j‖ := by
  have hnonneg : 0 ≤ ∑ j, ‖A j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  by_contra! h
  have hn : ∑ j, ‖A j‖ = 0 := le_antisymm h hnonneg
  have hA0 (j : Fin p) : A j = 0 := by
    apply norm_eq_zero.mp
    refine le_antisymm ?_ (norm_nonneg _)
    rw [← hn]
    exact Finset.single_le_sum (fun i _ => norm_nonneg (A i)) (Finset.mem_univ j)
  have hlift : liftInput ρ = (0 : Matrix (Fin d1 × Fin d0) (Fin d1 × Fin d0) ℂ) := by
    rw [← hA.2]
    simp [hA0]
  have hρ0 : ρ = 0 := lift_injective h1 (by simpa using hlift)
  simpa [hρ0] using hρ.2

/-- A dimension-independent bound controlled by the sum of the operator norms
of the effects. It applies to singular states and to zero effects. -/
theorem opNormRobustnessBound (h1 : 0 < d1) (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hA : HasNormalization A ρ) (hB : HasNormalization B σ) :
    testerRobustness A B ≤
      1 - (2 - (ρ * σ).trace.re^2 / ((∑ j, ‖A j‖) + ∑ k, ‖B k‖))⁻¹ :=
  weightedRobustnessBound h1 hρ hσ hA hB (fun j => ‖A j‖) (fun k => ‖B k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (sum_effect_norm_pos h1 hρ hA) (sum_effect_norm_pos h1 hσ hB)
    (fun j => posSemidef_le_norm_smul_one (hA.1 j))
    (fun k => posSemidef_le_norm_smul_one (hB.1 k))

/-- Splitting any effect into nonnegative proportional parts preserves the
operator-norm total in the robustness bound. -/
theorem sum_effect_norm_refinement {ι : Type*} [Fintype ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] (A : ι → Matrix n n ℂ)
    (θ : ∀ i, κ i → ℝ) (hθ : ∀ i j, 0 ≤ θ i j) (hsum : ∀ i, ∑ j, θ i j = 1) :
    ∑ z : Sigma κ, ‖θ z.1 z.2 • A z.1‖ = ∑ i, ‖A i‖ := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [norm_smul, Real.norm_of_nonneg (hθ i _)]
  rw [← Finset.sum_mul, hsum, one_mul]

end

end Trureturing.OpenProblems.SedlakWeightedTesterCover
