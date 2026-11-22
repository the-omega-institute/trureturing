/- GID: D5/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SedlakMaximalTesterOrthogonality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: One-step testers are maximally incompatible exactly when their normalization states are orthogonal. -/

import D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality
import D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Proj
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-! The maximal-incompatibility criterion for one-step testers in §V.C of
Sedlák, Reitzner, Chiribella and Ziman (arXiv:1511.00976v2, preregistration #24241).
The upper bound uses an explicit joint cover with a quadratic correction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Trureturing.OpenProblems.SedlakMaximalTesterOrthogonality

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.QuantumChannels.AncillaFreeTesterRobustnessEquality
  (IsTester TesterCompatibleAt testerRobustness)
open D5.S3.Quantum.Measurements.FiniteMemoryHistoryCapacity (zero_trace_mul_eq_zero)

private theorem density_le_one {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : IsDensity A) : A ≤ 1 := by
  let H : HermitianMat n ℂ := ⟨A, hA.1.isHermitian⟩
  have h := HermitianMat.le_trace_smul_one (HermitianMat.zero_le_iff.mpr hA.1 : 0 ≤ H)
  change A ≤ A.trace.re • (1 : Matrix n n ℂ) at h
  simpa only [hA.2, Complex.one_re, one_smul] using h

private theorem reTrace_pair_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ (X * Y).trace.re :=
  RHLinalg.trace_mul_nonneg_of_posSemidef hX hY

private theorem trace_pair_real {n : Type*} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    ((X * Y).trace.re : ℂ) = (X * Y).trace := by
  have h : star (X * Y).trace = (X * Y).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      hX.isHermitian.eq, hY.isHermitian.eq, Matrix.trace_mul_comm]
  apply Complex.ext
  · simp
  · have hi := congrArg Complex.im h
    simp at hi ⊢
    linarith

private theorem reTrace_pair_mono {n : Type*} [Fintype n] [DecidableEq n]
    {X Y Z : Matrix n n ℂ} (hX : X.PosSemidef) (hYZ : Y ≤ Z) :
    (X * Y).trace.re ≤ (X * Z).trace.re := by
  have h := reTrace_pair_nonneg hX (Matrix.le_iff.mp hYZ)
  rwa [mul_sub, Matrix.trace_sub, Complex.sub_re, sub_nonneg] at h

private theorem contraction_square_le {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.PosSemidef) (hX₁ : X ≤ 1) : X * X ≤ X := by
  have h := ((Commute.one_right X).sub_right (Commute.refl X)).mul_nonneg
    hX.nonneg (sub_nonneg.mpr hX₁)
  rwa [mul_sub, mul_one, sub_nonneg] at h

private theorem self_sandwich {n : Type*} [Fintype n] [DecidableEq n]
    {X Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Y.PosSemidef) :
    (X * Y * X).PosSemidef := by
  simpa only [hX.eq] using hY.conjTranspose_mul_mul_same X

private theorem effect_le_sum {n : Type*} [Fintype n] {i : Type*} [Fintype i]
    {A : i → Matrix n n ℂ} (hA : ∀ j, (A j).PosSemidef) (j : i) :
    A j ≤ ∑ a, A a := by
  classical
  exact Finset.single_le_sum (fun a _ => (hA a).nonneg) (Finset.mem_univ j)

section Tensor

variable {d0 d1 : ℕ}

private abbrev Input (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
private abbrev Joint (d0 d1 : ℕ) := Matrix (Fin d1 × Fin d0) (Fin d1 × Fin d0) ℂ

private def liftInput : Input d0 →ₗ[ℝ] Joint d0 d1 where
  toFun X := (1 : Input d1) ⊗ₖ X
  map_add' := Matrix.kronecker_add _
  map_smul' := fun r X => Matrix.kronecker_smul r _ X

private theorem lift_one : liftInput (1 : Input d0) = (1 : Joint d0 d1) :=
  Matrix.one_kronecker_one

private theorem lift_mul (X Y : Input d0) :
    liftInput (X * Y) = (liftInput X : Joint d0 d1) * liftInput Y := by
  simpa only [liftInput, LinearMap.coe_mk, AddHom.coe_mk, Matrix.one_mul] using
    Matrix.mul_kronecker_mul (1 : Input d1) 1 X Y

private theorem lift_psd {X : Input d0} (hX : X.PosSemidef) :
    (liftInput X : Joint d0 d1).PosSemidef :=
  Matrix.PosSemidef.one.kronecker hX

private theorem lift_psd_iff (h1 : 0 < d1) {X : Input d0} :
    (liftInput X : Joint d0 d1).PosSemidef ↔ X.PosSemidef := by
  refine ⟨fun h => ?_, lift_psd⟩
  let a : Fin d1 := ⟨0, h1⟩
  have hs := h.submatrix (fun i => (a, i))
  convert hs using 1
  ext i j
  change _ = (1 : Input d1) a a * X i j
  rw [Matrix.one_apply_eq, one_mul]

private theorem lift_le (X Y : Input d0) (h : X ≤ Y) :
    (liftInput X : Joint d0 d1) ≤ liftInput Y := by
  rw [Matrix.le_iff, ← map_sub]
  exact lift_psd (Matrix.le_iff.mp h)

private theorem lift_le_iff (h1 : 0 < d1) {X Y : Input d0} :
    (liftInput X : Joint d0 d1) ≤ liftInput Y ↔ X ≤ Y := by
  rw [Matrix.le_iff, ← map_sub, Matrix.le_iff, lift_psd_iff h1]

private theorem lift_injective (h1 : 0 < d1) :
    Function.Injective (liftInput : Input d0 →ₗ[ℝ] Joint d0 d1) := by
  intro X Y h
  exact le_antisymm ((lift_le_iff h1).mp h.le) ((lift_le_iff h1).mp h.ge)

end Tensor

section Cover

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- One entry of the explicit joint cover. -/
def coverEntry (p q ε M : ℝ) (X Y : Matrix n n ℂ) : Matrix n n ℂ :=
  q⁻¹ • X + p⁻¹ • Y - ε • (X * Y + Y * X) + (M * ε^2 / (p * q)) • 1

private theorem coverEntry_swap (p q ε M : ℝ) (X Y : Matrix n n ℂ) :
    coverEntry p q ε M X Y = coverEntry q p ε M Y X := by
  simp only [coverEntry, add_comm, mul_comm p q]

private theorem coverEntry_psd {p q ε M : ℝ} (hp : 0 < p) (hq : 0 < q)
    (he : 0 ≤ ε) (hep : ε ≤ p⁻¹) (heq : ε ≤ q⁻¹) (hM : 0 ≤ M)
    {X Y : Matrix n n ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hX₁ : X ≤ 1) (hY₁ : Y ≤ 1) :
    (coverEntry p q ε M X Y).PosSemidef := by
  have hs : (X * X + Y * Y - (X * Y + Y * X)).PosSemidef := by
    convert Matrix.posSemidef_conjTranspose_mul_self (X - Y) using 1
    rw [(hX.isHermitian.sub hY.isHermitian).eq]
    noncomm_ring
  have h := (((((hX.smul (sub_nonneg.mpr heq)).add (hY.smul (sub_nonneg.mpr hep))).add
    ((Matrix.le_iff.mp (contraction_square_le hX hX₁)).smul he)).add
    ((Matrix.le_iff.mp (contraction_square_le hY hY₁)).smul he)).add (hs.smul he)).add
    (Matrix.PosSemidef.one.smul (show 0 ≤ M * ε^2 / (p * q) by positivity))
  convert h using 1
  simp only [coverEntry, smul_add, smul_sub, sub_smul]
  abel

private theorem coverRow_psd {p ε M : ℝ} (hp : 0 < p) (hM : p^2 ≤ M)
    {X S : Matrix n n ℂ} (hX : X.PosSemidef) (hS : S.PosSemidef)
    (hX₁ : X ≤ 1) (hS₁ : S ≤ 1) :
    (p⁻¹ • S - ε • (X * S + S * X) + (M * ε^2 / p) • (1 : Matrix n n ℂ)).PosSemidef := by
  have hXS : X * S * X ≤ 1 := by
    apply le_trans _ ((contraction_square_le hX hX₁).trans hX₁)
    apply Matrix.le_iff.mpr
    simpa only [mul_sub, sub_mul, mul_one] using
      self_sandwich hX.isHermitian (Matrix.le_iff.mp hS₁)
  have hcorr : (M • (1 : Matrix n n ℂ) - p^2 • (X * S * X)).PosSemidef := by
    have h := (Matrix.PosSemidef.one.smul (sub_nonneg.mpr hM)).add
      ((Matrix.le_iff.mp hXS).smul (sq_nonneg p))
    simpa only [sub_smul, smul_sub, sub_add_sub_cancel] using h
  have hfactor : (1 - (p * ε) • X).IsHermitian :=
    Matrix.isHermitian_one.sub (hX.isHermitian.smul (by simp [IsSelfAdjoint]))
  have h := ((self_sandwich hfactor hS).smul (inv_nonneg.mpr hp.le)).add
    (hcorr.smul (show 0 ≤ ε^2 / p by positivity))
  convert h using 1
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
    smul_add, smul_sub, smul_smul]
  have hpε : p⁻¹ * (p * ε) = ε := by field_simp
  have hpε₂ : p⁻¹ * (p * ε * (p * ε)) = ε^2 / p * p^2 := by field_simp
  rw [hpε, hpε₂]
  rw [show ε^2 / p * M = M * ε^2 / p by ring]
  abel

private theorem sum_coverRow {p q : ℕ} (hq : 0 < q) (ε M : ℝ)
    (X : Matrix n n ℂ) (B : Fin q → Matrix n n ℂ) :
    (∑ k, coverEntry p q ε M X (B k)) =
      X + ((p : ℝ)⁻¹ • (∑ k, B k) -
        ε • (X * (∑ k, B k) + (∑ k, B k) * X) +
        (M * ε^2 / p) • (1 : Matrix n n ℂ)) := by
  simp only [coverEntry, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.smul_sum, ← Matrix.mul_sum, ← Matrix.sum_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [inv_mul_cancel₀ hq', one_smul]
  rw [show (M * ε^2 / ((p : ℝ) * q)) * q = M * ε^2 / p by
    rw [div_mul_eq_div_div, div_mul_cancel₀ _ hq']]
  abel

end Cover

section Testers

variable {d0 d1 p q : ℕ}
variable {A : Fin p → Joint d0 d1} {B : Fin q → Joint d0 d1}
variable {ρ σ : Input d0}

private abbrev HasNormalization {r : ℕ} (E : Fin r → Joint d0 d1) (ω : Input d0) :=
  (∀ i, (E i).PosSemidef) ∧ ∑ i, E i = liftInput ω

/-- A positive joint family with marginals that dominate the two testers. -/
structure IsJointCover (A : Fin p → Joint d0 d1) (B : Fin q → Joint d0 d1)
    (C : Fin p × Fin q → Joint d0 d1) (H : Input d0) : Prop where
  positive : ∀ jk, (C jk).PosSemidef
  total : ∑ jk, C jk = liftInput H
  row : ∀ j, A j ≤ ∑ k, C (j, k)
  col : ∀ k, B k ≤ ∑ j, C (j, k)

/-- The explicit joint cover for the maximal-incompatibility question in §V.C. -/
theorem explicitJointCover (hp : 0 < p) (hq : 0 < q)
    (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hA : HasNormalization A ρ) (hB : HasNormalization B σ)
    {ε M : ℝ} (he : 0 ≤ ε) (hep : ε ≤ (p : ℝ)⁻¹) (heq : ε ≤ (q : ℝ)⁻¹)
    (hMp : (p : ℝ)^2 ≤ M) (hMq : (q : ℝ)^2 ≤ M) :
    IsJointCover A B (fun jk => coverEntry p q ε M (A jk.1) (B jk.2))
      (ρ + σ - ε • (ρ * σ + σ * ρ) + (M * ε^2) • 1) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hR := lift_psd (d1 := d1) hρ.1
  have hS := lift_psd (d1 := d1) hσ.1
  have hR₁ : (liftInput ρ : Joint d0 d1) ≤ 1 := by
    simpa only [lift_one] using lift_le (d1 := d1) ρ 1 (density_le_one hρ)
  have hS₁ : (liftInput σ : Joint d0 d1) ≤ 1 := by
    simpa only [lift_one] using lift_le (d1 := d1) σ 1 (density_le_one hσ)
  have hA₁ (j : Fin p) : A j ≤ 1 :=
    (effect_le_sum hA.1 j).trans (hA.2.symm ▸ hR₁)
  have hB₁ (k : Fin q) : B k ≤ 1 :=
    (effect_le_sum hB.1 k).trans (hB.2.symm ▸ hS₁)
  refine ⟨fun jk => coverEntry_psd hp' hq' he hep heq
    ((sq_nonneg (p : ℝ)).trans hMp) (hA.1 jk.1) (hB.1 jk.2) (hA₁ jk.1) (hB₁ jk.2),
    ?_, ?_, ?_⟩
  · rw [Fintype.sum_prod_type]
    simp_rw [sum_coverRow hq, hB.2]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.smul_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [hA.2, inv_mul_cancel₀ hp'.ne', one_smul, div_mul_cancel₀ _ hp'.ne']
    simp only [map_add, map_sub, map_smul, lift_mul, lift_one]
    abel
  · intro j
    dsimp only
    rw [sum_coverRow hq, hB.2, Matrix.le_iff, add_sub_cancel_left]
    exact coverRow_psd hp' hMp (hA.1 j) hS (hA₁ j) hS₁
  · intro k
    dsimp only
    simp_rw [coverEntry_swap (p : ℝ) (q : ℝ), sum_coverRow hp]
    rw [hA.2, Matrix.le_iff, add_sub_cancel_left]
    exact coverRow_psd hq' hMq (hB.1 k) hR (hB₁ k) hR₁

private theorem reTrace_mono {X Y : Input d0} (h : X ≤ Y) : X.trace.re ≤ Y.trace.re := by
  have ht := (Complex.nonneg_iff.mp (Matrix.le_iff.mp h).trace_nonneg).1
  rwa [Matrix.trace_sub, Complex.sub_re, sub_nonneg] at ht

private theorem psd_of_lift_sum {i : Type*} [Fintype i] {L : i → Joint d0 d1} {X : Input d0}
    (h1 : 0 < d1) (hL : ∀ j, (L j).PosSemidef) (hX : ∑ j, L j = liftInput X) :
    X.PosSemidef := by
  apply (lift_psd_iff h1).mp
  rw [← hX]
  exact Matrix.posSemidef_sum _ (fun j _ => hL j)

private theorem sum_slack_eq_zero {i : Type*} [Fintype i] {L : i → Joint d0 d1}
    {X : Input d0} (h1 : 0 < d1) (hL : ∀ j, (L j).PosSemidef)
    (hX : ∑ j, L j = liftInput X) (htr : X.trace = 0) : ∀ j, L j = 0 := by
  have hx := (psd_of_lift_sum h1 hL hX).trace_eq_zero_iff.mp htr
  have hz : ∑ j, L j = 0 := by rw [hX, hx, map_zero]
  intro j
  exact le_antisymm ((effect_le_sum hL j).trans_eq hz) (hL j).nonneg

/-- Normalizing a positive joint cover gives feasible noise at its trace parameter. -/
theorem compatibleAt_of_jointCover (h1 : 0 < d1)
    (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hA : HasNormalization A ρ) (hB : HasNormalization B σ)
    {C : Fin p × Fin q → Joint d0 d1} {H : Input d0}
    (hC : IsJointCover A B C H) :
    let t := H.trace.re
    1 ≤ t ∧ TesterCompatibleAt (1 - t⁻¹) A B := by
  let row : Fin p → Joint d0 d1 := fun j => (∑ k, C (j, k)) - A j
  let col : Fin q → Joint d0 d1 := fun k => (∑ j, C (j, k)) - B k
  have hr (j) : (row j).PosSemidef := Matrix.le_iff.mp (hC.row j)
  have hc (k) : (col k).PosSemidef := Matrix.le_iff.mp (hC.col k)
  have hrt : ∑ j, row j = liftInput (H - ρ) := by
    simp only [row, Finset.sum_sub_distrib, ← Fintype.sum_prod_type, hC.total, hA.2, map_sub]
  have hct : ∑ k, col k = liftInput (H - σ) := by
    simp only [col, Finset.sum_sub_distrib, ← Fintype.sum_prod_type_right, hC.total, hB.2, map_sub]
  have hHr := psd_of_lift_sum h1 hr hrt
  have hHs := psd_of_lift_sum h1 hc hct
  have hH := psd_of_lift_sum h1 hC.positive hC.total
  let t := H.trace.re
  have htrace : H.trace = (t : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp hH.trace_nonneg).2.symm
  have ht : 1 ≤ t := by simpa only [hρ.2, Complex.one_re] using reTrace_mono (Matrix.le_iff.mpr hHr)
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  refine ⟨ht, ?_⟩
  change TesterCompatibleAt (1 - t⁻¹) A B
  have testerOfScale {i : Type} [Fintype i] {L : i → Joint d0 d1} {X : Input d0}
      (hL : ∀ j, (L j).PosSemidef) (hX : ∑ j, L j = liftInput X)
      (r : ℝ) (hr₀ : 0 < r) (htr : X.trace = (r : ℂ)) :
      IsTester (fun j => r⁻¹ • L j) := by
    refine ⟨fun j => (hL j).smul (inv_nonneg.mpr hr₀.le), r⁻¹ • X,
      ⟨(psd_of_lift_sum h1 hL hX).smul (inv_nonneg.mpr hr₀.le), ?_⟩, ?_⟩
    · rw [Matrix.trace_smul, htr, Complex.real_smul, ← Complex.ofReal_mul,
        inv_mul_cancel₀ hr₀.ne', Complex.ofReal_one]
    · change (∑ j, r⁻¹ • L j) = liftInput (r⁻¹ • X)
      simp only [← Finset.smul_sum, hX, map_smul]
  rcases ht.eq_or_lt with ht₁ | ht₁
  · have hz (ω : Input d0) (hω : IsDensity ω) : (H - ω).trace = 0 := by
      rw [Matrix.trace_sub, htrace, ← ht₁, Complex.ofReal_one, hω.2, sub_self]
    have hrow := sum_slack_eq_zero h1 hr hrt (hz ρ hρ)
    have hcol := sum_slack_eq_zero h1 hc hct (hz σ hσ)
    have HC : IsTester C := ⟨hC.positive, H,
      ⟨hH, by rw [htrace, ← ht₁, Complex.ofReal_one]⟩, hC.total⟩
    rw [← ht₁]
    refine ⟨A, B, C, ⟨hA.1, ρ, hρ, hA.2⟩, ⟨hB.1, σ, hσ, hB.2⟩, HC, ?_, ?_⟩
    · intro j
      simpa using sub_eq_zero.mp (hrow j)
    · intro k
      simpa using sub_eq_zero.mp (hcol k)
  · have hslack (ω : Input d0) (hω : IsDensity ω) :
        (H - ω).trace = ((t - 1 : ℝ) : ℂ) := by
      rw [Matrix.trace_sub, htrace, hω.2, Complex.ofReal_sub, Complex.ofReal_one]
    have hcoeff : (1 - t⁻¹) * (t - 1)⁻¹ = t⁻¹ := by field_simp
    refine ⟨fun j => (t - 1)⁻¹ • row j, fun k => (t - 1)⁻¹ • col k,
      fun jk => t⁻¹ • C jk,
      testerOfScale hr hrt _ (sub_pos.mpr ht₁) (hslack ρ hρ),
      testerOfScale hc hct _ (sub_pos.mpr ht₁) (hslack σ hσ),
      testerOfScale hC.positive hC.total t ht₀ htrace, ?_, ?_⟩
    · intro j
      simp only [← Finset.smul_sum, sub_sub_cancel, smul_smul, hcoeff, row, smul_sub]
      abel
    · intro k
      simp only [← Finset.smul_sum, sub_sub_cancel, smul_smul, hcoeff, col, smul_sub]
      abel

private theorem robustness_le_of_compatible {lam : ℝ}
    (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1) (h : TesterCompatibleAt lam A B) :
    testerRobustness A B ≤ lam := by
  apply csInf_le _ (show lam ∈ {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ TesterCompatibleAt r A B} from
    ⟨h₀, h₁, h⟩)
  exact ⟨0, fun _ hr => hr.1⟩

private theorem robustness_le_of_cover (h1 : 0 < d1)
    (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hA : HasNormalization A ρ) (hB : HasNormalization B σ)
    {C : Fin p × Fin q → Joint d0 d1} {H : Input d0} (hC : IsJointCover A B C H) :
    testerRobustness A B ≤ 1 - (H.trace.re)⁻¹ := by
  obtain ⟨ht, hc⟩ := compatibleAt_of_jointCover h1 hρ hσ hA hB hC
  exact robustness_le_of_compatible (sub_nonneg.mpr (inv_le_one_of_one_le₀ ht))
    (sub_le_self _ (inv_nonneg.mpr (zero_le_one.trans ht))) hc

private theorem trace_coverNormalization (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (ε M : ℝ) :
    (ρ + σ - ε • (ρ * σ + σ * ρ) + (M * ε^2) • (1 : Input d0)).trace.re =
      2 - 2 * ε * (ρ * σ).trace.re + M * ε^2 * d0 := by
  have hcomm : (σ * ρ).trace = (ρ * σ).trace := Matrix.trace_mul_comm _ _
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, hρ.2, hσ.2, hcomm, Complex.add_re, Complex.sub_re, Complex.smul_re,
    Complex.one_re, Complex.natCast_re, smul_eq_mul]
  ring

private theorem half_compatible (h1 : 0 < d1) (hp : 0 < p) (hq : 0 < q)
    (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hA : HasNormalization A ρ) (hB : HasNormalization B σ) :
    TesterCompatibleAt (1 / 2 : ℝ) A B := by
  let M : ℝ := max ((p : ℝ)^2) ((q : ℝ)^2)
  have hc := explicitJointCover hp hq hρ hσ hA hB (ε := 0) (M := M) le_rfl
    (by positivity) (by positivity) (le_max_left _ _) (le_max_right _ _)
  have ht := (compatibleAt_of_jointCover h1 hρ hσ hA hB hc).2
  rw [trace_coverNormalization hρ hσ] at ht
  norm_num at ht ⊢
  exact ht

/-- Nonorthogonal normalizations yield a strict constructive upper bound, with an
explicit comparison parameter for the repository's tester robustness. -/
theorem nonorthogonal_upper_bound (h0 : 0 < d0) (h1 : 0 < d1) (hp : 0 < p) (hq : 0 < q)
    (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hA : HasNormalization A ρ) (hB : HasNormalization B σ) (hne : ρ * σ ≠ 0) :
    let t : ℝ := 2 - (ρ * σ).trace.re ^ 2 / ((max (p : ℝ) (q : ℝ))^2 * d0)
    1 ≤ t ∧ testerRobustness A B ≤ 1 - t⁻¹ ∧ 1 - t⁻¹ < 1 / 2 := by
  let δ := (ρ * σ).trace.re
  let b := max (p : ℝ) (q : ℝ)
  let M := b^2
  let ε := δ / (M * d0)
  have hδ : 0 < δ := by
    refine lt_of_le_of_ne (reTrace_pair_nonneg hρ.1 hσ.1) (fun hz => hne ?_)
    apply zero_trace_mul_eq_zero _ _ hρ.1 hσ.1
    rw [← trace_pair_real hρ.1 hσ.1]
    change (δ : ℂ) = 0
    rw [← hz, Complex.ofReal_zero]
  have hδ₁ : δ ≤ 1 := by
    simpa only [mul_one, hρ.2, Complex.one_re] using reTrace_pair_mono hρ.1 (density_le_one hσ)
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have h0' : (1 : ℝ) ≤ d0 := by exact_mod_cast h0
  have hpb : (p : ℝ) ≤ b := le_max_left _ _
  have hqb : (q : ℝ) ≤ b := le_max_right _ _
  have hb : 1 ≤ b := hp'.trans hpb
  have hb₀ : 0 < b := zero_lt_one.trans_le hb
  have hM : 0 < M * (d0 : ℝ) := by positivity
  have he : ε ≤ b⁻¹ := by
    apply (div_le_iff₀ hM).mpr
    have hmul : 1 ≤ b * (d0 : ℝ) := one_le_mul_of_one_le_of_one_le hb h0'
    have hid : b⁻¹ * (M * d0) = b * d0 := by
      dsimp only [M]
      field_simp
    rw [hid]
    exact hδ₁.trans hmul
  have hc := explicitJointCover hp hq hρ hσ hA hB (ε := ε) (M := M)
    (div_nonneg hδ.le hM.le)
    (he.trans (inv_anti₀ (zero_lt_one.trans_le hp') hpb))
    (he.trans (inv_anti₀ (zero_lt_one.trans_le hq') hqb))
    (pow_le_pow_left₀ (by positivity) hpb _) (pow_le_pow_left₀ (by positivity) hqb _)
  have htrace : (ρ + σ - ε • (ρ * σ + σ * ρ) + (M * ε^2) • (1 : Input d0)).trace.re =
      2 - δ ^ 2 / (M * d0) := by
    rw [trace_coverNormalization hρ hσ]
    change 2 - 2 * ε * δ + M * ε ^ 2 * (d0 : ℝ) = _
    dsimp only [ε]
    field_simp
    ring
  have ht₁ := (compatibleAt_of_jointCover h1 hρ hσ hA hB hc).1
  have hr := robustness_le_of_cover h1 hρ hσ hA hB hc
  rw [htrace] at ht₁ hr
  refine ⟨ht₁, hr, ?_⟩
  have ht₂ : 2 - δ ^ 2 / (M * d0) < 2 := sub_lt_self _ (div_pos (sq_pos_of_pos hδ) hM)
  have hi := one_div_lt_one_div_of_lt (zero_lt_one.trans_le ht₁) ht₂
  change 1 - (2 - δ ^ 2 / (M * d0))⁻¹ < 1 / 2
  rw [← one_div]
  linarith

private theorem mul_eq_zero_iff_range_le_ker (X Y : Input d0) :
    X * Y = 0 ↔ LinearMap.range Y.toEuclideanLin ≤ LinearMap.ker X.toEuclideanLin := by
  rw [LinearMap.range_le_ker_iff]
  constructor
  · intro h
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, map_zero] using
      congrArg Matrix.toEuclideanLin h
  · intro h
    apply Matrix.toEuclideanLin.injective
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, map_zero] using h

private theorem trace_bound_of_orthogonal {K : Input d0} {a : ℝ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hz : ρ * σ = 0)
    (hKr : a • ρ ≤ K) (hKs : a • σ ≤ K) : 2 * a ≤ K.trace.re := by
  let R : HermitianMat (Fin d0) ℂ := ⟨ρ, hρ.1.isHermitian⟩
  let P := R.supportProj
  let Q := R.kerProj
  have hP : P.mat.PosSemidef :=
    HermitianMat.zero_le_iff.mp (HermitianMat.projector_nonneg R.support)
  have hQ : Q.mat.PosSemidef :=
    HermitianMat.zero_le_iff.mp (HermitianMat.projector_nonneg R.ker)
  have hQP : Q.mat + P.mat = 1 := by
    simpa only [HermitianMat.mat_add, HermitianMat.mat_one] using
      congrArg HermitianMat.mat R.kerProj_add_supportProj
  have hQr : Q.mat * ρ = 0 := by
    apply (mul_eq_zero_iff_range_le_ker _ _).mpr
    change R.support ≤ Q.ker
    rw [show Q.ker = R.support from R.kerProj_ker]
  have hPs : P.mat * σ = 0 := by
    apply (mul_eq_zero_iff_range_le_ker _ _).mpr
    change LinearMap.range σ.toEuclideanLin ≤ P.ker
    rw [show P.ker = R.ker from R.supportProj_ker]
    exact (mul_eq_zero_iff_range_le_ker ρ σ).mp hz
  have hPr : P.mat * ρ = ρ := by
    have h := congrArg (fun X : Input d0 => X * ρ) hQP
    simpa only [add_mul, one_mul, hQr, zero_add] using h
  have hQs : Q.mat * σ = σ := by
    have h := congrArg (fun X : Input d0 => X * σ) hQP
    simpa only [add_mul, one_mul, hPs, add_zero] using h
  have hr := reTrace_pair_mono hP hKr
  have hs := reTrace_pair_mono hQ hKs
  rw [Matrix.mul_smul, hPr, Matrix.trace_smul, Complex.smul_re, hρ.2,
    Complex.one_re, smul_eq_mul, mul_one] at hr
  rw [Matrix.mul_smul, hQs, Matrix.trace_smul, Complex.smul_re, hσ.2,
    Complex.one_re, smul_eq_mul, mul_one] at hs
  have hsplit : (Q.mat * K).trace.re + (P.mat * K).trace.re = K.trace.re := by
    rw [← Complex.add_re, ← Matrix.trace_add, ← add_mul, hQP, one_mul]
  linarith

private theorem half_le_of_orthogonal_compatible (h1 : 0 < d1)
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hz : ρ * σ = 0)
    (hA : HasNormalization A ρ) (hB : HasNormalization B σ) {lam : ℝ}
    (h₀ : 0 ≤ lam) (h : TesterCompatibleAt lam A B) : 1 / 2 ≤ lam := by
  obtain ⟨E, F, C, hE, hF, hC, hr, hc⟩ := h
  obtain ⟨η, hη, hEt⟩ := hE.2
  obtain ⟨θ, hθ, hFt⟩ := hF.2
  obtain ⟨τ, hτ, hCt⟩ := hC.2
  change (∑ j, E j) = liftInput η at hEt
  change (∑ k, F k) = liftInput θ at hFt
  change (∑ jk, C jk) = liftInput τ at hCt
  have hrn : τ = (1 - lam) • ρ + lam • η := by
    apply lift_injective h1
    have hs := congrArg (fun g : Fin p → Joint d0 d1 => ∑ j, g j) (funext hr)
    simpa only [← Fintype.sum_prod_type, hCt, Finset.sum_add_distrib, ← Finset.smul_sum,
      hA.2, hEt, map_add, map_smul] using hs
  have hcn : τ = (1 - lam) • σ + lam • θ := by
    apply lift_injective h1
    have hs := congrArg (fun g : Fin q → Joint d0 d1 => ∑ k, g k) (funext hc)
    simpa only [← Fintype.sum_prod_type_right, hCt, Finset.sum_add_distrib, ← Finset.smul_sum,
      hB.2, hFt, map_add, map_smul] using hs
  have hτr : (1 - lam) • ρ ≤ τ := by
    rw [hrn, Matrix.le_iff, add_sub_cancel_left]
    exact hη.1.smul h₀
  have hτs : (1 - lam) • σ ≤ τ := by
    rw [hcn, Matrix.le_iff, add_sub_cancel_left]
    exact hθ.1.smul h₀
  have htrace := trace_bound_of_orthogonal hρ hσ hz hτr hτs
  rw [hτ.2, Complex.one_re] at htrace
  linarith

private theorem half_le_of_orthogonal (h1 : 0 < d1) (hp : 0 < p) (hq : 0 < q)
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hz : ρ * σ = 0)
    (hA : HasNormalization A ρ) (hB : HasNormalization B σ) :
    1 / 2 ≤ testerRobustness A B := by
  have hhalf := half_compatible h1 hp hq hρ hσ hA hB
  refine le_csInf (s := {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ TesterCompatibleAt r A B})
    ⟨1 / 2, by norm_num [hhalf]⟩ ?_
  exact fun r hr => half_le_of_orthogonal_compatible h1 hρ hσ hz hA hB hr.1 hr.2.2

private theorem mul_eq_zero_of_reTrace_pair_zero {X Y : Joint d0 d1}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (h : (X * Y).trace.re = 0) : X * Y = 0 := by
  let e : Fin (d1 * d0) ≃ Fin d1 × Fin d0 := finProdFinEquiv.symm
  have ht : (X * Y).trace = 0 := by
    rw [← trace_pair_real hX hY, h, Complex.ofReal_zero]
  have hs := zero_trace_mul_eq_zero (X.submatrix e e) (Y.submatrix e e)
    (hX.submatrix e) (hY.submatrix e) (by
      rw [Matrix.submatrix_mul_equiv X Y e e e]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
      exact (e.sum_comp (fun i => (X * Y) i i)).trans ht)
  rw [Matrix.submatrix_mul_equiv X Y e e e] at hs
  ext i j
  simpa only [Matrix.submatrix_apply, e.apply_symm_apply, Matrix.zero_apply] using
    congrArg (fun Z : Input (d1 * d0) => Z (e.symm i) (e.symm j)) hs

/-- The normalization product vanishes exactly when every pair of effects has zero product. -/
theorem normalization_orthogonal_iff_effectwise (h1 : 0 < d1)
    (hρ : IsDensity ρ) (hA : HasNormalization A ρ) (hB : HasNormalization B σ) :
    ρ * σ = 0 ↔ ∀ j k, A j * B k = 0 := by
  have hsum : (liftInput (ρ * σ) : Joint d0 d1) = ∑ j, ∑ k, A j * B k := by
    rw [lift_mul, ← hA.2, ← hB.2, Matrix.sum_mul]
    simp only [Matrix.mul_sum]
  constructor
  · intro h j k
    have hz : (liftInput ρ : Joint d0 d1) * liftInput σ = 0 := by
      rw [← lift_mul, h, map_zero]
    have hAj : A j ≤ liftInput ρ := (effect_le_sum hA.1 j).trans_eq hA.2
    have hBk : B k ≤ liftInput σ := (effect_le_sum hB.1 k).trans_eq hB.2
    have h₁ := reTrace_pair_mono (hB.1 k) hAj
    rw [Matrix.trace_mul_comm (B k) (A j), Matrix.trace_mul_comm (B k) _] at h₁
    have h₂ := reTrace_pair_mono (lift_psd hρ.1) hBk
    rw [hz, Matrix.trace_zero, Complex.zero_re] at h₂
    exact mul_eq_zero_of_reTrace_pair_zero (hA.1 j) (hB.1 k)
      (le_antisymm (h₁.trans h₂) (reTrace_pair_nonneg (hA.1 j) (hB.1 k)))
  · intro h
    apply lift_injective h1
    rw [hsum, map_zero]
    simp only [h, Finset.sum_const_zero]

end Testers

set_option linter.unusedVariables false in
/-- The binding statement of preregistration #24241. -/
def claim : Prop :=
  ∀ (d0 d1 p q : ℕ),
    0 < d0 → 0 < d1 → 0 < p → 0 < q →
    ∀ (A : Fin p → Matrix (Fin d1 × Fin d0) (Fin d1 × Fin d0) ℂ)
      (B : Fin q → Matrix (Fin d1 × Fin d0) (Fin d1 × Fin d0) ℂ)
      (ρ σ : Matrix (Fin d0) (Fin d0) ℂ),
      IsDensity ρ → IsDensity σ →
      IsTester A → IsTester B →
      (∀ j, (A j).PosSemidef) ∧
        (∑ j, A j = Matrix.kronecker (1 : Matrix (Fin d1) (Fin d1) ℂ) ρ) →
      (∀ k, (B k).PosSemidef) ∧
        (∑ k, B k = Matrix.kronecker (1 : Matrix (Fin d1) (Fin d1) ℂ) σ) →
      (testerRobustness A B = (1 / 2 : ℝ) ↔ ρ * σ = 0) ∧
      (ρ * σ = 0 ↔ ∀ j k, A j * B k = 0)

/-- A one-step tester pair is maximally incompatible exactly for orthogonal
normalization states, equivalently for effectwise orthogonality. -/
theorem result : claim := by
  intro d0 d1 p q h0 h1 hp hq A B ρ σ hρ hσ _ _ hA hB
  refine ⟨⟨fun h => ?_, fun hz => ?_⟩, normalization_orthogonal_iff_effectwise h1 hρ hA hB⟩
  · by_contra hne
    obtain ⟨_, hle, hlt⟩ := nonorthogonal_upper_bound h0 h1 hp hq hρ hσ hA hB hne
    exact (not_lt_of_ge h.ge) (hle.trans_lt hlt)
  · exact le_antisymm
      (robustness_le_of_compatible (by norm_num) (by norm_num) (half_compatible h1 hp hq hρ hσ hA hB))
      (half_le_of_orthogonal h1 hp hq hρ hσ hz hA hB)

#print axioms explicitJointCover
#print axioms compatibleAt_of_jointCover
#print axioms nonorthogonal_upper_bound
#print axioms normalization_orthogonal_iff_effectwise
#print axioms result

end Trureturing.OpenProblems.SedlakMaximalTesterOrthogonality
