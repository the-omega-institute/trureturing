import GRH.Lib.General.LinearAlgebra.SmoothMatrices
import GRH.Lib.Weil.Fock.MixedFockModel
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: for ξ rapid, τ smooth of compact support and u smooth with unitary values, the vectors
τ(x)ω₀(u(x))ξ are the slices of one rapid vector. -/

open Continuous Complex ContDiff ContinuousLinearMap ENNReal Finset Matrix MeasureTheory Real
  Heisenberg.IsVacuum Norms.Elementwise

/-- For τ smooth of compact support, unitary u(x) depending smoothly on x, and ξ rapid, some
rapid vector Φ has value τ(x)ω₀(u(x))ξ at every x in the mixed model. -/
lemma MixedModel.exists_section {ι ι'} [Fintype ι] [Fintype ι'] {ε : ι → _} {ε' : ι' → _}
    {p : Type} [Fintype p] (h : MixedModel ε' ε p) {τ : _ → ℂ} (hτ : ContDiff ℝ ∞ τ)
    (hc : HasCompactSupport τ) {u : _ → _} (hu : ContDiff ℝ ∞ fun x ↦ (u x).1.1) {ξ}
    (hξ : IsRapidDatum ξ) : ∃ Φ, IsRapidDatum Φ ∧ ∀ x, h.slice x Φ = τ x • realWeil (u x) ξ := by
  set S := (u · |>.1.1)
  let k := ((-π * Complex.I) • h.K.toLpLin 2 ⊤).toContinuousLinearMap
  let d (x : EuclideanSpace ..) :=
    τ x * (star (principalMinor (S x) (ε · = -1)) * (star x ⬝ᵥ x).exp)
  have hc : HasCompactSupport d := (hc.comp_homeomorph (PiLp.homeomorph ..)).mul_right
  let A (x : EuclideanSpace ..) := (mulVecBilin ℝ ℝ).toContinuousBilinearMap (h.I * S x)
  have ⟨B, hB⟩ := hc.exists_bound_of_continuousOn (continuousOn (f := A) (by fun_prop))
  let G y x : fockSpace ε' := d x • ξ y • realHeisOp (A x y) vacVector
  have iG y : Integrable (G y) := hc.smul_right.integrable
  have mF : StronglyMeasurable (Function.uncurry (FourierTransform.fourier <| G ·)) :=
    .integral_prod_right (stronglyMeasurable (by simp; fun_prop))
  obtain ⟨q, eq, hq, hr⟩ : ∃ q, (∀ p : (_ × _) × _, cexp (q p) =
    (realHeisOp (A p.2 p.1.1) vacVector : fockSpace ε') p.1.2) ∧ ContDiff ℝ ∞ q ∧ ∀ r t x,
    q (r • t, x) = q (t, x) * .ofReal r ^ 2 := ⟨_, fun _ ↦ .trans (exp_add ..)
    (heisOp_apply ..).symm, by simp [entrywise]; fun_prop, by simp [star_trivial, field]⟩
  refine ⟨_, .imp_right (fun hI x ↦ ?_) (isRapidDatum_integral (ν := (realMeasure _).prod volume)
    (comp_aestronglyMeasurable₂ (g := (realHeisOp <| k ·.2)) (by fun_prop) aestronglyMeasurable_id
    mF.aestronglyMeasurable) fun N ↦ ?_).symm⟩
  rw [← integral_comp_comm _ hI, integral_prod _ (by fun_prop), integral_congr_ae
    (hI.prod_right_ae.mono fun y hy ↦
    have iF := hy.mono mF.of_uncurry_left.aestronglyMeasurable (by simp)
    .trans ?_ ((integral_comp_comm _ (iF.mono (by measurability) (by simp))).trans (congrArg
      (h.slice x <| · (.toLp 2 x)) (fourierInv_fourier_eq (by fun_prop) (iG y) iF))))]
  simp [G, d, A, ← integral_smul, weilRep, Heisenberg.Rep.integrated_apply,
    (by simpa using h.slice_realHeisOp · 0 · 0),
    h.slice_vac, smul_smul, ← mulVec_mulVec, mul_assoc, Complex.exp_neg, mul_left_comm]
  rfl
  simp [k, ← mulVec_smul, (by simpa using h.slice_realHeisOp · 0 0 ·), realHeis, fourierChar,
    sum_mul, PiLp.inner_apply, -neg_mul, dotProduct, Circle.smul_def, mul_sum,
    ← sum_sub_distrib, -mul_re, re_eq_add_conj]
  simp only [Finset.sum_div]; clear * -; grind
  have ⟨r', J'⟩ : (@volume (EuclideanSpace ℂ p)).HasTemperateGrowth := inferInstance
  have ⟨C, H⟩ :=
    exists_pow_mul_norm_fourier_le hc (r' + ⌈‖k‖⌉₊ * N) (by
    simp [d, principalMinor, dotProduct, det_apply, toSquareBlockProp]; fun_prop) hq fun _ ↦
    image_eq_zero_of_notMem_tsupport
  let m := 2 * (r' + ⌈‖k‖⌉₊ * N) + (realMeasure ι').integrablePower + N
  have K := ((((integrable_toReal_of_lintegral_ne_top (by fun_prop) (hξ m)).const_mul (rexp (m ^ 2)
    * (1 + |B|) ^ m)).const_mul C).mul_prod J').mul_prod
    (realMeasure ι').integrable_pow_neg_integrablePower
  apply (K.2.trans_le' _).ne
  grw [lintegral_prod _ K.1.enorm, weightedNorm_realHeisOp_le, (weightedNorm_eq ..).le,
    lintegral_const_mul_le]
  gcongr with ⟨y, b⟩ w
  simp (disch := finiteness) [↓← toReal_le_toReal, toReal_add, abs_of_pos, ← mul_assoc _ _ ‖_‖]
  let ρ := 1 + ‖y‖ + ‖w‖
  have o : ρ ≠ 0 := by positivity
  grw [le_opNorm, Nat.le_ceil ‖k‖, one_add_le_pow_of_two_add_nonneg (by bound), (by bound : 1 +
    ‖w‖ ≤ ρ), ← le_abs_self, ← div_mul_cancel₀ (C * _) (pow_ne_zero m o), ← mul_div,
    ← H b (ρ⁻¹ • (y, w)) (ρ⁻¹ ^ 2) _ ?_ (by simpa) fun x h ↦ (le_div_iff₀' (by positivity)).2 ?_]
  erw [← valueAt_apply, ← integral_comp_comm _ (by simp [*])]
  simp [G, ↓hr, o, eq, fourier_eq, Circle.smul_def, m, field, pow_add,
    pow_mul, mul_left_comm _ (ξ _), mul_pow]
  simp [norm_smul, field]; clear * -; grind [norm_nonneg]
  simpa [↓hr, eq, mul_assoc, ← mul_pow, o] using
    pow_mul_realVac_le m (by unfold ρ; grw [← sub_nonneg,
    norm_le_norm_sub_add w (A x y), le_opNorm, hB x h, le_abs_self B]; ring; bound)
