import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.Haar.RegularRepL2
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of real and complex analysis (textbook or folklore).

Part of: Schur orthogonality; coefficients of integrable discrete series are cusp forms (known
result; see Lib.DiscreteSeries.CuspKernel.CircleMean).

This file: Convolution with compactly supported smooth functions is smooth; derivatives fall on the
bump. -/

noncomputable section

open MeasureTheory ContinuousLinearMap Set Matrix Norms.L2Operator


variable {n} [Fintype n] (ε : n → _) {E} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex subspace of smooth complex functions on U(diag ε) that have compact support. -/
abbrev Bumps : Submodule ℂ (SmoothU ε ℂ) :=
  ⟨⟨⟨{β | HasCompactSupport β.1}, .add⟩, .zero⟩, fun _ ↦ .smul_left⟩

variable {ε} (F : USign ε → E) (α : Bumps ε) (hF : Continuous F := by fun_prop)

/-- The gl_n(ℂ)-module of compactly supported smooth complex functions on U(diag ε) under right
derivatives, a submodule of `rightDeriv`. -/
def bumpDeriv := (rightDeriv ..).restrictTo (Bumps ε) fun _ f ↦ (.intro · fun _ h ↦
  (rightDeriv_comp_clm (f := f) 0 (notMem_tsupport_iff_eventuallyEq.1 h)).eq_of_nhds)

include hF

lemma integrable_bump_inv_smul : Integrable fun y ↦ α.1.1 y⁻¹ • F y :=
  (α.2.comp_homeomorph (.inv _)).smul_right.integrable

/-- For continuous F : U(diag ε) → E, the linear map sending a compactly supported smooth α to
the function g ↦ ∫ α(y⁻¹)F(gy) dy. -/
@[simps] def smear : Bumps ε →ₗ[ℂ] USign ε → E := by
  use! fun α g ↦ ∫ y, α.1.1 y⁻¹ • F (g * y) <;> simp [add_smul, integral_add, mul_smul,
    fun g ↦ (integrable_bump_inv_smul (F <| g * ·) ·), integral_smul, funext_iff]

/-- Derivatives of a convolution fall on the test function: if a curve γ in U(diag ε) has γ'(t)
= γ(t)X, then `smear` α along γ has derivative at t the value at γ(t) of
`smear` (Xα), Xα the right derivative. -/
lemma hasDerivAt_smear {γ : ℝ → USign ε} {t X} (h : HasDerivAt (γ · |>.1.1) ((γ t).1 * X) t) :
    HasDerivAt (smear F hF α <| γ ·) (smear F hF (bumpDeriv X α) (γ t)) t := by
  obtain ⟨⟨A, a⟩, ⟨C, c⟩, N, k, m⟩ := α.1.2, h.isBigO_sub.bound, exists_compact_mem_nhds (γ t)
  obtain ⟨K, n⟩ := α.2.mul k.inv, mem_of_mem_nhds m
  let ⟨L, l⟩ := (contDiff_infty.1 A.2 1).locallyLipschitz.locallyLipschitzOn
    |>.exists_lipschitzOnWith_of_compact ((K.mul k).image_auto (·.1.1))
  have ⟨i, j⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip' (c.and
    (isClosedEmbedding_U.continuousAt_iff.2 h.continuousAt m)) (by fun_prop) (.congr
    ((integrable_bump_inv_smul (F <| γ t * ·) α).comp_mul_left (γ t)⁻¹) (by simp))
    (by simp [← smulRight_one_eq_toSpanSingleton]; fun_prop) (.of_forall fun y s ⟨p, q⟩ ↦ by
    rw [indicator]; split_ifs with b
    · simp [← a, ← sub_smul, norm_smul, mul_assoc, -coe_units_inv] at *
      grw [l.norm_sub_le, ← mul_sub, norm_mul_le, p, mul_comm] <;> exact ⟨_, mul_mem_mul b ‹_›, rfl⟩
    simp [fun x o ↦ image_eq_zero_of_notMem_tsupport (b ⟨y⁻¹ * x, ·, x⁻¹, o, by simp⟩), *])
    ((K.inv.integrableOn fun y ↦ ‖F y‖ * L * ‖y⁻¹.1.1‖ * C).integrable_indicator
    K.inv.measurableSet) (.of_forall fun y ↦ (hasDerivAt_curve α.1 (γ := (y⁻¹ * γ ·)) (X := X)
    (by simp [mul_assoc, h.const_mul])).smul_const (F y))
  convert ← j.hasDerivAt <;> simp [integral_apply i] <;>
    rw [← integral_mul_left_eq_self] <;> congr! 4 <;> simp

lemma rightDeriv_smear {α f} (e : smear F hF α = f.1) X : smear F hF (bumpDeriv X α) =
  (rightDeriv ε E X f).1 := have k Y g :=
    (hasDerivAt_smear F α hF (hasDerivAt_expU Y g 0)).unique (e ▸ hasDerivAt_rightDeriv_expU ..)
  eq_unitaryLiePart_add_I_smul ε X ▸ by simp_all [funext_iff]
