import GRH.Lib.Weil.Fock.RealData
import GRH.Lib.Weil.Construction.DataProduct
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q) (known
result; see Lib.Weil.Fock.OscillatorPair).

This file: Theta function of a real vacuum datum is entire and determines the datum. -/

open Complex ComplexConjugate Matrix Prod

variable {E} [Field E] [CMType E] [WeilData E] {n} [Fintype n] {s} {V : Space E n s} {f : 𝒮 V}

omit [Fintype n] in
@[fun_prop] lemma Space.continuous_realVec : Continuous (realVec : _ → n → 𝔸 E) := by continuity

/-- For f in 𝒮(V), the function Θ_f(y) = θ(ϱ(y)f)·exp(|y|²/2) of a real vector y in Fock
coordinates, placed in the adelic vectors with finite part zero. -/
noncomputable def Space.entireTheta (f : 𝒮 V) y := f (realVec y) / realVac y

/-- An element f of 𝒮(V) whose values f(y) = θ(ϱ(y)f) vanish at all adelic vectors y with finite
part zero is zero. -/
lemma Space.eq_zero_of_realVec (h : ∀ y, f (realVec y) = 0) : f = 0 :=
  V.data_ext ((MulAction.surjective V.x⁻¹).forall.2 ((DenseRange.piMap fun _ ↦
  denseRange_id.prodMap denseRange_algebraMap_finAdele).eq (by
    erw [← V.apply_vecAtPoint_add f <| -snd ∘ ·, ← mulVec_add, ← realVec_realCoord_add (_ *ᵥ _)]
    simp_all [mulVec_eq_sum, Pi.add_def, realVec, snd_sum])))

lemma Space.entireTheta_eq_integral (hs : s = 1) (h : V.projReal f = f) y : entireTheta f y = ∫ w,
  (∑ p, y p * conj (w p)).exp * (realVac w * f (realVec w)) ∂realMeasure _ := by
  rw [entireTheta, ← θ_ϱ, ← h, ← integrated_realHeisOp, theta_integrated,
    ← MeasureTheory.integral_div]
  simp_all [beta_mul_realVac, holCoord_eq, dotProduct]; grind [realVac, exp_ne_zero]

/-- For V with all signs positive and f a real vacuum, that is, fixed by inserting the Gaussian
as real datum, the theta function Θ_f(y) = f(y)·exp(|y|²/2) on real vectors is entire. -/
@[fun_prop] lemma Space.differentiable_entireTheta (hs : s = 1) (h : V.projReal f = f) :
  Differentiable ℂ (entireTheta f) := funext (entireTheta_eq_integral hs h) ▸ fun _ ↦
  (eventually_differentiableAt_integral ((integrable_exp_mul_realVac _).mul_const _)
  (by fun_prop [realVac]) ((tendsto_norm.eventually_lt_const (lt_add_one _)).mono (⟨by fun_prop, by
    grw [norm_mul, norm_exp_le_exp_norm, norm_sum_le, Finset.sum_mul]
    simp [mul_assoc]; grw [norm_apply_le, norm_le_pi_norm ·, ·, norm_le_pi_norm ·]⟩))).self_of_nhds
