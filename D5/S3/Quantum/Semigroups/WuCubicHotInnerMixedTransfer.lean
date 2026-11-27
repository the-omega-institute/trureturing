import D5.S3.Quantum.Semigroups.WuCubicHotInnerPartialTrace
import D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed
import D5.S3.Quantum.Matrix.SpectralPower
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The physical one-mode restriction of the two-mode Wu cubic deficit. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Filter
open scoped ContDiff Kronecker BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Semigroups.WuCubicHotInnerMixedTransfer

open WuCubicOperatorBridge (Mat D G generator)
open WuCubicOperatorNormalization (operatorDeficit)
open WuRepeatedMiddleCubic (alpha)
open WuCubicHotInnerPartialTrace (Local gibbs lift reduce rightGenerator product_energy)
open D5.S3.Quantum.Matrix.SpectralPower (posDef_two)
open private gibbsLow gibbsHigh gibbsOccupation from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private rootScale rootRatio rootScale_pos from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open private root rootValues root_posDef sqrt_rootScale_sq sandwich_lift
  cubed_base log_difference gibbs_trace trace_mass_base from
  D5.S3.Quantum.Semigroups.WuCubicHotInnerPartialTrace

local notation "a" => gibbsLow
local notation "b" => gibbsHigh
local notation "u" => (fun r : ℝ => 1 / r)
local notation "s" => (fun r : ℝ => rootScale r * r)

/-- The active observable in physical occupation order. -/
def physical (r k y : ℝ) : Local :=
  !![(1 + b r * y : ℝ), (k : ℂ); (k : ℂ), (1 - a r * y : ℝ)]

private theorem scale_pos {r : ℝ} (hr : 1 ≤ r) : 0 < s r :=
  mul_pos (rootScale_pos (zero_le_one.trans hr)) (zero_lt_one.trans_le hr)

private theorem scale_cube {r : ℝ} (hr : 1 ≤ r) : s r ^ 3 = b r := by
  have ha : 0 ≤ a r := by unfold gibbsLow; positivity
  have h : rootScale r ^ 3 = a r := by
    unfold rootScale
    rw [← Real.rpow_mul_natCast ha]
    norm_num
  rw [mul_pow, h, gibbsHigh, mul_comm]

private theorem ratio_mul {r : ℝ} (hr : 1 ≤ r) :
    r * Real.sqrt (u r) = rootRatio r := by
  have h := zero_lt_one.trans_le hr
  change r * Real.sqrt (1 / r) = Real.sqrt r
  rw [one_div, Real.sqrt_inv, ← div_eq_mul_inv]
  exact (div_eq_iff (Real.sqrt_ne_zero'.mpr h)).mpr
    ((Real.mul_self_sqrt h.le).symm)

private theorem sandwich_physical {r : ℝ} (hr : 1 ≤ r) (k y : ℝ) :
    root r * physical r k y * root r =
      s r • WuCubicHotInnerMixed.embedded (u r) (a r) (b r) k y := by
  have hr' : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  have hq := sqrt_rootScale_sq hr
  have ht : Real.sqrt r ^ 2 = r := Real.sq_sqrt (zero_le_one.trans hr)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [root, rootValues, physical, WuCubicHotInnerMixed.embedded,
      WuCubicHotInnerMixed.v, WuCubicHotInnerMixed.w,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
      ← Complex.ofReal_mul] <;>
    norm_cast <;> ring_nf <;>
    simp [hq, ← ratio_mul hr] <;>
    field_simp <;> try rw [ht]
  all_goals ring

private theorem rightGenerator_physical {r : ℝ} (hr : 1 ≤ r) (k y : ℝ) :
    rightGenerator r (physical r k y) =
      !![((2 * b r * y : ℝ) : ℂ), (k : ℂ); (k : ℂ), ((-2 * a r * y : ℝ) : ℂ)] := by
  have hab : a r + b r = 1 := by
    unfold gibbsHigh gibbsLow
    have h : 1 + r ^ 3 ≠ 0 := by positivity
    field_simp
  have hab' : (a r : ℂ) + (b r : ℂ) = 1 := by exact_mod_cast hab
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rightGenerator, physical, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct]
  · left
    linear_combination (y : ℂ) * hab'
  · linear_combination (k : ℂ) * hab'
  · linear_combination (k : ℂ) * hab'
  · linear_combination -2 * (a r : ℂ) * (y : ℂ) * hab'

private theorem sandwich_generator {r : ℝ} (hr : 1 ≤ r) (k y : ℝ) :
    root r * rightGenerator r (physical r k y) * root r =
      s r • WuCubicHotInnerMixed.embeddedGenerator (u r) (a r) (b r) k y := by
  have hr' : r ≠ 0 := (zero_lt_one.trans_le hr).ne'
  have hq := sqrt_rootScale_sq hr
  have ht : Real.sqrt r ^ 2 = r := Real.sq_sqrt (zero_le_one.trans hr)
  rw [rightGenerator_physical hr]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [root, rootValues, WuCubicHotInnerMixed.embeddedGenerator,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply,
      ← Complex.ofReal_mul] <;>
    norm_cast <;> ring_nf <;>
    simp [hq, ← ratio_mul hr] <;>
    field_simp
  rw [ht]

private theorem log_gibbs (r : ℝ) :
    cfc Real.log (gibbs r) =
      diagonal ![(Real.log (a r) : ℂ), (Real.log (b r) : ℂ)] := by
  unfold gibbs
  refine (Matrix.cfc_diagonal_real (𝕜 := ℂ) (gibbsOccupation r) Real.log).trans ?_
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem log_scale {T : Local} (hT : T.PosDef) {c : ℝ} (hc : 0 < c) :
    cfc Real.log (c • T) = Real.log c • (1 : Local) + cfc Real.log T := by
  have hzero (x : ℝ) (hx : x ∈ spectrum ℝ T) : x ≠ 0 := by
    rw [hT.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨j, rfl⟩ := hx
    exact (hT.eigenvalues_pos j).ne'
  have hsupport : cfc (fun x : ℝ => if x = 0 then (0 : ℝ) else 1) T = 1 := by
    rw [← cfc_const_one ℝ T]
    exact cfc_congr (fun x hx => by simp [hzero x hx])
  rw [hT.isHermitian.log_smul_of_ne_zero hc.ne', hsupport]

private theorem trace_product {r : ℝ} (hr : 1 ≤ r) (B L : Local) :
    ((((root r ^ 2) ⊗ₖ B) ^ 3) * lift L).trace = (B ^ 3 * L).trace := by
  rw [cubed_base hr, lift, ← mul_kronecker_mul, Matrix.mul_one,
    Matrix.trace_kronecker, gibbs_trace hr, one_mul]

/-- The literal product deficit equals the scalar deficit throughout the
positive physical locus, with both Gibbs log charges and the variable mass. -/
theorem operatorDeficit_physical {r : ℝ} (hr : 1 ≤ r) (k y : ℝ)
    (hP : (physical r k y).PosDef) :
    operatorDeficit r (lift (physical r k y)) =
      WuCubicHotInnerMixed.deficit (u r) (a r) (b r) (alpha r) (k ^ 2) y := by
  let V := WuCubicHotInnerMixed.embedded (u r) (a r) (b r) k y
  let W := WuCubicHotInnerMixed.embeddedGenerator (u r) (a r) (b r) k y
  let B := root r * physical r k y * root r
  let T := (V ^ 3).trace.re
  have hs : B = s r • V := sandwich_physical hr k y
  have hB : B.PosDef := by
    have hroot := root_posDef hr
    simpa only [B, hroot.isHermitian.eq] using
      hP.conjTranspose_mul_mul_same hroot.mulVec_injective
  have hV : V.PosDef := by
    have hh := hB.smul (inv_pos.mpr (scale_pos hr))
    rwa [hs, smul_smul, inv_mul_cancel₀ (scale_pos hr).ne', one_smul] at hh
  have hV3 : (V ^ 3).PosDef :=
    ((hV.posSemidef.pow 3).posDef_iff_isUnit).mpr (hV.isUnit.pow 3)
  have hb : 0 < b r := (scale_cube hr) ▸ pow_pos (scale_pos hr) 3
  have hT : 0 < T := (Complex.lt_def.mp hV3.trace_pos).1
  have hpow : B ^ 3 = b r • V ^ 3 := by rw [hs, smul_pow, scale_cube hr]
  have hmass : (B ^ 3).trace.re = b r * T := by
    rw [hpow, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  have henergy :
      (((G r * lift (physical r k y) * G r) ^ 2) *
        (G r * generator r (lift (physical r k y)) * G r)).trace.re =
        b r * ((V ^ 2 * W).trace).re := by
    rw [product_energy hr, show root r * physical r k y * root r = B from rfl, hs,
      sandwich_generator hr, smul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← pow_succ, scale_cube hr, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  have hcharge :
      (V ^ 3 * cfc Real.log (gibbs r)).trace.re =
        ((V ^ 3) 0 0).re * Real.log (a r) + ((V ^ 3) 1 1).re * Real.log (b r) := by
    rw [log_gibbs]
    simp [Matrix.trace_fin_two, Matrix.mul_diagonal, Complex.mul_re]
  have hent :
      (B ^ 3 * (cfc Real.log (B ^ 3) - cfc Real.log (gibbs r))).trace.re -
          (B ^ 3).trace.re * Real.log (B ^ 3).trace.re =
        b r * ((V ^ 3 * cfc Real.log (V ^ 3)).trace.re - T * Real.log T -
          (((V ^ 3) 0 0).re * Real.log (a r) + ((V ^ 3) 1 1).re * Real.log (b r))) := by
    rw [hmass, hpow, log_scale hV3 hb, Real.log_mul hb.ne' hT.ne']
    simp only [Matrix.smul_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub,
      Complex.smul_re, Complex.add_re, Complex.sub_re, smul_eq_mul, hcharge]
    dsimp only [T]
    ring
  rw [WuCubicHotInnerMixed.embedded_deficit _ _ _ _ _ _ (by dsimp; positivity)]
  unfold operatorDeficit
  dsimp only
  rw [henergy, sandwich_lift hr, log_difference hr hB, trace_product hr, trace_mass_base hr]
  change (9 / 8 : ℝ) * (b r * (V ^ 2 * W).trace.re) - alpha r *
    ((B ^ 3 * (cfc Real.log (B ^ 3) - cfc Real.log (gibbs r))).trace.re -
      (B ^ 3).trace.re * Real.log (B ^ 3).trace.re) = _
  rw [hent]
  dsimp only [V, W, T]
  ring


open scoped Topology

/-- The real diagonal contrast selected by the spectator Gibbs state. -/
def diagonalContrast (r : ℝ) (H : Mat) : ℝ :=
  a r * ((H (0, 0) (0, 0)).re - (H (0, 1) (0, 1)).re) +
    b r * ((H (1, 0) (1, 0)).re - (H (1, 1) (1, 1)).re)

open private reduce_apply reduce_hermitian from
  D5.S3.Quantum.Semigroups.WuCubicHotInnerPartialTrace

theorem diagonalContrast_eq_reduce (r : ℝ) (H : Mat) :
    diagonalContrast r H = (reduce r H 0 0).re - (reduce r H 1 1).re := by
  simp [diagonalContrast, reduce_apply, gibbsOccupation, Fin.sum_univ_two, Complex.mul_re]
  ring

private def tangent (r : ℝ) : Local :=
  diagonal ![(b r : ℂ), (-a r : ℝ)]

private theorem physical_path (r k y : ℝ) :
    physical r k y = physical r k 0 + y • tangent r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [physical, tangent, Matrix.smul_apply, Complex.real_smul] <;> ring

private theorem lift_add_smul (P Q : Local) (t : ℝ) :
    lift (P + t • Q) = lift P + t • lift Q := by
  ext i j
  simp [lift, Matrix.kroneckerMap_apply, Matrix.smul_apply, Complex.real_smul]
  ring

private theorem physical_posDef_of {r k y : ℝ} (h₁ : 0 < 1 + b r * y)
    (h₂ : 0 < (1 + b r * y) * (1 - a r * y) - k ^ 2) :
    (physical r k y).PosDef :=
  posDef_two _ _ _ h₁ h₂

private theorem physical_posDef_near (r : ℝ) {k : ℝ} (hk : k ^ 2 < 1) :
    ∀ᶠ y in 𝓝 (0 : ℝ), (physical r k y).PosDef := by
  have h₁ : Continuous fun y : ℝ => 1 + b r * y := by fun_prop
  have h₂ : Continuous fun y : ℝ => (1 + b r * y) * (1 - a r * y) - k ^ 2 := by fun_prop
  have e₁ := (continuousAt_const (x := (0 : ℝ)) (y := (0 : ℝ))).eventually_lt h₁.continuousAt
    (by simp : (0 : ℝ) < 1 + b r * 0)
  have e₂ := (continuousAt_const (x := (0 : ℝ)) (y := (0 : ℝ))).eventually_lt h₂.continuousAt
    (by simpa using sub_pos.mpr hk : (0 : ℝ) < (1 + b r * 0) * (1 - a r * 0) - k ^ 2)
  filter_upwards [e₁, e₂] with y hy₁ hy₂
  exact physical_posDef_of hy₁ hy₂

/-- The directional derivative for an arbitrary Hermitian perturbation whose
Gibbs reduction is the centered occupation-diagonal direction. -/
theorem deriv_operatorDeficit_diagonal {r k : ℝ} (hr : 1 ≤ r) (hk : k ^ 2 < 1)
    (H : Mat) (hH : H.IsHermitian)
    (hreduce : reduce r H = diagonalContrast r H • tangent r) :
    deriv (fun t : ℝ => operatorDeficit r (lift (physical r k 0) + t • H)) 0 =
      deriv (fun t : ℝ => WuCubicHotInnerMixed.deficit (u r) (a r) (b r) (alpha r)
        (k ^ 2) (t * diagonalContrast r H)) 0 := by
  have hpos := (physical_posDef_near r hk).self_of_nhds
  rw [WuCubicHotInnerPartialTrace.deriv_operatorDeficit_eq_lift_reduce hr _ hpos H hH, hreduce]
  apply Filter.EventuallyEq.deriv_eq
  have hcont : ContinuousAt (fun t : ℝ => t * diagonalContrast r H) 0 := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, (physical r k (t * diagonalContrast r H)).PosDef := by
    have h := physical_posDef_near r hk
    rw [show (0 : ℝ) = (fun t : ℝ => t * diagonalContrast r H) 0 by simp] at h
    exact hcont.tendsto.eventually h
  filter_upwards [hnear] with t ht
  rw [← operatorDeficit_physical hr _ _ ht, physical_path r k (t * diagonalContrast r H),
    mul_smul, lift_add_smul]

/-- The checked scalar extension of the physical deficit and its mixed
coefficient, specialized to the two occupation Gibbs weights. -/
theorem physical_mixed (r : ℝ) (hr : 1 < r) :
    HasDerivAt (fun y => deriv (fun z => WuCubicHotInnerMixed.deficit (u r)
      (a r) (b r) (alpha r) z y) 0)
      (-b r * (9 * a r / 4) * (1 + u r) / (1 - u r) *
        (2 * (1 - 2 * alpha r) + 2 * (1 - u r) ^ 2 / (1 + u r + (u r) ^ 2))) 0 := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hu : 0 < u r := one_div_pos.mpr hr0
  have hu1 : u r < 1 := (div_lt_one hr0).mpr hr
  have hb : 0 < b r := (scale_cube hr.le) ▸ pow_pos (scale_pos hr.le) 3
  have hmass : 0 < 1 + r ^ 3 := by positivity
  have ha : a r = (u r) ^ 3 * b r := by
    unfold gibbsHigh gibbsLow
    dsimp
    field_simp [hr0.ne', hmass.ne']
  have hn : b r * (1 + (u r) ^ 3) = 1 := by
    unfold gibbsHigh gibbsLow
    dsimp
    field_simp [hr0.ne', hmass.ne']
    ring
  simpa [one_div] using WuCubicHotInnerMixed.hot_inner_mixed (u r) (a r) (b r)
    hu hu1 hb ha hn

open WuCubicHotInnerMixed (deficit lower upper v w cubicLog spectral mass charges energy
  diagonalLow diagonalHigh)

/-- The scalar deficit with physical Gibbs parameters and signed squared coherence. -/
def scalar (r : ℝ) (p : ℝ × ℝ) : ℝ :=
  deficit (u r) (a r) (b r) (alpha r) p.1 p.2

/-- The mixed scalar coefficient at the physical Gibbs parameters. -/
def coefficient (r : ℝ) : ℝ :=
  -b r * (9 * a r / 4) * (1 + u r) / (1 - u r) *
    (2 * (1 - 2 * alpha r) + 2 * (1 - u r) ^ 2 / (1 + u r + (u r) ^ 2))

private theorem scalar_smooth (r : ℝ) (hr : 1 < r) :
    ContDiffAt ℝ 2 (scalar r) (0, 0) := by
  let U := u r
  let A := a r
  let B := b r
  let gap := fun p : ℝ × ℝ => (w A p.2 - v U B p.2) ^ 2 + 4 * U * p.1
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hu : 0 < U := one_div_pos.mpr hr0
  have hu1 : U < 1 := (div_lt_one hr0).mpr hr
  have hgap : gap (0, 0) ≠ 0 := by
    simpa [gap, v, w] using (pow_ne_zero 2 (sub_pos.mpr hu1).ne')
  have hg : ContDiffAt ℝ 2 gap (0, 0) := by unfold gap v w; fun_prop
  have hs := hg.sqrt hgap
  have hlow : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => lower U (v U B p.2) (w A p.2) p.1)
      (0, 0) := by
    change ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (v U B p.2 + w A p.2 - Real.sqrt (gap p)) / 2)
      (0, 0)
    unfold v w
    fun_prop
  have hupp : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => upper U (v U B p.2) (w A p.2) p.1)
      (0, 0) := by
    change ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (v U B p.2 + w A p.2 + Real.sqrt (gap p)) / 2)
      (0, 0)
    unfold v w
    fun_prop
  have hl : lower U (v U B 0) (w A 0) 0 = U := by
    simp [lower, v, w, Real.sqrt_sq (sub_nonneg.mpr hu1.le)]
    ring
  have hh : upper U (v U B 0) (w A 0) 0 = 1 := by
    simp [upper, v, w, Real.sqrt_sq (sub_nonneg.mpr hu1.le)]
    ring
  have hll := hlow.log (show lower U (v U B 0) (w A 0) 0 ≠ 0 by rw [hl]; exact hu.ne')
  have hhl := hupp.log (show upper U (v U B 0) (w A 0) 0 ≠ 0 by rw [hh]; exact one_ne_zero)
  have hm : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => mass U A B p.1 p.2) (0, 0) := by
    unfold mass diagonalLow diagonalHigh v w
    fun_prop
  have hml := hm.log (show mass U A B 0 0 ≠ 0 by
    simpa [mass, diagonalLow, diagonalHigh, v, w] using (by
      positivity : U ^ 3 + 1 ≠ 0))
  change ContDiffAt ℝ 2 (fun p : ℝ × ℝ => deficit U A B (alpha r) p.1 p.2) (0, 0)
  unfold deficit spectral cubicLog charges
  apply contDiffAt_const.mul
  apply ContDiffAt.sub
  · unfold energy v w
    fun_prop
  · apply contDiffAt_const.mul
    apply ContDiffAt.sub
    · fun_prop
    · apply ContDiffAt.add
      · apply ContDiffAt.add
        · exact hm.mul hml
        · unfold diagonalLow v w
          fun_prop
      · unfold diagonalHigh v w
        fun_prop

private theorem deriv_along {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {p q : ℝ × ℝ} (h : DifferentiableAt ℝ f p) :
    deriv (fun t : ℝ => f (p + t • q)) 0 = fderiv ℝ f p q := by
  have hp : HasDerivAt (fun t : ℝ => p + t • q) q 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const q).const_add p)
  exact (h.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)).deriv

private theorem mixed_derivatives_transfer {f : ℝ × ℝ → ℝ} {c : ℝ}
    (h : ContDiffAt ℝ 2 f (0, 0))
    (hc : HasDerivAt (fun y => deriv (fun z => f (z, y)) 0) c 0) :
    HasDerivAt (fun z => deriv (fun y => f (z, y)) 0) c 0 := by
  let e₁ : ℝ × ℝ := (1, 0)
  let e₂ : ℝ × ℝ := (0, 1)
  have hF := (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hne : ∀ᶠ p in 𝓝 ((0, 0) : ℝ × ℝ), DifferentiableAt ℝ f p :=
    (h.eventually (by simp)).mono fun _ hp => hp.differentiableAt (by norm_num)
  have hor : ContinuousAt (fun z : ℝ => (z, (0 : ℝ))) 0 := by fun_prop
  have hve : ContinuousAt (fun y : ℝ => ((0 : ℝ), y)) 0 := by fun_prop
  have ehor : ∀ᶠ z : ℝ in 𝓝 0, DifferentiableAt ℝ f (z, 0) := hor.tendsto.eventually hne
  have eve : ∀ᶠ y : ℝ in 𝓝 0, DifferentiableAt ℝ f (0, y) := hve.tendsto.eventually hne
  have hleft : (fun z => deriv (fun y => f (z, y)) 0) =ᶠ[𝓝 (0 : ℝ)]
      (fun z => fderiv ℝ f (z, 0) e₂) := by
    filter_upwards [ehor] with z hz
    simpa [e₂, Prod.smul_mk, Prod.mk_add_mk] using (deriv_along (q := e₂) hz)
  have hright : (fun y => deriv (fun z => f (z, y)) 0) =ᶠ[𝓝 (0 : ℝ)]
      (fun y => fderiv ℝ f (0, y) e₁) := by
    filter_upwards [eve] with y hy
    simpa [e₁, Prod.smul_mk, Prod.mk_add_mk] using (deriv_along (q := e₁) hy)
  have hmain (p q : ℝ × ℝ) :
      HasDerivAt (fun t : ℝ => fderiv ℝ f (t • p) q)
        (fderiv ℝ (fderiv ℝ f) (0, 0) p q) 0 := by
    have hp : HasDerivAt (fun t : ℝ => t • p) p 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const p
    have hf := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)
    simpa [Function.comp_def] using hf.clm_apply (hasDerivAt_const 0 q)
  have hy := hmain e₂ e₁
  have hx := hmain e₁ e₂
  simp only [e₁, e₂, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero] at hy hx
  have hy' := hy.congr_of_eventuallyEq hright
  have hx' := hx.congr_of_eventuallyEq hleft
  have hsym := h.isSymmSndFDerivAt (by norm_num) e₁ e₂
  have hyc := hy'.unique hc
  change fderiv ℝ (fderiv ℝ f) (0, 0) e₂ e₁ = c at hyc
  rw [← hyc, ← hsym]
  exact hx'

/-- The derivative in the physical diagonal direction has the checked mixed
coefficient after extending the squared coherence to a real variable. -/
theorem physical_mixed_direction (r : ℝ) (hr : 1 < r) :
    HasDerivAt (fun z => deriv (fun y => scalar r (z, y)) 0) (coefficient r) 0 :=
  mixed_derivatives_transfer (scalar_smooth r hr) (physical_mixed r hr)

private def gauge (q : ℂ) : Local := diagonal ![q, 1]

private def gaugeConj (q : ℂ) (P : Local) : Local := gauge q * P * (gauge q)ᴴ

private theorem gauge_isometry {q : ℂ} (hq : q * star q = 1) :
    (gauge q).Isometry ∧ (gauge q)ᴴ.Isometry := by
  have hq' : star q * q = 1 := (mul_comm _ _).trans hq
  constructor <;>
    (rw [Matrix.Isometry]
     simp only [Matrix.conjTranspose_conjTranspose, gauge, Matrix.diagonal_conjTranspose,
       Matrix.diagonal_mul_diagonal]
     rw [← Matrix.diagonal_one]
     congr 1
     funext i
     fin_cases i <;> simp)
  · exact hq'
  · exact hq

private theorem gaugeConj_mul {q : ℂ} (hq : q * star q = 1) (P Q : Local) :
    gaugeConj q P * gaugeConj q Q = gaugeConj q (P * Q) := by
  have hi : (gauge q)ᴴ * gauge q = 1 := (gauge_isometry hq).1
  simp only [gaugeConj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (gauge q)ᴴ, hi, Matrix.one_mul]

private theorem gaugeConj_trace {q : ℂ} (hq : q * star q = 1) (P : Local) :
    (gaugeConj q P).trace = P.trace := by
  have hi : (gauge q)ᴴ * gauge q = 1 := (gauge_isometry hq).1
  rw [gaugeConj, Matrix.trace_mul_cycle, hi, Matrix.one_mul]

private theorem gaugeConj_smul (q : ℂ) (m : ℝ) (P : Local) :
    gaugeConj q (m • P) = m • gaugeConj q P := by
  simp only [gaugeConj, Matrix.mul_smul, Matrix.smul_mul]

private theorem gaugeConj_sub (q : ℂ) (P Q : Local) :
    gaugeConj q (P - Q) = gaugeConj q P - gaugeConj q Q := by
  simp only [gaugeConj, Matrix.mul_sub, Matrix.sub_mul]

private theorem gauge_entries {q : ℂ} (hq : q * star q = 1) (P : Local) :
    gaugeConj q P = !![P 0 0, q * P 0 1; P 1 0 * star q, P 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gaugeConj, gauge, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
  change q * P 0 0 * star q = P 0 0
  rw [mul_right_comm, hq, one_mul]

private theorem gaugeConj_diagonal {q : ℂ} (hq : q * star q = 1) (f : Fin 2 → ℂ) :
    gaugeConj q (diagonal f) = diagonal f := by
  simp only [gaugeConj, gauge, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp
  change q * f 0 * star q = f 0
  rw [mul_right_comm, hq, one_mul]

private theorem root_gauge (r : ℝ) (q : ℂ) (P : Local) :
    root r * gaugeConj q P * root r = gaugeConj q (root r * P * root r) := by
  have h₁ : root r * gauge q = gauge q * root r := by
    simp only [root, gauge, Matrix.diagonal_mul_diagonal, mul_comm]
  have h₂ : (gauge q)ᴴ * root r = root r * (gauge q)ᴴ := by
    simp only [root, gauge, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, mul_comm]
  simp only [gaugeConj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (root r), h₁, h₂]
  simp only [Matrix.mul_assoc]

private theorem rightGenerator_entries {r : ℝ} (hr : 1 ≤ r) (P : Local) :
    rightGenerator r P =
      !![2 * (b r : ℂ) * (P 0 0 - P 1 1), P 0 1;
        P 1 0, 2 * (a r : ℂ) * (P 1 1 - P 0 0)] := by
  have hab : a r + b r = 1 := by
    unfold gibbsHigh gibbsLow
    have h : 1 + r ^ 3 ≠ 0 := by positivity
    field_simp
  have hc : (a r : ℂ) + (b r : ℂ) = 1 := by exact_mod_cast hab
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rightGenerator, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct]
  · left
    ring
  · linear_combination (P 0 1) * hc
  · linear_combination (P 1 0) * hc
  · left
    ring

private theorem rightGenerator_gauge {r : ℝ} (hr : 1 ≤ r) {q : ℂ} (hq : q * star q = 1)
    (P : Local) :
    rightGenerator r (gaugeConj q P) = gaugeConj q (rightGenerator r P) := by
  rw [gauge_entries hq (rightGenerator r P)]
  rw [rightGenerator_entries hr, rightGenerator_entries hr, gauge_entries hq]
  simp

private theorem rightGenerator_smul {r : ℝ} (hr : 1 ≤ r) (m : ℝ) (P : Local) :
    rightGenerator r (m • P) = m • rightGenerator r P := by
  rw [rightGenerator_entries hr, rightGenerator_entries hr]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, Complex.real_smul] <;> ring

private theorem operatorDeficit_gauge_smul {r : ℝ} (hr : 1 ≤ r)
    (P : Local) (hP : P.PosDef) {q : ℂ} (hq : q * star q = 1) {m : ℝ} (hm : 0 < m) :
    operatorDeficit r (lift (m • gaugeConj q P)) =
      m ^ 3 * operatorDeficit r (lift P) := by
  let B := root r * P * root r
  let E := root r * rightGenerator r P * root r
  let T := (B ^ 3).trace.re
  have hroot := root_posDef hr
  have hB : B.PosDef := by
    simpa only [B, hroot.isHermitian.eq] using
      hP.conjTranspose_mul_mul_same hroot.mulVec_injective
  have hB3 : (B ^ 3).PosDef :=
    ((hB.posSemidef.pow 3).posDef_iff_isUnit).mpr (hB.isUnit.pow 3)
  have hT : 0 < T := (Complex.lt_def.mp hB3.trace_pos).1
  have hU : (gauge q) * (gauge q)ᴴ = 1 := by
    simpa only [Matrix.Isometry, Matrix.conjTranspose_conjTranspose] using (gauge_isometry hq).2
  have hInj : Function.Injective (gauge q)ᴴ.mulVec := by
    intro x y hxy
    have h := congrArg ((gauge q).mulVec) hxy
    simpa only [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec] using h
  have hB' : (m • gaugeConj q B).PosDef := by
    have h := hB.conjTranspose_mul_mul_same hInj
    rw [Matrix.conjTranspose_conjTranspose] at h
    exact h.smul hm
  have hpow (n : ℕ) : (gaugeConj q B) ^ n = gaugeConj q (B ^ n) := by
    induction n with
    | zero =>
      simp only [pow_zero]
      rw [← Matrix.diagonal_one, gaugeConj_diagonal hq]
    | succ n ih => rw [pow_succ, ih, gaugeConj_mul hq, ← pow_succ]
  have hGB : root r * (m • gaugeConj q P) * root r = m • gaugeConj q B := by
    rw [Matrix.mul_smul, Matrix.smul_mul, root_gauge]
  have hGE : root r * rightGenerator r (m • gaugeConj q P) * root r = m • gaugeConj q E := by
    rw [rightGenerator_smul hr, rightGenerator_gauge hr hq, Matrix.mul_smul,
      Matrix.smul_mul, root_gauge]
  have hLog : cfc Real.log (gibbs r) = gaugeConj q (cfc Real.log (gibbs r)) := by
    rw [log_gibbs, gaugeConj_diagonal hq]
  have hCfc :
      cfc Real.log (gaugeConj q (B ^ 3)) = gaugeConj q (cfc Real.log (B ^ 3)) :=
    Matrix.cfc_conj_isometry Real.log (gauge_isometry hq).1 (gauge_isometry hq).2
  have hCfcPos : (gaugeConj q (B ^ 3)).PosDef := by
    have h := hB3.conjTranspose_mul_mul_same hInj
    simpa only [gaugeConj, Matrix.conjTranspose_conjTranspose] using h
  unfold operatorDeficit
  dsimp only
  rw [product_energy hr, product_energy hr, sandwich_lift hr, sandwich_lift hr, hGB, hGE,
    log_difference hr hB', log_difference hr hB, trace_product hr, trace_product hr,
    trace_mass_base hr, trace_mass_base hr, smul_pow, smul_pow, hpow, hpow,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_succ, gaugeConj_mul hq,
    log_scale hCfcPos (pow_pos hm 3), hCfc,
    add_sub_assoc]
  simp only [Matrix.smul_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul,
    gaugeConj_trace hq]
  have hc :
      (gaugeConj q (B ^ 3) *
        (gaugeConj q (cfc Real.log (B ^ 3)) - cfc Real.log (gibbs r))).trace =
      (B ^ 3 * (cfc Real.log (B ^ 3) - cfc Real.log (gibbs r))).trace := by
    conv_lhs => rw [hLog]
    rw [← gaugeConj_sub, gaugeConj_mul hq, gaugeConj_trace hq]
  rw [hc, Real.log_mul (pow_pos hm 3).ne' hT.ne']
  ring

private theorem gauge_polar (c : ℂ) :
    ∃ q : ℂ, q * star q = 1 ∧ q * (‖c‖ : ℂ) = c := by
  by_cases hc : c = 0
  · subst c
    exact ⟨1, by simp⟩
  have hn : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hc
  refine ⟨c / (‖c‖ : ℂ), ?_, div_mul_cancel₀ _ hn⟩
  change (c / (‖c‖ : ℂ)) * (starRingEnd ℂ) (c / (‖c‖ : ℂ)) = 1
  rw [map_div₀]
  change (c / (‖c‖ : ℂ)) * (star c / star (‖c‖ : ℂ)) = 1
  change (c / (‖c‖ : ℂ)) * ((starRingEnd ℂ) c / (starRingEnd ℂ) (‖c‖ : ℂ)) = 1
  rw [Complex.conj_ofReal, div_mul_div_comm, Complex.mul_conj', ← pow_two]
  exact div_self (pow_ne_zero 2 hn)

/-- The scalar part of the one-mode Gibbs reduction of a direction. -/
def directionMass (r : ℝ) (H : Mat) : ℝ :=
  a r * (reduce r H 0 0).re + b r * (reduce r H 1 1).re

private theorem product_path_factor {r k : ℝ} (hr : 1 ≤ r) (H : Mat) (hH : H.IsHermitian)
    (t : ℝ) (hm : 0 < 1 + t * directionMass r H)
    (hP : (physical r (‖(k : ℂ) + t • reduce r H 0 1‖ / (1 + t * directionMass r H))
      (t * diagonalContrast r H / (1 + t * directionMass r H))).PosDef) :
    operatorDeficit r (lift (physical r k 0) + t • lift (reduce r H)) =
      (1 + t * directionMass r H) ^ 3 *
        scalar r (‖(k : ℂ) + t • reduce r H 0 1‖ ^ 2 / (1 + t * directionMass r H) ^ 2,
          t * diagonalContrast r H / (1 + t * directionMass r H)) := by
  let Q := reduce r H
  let m := 1 + t * directionMass r H
  let y := t * diagonalContrast r H / m
  let c := (k : ℂ) + t • Q 0 1
  let k' := ‖c‖ / m
  have hm' : m ≠ 0 := hm.ne'
  obtain ⟨q, hq, hqc⟩ := gauge_polar c
  have hQ : Q.IsHermitian := reduce_hermitian r hH
  have hdiag (i : Fin 2) : ((Q i i).re : ℂ) = Q i i := by
    exact (Complex.ofReal_eq_re_of_isSelfAdjoint
      (congrFun (congrFun hQ.eq i) i : IsSelfAdjoint (Q i i))).mp rfl
  have hoff : star (Q 0 1) = Q 1 0 := congrFun (congrFun hQ.eq 1) 0
  have hab : a r + b r = 1 := by
    unfold gibbsHigh gibbsLow
    have hd : 1 + r ^ 3 ≠ 0 := by positivity
    field_simp
  have hentry : physical r k 0 + t • Q = m • gaugeConj q (physical r k' y) := by
    have h01 : (m : ℂ) * (q * (k' : ℂ)) = c := by
      have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm'
      dsimp [k']
      push_cast
      field_simp [hmC]
      rw [hqc]
    have h10 : (m : ℂ) * ((k' : ℂ) * star q) = star c := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using congrArg star h01
    have hmy : m * y = t * diagonalContrast r H := by
      dsimp [y]
      field_simp [hm']
    have h00 : m * (1 + b r * y) = 1 + t * (Q 0 0).re := by
      rw [show m * (1 + b r * y) = m + b r * (m * y) by ring, hmy,
        diagonalContrast_eq_reduce]
      dsimp [m, directionMass, Q]
      linear_combination t * (reduce r H 0 0).re * hab
    have h11 : m * (1 - a r * y) = 1 + t * (Q 1 1).re := by
      rw [show m * (1 - a r * y) = m - a r * (m * y) by ring, hmy,
        diagonalContrast_eq_reduce]
      dsimp [m, directionMass, Q]
      linear_combination t * (reduce r H 1 1).re * hab
    rw [gauge_entries hq]
    ext i j
    fin_cases i <;> fin_cases j
    · change (physical r k 0) 0 0 + (t • Q) 0 0 =
        (m • !![_, _; _, _]) 0 0
      change ((1 + b r * 0 : ℝ) : ℂ) + (t : ℂ) * Q 0 0 =
        (m : ℂ) * ((1 + b r * y : ℝ) : ℂ)
      rw [← hdiag 0, mul_zero, add_zero]
      exact_mod_cast (by simpa using h00.symm : 1 + t * (Q 0 0).re = m * (1 + b r * y))
    · simpa [physical, Matrix.smul_apply, Complex.real_smul, c] using h01.symm
    · simpa [physical, Matrix.smul_apply, Complex.real_smul, c, hoff] using h10.symm
    · change ((1 - a r * 0 : ℝ) : ℂ) + (t : ℂ) * Q 1 1 =
        (m : ℂ) * ((1 - a r * y : ℝ) : ℂ)
      rw [← hdiag 1, mul_zero, sub_zero]
      exact_mod_cast (by simpa using h11.symm : 1 + t * (Q 1 1).re = m * (1 - a r * y))
  rw [← lift_add_smul, show reduce r H = Q from rfl, hentry,
    operatorDeficit_gauge_smul hr _ hP hq hm, operatorDeficit_physical hr _ _ hP]
  change m ^ 3 * scalar r (k' ^ 2, y) = m ^ 3 * scalar r (‖c‖ ^ 2 / m ^ 2, y)
  rw [show k' ^ 2 = ‖c‖ ^ 2 / m ^ 2 from div_pow _ _ _]

/-- The normalized scalar path of a reduced Hermitian perturbation. -/
def directionalScalar (r : ℝ) (H : Mat) (k t : ℝ) : ℝ :=
  let m := 1 + t * directionMass r H
  m ^ 3 * scalar r (‖(k : ℂ) + t • reduce r H 0 1‖ ^ 2 / m ^ 2,
    t * diagonalContrast r H / m)

/-- Every Hermitian direction transfers to the same scalar deficit after
Gibbs contraction, positive scalar normalization, and a local phase change. -/
theorem deriv_operatorDeficit_factor {r k : ℝ} (hr : 1 ≤ r) (hk : k ^ 2 < 1)
    (H : Mat) (hH : H.IsHermitian) :
    deriv (fun t : ℝ => operatorDeficit r (lift (physical r k 0) + t • H)) 0 =
      deriv (directionalScalar r H k) 0 := by
  let m := fun t : ℝ => 1 + t * directionMass r H
  let k' := fun t : ℝ => ‖(k : ℂ) + t • reduce r H 0 1‖ / m t
  let y := fun t : ℝ => t * diagonalContrast r H / m t
  have h₀ : ContinuousAt m 0 := by unfold m; fun_prop
  have hM := h₀.tendsto.eventually (eventually_gt_nhds (show 0 < m 0 by simp [m]))
  have hk' : ContinuousAt k' 0 := by
    apply ContinuousAt.div (by fun_prop) h₀
    simp [m]
  have hy : ContinuousAt y 0 := by
    apply ContinuousAt.div (by fun_prop) h₀
    simp [m]
  have h1 : ContinuousAt (fun t => 1 + b r * y t) 0 := by fun_prop
  have h2 : ContinuousAt (fun t => (1 + b r * y t) * (1 - a r * y t) - k' t ^ 2) 0 := by
    fun_prop
  have e1 := h1.tendsto.eventually (eventually_gt_nhds (show 0 < 1 + b r * y 0 by
    simp [y]))
  have e2 := h2.tendsto.eventually (eventually_gt_nhds (show
    0 < (1 + b r * y 0) * (1 - a r * y 0) - k' 0 ^ 2 by
      simpa [k', y, m, Complex.norm_real, Real.norm_eq_abs, sq_abs] using sub_pos.mpr hk))
  have hpos := (physical_posDef_near r hk).self_of_nhds
  rw [WuCubicHotInnerPartialTrace.deriv_operatorDeficit_eq_lift_reduce hr _ hpos _ hH]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hM, e1, e2] with t ht ht₁ ht₂
  exact product_path_factor hr H hH t ht (physical_posDef_of ht₁ ht₂)

private theorem scalar_edge_slope_zero (r : ℝ) (hr : 1 < r) :
    HasDerivAt (fun z => scalar r (z, 0)) 0 0 := by
  let U := u r
  let A := a r
  let B := b r
  let δ := 1 - U
  let T := 1 + U ^ 3
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hu : 0 < U := one_div_pos.mpr hr0
  have hu1 : U < 1 := (div_lt_one hr0).mpr hr
  have hδ : 0 < δ := sub_pos.mpr hu1
  have hT : 0 < T := by dsimp [T]; positivity
  have hb : 0 < B := by
    change 0 < b r
    rw [← scale_cube hr.le]
    exact pow_pos (scale_pos hr.le) 3
  have ha : A = U ^ 3 * B := by
    dsimp [A, B, U, gibbsLow, gibbsHigh]
    field_simp [hr0.ne']
  have hBT : B * T = 1 := by
    dsimp [B, T, U, gibbsHigh, gibbsLow]
    field_simp [hr0.ne']
    ring
  have hloga : Real.log A = 3 * Real.log U + Real.log B := by
    rw [ha, Real.log_mul (pow_ne_zero _ hu.ne') hb.ne', Real.log_pow]
    norm_num
  have hlogT : Real.log T + Real.log B = 0 := by
    rw [← Real.log_mul hT.ne' hb.ne', mul_comm, hBT, Real.log_one]
  have hα : 4 * alpha r * Real.log U * (1 + U + U ^ 2) = 3 * U ^ 2 - 3 := by
    have hp : 0 < r ^ 2 + r + 1 := by positivity
    have hlog : Real.log r ≠ 0 := (Real.log_pos hr).ne'
    dsimp [U]
    rw [alpha, ite_eq_right hr.ne', Real.log_div one_ne_zero hr0.ne', Real.log_one, zero_sub]
    field_simp [hr0.ne', hp.ne', hlog]
    ring
  have hs0 : Real.sqrt (δ ^ 2) = δ := Real.sqrt_sq hδ.le
  have hd : HasDerivAt (fun z : ℝ => δ ^ 2 + 4 * U * z) (4 * U) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul (4 * U)).const_add (δ ^ 2))
  have hs := hd.sqrt (by simpa using (pow_ne_zero 2 hδ.ne'))
  have hL : HasDerivAt (fun z => lower U U 1 z) (-U / δ) 0 := by
    have h := (hs.const_sub (U + 1)).div_const 2
    convert h using 1
    · rfl
    · simp only [mul_zero, add_zero, hs0]
      field_simp
      ring
  have hU : HasDerivAt (fun z => upper U U 1 z) (U / δ) 0 := by
    have h := (hs.const_add (U + 1)).div_const 2
    convert h using 1
    · rfl
    · simp only [mul_zero, add_zero, hs0]
      field_simp
      ring
  have hl0 : lower U U 1 0 = U := by simp [lower, show 1 - U = δ from rfl, hs0, δ]; ring
  have hu0 : upper U U 1 0 = 1 := by simp [upper, show 1 - U = δ from rfl, hs0, δ]; ring
  have hlogCube (x : ℝ) (hx : x ≠ 0) :
      HasDerivAt cubicLog (9 * x ^ 2 * Real.log x + 3 * x ^ 2) x := by
    convert (((hasDerivAt_pow 3 x).const_mul 3).mul (Real.hasDerivAt_log hx)) using 1
    · rfl
    · field_simp
      ring
  have hspec :
      HasDerivAt (fun z => spectral U A B z 0)
        (u r * (3 - (9 * U ^ 2 * Real.log U + 3 * U ^ 2)) / δ) 0 := by
    have h₁ := (hlogCube U hu.ne').comp_of_eq 0 hL hl0.symm
    have h₂ := (hlogCube 1 one_ne_zero).comp_of_eq 0 hU hu0.symm
    convert h₁.add h₂ using 1
    · ext z
      simp [spectral, v, w, Function.comp_def]
    · simp [U]
      ring
  have hlow : HasDerivAt (fun z => diagonalLow U A B z 0) (U * (2 * U + 1)) 0 := by
    simpa [diagonalLow, v, w, mul_assoc, mul_left_comm, mul_comm] using
      (((hasDerivAt_id (0 : ℝ)).const_mul (U * (2 * U + 1))).const_add (U ^ 3))
  have hhigh : HasDerivAt (fun z => diagonalHigh U A B z 0) (U * (U + 2)) 0 := by
    simpa [diagonalHigh, v, w, mul_assoc, mul_left_comm, mul_comm] using
      (((hasDerivAt_id (0 : ℝ)).const_mul (U * (U + 2))).const_add (1 : ℝ))
  have hmass :
      HasDerivAt (fun z => mass U A B z 0) (3 * U * (1 + U)) 0 := by
    convert hlow.add hhigh using 1
    · rfl
    · ring
  have hmass0 : mass U A B 0 0 = T := by simp [T, mass, diagonalLow, diagonalHigh, v, w, add_comm]
  have henergy : HasDerivAt (fun z => energy U A B z 0) (2 * U * (1 + U)) 0 := by
    simpa [energy, v, w, mul_assoc, mul_left_comm, mul_comm, add_comm] using
      ((hasDerivAt_id (0 : ℝ)).const_mul (2 * U * (1 + U)))
  have hch := ((hmass.mul ((Real.hasDerivAt_log hT.ne').comp_of_eq _ hmass hmass0.symm)).add
    (hlow.mul_const (Real.log A))).add (hhigh.mul_const (Real.log B))
  have hch' : HasDerivAt (fun z => charges U A B z 0)
      (3 * U * (1 + U) + 3 * U * (2 * U + 1) * Real.log U) 0 := by
    convert hch using 1
    · rfl
    · rw [hmass0, hloga, ← mul_assoc T, mul_inv_cancel₀ hT.ne', one_mul]
      simp only [Function.comp_apply, hmass0]
      linear_combination -(3 * U * (1 + U)) * hlogT
  have h := ((henergy.const_mul (9/8)).sub ((hspec.sub hch').const_mul (alpha r))).const_mul B
  change HasDerivAt (fun z => deficit U A B (alpha r) z 0) 0 0
  convert h using 1
  · rfl
  · change 0 = B * (9/8 * (2 * U * (1 + U)) - alpha r *
      (U * (3 - (9 * U ^ 2 * Real.log U + 3 * U ^ 2)) / δ -
        (3 * U * (1 + U) + 3 * U * (2 * U + 1) * Real.log U)))
    have hfactor :
        B * (9/8 * (2 * U * (1 + U)) - alpha r *
          (U * (3 - (9 * U ^ 2 * Real.log U + 3 * U ^ 2)) / δ -
            (3 * U * (1 + U) + 3 * U * (2 * U + 1) * Real.log U))) =
        (3 * B * U / (4 * δ)) *
          (4 * alpha r * Real.log U * (1 + U + U ^ 2) - (3 * U ^ 2 - 3)) := by
      field_simp [hδ.ne']
      dsimp [δ]
      ring
    rw [hfactor, hα, sub_self, mul_zero]

private theorem directionalScalar_deriv (r : ℝ) (H : Mat) (k : ℝ)
    (hd : DifferentiableAt ℝ (scalar r) (k ^ 2, 0)) :
    deriv (directionalScalar r H k) 0 =
      3 * directionMass r H * scalar r (k ^ 2, 0) +
        (2 * k * (reduce r H 0 1).re - 2 * directionMass r H * k ^ 2) *
          deriv (fun z => scalar r (z, 0)) (k ^ 2) +
        diagonalContrast r H * deriv (fun y => scalar r (k ^ 2, y)) 0 := by
  let m := directionMass r H
  let d := diagonalContrast r H
  let c := reduce r H 0 1
  let F := scalar r
  have hm : HasDerivAt (fun t : ℝ => 1 + t*m) m 0 := by
    simpa [mul_comm] using (((hasDerivAt_id (0 : ℝ)).const_mul m).const_add 1)
  have hh : HasDerivAt (fun t : ℝ => ‖(k : ℂ) + t • c‖ ^ 2) (2 * k * c.re) 0 := by
    have hre : HasDerivAt (fun t : ℝ => k + t * c.re) c.re 0 := by
      simpa [mul_comm] using (((hasDerivAt_id (0 : ℝ)).const_mul c.re).const_add k)
    have him : HasDerivAt (fun t : ℝ => t * c.im) c.im 0 := by
      simpa [mul_comm] using ((hasDerivAt_id (0 : ℝ)).const_mul c.im)
    convert (hre.pow 2).add (him.pow 2) using 1
    · ext t
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
      ring
    · simp
  have h0 : ‖(k : ℂ) + (0 : ℝ) • c‖ ^ 2 = k ^ 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hz : HasDerivAt
      (fun t : ℝ => ‖(k : ℂ) + t • c‖ ^ 2 / (1 + t*m)^2)
      (2 * k * c.re - 2*m*k^2) 0 := by
    convert hh.div (hm.pow 2) (by norm_num) using 1
    · simp [h0]
      ring
  have hy : HasDerivAt (fun t : ℝ => t*d / (1+t*m)) d 0 := by
    have htd : HasDerivAt (fun t : ℝ => t * d) d 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const d
    simpa using htd.fun_div hm (by norm_num)
  have hp := hz.prodMk hy
  have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp [h0])
  have hmain := ((hm.pow 3).mul h).deriv
  have hfd := (deriv_along (q := (0, 1)) hd)
  have hfk : deriv (fun z => F (z, 0)) (k ^ 2) = fderiv ℝ F (k ^ 2, 0) (1, 0) := by
    have hh' : HasDerivAt (fun z : ℝ => (z, (0 : ℝ))) (1, 0) (k ^ 2) :=
      (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
    exact (hd.hasFDerivAt.comp_hasDerivAt_of_eq (k ^ 2) hh' rfl).deriv
  change deriv (directionalScalar r H k) 0 = _
  change deriv (directionalScalar r H k) 0 = _ at hmain
  rw [hmain, hfk]
  have hfd' : deriv (fun y => F (k ^ 2, y)) 0 = fderiv ℝ F (k ^ 2, 0) (0, 1) := by
    simpa [Prod.mk_add_mk, Prod.smul_mk] using hfd
  rw [hfd']
  have hp' :
      (2 * k * c.re - 2 * m * k ^ 2, d) =
        (2 * k * c.re - 2 * m * k ^ 2) • ((1, 0) : ℝ × ℝ) + d • ((0, 1) : ℝ × ℝ) := by
    simp [Prod.smul_mk, Prod.mk_add_mk]
  simp only [Function.comp_apply, h0, mul_zero, zero_mul, add_zero, one_pow, div_one,
    zero_div, Nat.cast_ofNat, one_mul, mul_one, hp', map_add, map_smul, smul_eq_mul]
  dsimp [m, d, c, F]
  ring

/-- The even part of the first variation cancels the entire off-diagonal
contribution. The extension variable is squared real coherence. -/
def evenVariation (r : ℝ) (H : Mat) (z : ℝ) : ℝ :=
  let m := directionMass r H
  let F := scalar r
  3 * m * F (z, 0) - 2 * m * z * deriv (fun z' => F (z', 0)) z +
    diagonalContrast r H * deriv (fun y => F (z, y)) 0

theorem evenVariation_physical (r : ℝ) (hr : 1 < r) (H : Mat) (hH : H.IsHermitian) :
    ∀ᶠ k : ℝ in 𝓝 0,
      (deriv (fun t : ℝ => operatorDeficit r (lift (physical r k 0) + t • H)) 0 +
        deriv (fun t : ℝ => operatorDeficit r (lift (physical r (-k) 0) + t • H)) 0) / 2 =
        evenVariation r H (k ^ 2) := by
  have hline : ContinuousAt (fun k : ℝ => (k ^ 2, (0 : ℝ))) 0 := by fun_prop
  have hpow : ContinuousAt (fun k : ℝ => k ^ 2) 0 := by fun_prop
  have hk := hpow.tendsto.eventually (eventually_lt_nhds (show (0 : ℝ) ^ 2 < 1 by norm_num))
  have hn := ((scalar_smooth r hr).eventually (by simp)).mono
    fun _ hp => hp.differentiableAt (by norm_num)
  have hd : ∀ᶠ k : ℝ in 𝓝 0, DifferentiableAt ℝ (scalar r) (k ^ 2, 0) :=
    hline.tendsto.eventually (by simpa using hn)
  filter_upwards [hk, hd] with k hk hd
  have hkneg : (-k) ^ 2 < 1 := by simpa using hk
  have hdneg : DifferentiableAt ℝ (scalar r) ((-k) ^ 2, 0) := by simpa using hd
  rw [deriv_operatorDeficit_factor hr.le hk H hH, deriv_operatorDeficit_factor hr.le hkneg H hH,
    directionalScalar_deriv r H k hd, directionalScalar_deriv r H (-k) hdneg]
  simp only [evenVariation, neg_sq]
  ring

/-- The coefficient of squared coherence in the even physical first variation
is the Gibbs-weighted real diagonal contrast times the one-mode coefficient. -/
theorem evenVariation_mixed (r : ℝ) (hr : 1 < r) (H : Mat) :
    HasDerivAt (evenVariation r H) (diagonalContrast r H * coefficient r) 0 := by
  let F := scalar r
  let m := directionMass r H
  let d := diagonalContrast r H
  have hF : ContDiffAt ℝ 2 (fun z => F (z, 0)) 0 := by
    have hline : ContDiffAt ℝ 2 (fun z : ℝ => (z, (0 : ℝ))) 0 := by fun_prop
    change ContDiffAt ℝ 2 (fun z => scalar r (z, 0)) 0
    exact (scalar_smooth r hr).fun_comp (f := fun z : ℝ => (z, (0 : ℝ))) 0 hline
  have hder : DifferentiableAt ℝ (deriv (fun z => F (z, 0))) 0 :=
    (hF.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h0 := scalar_edge_slope_zero r hr
  have hm := ((hasDerivAt_id (0 : ℝ)).const_mul (2 * m)).fun_mul hder.hasDerivAt
  have h := ((h0.const_mul (3 * m)).fun_sub hm).fun_add
    ((physical_mixed_direction r hr).const_mul d)
  have hh : HasDerivAt (fun z : ℝ => 3 * m * F (z, 0) -
      2 * m * z * deriv (fun z' => F (z', 0)) z +
        d * deriv (fun y => F (z, y)) 0) (d * coefficient r) 0 := by
    simpa [m, d, F, h0.deriv] using h
  exact hh

#print axioms evenVariation_physical
#print axioms evenVariation_mixed
#print axioms deriv_operatorDeficit_factor
#print axioms product_path_factor
#print axioms physical_mixed_direction
#print axioms operatorDeficit_physical
#print axioms diagonalContrast_eq_reduce
#print axioms deriv_operatorDeficit_diagonal
#print axioms physical_mixed

end D5.S3.Quantum.Semigroups.WuCubicHotInnerMixedTransfer
