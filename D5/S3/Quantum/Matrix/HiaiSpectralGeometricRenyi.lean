/- GID: D5/S3/Quantum/Matrix/HiaiSpectralGeometricRenyi
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/HiaiSpectralGeometricRenyi
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/HiaiSpectralGeometricRenyi.claim; result=D5/S3/Quantum/Matrix/HiaiSpectralGeometricRenyi.result; claim=D5/S3/Quantum/Matrix/HiaiSpectralGeometricRenyi.claim
   digest: Failure of the spectral geometric Renyi comparison beyond the sharp power boundary. -/

import D5.S3.Quantum.Matrix.SpectralGeometricLogEuclideanRefutation
import D5.S3.Quantum.Matrix.HiaiHarmonicArithmetic
import D5.S3.Quantum.Matrix.AlternativeMeanLinearization
import D5.S3.Quantum.Matrix.SharpWeightedLin.Settlement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/- admission_basis: open-problem-resolution (preregistration #31215).
   The general family is used at alpha=2, p=3, q=1 to refute the closed claim.
   Existing spectral means and matrix powers are reused without redefinition. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace D5.S3.Quantum.Matrix.HiaiSpectralGeometricRenyi
open Filter Topology
open _root_.Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.Quantum.Matrix.SpectralPower (mpow)
open _root_.D5.S3.Quantum.Matrix.SpectralGeometricLogEuclideanRefutation (wgm specMean SG)
open _root_.D5.S3.Quantum.Matrix.HiaiHarmonicArithmetic (symmetricTwo symmetricTwo_selfAdjoint symmetricTwo_cfc)

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

local notation "R" => SharpWeightedLin.hiaiRMean

/-- The first log-majorization inequality suggested in Problem 3.5. -/
def claim : Prop := ∀ (α p q : ℝ), 1 < α → 0 < p → 0 < q →
  ∀ (A B : Matrix (Fin 2) (Fin 2) ℂ), A.PosDef → B.PosDef →
  ∀ (hS : (SG α p A B).IsHermitian) (hR : (R α q A B).IsHermitian),
    hS.eigenvalues₀ 0 ≤ hR.eigenvalues₀ 0

private lemma top_formula (a b c : ℝ) :
    (show (symmetricTwo a b c).IsHermitian from symmetricTwo_selfAdjoint a b c).eigenvalues₀ 0 =
      (a+c+Real.sqrt ((a-c)^2+4*b^2))/2 := by
  let h : (symmetricTwo a b c).IsHermitian := symmetricTwo_selfAdjoint a b c
  let l := h.eigenvalues₀
  have hs : a+c = l 0+l 1 := by
    have ht : (symmetricTwo a b c).trace.re = l 0 + l 1 := by
      rw [h.trace_eq_sum_eigenvalues]
      simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_sum, Complex.ofReal_re]
      calc
        _ = ∑ i, l i :=
          Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 2)))).symm l
        _ = _ := Fin.sum_univ_two _
    simpa [symmetricTwo, Matrix.trace, Fin.sum_univ_two] using ht
  have hp : a*c-b^2 = l 0*l 1 := by
    have ht : (symmetricTwo a b c).det.re = l 0 * l 1 := by
      rw [h.det_eq_prod_eigenvalues]
      simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_prod, Complex.ofReal_re]
      calc
        _ = ∏ i, l i :=
          Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 2)))).symm l
        _ = _ := Fin.prod_univ_two _
    simpa [symmetricTwo, Matrix.det_fin_two, Complex.mul_re, pow_two] using ht
  have hl : l 1 ≤ l 0 := h.eigenvalues₀_antitone (by decide)
  have hd : (a-c)^2+4*b^2 = (l 0-l 1)^2 := by nlinarith [congrArg (fun r : ℝ => r^2) hs]
  rw [hd, Real.sqrt_sq (sub_nonneg.mpr hl)]
  change l 0 = _
  linarith

private def topScalar (a b c : ℝ) : ℝ := (a+c+Real.sqrt ((a-c)^2+4*b^2))/2

private lemma top_slope {a b c : ℝ → ℝ} {d : ℝ}
    (ha : HasDerivAt a 0 0) (hb : HasDerivAt b d 0) (hc : HasDerivAt c 0 0)
    (ha0 : a 0 = 1) (hb0 : b 0 = 0) (hc0 : c 0 = 1) (hd : 0 ≤ d) :
    HasDerivWithinAt (fun θ => topScalar (a θ) (b θ) (c θ)) d (Set.Ioi 0) 0 := by
  have hla := ha.tendsto_slope_zero_right
  have hlb := hb.tendsto_slope_zero_right
  have hlc := hc.tendsto_slope_zero_right
  simp only [zero_add, ha0, hb0, hc0, sub_zero, smul_eq_mul, ← div_eq_inv_mul] at hla hlb hlc
  have hdiff := hla.sub hlc
  have hlim := ((hla.add hlc).add (((hdiff.pow 2).add
    ((hlb.pow 2).const_mul 4)).sqrt)).div_const 2
  have hval : (0+0+Real.sqrt ((0-0)^2+4*d^2))/2 = d := by
    rw [show (0-0)^2+4*d^2 = (2*d)^2 by ring, Real.sqrt_sq (by positivity)]
    ring
  rw [hval] at hlim
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi 0)).mpr
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ0 : θ ≠ 0 := ne_of_gt hθ
  have hroot : Real.sqrt (((a θ-1)/θ-(c θ-1)/θ)^2+4*(b θ/θ)^2) =
      Real.sqrt ((a θ-c θ)^2+4*b θ^2)/θ := by
    rw [show ((a θ-1)/θ-(c θ-1)/θ)^2+4*(b θ/θ)^2 =
        ((a θ-c θ)^2+4*b θ^2)/θ^2 by field_simp; ring]
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hθ.le]
  simp only [slope, vsub_eq_sub, smul_eq_mul, zero_sub, sub_zero, ha0, hb0, hc0,
    topScalar, sub_self, zero_pow, mul_zero, add_zero, Real.sqrt_zero]
  rw [hroot]
  field_simp
  <;> ring


private lemma sinh_separation {p q k : ℝ} (hp : 0 < p) (hq : 0 < q)
    (_hk : 0 < k) (hk1 : k < 1) :
    ∃ z : ℝ, 0 < z ∧ p * Real.sinh (k*z) < q * Real.sinh z := by
  let z : ℝ := max 1 (Real.log (4*p/q)/(1-k)) + 1
  have hz1 : 1 < z := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have hδ : 0 < 1-k := sub_pos.mpr hk1
  have hzm : Real.log (4*p/q)/(1-k) < z :=
    lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  have hlog : Real.log (4*p/q) < (1-k)*z := by
    have hh := (div_lt_iff₀ hδ).mp hzm
    nlinarith
  have harg : 0 < 4*p/q := by positivity
  have hexp : 4*p/q < Real.exp ((1-k)*z) := by
    rw [← Real.exp_log harg]
    exact Real.exp_lt_exp.mpr hlog
  have hmul := mul_lt_mul_of_pos_left hexp (show 0 < q*Real.exp (k*z) by positivity)
  have hcancel : q*Real.exp (k*z)*(4*p/q) = 4*p*Real.exp (k*z) := by
    field_simp [hq.ne']
    <;> ring
  have hexps : Real.exp z = Real.exp (k*z)*Real.exp ((1-k)*z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcomp : 4*p*Real.exp (k*z) < q*Real.exp z := by
    rw [hcancel] at hmul
    rw [hexps]
    nlinarith
  have hez : 2 ≤ Real.exp z := by
    have hh := Real.add_one_le_exp z
    linarith
  have heneg : Real.exp (-z) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hlow : Real.exp z/4 ≤ Real.sinh z := by
    rw [Real.sinh_eq]
    nlinarith
  have hupp : Real.sinh (k*z) < Real.exp (k*z)/2 := by
    rw [Real.sinh_eq]
    have hh := Real.exp_pos (-(k*z))
    linarith
  refine ⟨z, by linarith, ?_⟩
  have hupper := mul_lt_mul_of_pos_left hupp hp
  have hlower := mul_le_mul_of_nonneg_left hlow hq.le
  nlinarith

private lemma coefficient_separation {α p q : ℝ}
    (hα : 1 < α) (hq : 0 < q) (hpq : α*q < p) :
    ∃ u : ℝ, 0 < u ∧
      p * Real.sinh ((α*q/p)*(α-1)*u) < q * Real.sinh ((α-1)*u) := by
  have hs : 0 < α-1 := sub_pos.mpr hα
  have hp : 0 < p := lt_trans (mul_pos (by linarith) hq) hpq
  have hk : 0 < α*q/p := div_pos (mul_pos (by linarith) hq) hp
  have hk1 : α*q/p < 1 := (div_lt_one hp).mpr hpq
  obtain ⟨z, hz, hsep⟩ := sinh_separation hp hq hk hk1
  refine ⟨z/(α-1), div_pos hz hs, ?_⟩
  have he : (α-1)*(z/(α-1)) = z := by field_simp [hs.ne']
  have hek : (α*q/p)*(α-1)*(z/(α-1)) = (α*q/p)*z := by rw [mul_assoc, he]
  rw [hek, he]
  exact hsep

private lemma two_point_power_slope {x y d k : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : y < x) (a b c : ℝ → ℝ)
    (ha0 : a 0 = x) (hb0 : b 0 = 0) (hc0 : c 0 = y)
    (ha : HasDerivAt a 0 0) (hb : HasDerivAt b d 0) (hc : HasDerivAt c 0 0) :
    ∃ f g h : ℝ → ℝ,
      (∀ᶠ t in 𝓝 (0 : ℝ),
        mpow (symmetricTwo (a t) (b t) (c t)) k = symmetricTwo (f t) (g t) (h t)) ∧
      f 0 = x^k ∧ g 0 = 0 ∧ h 0 = y^k ∧
      HasDerivAt f 0 0 ∧
      HasDerivAt g (d*(x^k-y^k)/(x-y)) 0 ∧ HasDerivAt h 0 0 := by
  let E : ℝ → ℝ := fun t => Real.sqrt ((a t-c t)^2+4*(b t)^2)
  let U : ℝ → ℝ := fun t => (a t+c t+E t)/2
  let V : ℝ → ℝ := fun t => (a t+c t-E t)/2
  let D : ℝ → ℝ := fun t => (U t^k-V t^k)/E t
  let f : ℝ → ℝ := fun t => U t^k+D t*(a t-U t)
  let g : ℝ → ℝ := fun t => D t*b t
  let h : ℝ → ℝ := fun t => U t^k+D t*(c t-U t)
  have hgap : x-y ≠ 0 := (sub_pos.mpr hxy).ne'
  have hE0 : E 0 = x-y := by
    dsimp [E]
    rw [ha0, hb0, hc0]
    simpa using Real.sqrt_sq (sub_nonneg.mpr hxy.le)
  have hbase : HasDerivAt (fun t => (a t-c t)^2+4*(b t)^2) 0 0 := by
    convert ((ha.sub hc).pow 2).add ((hb.pow 2).const_mul 4) using 1 <;>
      simp [hb0]
  have hE : HasDerivAt E 0 0 := by
    have hh := hbase.sqrt (by simpa [ha0, hb0, hc0] using pow_ne_zero 2 hgap)
    simpa only [E, zero_div] using hh
  have hU0 : U 0 = x := by dsimp [U]; rw [ha0, hc0, hE0]; ring
  have hV0 : V 0 = y := by dsimp [V]; rw [ha0, hc0, hE0]; ring
  have hU : HasDerivAt U 0 0 := by
    simpa only [U, Pi.add_apply, zero_add, zero_div] using ((ha.add hc).add hE).div_const 2
  have hV : HasDerivAt V 0 0 := by
    simpa only [V, Pi.add_apply, Pi.sub_apply, zero_add, sub_zero, zero_div] using ((ha.add hc).sub hE).div_const 2
  have hUP : HasDerivAt (fun t => U t^k) 0 0 := by
    simpa only [zero_mul] using hU.rpow_const (p := k) (Or.inl (by rw [hU0]; exact hx.ne'))
  have hVP : HasDerivAt (fun t => V t^k) 0 0 := by
    simpa only [zero_mul] using hV.rpow_const (p := k) (Or.inl (by rw [hV0]; exact hy.ne'))
  have hD0 : D 0 = (x^k-y^k)/(x-y) := by simp only [D, hU0, hV0, hE0]
  have hD : HasDerivAt D 0 0 := by
    convert (hUP.sub hVP).div hE (by rw [hE0]; exact hgap) using 1 <;>
      first | rfl | simp
  have hf : HasDerivAt f 0 0 := by
    convert hUP.add (hD.mul (ha.sub hU)) using 1 <;> first | rfl | simp
  have hg : HasDerivAt g (d*(x^k-y^k)/(x-y)) 0 := by
    convert hD.mul hb using 1
    rw [hD0]
    ring
  have hh : HasDerivAt h 0 0 := by
    convert hUP.add (hD.mul (hc.sub hU)) using 1 <;> first | rfl | simp
  refine ⟨f, g, h, ?_, ?_, ?_, ?_, hf, hg, hh⟩
  · filter_upwards [hE.continuousAt.eventually_ne (by rw [hE0]; exact hgap)] with t ht
    have hs : E t ^ 2 = (a t-c t)^2+4*(b t)^2 := Real.sq_sqrt (by positivity)
    rw [mpow, symmetricTwo_cfc (fun z : ℝ => z^k) ht hs]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symmetricTwo, f, g, h, D, U, V, Matrix.smul_apply, Complex.real_smul,
        ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub,
        ← Complex.ofReal_div]
    all_goals push_cast
    all_goals field_simp [ht]
    all_goals ring
  · simp only [f, hU0, ha0, sub_self, mul_zero, add_zero]
  · simp only [g, hb0, mul_zero]
  · dsimp only [h]
    rw [hU0, hc0, hD0]
    field_simp [hgap]
    <;> ring

private def J (θ : ℝ) : Mat := symmetricTwo (-Real.cos (2*θ)) (Real.sin (2*θ)) (Real.cos (2*θ))
private def ta (v θ : ℝ) := Real.cosh v - Real.sinh v * Real.cos (2*θ)
private def tb (v θ : ℝ) := Real.sinh v * Real.sin (2*θ)
private def tc (v θ : ℝ) := Real.cosh v + Real.sinh v * Real.cos (2*θ)
private def turn (v θ : ℝ) : Mat := symmetricTwo (ta v θ) (tb v θ) (tc v θ)
private def D (v : ℝ) : Mat := turn (-v) 0

private lemma J_data (θ : ℝ) : IsSelfAdjoint (J θ) ∧ J θ * J θ = 1 := by
  refine ⟨symmetricTwo_selfAdjoint _ _ _, ?_⟩
  have ht := Real.sin_sq_add_cos_sq (2*θ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, symmetricTwo, Matrix.mul_apply, Fin.sum_univ_two,
      ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_neg]
  all_goals norm_cast
  all_goals nlinarith

private lemma turn_affine (v θ : ℝ) :
    turn v θ = Real.cosh v • (1 : Mat) + Real.sinh v • J θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [turn, ta, tb, tc, J, symmetricTwo, Matrix.smul_apply, Complex.real_smul]
  all_goals push_cast
  all_goals ring

private lemma turn_power (v θ k : ℝ) : mpow (turn v θ) k = turn (v*k) θ := by
  rw [mpow, turn_affine, QuantumTwoPointFunctionalCalculus.two_point_cfc
    _ _ _ _ (J_data θ).1 (J_data θ).2, turn_affine]
  rw [Real.cosh_add_sinh, Real.cosh_sub_sinh, ← Real.exp_mul, ← Real.exp_mul]
  simp only [neg_mul, Real.cosh_eq, Real.sinh_eq]

private lemma turn_pos (v θ : ℝ) : (turn v θ).PosDef := by
  have he : turn v θ = cfc (fun z : ℝ => Real.exp (v*z)) (J θ) := by
    have hh := QuantumTwoPointFunctionalCalculus.two_point_cfc
      (fun z : ℝ => Real.exp (v*z)) 0 1 (J θ) (J_data θ).1 (J_data θ).2
    simpa [turn_affine, Real.cosh_eq, Real.sinh_eq] using hh.symm
  rw [he]
  exact ((cfc_isStrictlyPositive_iff _ _ (by fun_prop) (J_data θ).1).mpr
    (fun _ _ => Real.exp_pos _)).posDef

private lemma D_eq (v : ℝ) : D v = diagonal ![(Real.exp v : ℂ), (Real.exp (-v) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [D, turn, ta, tb, tc, symmetricTwo, Real.cosh_add_sinh, Real.cosh_sub_sinh,
      ← sub_eq_add_neg]

private lemma D_power (v k : ℝ) : mpow (D v) k = D (v*k) := by
  simpa only [D, neg_mul] using turn_power (-v) 0 k

private lemma turn_derivatives (v : ℝ) :
    ta v 0 = Real.exp (-v) ∧ tb v 0 = 0 ∧ tc v 0 = Real.exp v ∧
    HasDerivAt (ta v) 0 0 ∧ HasDerivAt (tb v) (2*Real.sinh v) 0 ∧
    HasDerivAt (tc v) 0 0 := by
  have hs := ((hasDerivAt_id (0 : ℝ)).const_mul 2).sin
  have hc := ((hasDerivAt_id (0 : ℝ)).const_mul 2).cos
  refine ⟨by simp [ta, Real.cosh_sub_sinh], by simp [tb],
    by simp [tc, Real.cosh_add_sinh], ?_, ?_, ?_⟩
  · convert (hasDerivAt_const (0 : ℝ) (Real.cosh v)).sub (hc.const_mul (Real.sinh v)) using 1 <;>
      first | rfl | simp
  · convert hs.const_mul (Real.sinh v) using 1 <;> first | rfl | simp [mul_comm]
  · convert (hasDerivAt_const (0 : ℝ) (Real.cosh v)).add (hc.const_mul (Real.sinh v)) using 1 <;>
      first | rfl | simp
  all_goals ring


private def sa (w a b : ℝ) : ℝ := Real.exp w*a^2+Real.exp (-w)*b^2
private def sb (w a b c : ℝ) : ℝ := b*(Real.exp w*a+Real.exp (-w)*c)
private def sc (w b c : ℝ) : ℝ := Real.exp w*b^2+Real.exp (-w)*c^2

private lemma sandwich_formula (w a b c : ℝ) :
    symmetricTwo a b c * symmetricTwo (Real.exp w) 0 (Real.exp (-w)) *
      symmetricTwo a b c = symmetricTwo (sa w a b) (sb w a b c) (sc w b c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricTwo, sa, sb, sc, Matrix.mul_apply, Fin.sum_univ_two,
      ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_pow]
  all_goals push_cast
  all_goals ring

private lemma sandwich_slope {w x y d : ℝ} (a b c : ℝ → ℝ)
    (ha0 : a 0 = x) (hb0 : b 0 = 0) (hc0 : c 0 = y)
    (ha : HasDerivAt a 0 0) (hb : HasDerivAt b d 0) (hc : HasDerivAt c 0 0) :
    sa w (a 0) (b 0) = Real.exp w*x^2 ∧
    sb w (a 0) (b 0) (c 0) = 0 ∧
    sc w (b 0) (c 0) = Real.exp (-w)*y^2 ∧
    HasDerivAt (fun t => sa w (a t) (b t)) 0 0 ∧
    HasDerivAt (fun t => sb w (a t) (b t) (c t))
      (d*(Real.exp w*x+Real.exp (-w)*y)) 0 ∧
    HasDerivAt (fun t => sc w (b t) (c t)) 0 0 := by
  refine ⟨by simp [sa, ha0, hb0], by simp [sb, hb0], by simp [sc, hb0, hc0], ?_, ?_, ?_⟩
  · convert ((ha.pow 2).const_mul (Real.exp w)).add
      ((hb.pow 2).const_mul (Real.exp (-w))) using 1 <;> first | rfl | simp [sa, hb0]
  · convert hb.mul ((ha.const_mul (Real.exp w)).add (hc.const_mul (Real.exp (-w)))) using 1 <;> first | rfl | simp [sb, ha0, hc0]
  · convert ((hb.pow 2).const_mul (Real.exp w)).add
      ((hc.pow 2).const_mul (Real.exp (-w))) using 1 <;> first | rfl | simp [sc, hb0]
  all_goals rfl

private lemma sandwich_zero (v w : ℝ) :
    sa w (Real.exp (-v)) 0 = Real.exp (w-2*v) ∧
    sb w (Real.exp (-v)) 0 (Real.exp v) = 0 ∧
    sc w 0 (Real.exp v) = Real.exp (2*v-w) := by
  refine ⟨?_, by simp [sb], ?_⟩
  · simp only [sa, zero_pow, mul_zero, add_zero, pow_two]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · simp only [sc, zero_pow, mul_zero, zero_add, pow_two]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

private lemma spectral_core_slope (z : ℝ) :
    2*Real.sinh (z/2)*(Real.exp (z-z/2)+Real.exp (z/2-z)) = 2*Real.sinh z := by
  have he : z-z/2 = z/2 := by ring
  have he' : z/2-z = -(z/2) := by ring
  rw [he, he', Real.sinh_eq, Real.sinh_eq]
  have hp : Real.exp (z/2)*Real.exp (z/2) = Real.exp z := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hm : Real.exp (-(z/2))*Real.exp (-(z/2)) = Real.exp (-z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith

private lemma input_core_slope (α u : ℝ) :
    2*Real.sinh (u/2)*(Real.exp (α*u-u/2)+Real.exp (u/2-α*u)) =
      2*(Real.sinh (α*u)-Real.sinh ((α-1)*u)) := by
  rw [Real.sinh_eq, Real.sinh_eq, Real.sinh_eq]
  have h₁ : Real.exp (u/2)*Real.exp (α*u-u/2) = Real.exp (α*u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₂ : Real.exp (u/2)*Real.exp (u/2-α*u) = Real.exp (-((α-1)*u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₃ : Real.exp (-(u/2))*Real.exp (α*u-u/2) = Real.exp ((α-1)*u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₄ : Real.exp (-(u/2))*Real.exp (u/2-α*u) = Real.exp (-(α*u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith

private lemma sandwich_slope_factor (v w d : ℝ) :
    d*(Real.exp w*Real.exp (-v)+Real.exp (-w)*Real.exp v) =
      d*(Real.exp (w-v)+Real.exp (v-w)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  rw [show w + -v = w-v by ring, show -w+v = v-w by ring]

private lemma mpow_pos {M : Mat} (hM : M.PosDef) (r : ℝ) : (mpow M r).PosDef := by
  rw [mpow, ← CFC.rpow_eq_cfc_real hM.posSemidef.nonneg]
  exact (hM.isStrictlyPositive.rpow M r).posDef

private lemma mpow_eq {M : Mat} (hM : M.PosDef) (r : ℝ) :
    mpow M r = CFC.rpow M r := (CFC.rpow_eq_cfc_real hM.posSemidef.nonneg).symm

private lemma mpow_comp {M : Mat} (hM : M.PosDef) {r : ℝ} (hr : r ≠ 0) (s : ℝ) :
    mpow (mpow M r) s = mpow M (r*s) := by
  rw [mpow_eq (mpow_pos hM r), mpow_eq hM, mpow_eq hM]
  simpa only [← CFC.rpow_eq_pow] using CFC.rpow_rpow M r s hr hM.isStrictlyPositive

private lemma D_pos (v : ℝ) : (D v).PosDef := turn_pos (-v) 0

private lemma D_sym (v : ℝ) : D v = symmetricTwo (Real.exp v) 0 (Real.exp (-v)) := by
  rw [D_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmetricTwo]

private lemma D_inverse (v : ℝ) : (D v)⁻¹ = D (-v) := by
  apply Matrix.inv_eq_left_inv
  have he : Real.exp (-v)*Real.exp v = 1 := by rw [← Real.exp_add]; simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [D_eq, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]

private lemma geometric_bridge (w : ℝ) (Y : Mat) :
    wgm (D w)⁻¹ Y (1/2) = AlternativeMeanLinearization.gmInv (D w) Y := by
  change wgm (D w)⁻¹ Y (1/2) =
    mpow (D w) (-(1/2)) * mpow (mpow (D w) (1/2) * Y * mpow (D w) (1/2)) (1/2) *
      mpow (D w) (-(1/2))
  rw [wgm, D_inverse, D_power, D_power, D_power, D_power]
  simp only [neg_mul, mul_neg, neg_neg, neg_div]

private lemma core_pos (v w θ : ℝ) : (turn v θ * D w * turn v θ).PosDef := by
  have ht := turn_pos v θ
  simpa only [Matrix.star_eq_conjTranspose, ht.isHermitian.eq] using
    ht.isUnit.posDef_star_right_conjugate_iff.mpr (D_pos w)

private lemma geometric_core (v w θ : ℝ) :
    wgm (D w)⁻¹ (turn v θ * D w * turn v θ) (1/2) = turn v θ := by
  rw [geometric_bridge]
  exact AlternativeMeanLinearization.riccati_unique (D_pos w) (turn_pos v θ) rfl

private def Y (α u θ : ℝ) : Mat := turn (u/2) θ * D (α*u) * turn (u/2) θ
private def A (α u p : ℝ) : Mat := D (α*u/p)
private def B (α u p θ : ℝ) : Mat := mpow (Y α u θ) (1/p)

private lemma input_pos (α u p θ : ℝ) : (A α u p).PosDef ∧ (B α u p θ).PosDef :=
  ⟨D_pos _, mpow_pos (core_pos _ _ _) _⟩

private lemma SG_core {p : ℝ} (hp : p ≠ 0) (α u θ : ℝ) :
    SG α p (A α u p) (B α u p θ) =
      mpow (turn (α*u/2) θ * D (α*u) * turn (α*u/2) θ) (1/p) := by
  have hA : mpow (A α u p) p = D (α*u) := by
    rw [A, D_power, div_mul_cancel₀ _ hp]
  have hB : mpow (B α u p θ) p = Y α u θ := by
    rw [B, mpow_comp (show (Y α u θ).PosDef from core_pos _ _ _) (one_div_ne_zero hp), one_div_mul_cancel hp,
      SpectralPower.mpow_one (show (Y α u θ).IsHermitian from (core_pos _ _ _).isHermitian)]
  rw [SG, hA, hB, specMean, Y, geometric_core, turn_power]
  rw [show u/2*α = α*u/2 by ring]

private lemma R_core {p : ℝ} (hp : p ≠ 0) (α u q θ : ℝ) :
    R α q (A α u p) (B α u p θ) =
      mpow (D ((α*u/p)*((1-α)*q/2)) * mpow (Y α u θ) (α*q/p) *
        D ((α*u/p)*((1-α)*q/2))) (1/q) := by
  have hA := (input_pos α u p θ).1
  have hB := (input_pos α u p θ).2
  let H := mpow (A α u p) ((1-α)*q/2)
  have hH : H.PosDef := mpow_pos hA _
  have hC : (H * mpow (B α u p θ) (α*q) * H).PosDef := by
    simpa only [Matrix.star_eq_conjTranspose, hH.isHermitian.eq] using
      hH.isUnit.posDef_star_right_conjugate_iff.mpr (mpow_pos hB (α*q))
  change CFC.rpow _ _ = _
  rw [← mpow_eq hA, ← mpow_eq hB, ← mpow_eq hC]
  dsimp only [H]
  rw [A, D_power, B, mpow_comp (show (Y α u θ).PosDef from core_pos _ _ _)
    (one_div_ne_zero hp)]
  congr 3 <;> congr 1 <;> ring

private lemma core_coordinates (v w : ℝ) :
    ∃ a b c : ℝ → ℝ,
      (∀ θ, turn v θ * D w * turn v θ = symmetricTwo (a θ) (b θ) (c θ)) ∧
      a 0 = Real.exp (w-2*v) ∧ b 0 = 0 ∧ c 0 = Real.exp (2*v-w) ∧
      HasDerivAt a 0 0 ∧
      HasDerivAt b (2*Real.sinh v*(Real.exp (w-v)+Real.exp (v-w))) 0 ∧
      HasDerivAt c 0 0 := by
  rcases turn_derivatives v with ⟨ha0, hb0, hc0, ha, hb, hc⟩
  rcases sandwich_slope (w := w) (ta v) (tb v) (tc v) ha0 hb0 hc0 ha hb hc with
    ⟨_, hb0', _, ha', hb', hc'⟩
  refine ⟨(fun θ => sa w (ta v θ) (tb v θ)),
    (fun θ => sb w (ta v θ) (tb v θ) (tc v θ)),
    (fun θ => sc w (tb v θ) (tc v θ)), ?_, ?_, hb0', ?_, ha', ?_, hc'⟩
  · intro θ; rw [D_sym]; exact sandwich_formula _ _ _ _
  · dsimp only; rw [ha0, hb0]; exact (sandwich_zero v w).1
  · dsimp only; rw [hb0, hc0]; exact (sandwich_zero v w).2.2
  · simpa only [sandwich_slope_factor] using hb'

private lemma diagonal_congruence (v a b c : ℝ) :
    D v * symmetricTwo a b c * D v =
      symmetricTwo (Real.exp (2*v)*a) b (Real.exp (-2*v)*c) := by
  rw [D_sym]
  have hm : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
  have hp : Real.exp v * Real.exp v = Real.exp (2*v) := by rw [← Real.exp_add]; congr 1; ring
  have hn : Real.exp (-v) * Real.exp (-v) = Real.exp (-2*v) := by rw [← Real.exp_add]; congr 1; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmetricTwo, Matrix.mul_apply, Fin.sum_univ_two,
      ← Complex.ofReal_mul, ← Complex.ofReal_add]
  all_goals norm_cast
  · linear_combination a*hp
  · linear_combination b*hm
  · linear_combination b*hm
  · simp only [neg_mul] at hn
    linear_combination c*hn

private lemma power_top (a b c r : ℝ) (hM : (symmetricTwo a b c).PosDef) (hr : 0 ≤ r) :
    (mpow_pos hM r).isHermitian.eigenvalues₀ 0 = topScalar a b c ^ r := by
  have hh : (CFC.rpow (symmetricTwo a b c) r).IsHermitian :=
    (hM.isStrictlyPositive.rpow _ r).posDef.isHermitian
  have he := SharpWeightedLin.eigenvalues_zero_rpow hM.posSemidef hr hh 0
  rw [show hM.isHermitian.eigenvalues₀ 0 = topScalar a b c from top_formula a b c] at he
  simpa only [mpow_eq hM] using he

private lemma exp_divided_power (t k : ℝ) :
    ((Real.exp t)^k-(Real.exp (-t))^k)/(Real.exp t-Real.exp (-t)) =
      Real.sinh (k*t)/Real.sinh t := by
  rw [← Real.exp_mul, ← Real.exp_mul]
  rw [show t*k=k*t by ring, show (-t)*k=-(k*t) by ring]
  simp only [Real.sinh_eq]
  rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]

private lemma power_top_slope {a b c : ℝ → ℝ} {d r : ℝ}
    (ha : HasDerivAt a 0 0) (hb : HasDerivAt b d 0) (hc : HasDerivAt c 0 0)
    (ha0 : a 0 = 1) (hb0 : b 0 = 0) (hc0 : c 0 = 1) (hd : 0 ≤ d) :
    HasDerivWithinAt (fun θ => topScalar (a θ) (b θ) (c θ)^r)
      (d*r) (Set.Ioi 0) 0 := by
  have hz : topScalar (a 0) (b 0) (c 0) = 1 := by simp [topScalar, ha0, hb0, hc0]
  have hh := (top_slope ha hb hc ha0 hb0 hc0 hd).rpow_const (p := r)
    (Or.inl (by rw [hz]; norm_num))
  simpa only [hz, Real.one_rpow, mul_one] using hh

private def renyiSlope (α u k : ℝ) :=
  2*(Real.sinh (α*u)-Real.sinh ((α-1)*u))*Real.sinh (k*((α-1)*u))/Real.sinh ((α-1)*u)

private lemma slopes_order {α u p q : ℝ} (hα : 1 < α) (hu : 0 < u)
    (hp : 0 < p) (hq : 0 < q)
    (hsep : p*Real.sinh ((α*q/p)*(α-1)*u) < q*Real.sinh ((α-1)*u)) :
    0 ≤ renyiSlope α u (α*q/p) ∧
      renyiSlope α u (α*q/p)/q < 2*Real.sinh (α*u)/p := by
  have hs : 0 < Real.sinh ((α-1)*u) := Real.sinh_pos_iff.mpr (by positivity)
  have ht : 0 < Real.sinh (α*u) := Real.sinh_pos_iff.mpr (by positivity)
  have hdiff : 0 < Real.sinh (α*u)-Real.sinh ((α-1)*u) :=
    sub_pos.mpr (Real.sinh_lt_sinh.mpr (by nlinarith))
  have hk : 0 < Real.sinh ((α*q/p)*((α-1)*u)) := Real.sinh_pos_iff.mpr (by positivity)
  have hsep' : p*Real.sinh ((α*q/p)*((α-1)*u)) < q*Real.sinh ((α-1)*u) := by
    simpa only [mul_assoc] using hsep
  refine ⟨by dsimp [renyiSlope]; positivity, ?_⟩
  rw [div_lt_div_iff₀ hq hp]
  dsimp [renyiSlope]
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hs).mpr
  have hh := mul_lt_mul_of_pos_left hsep' (show 0 < 2*(Real.sinh (α*u)-Real.sinh ((α-1)*u)) by positivity)
  nlinarith [mul_pos hs (mul_pos hq hs)]

private lemma renyi_coordinates {α u : ℝ} (hα : 1 < α) (hu : 0 < u) (k : ℝ) :
    ∃ f g h : ℝ → ℝ,
      (∀ᶠ θ in 𝓝 (0 : ℝ),
        D (-k*((α-1)*u)/2) * mpow (Y α u θ) k * D (-k*((α-1)*u)/2) =
          symmetricTwo (f θ) (g θ) (h θ)) ∧
      f 0 = 1 ∧ g 0 = 0 ∧ h 0 = 1 ∧ HasDerivAt f 0 0 ∧
      HasDerivAt g (renyiSlope α u k) 0 ∧ HasDerivAt h 0 0 := by
  let t := (α-1)*u
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨a, b, c, he, ha0, hb0, hc0, ha, hb, hc⟩ := core_coordinates (u/2) (α*u)
  rw [show α*u-2*(u/2)=t by dsimp [t]; ring] at ha0
  rw [show 2*(u/2)-α*u = -t by dsimp [t]; ring] at hc0
  rw [input_core_slope] at hb
  obtain ⟨f, g, h, hpow, hf0, hg0, hh0, hf, hg, hh⟩ :=
    two_point_power_slope (k := k) (Real.exp_pos t) (Real.exp_pos (-t))
      (Real.exp_lt_exp.mpr (by linarith)) a b c ha0 hb0 hc0 ha hb hc
  refine ⟨(fun θ => Real.exp (-k*t)*f θ), g, (fun θ => Real.exp (k*t)*h θ),
    ?_, ?_, hg0, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hpow] with θ hθ
    change D (-k*t/2) * mpow (Y α u θ) k * D (-k*t/2) = _
    rw [Y, he θ, hθ, diagonal_congruence,
      show 2*(-k*t/2) = -k*t by ring, show -2*(-k*t/2)=k*t by ring]
  · dsimp only
    rw [hf0, ← Real.exp_mul, ← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  · dsimp only
    rw [hh0, ← Real.exp_mul, ← Real.exp_add]
    convert Real.exp_zero using 1 <;> congr 1 <;> ring
  · simpa only [mul_zero] using hf.const_mul (Real.exp (-k*t))
  · convert hg using 1
    dsimp [renyiSlope]
    rw [mul_div_assoc]
    conv_rhs => rw [mul_div_assoc, exp_divided_power]
  · simpa only [mul_zero] using hh.const_mul (Real.exp (k*t))

private lemma power_top_of_eq {M : Mat} (hM : M.IsHermitian) (a b c r : ℝ)
    (hP : (symmetricTwo a b c).PosDef) (hr : 0 ≤ r)
    (he : M = mpow (symmetricTwo a b c) r) :
    hM.eigenvalues₀ 0 = topScalar a b c ^ r := by
  subst M
  exact power_top a b c r hP hr

private lemma counterexample {α p q : ℝ} (hα : 1 < α) (hq : 0 < q) (hpq : α*q < p) :
    ∃ (A B : Matrix (Fin 2) (Fin 2) ℂ), A.PosDef ∧ B.PosDef ∧
      ∃ (hS : (SG α p A B).IsHermitian) (hR : (R α q A B).IsHermitian),
        hR.eigenvalues₀ 0 < hS.eigenvalues₀ 0 := by
  have hp : 0 < p := lt_trans (mul_pos (by linarith) hq) hpq
  obtain ⟨u, hu, hsep⟩ := coefficient_separation hα hq hpq
  have horder := slopes_order hα hu hp hq hsep
  obtain ⟨a, b, c, he, ha0, hb0, hc0, ha, hb, hc⟩ := core_coordinates (α*u/2) (α*u)
  have ha1 : a 0 = 1 := by simpa only [show α*u-2*(α*u/2)=0 by ring, Real.exp_zero] using ha0
  have hc1 : c 0 = 1 := by simpa only [show 2*(α*u/2)-α*u=0 by ring, Real.exp_zero] using hc0
  rw [spectral_core_slope] at hb
  obtain ⟨f, g, h, hRC, hf0, hg0, hh0, hf, hg, hh⟩ := renyi_coordinates hα hu (α*q/p)
  have hslope := power_top_slope (r := 1/p) ha hb hc ha1 hb0 hc1
    (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (Real.sinh_pos_iff.mpr (mul_pos (by linarith : 0 < α) hu)).le)
  have hrslope := power_top_slope (r := 1/q) hf hg hh hf0 hg0 hh0 horder.1
  have hsz : topScalar (a 0) (b 0) (c 0) = 1 := by simp [topScalar, ha1, hb0, hc1]
  have hrz : topScalar (f 0) (g 0) (h 0) = 1 := by simp [topScalar, hf0, hg0, hh0]
  have hlim := (hasDerivWithinAt_iff_tendsto_slope'
    (by simp : (0 : ℝ) ∉ Set.Ioi 0)).mp (hslope.sub hrslope)
  have hpos : 0 < 2*Real.sinh (α*u)*(1/p)-renyiSlope α u (α*q/p)*(1/q) := by
    simpa only [div_eq_mul_inv, one_mul] using sub_pos.mpr horder.2
  have hev := hlim.eventually (eventually_gt_nhds hpos)
  have hex : ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      ∃ (hS : (SG α p (A α u p) (B α u p θ)).IsHermitian)
        (hR : (R α q (A α u p) (B α u p θ)).IsHermitian),
        hR.eigenvalues₀ 0 < hS.eigenvalues₀ 0 := by
    filter_upwards [hev, hRC.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with θ hθ hRCθ hθpos
    have hSP : (symmetricTwo (a θ) (b θ) (c θ)).PosDef := (he θ) ▸ core_pos _ _ _
    have hSG : SG α p (A α u p) (B α u p θ) =
        mpow (symmetricTwo (a θ) (b θ) (c θ)) (1/p) := by rw [SG_core hp.ne', he θ]
    have hS : (SG α p (A α u p) (B α u p θ)).PosDef := hSG.symm ▸ mpow_pos hSP _
    let v := -(α*q/p)*((α-1)*u)/2
    have hH : (D v).PosDef := D_pos v
    have hY : (mpow (Y α u θ) (α*q/p)).PosDef := mpow_pos (core_pos _ _ _) _
    have hC : (D v * mpow (Y α u θ) (α*q/p) * D v).PosDef := by
      simpa only [Matrix.star_eq_conjTranspose, hH.isHermitian.eq] using
        hH.isUnit.posDef_star_right_conjugate_iff.mpr hY
    have hRP : (symmetricTwo (f θ) (g θ) (h θ)).PosDef := hRCθ ▸ hC
    have hRmean : R α q (A α u p) (B α u p θ) =
        mpow (symmetricTwo (f θ) (g θ) (h θ)) (1/q) := by
      rw [R_core hp.ne', show (α*u/p)*((1-α)*q/2) = v by dsimp [v]; ring, hRCθ]
    have hR : (R α q (A α u p) (B α u p θ)).PosDef := hRmean.symm ▸ mpow_pos hRP _
    refine ⟨hS.isHermitian, hR.isHermitian, ?_⟩
    rw [power_top_of_eq hS.isHermitian _ _ _ _ hSP (by positivity) hSG,
      power_top_of_eq hR.isHermitian _ _ _ _ hRP (by positivity) hRmean]
    have hθ' : 0 < (topScalar (a θ) (b θ) (c θ)^(1/p) -
        topScalar (f θ) (g θ) (h θ)^(1/q)) / θ := by
      rw [slope_def_field] at hθ
      change 0 < ((topScalar (a θ) (b θ) (c θ)^(1/p) -
        topScalar (f θ) (g θ) (h θ)^(1/q)) -
        (topScalar (a 0) (b 0) (c 0)^(1/p) -
        topScalar (f 0) (g 0) (h 0)^(1/q))) / (θ-0) at hθ
      simpa only [hsz, hrz, Real.one_rpow, sub_self, sub_zero] using hθ
    have hnum : 0 < topScalar (a θ) (b θ) (c θ)^(1/p)-
        topScalar (f θ) (g θ) (h θ)^(1/q) := by
      rcases div_pos_iff.mp hθ' with h | h
      · exact h.1
      · exact False.elim (not_lt_of_ge hθpos.le h.2)
    exact sub_pos.mp hnum
  obtain ⟨θ, hS, hR, hstrict⟩ := hex.exists
  exact ⟨A α u p, B α u p θ, (input_pos α u p θ).1, (input_pos α u p θ).2,
    hS, hR, hstrict⟩

/-- Problem 3.5's unrestricted first spectral inequality is false. -/
theorem result : ¬ claim := by
  intro hc
  obtain ⟨A, B, hA, hB, hS, hR, hstrict⟩ :=
    counterexample (α := 2) (p := 3) (q := 1) (by norm_num) (by norm_num) (by norm_num)
  exact (not_le_of_gt hstrict) (hc 2 3 1 (by norm_num) (by norm_num) (by norm_num) A B hA hB hS hR)

#print axioms result

end D5.S3.Quantum.Matrix.HiaiSpectralGeometricRenyi
