/- GID: D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfIdentityCubicDerivatives
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.HermitianFunctionalCalculus]
   utility: none
   digest: Actual derivatives of affine Hermitian matrix powers at the identity. -/

/-
admission_basis: escape-witness
proof_shape: qubit_cubic_compatibility: content
escape_witness: HsfQubitMixedCubic.coefficient_compatibility
The fixed-spectrum differentiation and cubic trace helpers are consumed by the
actual identity-denominator derivative bridge and qubit compatibility result.
No Taylor premise, arbitrary-denominator reduction, or novelty claim is used.
-/

module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Tactic
public import D5.S3.Quantum.Matrix.HsfQubitMixedCubic

/-! Differentiation on a fixed finite spectrum, with actual CFC powers of the affine pencil. -/

@[expose] public section

noncomputable section
open Matrix Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives

variable {n : Type*} [Fintype n] [DecidableEq n]

private def spectralMap {K : Matrix n n ℂ} (hK : K.IsHermitian) :
    (n → ℝ) →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => Unitary.conjStarAlgAut ℝ _ hK.eigenvectorUnitary
        (Matrix.diagonal (fun i => (v i : ℂ)))
      map_add' := by
        intro v w
        simp only [Pi.add_apply, Complex.ofReal_add, ← Matrix.diagonal_add, map_add]
      map_smul' := by
        intro r v
        change _ = r • _
        simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, ← Complex.real_smul]
        change (Unitary.conjStarAlgAut ℝ _ hK.eigenvectorUnitary)
          (Matrix.diagonal (r • (fun i => (v i : ℂ)))) = _
        rw [Matrix.diagonal_smul, map_smul] }

private theorem spectralMap_cfc {K : Matrix n n ℂ} (hK : K.IsHermitian) (f : ℝ → ℝ) :
    spectralMap hK (fun i => f (hK.eigenvalues i)) = cfc f K := by
  rw [hK.cfc_eq]
  rfl

/-- Differentiation of a fixed Hermitian functional calculus reduces to its finite spectrum. -/
theorem hasDerivAt_cfc {K : Matrix n n ℂ} (hK : K.IsHermitian)
    (f : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (t : ℝ)
    (h : ∀ i, HasDerivAt (fun s => f s (hK.eigenvalues i)) (g (hK.eigenvalues i)) t) :
    HasDerivAt (fun s => cfc (f s) K) (cfc g K) t := by
  have hd := (spectralMap hK).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_pi.mpr h)
  simpa only [Function.comp_def, spectralMap_cfc] using hd

private theorem affine_cfc {K : Matrix n n ℂ} (hK : K.IsHermitian) (t : ℝ) :
    cfc (fun x : ℝ => 1 + t*x) K = 1 + t • K := by
  rw [cfc_const_add _ _ _ (by fun_prop) hK.isSelfAdjoint,
    cfc_const_mul_id t K hK.isSelfAdjoint, map_one]

private theorem affine_positive_near_zero {K : Matrix n n ℂ} (hK : K.IsHermitian) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ x ∈ spectrum ℝ K, 0 < 1+t*x := by
  have hi : ∀ i : n, ∀ᶠ t : ℝ in 𝓝 0, 0 < 1+t*hK.eigenvalues i := by
    intro i
    exact (show ContinuousAt (fun t : ℝ => 1+t*hK.eigenvalues i) 0 by fun_prop).eventually
      (eventually_gt_nhds (by norm_num))
  filter_upwards [Filter.eventually_all.mpr hi] with t ht x hx
  obtain ⟨i, rfl⟩ := hK.spectrum_real_eq_range_eigenvalues ▸ hx
  exact ht i

private theorem affine_rpow_cfc {K : Matrix n n ℂ} (hK : K.IsHermitian) (p t : ℝ)
    (ht : ∀ x ∈ spectrum ℝ K, 0 < 1+t*x) :
    CFC.rpow (1+t • K) p = cfc (fun x : ℝ => (1+t*x)^p) K := by
  rw [← affine_cfc hK t]
  exact CFC.cfc_rpow ht (by fun_prop) hK.isSelfAdjoint

/-- The CFC power of an affine Hermitian pencil has the ordinary scalar-power derivative.
The positivity hypothesis is only on the fixed spectrum of `K`. -/
theorem hasDerivAt_affine_rpow {K : Matrix n n ℂ} (hK : K.IsHermitian) (p t : ℝ)
    (ht : ∀ x ∈ spectrum ℝ K, 0 < 1+t*x) :
    HasDerivAt (fun s : ℝ => CFC.rpow (1+s • K) p)
      (p • (K * CFC.rpow (1+t • K) (p-1))) t := by
  have hn : ∀ᶠ s : ℝ in 𝓝 t, ∀ x ∈ spectrum ℝ K, 0 < 1+s*x := by
    have hi : ∀ i : n, ∀ᶠ s : ℝ in 𝓝 t, 0 < 1+s*hK.eigenvalues i := by
      intro i
      exact (show ContinuousAt (fun s : ℝ => 1+s*hK.eigenvalues i) t by fun_prop).eventually
        (eventually_gt_nhds (ht _ (hK.eigenvalues_mem_spectrum_real i)))
    filter_upwards [Filter.eventually_all.mpr hi] with s hs x hx
    obtain ⟨i, rfl⟩ := hK.spectrum_real_eq_range_eigenvalues ▸ hx
    exact hs i
  have hd := hasDerivAt_cfc hK (fun s x => (1+s*x)^p)
    (fun x => p*x*(1+t*x)^(p-1)) t (fun i => by
      have ha : HasDerivAt (fun s : ℝ => 1+s*hK.eigenvalues i) (hK.eigenvalues i) t := by
        convert! (hasDerivAt_const t 1).add
          ((hasDerivAt_id t).mul_const (hK.eigenvalues i)) using 1 <;> simp
      convert ha.rpow_const
        (Or.inl (ne_of_gt (ht _ (hK.eigenvalues_mem_spectrum_real i)))) using 1 <;>
        ring)
  have he : (fun s : ℝ => CFC.rpow (1+s • K) p) =ᶠ[𝓝 t]
      (fun s => cfc (fun x : ℝ => (1+s*x)^p) K) :=
    hn.mono fun s hs => affine_rpow_cfc hK p s hs
  have hv : cfc (fun x : ℝ => p*x*(1+t*x)^(p-1)) K =
      p • (K * CFC.rpow (1+t • K) (p-1)) := by
    have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ K) := by
      rw [continuousOn_iff_continuous_domRestrict]
      fun_prop
    calc
      _ = cfc (fun x : ℝ => p * (x * (1+t*x)^(p-1))) K := by
        congr 1
        funext x
        ring
      _ = p • (cfc (fun x : ℝ => x) K *
          cfc (fun x : ℝ => (1+t*x)^(p-1)) K) := by
        rw [cfc_const_mul _ _ _ (hc _), cfc_mul _ _ _ (hc _) (hc _)]
      _ = _ := by
        rw [cfc_id' ℝ K hK.isSelfAdjoint, affine_rpow_cfc hK (p-1) t ht]
  rw [hv] at hd
  exact hd.congr_of_eventuallyEq he

private theorem trace_sandwich_cube (S A : Matrix n n ℂ) :
    Matrix.trace ((S*A*S)^3) = Matrix.trace ((A*(S*S))^3) := by
  have he : (S*A*S)^3 = S * (A*(S*S)*A*(S*S)*A) * S := by noncomm_ring
  rw [he, Matrix.mul_assoc, Matrix.trace_mul_comm]
  congr 1 <;> simp [pow_succ, Matrix.mul_assoc]

/-- The original sandwich cubic trace agrees locally with the reduced inverse two-thirds trace.
This is an identity-denominator statement and makes no congruence claim for a general denominator. -/
theorem sandwich_trace_germ (X H K : Matrix n n ℂ) (hK : K.IsHermitian) :
    (fun t : ℝ => (Matrix.trace
      ((CFC.rpow (1+t • K) (-(1 : ℝ)/3) * (X+t • H) *
        CFC.rpow (1+t • K) (-(1 : ℝ)/3))^3)).re) =ᶠ[𝓝 0]
    (fun t : ℝ => (Matrix.trace
      (((X+t • H)*CFC.rpow (1+t • K) (-(2 : ℝ)/3))^3)).re) := by
  filter_upwards [affine_positive_near_zero hK] with t ht
  have hs : CFC.rpow (1+t • K) (-(1 : ℝ)/3) *
      CFC.rpow (1+t • K) (-(1 : ℝ)/3) =
      CFC.rpow (1+t • K) (-(2 : ℝ)/3) := by
    rw [affine_rpow_cfc hK _ t ht, affine_rpow_cfc hK _ t ht]
    have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ K) := by
      rw [continuousOn_iff_continuous_domRestrict]
      fun_prop
    rw [← cfc_mul _ _ _ (hc _) (hc _)]
    · apply cfc_congr
      intro x hx
      dsimp only
      rw [← Real.rpow_add (ht x hx)]
      congr 1
      norm_num
  rw [trace_sandwich_cube, hs]

private def traceRealMap : Matrix n n ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℝ ℂ))

private theorem hasDerivAt_traceReal {f : ℝ → Matrix n n ℂ} {f' : Matrix n n ℂ}
    {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => (Matrix.trace (f s)).re) (Matrix.trace f').re t := by
  convert! traceRealMap.hasFDerivAt.comp_hasDerivAt t hf using 1

/-- Actual second and third derivatives of a cubic trace from nearby matrix derivatives. -/
theorem cubic_trace_derivatives (B B1 B2 B3 : ℝ → Matrix n n ℂ)
    (h0 : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt B (B1 t) t)
    (h1 : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt B1 (B2 t) t)
    (h2 : HasDerivAt B2 (B3 0) 0) :
    iteratedDeriv 2 (fun t => (Matrix.trace ((B t)^3)).re) 0 =
      (Matrix.trace ((3 : ℝ) • (B2 0 * B 0 * B 0) +
        (6 : ℝ) • (B1 0 * B1 0 * B 0))).re ∧
    iteratedDeriv 3 (fun t => (Matrix.trace ((B t)^3)).re) 0 =
      (Matrix.trace ((3 : ℝ) • (B3 0 * B 0 * B 0) +
        (9 : ℝ) • (B2 0 * B1 0 * B 0) + (9 : ℝ) • (B2 0 * B 0 * B1 0) +
        (6 : ℝ) • (B1 0 * B1 0 * B1 0))).re := by
  let f0 := fun t => (Matrix.trace ((B t)^3)).re
  let f1 := fun t => (Matrix.trace ((3 : ℝ) • (B1 t * B t * B t))).re
  let f2 := fun t => (Matrix.trace ((3 : ℝ) • (B2 t * B t * B t) +
    (6 : ℝ) • (B1 t * B1 t * B t))).re
  let f3 := fun t => (Matrix.trace ((3 : ℝ) • (B3 t * B t * B t) +
    (9 : ℝ) • (B2 t * B1 t * B t) + (9 : ℝ) • (B2 t * B t * B1 t) +
    (6 : ℝ) • (B1 t * B1 t * B1 t))).re
  have hd0 (t : ℝ) (ht : HasDerivAt B (B1 t) t) : HasDerivAt f0 (f1 t) t := by
    have hd := hasDerivAt_traceReal (((ht.mul ht).mul ht))
    convert hd using 1
    · funext s
      simp [f0, pow_succ, Matrix.mul_assoc]
    · dsimp [f1]
      simp only [Pi.mul_apply, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add,
        Matrix.trace_smul, Complex.add_re, Complex.real_smul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [Matrix.trace_mul_cycle (B t) (B1 t) (B t),
        Matrix.trace_mul_cycle (B t) (B t) (B1 t)]
      ring
  have hd1 (t : ℝ) (ht : HasDerivAt B (B1 t) t)
      (ht1 : HasDerivAt B1 (B2 t) t) : HasDerivAt f1 (f2 t) t := by
    have hd := hasDerivAt_traceReal (((ht1.mul ht).mul ht).const_smul (3 : ℝ))
    convert hd using 1
    dsimp [f2]
    simp only [Pi.mul_apply, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add,
      Matrix.trace_smul, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [Matrix.trace_mul_cycle (B1 t) (B t) (B1 t)]
    ring
  have hd2 : HasDerivAt f2 (f3 0) 0 := by
    have ht := h0.self_of_nhds
    have ht1 := h1.self_of_nhds
    have hd := hasDerivAt_traceReal
      ((((h2.mul ht).mul ht).const_smul (3 : ℝ)).add
        (((ht1.mul ht1).mul ht).const_smul (6 : ℝ)))
    convert hd using 1
    dsimp [f3]
    simp only [Pi.mul_apply, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add,
      Matrix.trace_smul, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [Matrix.trace_mul_cycle (B1 0) (B2 0) (B 0),
      Matrix.trace_mul_cycle (B 0) (B1 0) (B2 0)]
    ring
  have he1 : deriv f0 =ᶠ[𝓝 (0 : ℝ)] f1 := h0.mono fun t ht => (hd0 t ht).deriv
  have he2 : deriv (deriv f0) =ᶠ[𝓝 (0 : ℝ)] f2 :=
    he1.deriv.trans ((h0.and h1).mono fun t ht => (hd1 t ht.1 ht.2).deriv)
  constructor
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using he2.eq_of_nhds
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using he2.deriv_eq.trans hd2.deriv

/-- The actual reduced cubic trace derivatives for any real exponent of the affine pencil. -/
theorem affine_power_cubic_derivatives (X H K : Matrix n n ℂ) (hK : K.IsHermitian)
    (p : ℝ) :
    let L := H + p • (X*K)
    let M := (2*p) • (H*K) + (p*(p-1)) • (X*K^2)
    let N := (3*p*(p-1)) • (H*K^2) + (p*(p-1)*(p-2)) • (X*K^3)
    iteratedDeriv 2 (fun t : ℝ =>
      (Matrix.trace (((X+t • H)*CFC.rpow (1+t • K) p)^3)).re) 0 =
      (Matrix.trace ((3 : ℝ) • (M*X*X) + (6 : ℝ) • (L*L*X))).re ∧
    iteratedDeriv 3 (fun t : ℝ =>
      (Matrix.trace (((X+t • H)*CFC.rpow (1+t • K) p)^3)).re) 0 =
      (Matrix.trace ((3 : ℝ) • (N*X*X) + (9 : ℝ) • (M*L*X) +
        (9 : ℝ) • (M*X*L) + (6 : ℝ) • (L*L*L))).re := by
  let A := fun t : ℝ => X+t • H
  let T0 := fun t : ℝ => CFC.rpow (1+t • K) p
  let T1 := fun t : ℝ => p • (K*CFC.rpow (1+t • K) (p-1))
  let T2 := fun t : ℝ => p • (K*((p-1) • (K*CFC.rpow (1+t • K) (p-1-1))))
  let T3 := fun t : ℝ => p • (K*((p-1) •
    (K*((p-1-1) • (K*CFC.rpow (1+t • K) (p-1-1-1))))))
  let B := fun t => A t*T0 t
  let B1 := fun t => H*T0 t+A t*T1 t
  let B2 := fun t => H*T1 t+(H*T1 t+A t*T2 t)
  let B3 := fun t => H*T2 t+(H*T2 t+(H*T2 t+A t*T3 t))
  have hA (t : ℝ) : HasDerivAt A H t := by
    convert! (hasDerivAt_const t X).add ((hasDerivAt_id t).smul_const H) using 1
    simp
  have hT0 (t : ℝ) (ht : ∀ x ∈ spectrum ℝ K, 0 < 1+t*x) :
      HasDerivAt T0 (T1 t) t := hasDerivAt_affine_rpow hK p t ht
  have hT1 (t : ℝ) (ht : ∀ x ∈ spectrum ℝ K, 0 < 1+t*x) :
      HasDerivAt T1 (T2 t) t :=
    ((hasDerivAt_affine_rpow hK (p-1) t ht).const_mul K).const_smul p
  have hT2 (t : ℝ) (ht : ∀ x ∈ spectrum ℝ K, 0 < 1+t*x) :
      HasDerivAt T2 (T3 t) t :=
    ((((hasDerivAt_affine_rpow hK (p-1-1) t ht).const_mul K).const_smul
      (p-1)).const_mul K).const_smul p
  have hB (t : ℝ) (ht : ∀ x ∈ spectrum ℝ K, 0 < 1+t*x) :
      HasDerivAt B (B1 t) t := (hA t).mul (hT0 t ht)
  have hB1 (t : ℝ) (ht : ∀ x ∈ spectrum ℝ K, 0 < 1+t*x) :
      HasDerivAt B1 (B2 t) t :=
    ((hT0 t ht).const_mul H).add ((hA t).mul (hT1 t ht))
  have hB2 (t : ℝ) (ht : ∀ x ∈ spectrum ℝ K, 0 < 1+t*x) :
      HasDerivAt B2 (B3 t) t :=
    ((hT1 t ht).const_mul H).add
      (((hT1 t ht).const_mul H).add ((hA t).mul (hT2 t ht)))
  have hn := affine_positive_near_zero hK
  have hj := cubic_trace_derivatives B B1 B2 B3
    (hn.mono fun t ht => hB t ht) (hn.mono fun t ht => hB1 t ht)
    (hB2 0 (by intros; norm_num))
  have e0 : B 0 = X := by simp [B, A, T0]
  have e1 : B1 0 = H+p • (X*K) := by
    simp [B1, A, T0, T1]
  have e2 : B2 0 = (2*p) • (H*K)+(p*(p-1)) • (X*K^2) := by
    simp only [B2, A, T1, T2, zero_smul, add_zero, CFC.rpow_eq_pow,
      CFC.one_rpow, mul_one, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      pow_succ, pow_zero, one_mul, Matrix.mul_assoc]
    module
  have e3 : B3 0 = (3*p*(p-1)) • (H*K^2)+(p*(p-1)*(p-2)) • (X*K^3) := by
    simp only [B3, A, T2, T3, zero_smul, add_zero, CFC.rpow_eq_pow,
      CFC.one_rpow, mul_one, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      pow_succ, pow_zero, one_mul, Matrix.mul_assoc]
    module
  simpa only [B, A, T0, e0, e1, e2, e3] using hj

/-- The original CFC sandwich trace has exactly the original ordered-word coefficients.
The statement holds in arbitrary finite dimension and requires only Hermitian `K`. -/
theorem identity_cubic_trace_derivatives (X H K : Matrix n n ℂ) (hK : K.IsHermitian) :
    let phi := fun t : ℝ => (Matrix.trace
      ((CFC.rpow (1+t • K) (-(1 : ℝ)/3) * (X+t • H) *
        CFC.rpow (1+t • K) (-(1 : ℝ)/3))^3)).re
    iteratedDeriv 2 phi 0 = 2*HsfQubitMixedCubic.coefficient2 X H K ∧
    iteratedDeriv 3 phi 0 = 6*HsfQubitMixedCubic.coefficient3 X H K := by
  dsimp only
  have hg := sandwich_trace_germ X H K hK
  have hc := affine_power_cubic_derivatives X H K hK (-(2 : ℝ)/3)
  norm_num at hc
  constructor
  · rw [hg.iteratedDeriv_eq 2]
    simp only [CFC.rpow_eq_pow, neg_div]
    rw [hc.1]
    simpa [HsfQubitMixedCubic.coefficient2, sub_eq_add_neg, neg_smul] using
      congrArg Complex.re (HsfQubitMixedCubic.trace_jet_coefficient2 X H K)
  · rw [hg.iteratedDeriv_eq 3]
    simp only [CFC.rpow_eq_pow, neg_div]
    rw [hc.2]
    simpa [HsfQubitMixedCubic.coefficient3, sub_eq_add_neg, neg_smul] using
      congrArg Complex.re (HsfQubitMixedCubic.trace_jet_coefficient3 X H K)

/-- The actual identity-denominator qubit cubic trace satisfies the HSF constant-five estimate.
The four PSD endpoints may be singular; the two eigenvalues of `X` are strictly positive. -/
theorem qubit_cubic_compatibility (a b : ℝ) (H K : HsfQubitCoupledCubic.Mat)
    (ha : 0 < a) (hb : 0 < b) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hp : (HsfQubitCoupledCubic.hermitian a b 0+H).PosSemidef)
    (hn : (HsfQubitCoupledCubic.hermitian a b 0-H).PosSemidef)
    (kp : (1+K).PosSemidef) (kn : (1-K).PosSemidef) :
    let X := HsfQubitCoupledCubic.hermitian a b 0
    let phi := fun t : ℝ => (Matrix.trace
      ((CFC.rpow (1+t • K) (-(1 : ℝ)/3) * (X+t • H) *
        CFC.rpow (1+t • K) (-(1 : ℝ)/3))^3)).re
    0 ≤ iteratedDeriv 2 phi 0 ∧
      |iteratedDeriv 3 phi 0| ≤ 5*iteratedDeriv 2 phi 0 := by
  dsimp only
  obtain ⟨hd2, hd3⟩ :=
    identity_cubic_trace_derivatives (HsfQubitCoupledCubic.hermitian a b 0) H K hK
  obtain ⟨h2, h3⟩ := HsfQubitMixedCubic.coefficient_compatibility a b H K
    ha hb hH hK hp hn kp kn
  rw [hd2, hd3, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  constructor <;> linarith

/-- The identity-denominator cubic compatibility estimate for every positive definite qubit `X`.
Unitary diagonalization transports the original ordered coefficients, leaving the CFC function
in the statement unchanged. The four PSD endpoints may be singular. -/
theorem qubit_posdef_cubic_compatibility (X H K : HsfQubitCoupledCubic.Mat)
    (hX : X.PosDef) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hp : (X+H).PosSemidef) (hn : (X-H).PosSemidef)
    (kp : (1+K).PosSemidef) (kn : (1-K).PosSemidef) :
    let phi := fun t : ℝ => (Matrix.trace
      ((CFC.rpow (1+t • K) (-(1 : ℝ)/3) * (X+t • H) *
        CFC.rpow (1+t • K) (-(1 : ℝ)/3))^3)).re
    0 ≤ iteratedDeriv 2 phi 0 ∧
      |iteratedDeriv 3 phi 0| ≤ 5*iteratedDeriv 2 phi 0 := by
  dsimp only
  let U := hX.isHermitian.eigenvectorUnitary
  let e := Unitary.conjStarAlgAut ℂ HsfQubitCoupledCubic.Mat (star U)
  let a := hX.isHermitian.eigenvalues 0
  let b := hX.isHermitian.eigenvalues 1
  have heX : e X = HsfQubitCoupledCubic.hermitian a b 0 := by
    change Unitary.conjStarAlgAut ℂ _ (star hX.isHermitian.eigenvectorUnitary) X = _
    rw [hX.isHermitian.conjStarAlgAut_star_eigenvectorUnitary]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HsfQubitCoupledCubic.hermitian, a, b, Function.comp_def]
  have hepsd (M : HsfQubitCoupledCubic.Mat) (hM : M.PosSemidef) :
      (e M).PosSemidef := by
    simpa only [e, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] using
      hM.conjTranspose_mul_mul_same (U : HsfQubitCoupledCubic.Mat)
  have heH : (e H).IsHermitian := by
    simpa only [e, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] using
      Matrix.isHermitian_conjTranspose_mul_mul (U : HsfQubitCoupledCubic.Mat) hH
  have heK : (e K).IsHermitian := by
    simpa only [e, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] using
      Matrix.isHermitian_conjTranspose_mul_mul (U : HsfQubitCoupledCubic.Mat) hK
  have hetrace (M : HsfQubitCoupledCubic.Mat) : Matrix.trace (e M) = Matrix.trace M := by
    change Matrix.trace (Unitary.conjStarAlgAut ℂ _ (star U) M) = _
    rw [Unitary.conjStarAlgAut_star_apply, Matrix.trace_mul_cycle,
      ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_mul]
  have hcoeff2 (A B C : HsfQubitCoupledCubic.Mat) :
      HsfQubitMixedCubic.coefficient2 (e A) (e B) (e C) =
        HsfQubitMixedCubic.coefficient2 A B C := by
    simp only [HsfQubitMixedCubic.coefficient2, HsfQubitMixedCubic.traceCoefficient2,
      ← map_mul, hetrace]
  have hcoeff3 (A B C : HsfQubitCoupledCubic.Mat) :
      HsfQubitMixedCubic.coefficient3 (e A) (e B) (e C) =
        HsfQubitMixedCubic.coefficient3 A B C := by
    simp only [HsfQubitMixedCubic.coefficient3, HsfQubitMixedCubic.traceCoefficient3,
      ← map_mul, hetrace]
  have hp' : (HsfQubitCoupledCubic.hermitian a b 0+e H).PosSemidef := by
    simpa only [map_add, heX] using hepsd (X+H) hp
  have hn' : (HsfQubitCoupledCubic.hermitian a b 0-e H).PosSemidef := by
    simpa only [map_sub, heX] using hepsd (X-H) hn
  have kp' : (1+e K).PosSemidef := by
    simpa only [map_add, map_one] using hepsd (1+K) kp
  have kn' : (1-e K).PosSemidef := by
    simpa only [map_sub, map_one] using hepsd (1-K) kn
  have hcompat := qubit_cubic_compatibility a b (e H) (e K)
    (hX.eigenvalues_pos 0) (hX.eigenvalues_pos 1) heH heK hp' hn' kp' kn'
  obtain ⟨he2, he3⟩ := identity_cubic_trace_derivatives
    (HsfQubitCoupledCubic.hermitian a b 0) (e H) (e K) heK
  dsimp only at hcompat
  rw [he2, he3, ← heX, hcoeff2, hcoeff3] at hcompat
  obtain ⟨hd2, hd3⟩ := identity_cubic_trace_derivatives X H K hK
  simpa only [hd2, hd3] using hcompat

end D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives
