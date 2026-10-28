/- GID: D5/S3/Quantum/Matrix/HsfIdentityCubicDerivatives
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfIdentityCubicDerivatives
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.HermitianFunctionalCalculus]
   utility: none
   digest: Actual derivatives of affine Hermitian matrix powers at the identity. -/

module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Tactic

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

/-- The second and third actual derivatives of an affine Hermitian power at the identity.
There is no commutation condition on any other matrix and no Taylor assumption. -/
theorem affine_rpow_derivatives {K : Matrix n n ℂ} (hK : K.IsHermitian) (p : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => CFC.rpow (1+t • K) p) 0 =
      (p*(p-1)) • K^2 ∧
    iteratedDeriv 3 (fun t : ℝ => CFC.rpow (1+t • K) p) 0 =
      (p*(p-1)*(p-2)) • K^3 := by
  let f0 := fun t : ℝ => CFC.rpow (1+t • K) p
  let f1 := fun t : ℝ => p • (K * CFC.rpow (1+t • K) (p-1))
  let f2 := fun t : ℝ => p • (K * ((p-1) •
    (K * CFC.rpow (1+t • K) ((p-1)-1))))
  let f3 := fun t : ℝ => p • (K * ((p-1) • (K * (((p-1)-1) •
    (K * CFC.rpow (1+t • K) (((p-1)-1)-1))))))
  have hd0 (t : ℝ) (ht : ∀ x ∈ spectrum ℝ K, 0 < 1+t*x) :
      HasDerivAt f0 (f1 t) t := hasDerivAt_affine_rpow hK p t ht
  have hd1 (t : ℝ) (ht : ∀ x ∈ spectrum ℝ K, 0 < 1+t*x) :
      HasDerivAt f1 (f2 t) t :=
    ((hasDerivAt_affine_rpow hK (p-1) t ht).const_mul K).const_smul p
  have hd2 (t : ℝ) (ht : ∀ x ∈ spectrum ℝ K, 0 < 1+t*x) :
      HasDerivAt f2 (f3 t) t :=
    (((((hasDerivAt_affine_rpow hK ((p-1)-1) t ht).const_mul K).const_smul
      (p-1)).const_mul K).const_smul p)
  have hn := affine_positive_near_zero hK
  have he1 : deriv f0 =ᶠ[𝓝 (0 : ℝ)] f1 := hn.mono fun t ht => (hd0 t ht).deriv
  have he2 : deriv (deriv f0) =ᶠ[𝓝 (0 : ℝ)] f2 :=
    he1.deriv.trans (hn.mono fun t ht => (hd1 t ht).deriv)
  have e2 : iteratedDeriv 2 f0 0 = f2 0 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using he2.eq_of_nhds
  have e3 : iteratedDeriv 3 f0 0 = f3 0 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      he2.deriv_eq.trans (hd2 0 (by intros; norm_num)).deriv
  constructor
  · rw [e2]
    simp [f2, Matrix.mul_smul, smul_smul, pow_two]
  · rw [e3]
    simp only [f3, zero_smul, add_zero, CFC.rpow_eq_pow, CFC.one_rpow, mul_one,
      Matrix.mul_smul, smul_smul]
    rw [show p-1-1 = p-2 by ring]
    simp only [pow_succ, pow_zero, one_mul, Matrix.mul_assoc]
    module

/-- The inverse two-thirds power supplies the exact coefficients needed by the cubic trace. -/
theorem inverse_two_thirds_derivatives {K : Matrix n n ℂ} (hK : K.IsHermitian) :
    iteratedDeriv 2 (fun t : ℝ => CFC.rpow (1+t • K) (-(2 : ℝ)/3)) 0 =
      (10/9 : ℝ) • K^2 ∧
    iteratedDeriv 3 (fun t : ℝ => CFC.rpow (1+t • K) (-(2 : ℝ)/3)) 0 =
      (-(80 : ℝ)/27) • K^3 := by
  have h := affine_rpow_derivatives hK (-(2 : ℝ)/3)
  norm_num at h ⊢
  exact h

end D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives
