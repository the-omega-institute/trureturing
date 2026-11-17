/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/BalancedHalfCap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Half-identity bound for every completed skew marginal and every density input with odd Fock environment at balance. -/
/-
admission_basis: escape-witness
The contraction-wedge estimate in antisymmetric_partial_trace_quadratic_le
is the substantive estimate; antisymmetric_partial_trace_le is its actual
Loewner-order form. balanced_odd_attenuator_le_half transports it through
the owner's norm-summable square-root ensemble for every density input.
The completed swap, kernel parity and scalar half-membership are consumed
helpers. utility: none denotes an analytic all-input theorem, with no
bounded enumeration, checker, numerical reduction or certified-instance
result. The odd-occupation bound asserts no attainment when n > 1.
The balanced one-photon all-density spectral minimum and every-coherent
attainment are attributed to Zixuan He, The energy cost of optical noise,
v1.0, DOI 10.5281/zenodo.23629201, Theorem 2 and Appendix A.2-A.3.
This is formal library integration of that written result; no literature
resolution or priority for the odd-occupation application is claimed.
-/

import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteRankClassification
import D5.S3.Quantum.QuantumChannels.FockAttenuator.CompletedKernel

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal ComplexOrder
open Filter Topology
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.BalancedHalfCap
open Bargmann BeamSplitter Attenuator DisplacementCovariance

private theorem lp_square_sum {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
    (x : lp E 2) : HasSum (fun j => ‖x j‖ ^ 2) (‖x‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x)

private theorem coordinate_square_sum (V : TwoMode) :
    Summable (fun q : ℕ × ℕ => ‖V q.1 q.2‖ ^ 2) := by
  rw [summable_prod_of_nonneg (fun q => sq_nonneg _)]
  refine ⟨fun j => (lp_square_sum (V j)).summable, ?_⟩
  simpa only [(lp_square_sum _).tsum_eq] using (lp_square_sum V).summable

private def swapColumn (V : TwoMode) (i : ℕ) : Fock :=
  ⟨fun j => V j i, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      ((summable_prod_of_nonneg (fun q : ℕ × ℕ => sq_nonneg (‖V q.2 q.1‖))).mp
        (coordinate_square_sum V).prod_symm).1 i⟩

private def swapVec (V : TwoMode) : TwoMode :=
  ⟨swapColumn V, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, ← (lp_square_sum (swapColumn V _)).tsum_eq]
    exact ((summable_prod_of_nonneg (fun q : ℕ × ℕ => sq_nonneg (‖V q.2 q.1‖))).mp
      (coordinate_square_sum V).prod_symm).2⟩

private def swapIso : TwoMode →ₗᵢ[ℂ] TwoMode where
  toFun := swapVec
  map_add' V W := by
    apply lp.ext; funext i; apply lp.ext; funext j
    rfl
  map_smul' c V := by
    apply lp.ext; funext i; apply lp.ext; funext j
    rfl
  norm_map' V := by
    apply le_antisymm <;> apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    all_goals
      have h := (coordinate_square_sum V).tsum_comm'
        (fun j => (lp_square_sum (V j)).summable)
        (fun i => (lp_square_sum (swapColumn V i)).summable)
      change (∑' i, ∑' j, ‖swapColumn V i j‖ ^ 2) =
        ∑' j, ∑' i, ‖V j i‖ ^ 2 at h
      simp_rw [(lp_square_sum _).tsum_eq] at h
      change (∑' i, ‖swapVec V i‖ ^ 2) = ‖V‖ ^ 2 at h
      rw [(lp_square_sum (swapVec V)).tsum_eq] at h
    · exact h.le
    · exact h.ge

private theorem swap_tensor (u v : Fock) : swapIso (tensor u v) = tensor v u := by
  apply lp.ext; funext i; apply lp.ext; funext j
  change v j * u i = u i * v j
  exact mul_comm _ _

private theorem kernel_swap (V : TwoMode) (z w : ℂ) :
    kernel (swapIso V) z w = kernel V w z := by
  rw [kernel_eq_inner, kernel_eq_inner]
  let e := exponentialPair ((starRingEnd ℂ) w, (starRingEnd ℂ) z)
  have he : swapIso e = exponentialPair ((starRingEnd ℂ) z, (starRingEnd ℂ) w) :=
    swap_tensor _ _
  rw [← he, swapIso.inner_map_map]

private theorem kernel_neg (V : TwoMode) (z w : ℂ) : kernel (-V) z w = -kernel V z w := by
  rw [kernel_eq_inner, kernel_eq_inner, inner_neg_right]

theorem balanced : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num

/-- Balanced output with any odd environment occupation has skew occupation coefficients. -/
theorem balanced_odd_skew (x : Fock) (n : ℕ) (hn : Odd n) (i j : ℕ) :
    let V := beamSplitter (1/2) balanced (tensor x (lp.single 2 n (1 : ℂ)))
    V i j = -V j i := by
  dsimp only
  let V := beamSplitter (1/2) balanced (tensor x (lp.single 2 n (1 : ℂ)))
  have hV : swapIso V = -V := by
    apply kernel_injective
    funext z w
    rw [kernel_swap, kernel_neg]
    have hk (z w : ℂ) :
        kernel V z w = transform x ((Real.sqrt (1/2 : ℝ) : ℂ) * (z+w)) *
          (((Real.sqrt (1/2 : ℝ) : ℂ) * (w-z)) ^ n /
            (Real.sqrt (n.factorial : ℝ) : ℂ)) := by
      dsimp only [V]
      rw [beamSplitter, kernel_beam_unitary, kernel_tensor, transform_single]
      rw [show (1 - 1/2 : ℝ) = 1/2 by norm_num]
      congr 1 <;> try ring
    rw [hk, hk, add_comm w z, show z - w = -(w - z) by ring,
      mul_neg, hn.neg_pow, neg_div, mul_neg]
  have h := congrArg (fun W : TwoMode => W j i) hV
  exact h

private theorem tensor_inner_tensor (u v x y : Fock) :
    ⟪tensor u v, tensor x y⟫_ℂ = ⟪v, y⟫_ℂ * ⟪u, x⟫_ℂ := by
  apply (lp.hasSum_inner (tensor u v) (tensor x y)).unique
  apply ((lp.hasSum_inner v y).mul_right ⟪u, x⟫_ℂ).congr_fun
  intro j
  change ⟪v j • u, y j • x⟫_ℂ = ⟪v j, y j⟫_ℂ * ⟪u, x⟫_ℂ
  rw [inner_smul_left, inner_smul_right, RCLike.inner_apply]
  ring

private def contraction (V : TwoMode) (u : Fock) : Fock :=
  ⟨fun j => ⟪u, V j⟫_ℂ, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) ?_
      ((lp_square_sum V).summable.mul_left (‖u‖ ^ 2))
    intro j
    rw [← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_inner_le_norm _ _)⟩

private theorem tensor_inner_contraction (V : TwoMode) (u a : Fock) :
    ⟪tensor u a, V⟫_ℂ = ⟪a, contraction V u⟫_ℂ := by
  apply (lp.hasSum_inner (tensor u a) V).unique
  apply (lp.hasSum_inner a (contraction V u)).congr_fun
  intro j
  change ⟪a j • u, V j⟫_ℂ = ⟪a j, ⟪u, V j⟫_ℂ⟫_ℂ
  rw [inner_smul_left, RCLike.inner_apply, mul_comm]

private theorem tensor_norm_sq (u v : Fock) :
    ‖tensor u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := lp_square_sum (tensor u v)
  have hv := (lp_square_sum v).mul_right (‖u‖ ^ 2)
  rw [mul_comm]
  apply h.unique
  apply hv.congr_fun
  intro j
  change ‖v j • u‖ ^ 2 = _
  rw [norm_smul, mul_pow]

private theorem partial_trace_quadratic (V : TwoMode) (u : Fock) :
    (⟪u, purePartialTrace V u⟫_ℂ).re = ‖contraction V u‖ ^ 2 := by
  rw [pure_partial_trace_eq]
  change (⟪u, coefficientOperator V (ContinuousLinearMap.adjoint (coefficientOperator V) u)⟫_ℂ).re = _
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change RCLike.re (inner ℂ _ _) = _
  rw [inner_self_eq_norm_sq]
  rw [← (lp_square_sum _).tsum_eq, ← (lp_square_sum (contraction V u)).tsum_eq]
  apply tsum_congr
  intro j
  rw [adjoint_coefficient, ← inner_conj_symm]
  simp only [contraction, Complex.norm_conj]

private theorem wedge_norm_sq_le (u a : Fock) :
    ‖tensor u a - tensor a u‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 * ‖a‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), tensor_norm_sq, tensor_norm_sq, tensor_inner_tensor]
  have h : 0 ≤ (⟪a, u⟫_ℂ * ⟪u, a⟫_ℂ).re := by
    rw [← inner_conj_symm a u, mul_comm, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  change 0 ≤ RCLike.re (⟪a, u⟫_ℂ * ⟪u, a⟫_ℂ) at h
  linarith [mul_comm (‖a‖ ^ 2) (‖u‖ ^ 2)]

/-- The quadratic form of the actual completed marginal satisfies the half bound. -/
theorem antisymmetric_partial_trace_quadratic_le (V : TwoMode)
    (hskew : ∀ i j, V i j = -V j i) (u : Fock) :
    (⟪u, purePartialTrace V u⟫_ℂ).re ≤ ‖V‖ ^ 2 / 2 * ‖u‖ ^ 2 := by
  rw [partial_trace_quadratic]
  let a := contraction V u
  change ‖a‖ ^ 2 ≤ _
  by_cases ha : ‖a‖ ^ 2 = 0
  · rw [ha]; positivity
  have hs : swapIso V = -V := by
    apply lp.ext; funext i; apply lp.ext; funext j
    exact hskew j i
  have h₁ : ⟪tensor u a, V⟫_ℂ = (‖a‖ : ℂ) ^ 2 := by
    rw [tensor_inner_contraction]
    exact inner_self_eq_norm_sq_to_K _
  have h₂ : ⟪tensor a u, V⟫_ℂ = -⟪tensor u a, V⟫_ℂ := by
    rw [← swapIso.inner_map_map (tensor a u) V, swap_tensor, hs, inner_neg_right]
  have hcs := re_inner_le_norm (𝕜 := ℂ) (tensor u a - tensor a u) V
  rw [inner_sub_left, h₂, h₁] at hcs
  have hr : RCLike.re (((‖a‖ : ℂ) ^ 2) - -((‖a‖ : ℂ) ^ 2)) = 2 * ‖a‖ ^ 2 := by
    change (((‖a‖ : ℂ) ^ 2) - -((‖a‖ : ℂ) ^ 2)).re = _
    rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_sub, Complex.ofReal_re]
    ring
  rw [hr] at hcs
  have hsq : (2 * ‖a‖ ^ 2) ^ 2 ≤ (‖tensor u a - tensor a u‖ * ‖V‖) ^ 2 := (sq_le_sq₀ (show 0 ≤ 2 * ‖a‖ ^ 2 by positivity)
    (show 0 ≤ ‖tensor u a - tensor a u‖ * ‖V‖ by positivity)).mpr hcs
  have hsq' : (2 * ‖a‖ ^ 2) ^ 2 ≤ ‖tensor u a - tensor a u‖ ^ 2 * ‖V‖ ^ 2 :=
    hsq.trans_eq (mul_pow _ _ _)
  have hb := hsq'.trans (mul_le_mul_of_nonneg_right (wedge_norm_sq_le u a) (sq_nonneg ‖V‖))
  have hm : ‖a‖ ^ 2 * ‖a‖ ^ 2 ≤ (‖V‖ ^ 2 / 2 * ‖u‖ ^ 2) * ‖a‖ ^ 2 := by
    linarith only [hb]
  exact le_of_mul_le_mul_right hm (lt_of_le_of_ne (sq_nonneg _) (Ne.symm ha))

private theorem le_smul_id_of_quadratic (T : Fock →L[ℂ] Fock) (hT : T.IsPositive)
    (c : ℝ) (hc : ∀ u : Fock, (⟪u, T u⟫_ℂ).re ≤ c * ‖u‖ ^ 2) :
    T ≤ (c : ℂ) • (1 : Fock →L[ℂ] Fock) := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff']
  have hs : IsSelfAdjoint ((c : ℂ) • (1 : Fock →L[ℂ] Fock)) :=
    IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) (by simp)
  refine ⟨hs.sub hT.isSelfAdjoint, fun u => ?_⟩
  rw [sub_apply, smul_apply,
    one_apply_eq_self, inner_sub_left, inner_smul_left,
    Complex.conj_ofReal, inner_self_eq_norm_sq_to_K]
  have he : ⟪T u, u⟫_ℂ = ⟪u, T u⟫_ℂ := hT.isSelfAdjoint.isSymmetric u u
  have h0 := Complex.nonneg_iff.mp (hT.inner_nonneg_right u)
  rw [he]
  change 0 ≤ (c : ℂ) * ((‖u‖ : ℝ) : ℂ) ^ 2 - ⟪u, T u⟫_ℂ
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.nonneg_iff,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨sub_nonneg.mpr (hc u), (sub_eq_zero.mpr h0.2).symm⟩

/-- Loewner order on the actual partial trace, for arbitrary completed skew output. -/
theorem antisymmetric_partial_trace_le (V : TwoMode)
    (hskew : ∀ i j, V i j = -V j i) :
    purePartialTrace V ≤ ((‖V‖ ^ 2 / 2 : ℝ) : ℂ) • (1 : Fock →L[ℂ] Fock) := by
  apply le_smul_id_of_quadratic
  · rw [pure_partial_trace_eq]
    exact ContinuousLinearMap.nonneg_iff_isPositive.mp (mul_star_self_nonneg _)
  · exact antisymmetric_partial_trace_quadratic_le V hskew

private theorem quadratic_mixture {ι : Type} (v : ι → Fock)
    (hv : Summable (fun j => ‖v j‖ ^ 2)) (u : Fock) :
    HasSum (fun j => (⟪u, InnerProductSpace.rankOne ℂ (v j) (v j) u⟫_ℂ).re)
      (⟪u, mixture v u⟫_ℂ).re := by
  have hrank : Summable (fun j => InnerProductSpace.rankOne ℂ (v j) (v j)) := by
    apply Summable.of_norm
    simpa only [InnerProductSpace.norm_rankOne, ← sq] using hv
  let φ : (Fock →L[ℂ] Fock) →L[ℝ] ℝ :=
    Complex.reCLM.comp (((innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ Fock u)).restrictScalars ℝ)
  exact hrank.hasSum.mapL φ

private def occupation (n : ℕ) : Fock := lp.single 2 n 1

private def densityRoot (ρ : DensityOperator) : Fock →L[ℂ] Fock := by
  letI : Nontrivial (lp (fun _ : ℕ => ℂ) 2) := ⟨⟨lp.single 2 0 1, 0, by
    intro h
    have hc := congrArg (fun v : lp (fun _ : ℕ => ℂ) 2 => v 0) h
    simp [lp.single_apply] at hc⟩⟩
  letI : IsometricContinuousFunctionalCalculus ℝ
      ((lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      ((lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  exact CFC.sqrt ρ.operator

private theorem densitySqrt_norm_sum (ρ : DensityOperator) :
    HasSum (fun m : ℕ => ‖densityRoot ρ (occupation m)‖ ^ 2) 1 := by
  letI : Nontrivial (lp (fun _ : ℕ => ℂ) 2) := ⟨⟨lp.single 2 0 1, 0, by
    intro h
    have hc := congrArg (fun v : lp (fun _ : ℕ => ℂ) 2 => v 0) h
    simp [lp.single_apply] at hc⟩⟩
  letI : IsometricContinuousFunctionalCalculus ℝ
      ((lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      ((lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  have hprod : CFC.sqrt ρ.operator * CFC.sqrt ρ.operator = ρ.operator :=
    CFC.sqrt_mul_sqrt_self ρ.operator
      ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr ρ.positive)
  have hsa : IsSelfAdjoint (CFC.sqrt ρ.operator) :=
    (CFC.sqrt_nonneg ρ.operator).isSelfAdjoint
  refine ρ.trace_one.congr_fun (fun m => ?_)
  let v := occupation m
  have h := hsa.isSymmetric v (CFC.sqrt ρ.operator v)
  change ⟪CFC.sqrt ρ.operator v, CFC.sqrt ρ.operator v⟫_ℂ =
    ⟪v, (CFC.sqrt ρ.operator * CFC.sqrt ρ.operator) v⟫_ℂ at h
  rw [hprod, inner_self_eq_norm_sq_to_K] at h
  have hr := congrArg Complex.re h
  norm_cast at hr

private theorem occupied_output (n : ℕ) (ρ : DensityOperator) :
    let V := fun m : ℕ => beamSplitter (1/2) balanced
      (tensor (densityRoot ρ (occupation m)) (occupation n))
    (∀ q : ℕ × ℕ × ℕ, outputVector (1/2) balanced (pointMassEnvironment n) ρ q =
      if q.1 = n then V q.2.1 q.2.2 else 0) ∧
    HasSum (fun m : ℕ => ‖V m‖ ^ 2) 1 := by
  dsimp only
  constructor
  · rintro ⟨j, m, l⟩
    by_cases hj : j = n
    · subst j
      simp [outputVector, pointMassEnvironment, occupation, densityRoot]
    · simp [outputVector, pointMassEnvironment, hj]
  · refine (densitySqrt_norm_sum ρ).congr_fun fun m => ?_
    rw [LinearIsometryEquiv.norm_map, tensor_norm_sq]
    simp [occupation, lp.norm_single]

/-- The actual attenuator satisfies the half-identity cap for every density input
at balance with any odd occupation point-mass environment. -/
theorem balanced_odd_attenuator_le_half (n : ℕ) (hn : Odd n) (ρ : DensityOperator) :
    attenuatorOperator (1/2) balanced (pointMassEnvironment n) ρ ≤
      ((1 / 2 : ℝ) : ℂ) • (1 : Fock →L[ℂ] Fock) := by
  apply le_smul_id_of_quadratic
  · exact (attenuator (1/2) balanced (pointMassEnvironment n) ρ).positive
  intro u
  let V := fun m : ℕ => beamSplitter (1/2) balanced
    (tensor (densityRoot ρ (occupation m)) (occupation n))
  let v := outputVector (1/2) balanced (pointMassEnvironment n) ρ
  obtain ⟨hv, hV⟩ := occupied_output n ρ
  change (∀ q : ℕ × ℕ × ℕ, v q = if q.1 = n then V q.2.1 q.2.2 else 0) at hv
  change HasSum (fun m : ℕ => ‖V m‖ ^ 2) 1 at hV
  have hsq : Summable (fun q : ℕ × ℕ => ‖V q.1 q.2‖ ^ 2) := by
    rw [summable_prod_of_nonneg (fun q => sq_nonneg _)]
    refine ⟨fun m => (lp_square_sum (V m)).summable, ?_⟩
    simpa only [(lp_square_sum _).tsum_eq] using hV.summable
  have hsq' : Summable (fun q : ℕ × ℕ × ℕ => ‖v q‖ ^ 2) := by
    rw [summable_prod_of_nonneg (fun q => sq_nonneg _)]
    have he (j : ℕ) (q : ℕ × ℕ) : ‖v (j,q)‖ ^ 2 =
        if j = n then ‖V q.1 q.2‖ ^ 2 else 0 := by
      rw [hv]; split_ifs <;> simp
    simp_rw [he]
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : j = n <;> simp [hj, hsq]
    · have ht (j : ℕ) : (∑' q : ℕ × ℕ, if j = n then ‖V q.1 q.2‖ ^ 2 else 0) =
          if j = n then (∑' q : ℕ × ℕ, ‖V q.1 q.2‖ ^ 2) else 0 := by
        by_cases hj : j = n <;> simp [hj]
      simp_rw [ht]
      exact (hasSum_ite_eq n _).summable
  have hq := quadratic_mixture v hsq' u
  change (⟪u, mixture v u⟫_ℂ).re ≤ _
  rw [← hq.tsum_eq, hq.summable.tsum_prod]
  have he (j : ℕ) : (∑' q : ℕ × ℕ, (⟪u, InnerProductSpace.rankOne ℂ (v (j,q)) (v (j,q)) u⟫_ℂ).re) =
      if j = n then (∑' q : ℕ × ℕ, (⟪u, InnerProductSpace.rankOne ℂ (V q.1 q.2) (V q.1 q.2) u⟫_ℂ).re) else 0 := by
    by_cases hj : j = n <;> simp [hv, hj, InnerProductSpace.rankOne_apply]
  simp_rw [he]
  rw [tsum_ite_eq]
  have hs := quadratic_mixture (fun q : ℕ × ℕ => V q.1 q.2) hsq u
  rw [hs.summable.tsum_prod]
  have hi (m : ℕ) := quadratic_mixture (V m) (lp_square_sum (V m)).summable u
  simp_rw [(hi _).tsum_eq]
  have hbound (m : ℕ) :
      (⟪u, mixture (V m) u⟫_ℂ).re ≤ ‖V m‖ ^ 2 / 2 * ‖u‖ ^ 2 :=
    antisymmetric_partial_trace_quadratic_le (V m)
      (balanced_odd_skew _ n hn) u
  have hb := hV.mul_right (1/2 * ‖u‖ ^ 2)
  have hb' : HasSum (fun m : ℕ => ‖V m‖ ^ 2 / 2 * ‖u‖ ^ 2) (1/2 * ‖u‖ ^ 2) := by
    simpa only [one_mul, div_eq_mul_inv, mul_assoc, one_div] using hb
  rw [← hb'.tsum_eq]
  apply Summable.tsum_le_tsum hbound _ hb'.summable
  have hf (q : ℕ × ℕ) : 0 ≤ (⟪u, InnerProductSpace.rankOne ℂ
      (V q.1 q.2) (V q.1 q.2) u⟫_ℂ).re :=
    (InnerProductSpace.isPositive_rankOne_self (𝕜 := ℂ) (V q.1 q.2)).re_inner_nonneg_right u
  have h := ((summable_prod_of_nonneg hf).mp hs.summable).2
  simpa only [(hi _).tsum_eq] using h

end D5.S3.Quantum.QuantumChannels.FockAttenuator.BalancedHalfCap
