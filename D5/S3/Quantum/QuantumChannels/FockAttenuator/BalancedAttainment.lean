/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/BalancedAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vacuum and every coherent density attain the balanced one-photon extended spectral minimum over all density inputs. -/
/-
admission_basis: escape-witness
attenuator_pureDensity_eq identifies the actual square-root density channel
with the owner's pure-input interface by a norm-summable rank-one ensemble.
The vacuum operator polynomial and the existing coherent_output_covariance
supply exact spectral attainment. The minimization theorems combine this
attainment with the all-density lower bound, without assuming the conclusion.
utility: none denotes analytic all-input/coherent-family results; the finite
vacuum calculation is a consumed helper, not an isolated certified instance.
Conjecture 1 at other occupations/transmissivities remains open here; no
uniqueness of coherent minimizers or separate entropy-API equivalence follows.
The balanced one-photon all-density spectral minimum and every-coherent
attainment are attributed to Zixuan He, The energy cost of optical noise,
v1.0, DOI 10.5281/zenodo.23629201, Theorem 2 and Appendix A.2-A.3.
This is formal library integration of that written result; no literature
resolution or priority for the odd-occupation application is claimed.
-/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.BalancedSpectralEntropy

noncomputable section
open scoped InnerProductSpace ENNReal NNReal ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.BalancedHalfCap
open Bargmann BeamSplitter Attenuator DisplacementCovariance QuantumLogEnergy

private def e (n : ℕ) : Fock := lp.single 2 n 1
private def proj (x : Fock) : Fock →L[ℂ] Fock := InnerProductSpace.rankOne ℂ x x

private theorem squares {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
    (x : lp E 2) : HasSum (fun j => ‖x j‖ ^ 2) (‖x‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x)

private theorem proj_smul (c : ℂ) (v : Fock) :
    proj (c • v) = ‖c‖ ^ 2 • proj v := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [proj, InnerProductSpace.rankOne_apply, inner_smul_left, smul_apply, smul_smul]
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  change (starRingEnd ℂ) c * ⟪v, u⟫_ℂ * c = ((‖c‖ ^ 2 : ℝ) : ℂ) * ⟪v, u⟫_ℂ
  rw [Complex.sq_norm, ← Complex.mul_conj]
  ring

/-- The actual density-input attenuator and its pure-input interface agree. -/
theorem attenuator_pureDensity_eq (n : ℕ) (x : Fock) (hx : ‖x‖ = 1) :
    attenuatorOperator (1/2) balanced (pointMassEnvironment n) (pureDensity x hx) =
    pureAttenuatorOperator (1/2) balanced (pointMassEnvironment n) x := by
  letI : Nontrivial Fock := ⟨⟨e 0, 0, by
    intro h
    have h' := congrArg (fun v : Fock => v 0) h
    simp [e, lp.single_apply] at h'⟩⟩
  letI : IsometricContinuousFunctionalCalculus ℝ
      (Fock →L[ℂ] Fock) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  letI : NonUnitalIsometricContinuousFunctionalCalculus ℝ
      (Fock →L[ℂ] Fock) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus
  have hr : CFC.sqrt (pureDensity x hx).operator = proj x := by
    apply CFC.sqrt_unique
    · exact InnerProductSpace.isIdempotentElem_rankOne_self hx
    · exact ContinuousLinearMap.nonneg_iff_isPositive.mpr (pureDensity x hx).positive
  let V := beamSplitter (1/2) balanced (tensor x (e n))
  let v := outputVector (1/2) balanced (pointMassEnvironment n) (pureDensity x hx)
  let c := fun m => ⟪x, e m⟫_ℂ
  have hcv (m : ℕ) : ‖c m‖ = ‖x m‖ := by
    dsimp [c,e]
    rw [lp.inner_single_right]
    simp only [RCLike.inner_apply, one_mul, Complex.norm_conj]
  have hc : HasSum (fun m => ‖c m‖ ^ 2) 1 := by
    simpa only [hcv, hx, one_pow] using squares x
  have hv (j m l : ℕ) : v (j,m,l) = if j = n then c m • V l else 0 := by
    by_cases hj : j = n
    · subst j
      simp only [v, outputVector, pointMassEnvironment, ite_true, Real.sqrt_one,
        Complex.ofReal_one, one_smul, hr, proj, InnerProductSpace.rankOne_apply]
      have ht : tensor (c m • x) (e n) = c m • tensor x (e n) := by
        apply lp.ext; funext k
        change e n k • (c m • x) = c m • (e n k • x)
        exact smul_comm _ _ _
      change (beamSplitter (1/2) balanced (tensor (c m • x) (e n))) l = _
      rw [ht, map_smul]
      rfl
    · simp [v, outputVector, pointMassEnvironment, hj]
  rw [point_mass_pure_attenuator]
  change (∑' q : ℕ × ℕ × ℕ, proj (v q)) = ∑' l, proj (V l)
  have hV : Summable (fun l => proj (V l)) := by
    apply Summable.of_norm
    simpa only [proj, InnerProductSpace.norm_rankOne, ← sq] using (squares V).summable
  have he (j : ℕ) (q : ℕ × ℕ) : proj (v (j,q)) =
      if j = n then ‖c q.1‖ ^ 2 • proj (V q.2) else 0 := by
    rw [hv]
    by_cases hj : j = n
    · simpa only [ite_eq_left hj] using proj_smul (c q.1) (V q.2)
    · simp [hj, proj]
  have hpairNorm : Summable (fun q : ℕ × ℕ => ‖(‖c q.1‖ ^ 2 : ℝ) • proj (V q.2)‖) := by
    have heq (q : ℕ × ℕ) : ‖(‖c q.1‖ ^ 2 : ℝ) • proj (V q.2)‖ =
        ‖c q.1‖ ^ 2 * ‖proj (V q.2)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
    simp_rw [heq]
    apply (summable_prod_of_nonneg (fun q : ℕ × ℕ =>
      mul_nonneg (sq_nonneg ‖c q.1‖) (norm_nonneg (proj (V q.2))))).mpr
    have hh : Summable (fun l => ‖proj (V l)‖) := by
      simpa only [proj, InnerProductSpace.norm_rankOne, ← sq] using (squares V).summable
    constructor
    · intro m
      exact hh.mul_left (‖c m‖ ^ 2)
    · change Summable (fun m : ℕ => ∑' l : ℕ, ‖c m‖ ^ 2 * ‖proj (V l)‖)
      simp_rw [hh.tsum_mul_left]
      exact hc.summable.mul_right (∑' l, ‖proj (V l)‖)
  have hpair : Summable (fun q : ℕ × ℕ => ‖c q.1‖ ^ 2 • proj (V q.2)) :=
    Summable.of_norm hpairNorm
  have htot : Summable (fun q : ℕ × ℕ × ℕ => proj (v q)) := by
    apply Summable.of_norm
    rw [summable_prod_of_nonneg (fun q => norm_nonneg _)]
    have hnorm (j : ℕ) (q : ℕ × ℕ) : ‖proj (v (j,q))‖ =
        if j = n then ‖‖c q.1‖ ^ 2 • proj (V q.2)‖ else 0 := by
      rw [he]; split_ifs <;> simp
    simp_rw [hnorm]
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : j = n <;> simp [hj, hpairNorm]
    · have ht (j : ℕ) :
          (∑' q : ℕ × ℕ, if j = n then ‖‖c q.1‖ ^ 2 • proj (V q.2)‖ else 0) =
          if j = n then (∑' q : ℕ × ℕ, ‖‖c q.1‖ ^ 2 • proj (V q.2)‖) else 0 := by
        by_cases hj : j = n <;> simp [hj]
      simp_rw [ht]
      exact (hasSum_ite_eq n _).summable
  rw [htot.tsum_prod]
  simp_rw [he]
  have hinner (j : ℕ) :
      (∑' q : ℕ × ℕ, if j = n then ‖c q.1‖ ^ 2 • proj (V q.2) else 0) =
      if j = n then (∑' q : ℕ × ℕ, ‖c q.1‖ ^ 2 • proj (V q.2)) else 0 := by
    by_cases hj : j = n <;> simp [hj]
  simp_rw [hinner]
  rw [tsum_ite_eq, hpair.tsum_prod]
  simp_rw [hV.tsum_const_smul]
  exact (hc.smul_const _).tsum_eq.trans (one_smul _ _)

private def t : ℂ := (Real.sqrt (1/2 : ℝ) : ℂ)

private theorem vacuum_beam :
    beamSplitter (1/2) balanced (tensor (e 0) (e 1)) =
      t • (tensor (e 0) (e 1) - tensor (e 1) (e 0)) := by
  apply kernel_injective
  funext z w
  rw [beamSplitter, kernel_beam_unitary, kernel_tensor]
  rw [kernel_eq_inner, inner_smul_right, inner_sub_right, ← kernel_eq_inner, ← kernel_eq_inner,
    kernel_tensor, kernel_tensor]
  simp only [e, transform_single, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
    Real.sqrt_one, Complex.ofReal_one, div_one, pow_zero, pow_one, one_mul, mul_one,
    show (1 - 1/2 : ℝ) = 1/2 by norm_num, t]
  ring

private theorem vacuum_pure_operator :
    pureAttenuatorOperator (1/2) balanced (pointMassEnvironment 1) (e 0) =
      ((1/2 : ℝ) : ℂ) • (proj (e 0) + proj (e 1)) := by
  rw [point_mass_pure_attenuator, show (lp.single 2 1 (1 : ℂ)) = e 1 from rfl, vacuum_beam]
  change (∑' j : ℕ, proj ((t • (tensor (e 0) (e 1) - tensor (e 1) (e 0))) j)) = _
  have h (j : ℕ) : proj ((t • (tensor (e 0) (e 1) - tensor (e 1) (e 0))) j) =
      (if j = 0 then (1/2 : ℝ) • proj (e 1) else 0) +
      (if j = 1 then (1/2 : ℝ) • proj (e 0) else 0) := by
    change proj (t • (e 1 j • e 0 - e 0 j • e 1)) = _
    have ht : ‖t‖ ^ 2 = (1/2 : ℝ) := by
      rw [t, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (by norm_num)]
    rw [proj_smul, ht]
    by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;>
      simp_all [e, lp.single_apply, Pi.single, proj]
  simp_rw [h]
  rw [(hasSum_ite_eq 0 _).summable.tsum_add (hasSum_ite_eq 1 _).summable,
    tsum_ite_eq, tsum_ite_eq, smul_add, add_comm]
  rfl

private theorem vacuum_pure_square :
    let A := pureAttenuatorOperator (1/2) balanced (pointMassEnvironment 1) (e 0)
    A * A = ((1/2 : ℝ) : ℂ) • A := by
  dsimp only
  rw [vacuum_pure_operator, smul_mul_smul, smul_smul]
  congr 1
  have h (n : ℕ) : proj (e n) * proj (e n) = proj (e n) :=
    InnerProductSpace.isIdempotentElem_rankOne_self (by simp [e, lp.norm_single])
  have h01 : proj (e 0) * proj (e 1) = 0 := by
    simp [ContinuousLinearMap.mul_def, proj, InnerProductSpace.rankOne_comp_rankOne,
      e, lp.inner_single_left, lp.single_apply, Pi.single]
  have h10 : proj (e 1) * proj (e 0) = 0 := by
    simp [ContinuousLinearMap.mul_def, proj, InnerProductSpace.rankOne_comp_rankOne,
      e, lp.inner_single_left, lp.single_apply, Pi.single]
  simp only [add_mul, mul_add, h, h01, h10, add_zero, zero_add]

/-- The actual density output for vacuum attains the lower bound. -/
theorem balanced_one_photon_vacuum_entropy :
    spectralEntropy (densityReference
      (attenuator (1/2) balanced (pointMassEnvironment 1) (fockDensity 0))) =
    ENNReal.ofReal (Real.log 2) := by
  apply density_entropy_eq_log_two_of_square
  have hunit : ‖e 0‖ = 1 := by simp [e, lp.norm_single]
  change attenuatorOperator (1/2) balanced (pointMassEnvironment 1) (pureDensity (e 0) hunit) *
    attenuatorOperator (1/2) balanced (pointMassEnvironment 1) (pureDensity (e 0) hunit) =
    ((1/2 : ℝ) : ℂ) • attenuatorOperator (1/2) balanced (pointMassEnvironment 1) (pureDensity (e 0) hunit)
  rw [attenuator_pureDensity_eq]
  exact vacuum_pure_square

private theorem displacement_vacuum (α : ℂ) : displacement α (e 0) = coherent α := by
  have hzero : exponentialVector 0 = e 0 := by
    apply lp.ext; funext j
    by_cases h : j = 0
    · subst j
      simp [e, exponentialVector, exponentialCoeff, lp.single_apply]
    · simp [e, exponentialVector, exponentialCoeff, lp.single_apply, Pi.single, h,
        zero_pow (Nat.pos_of_ne_zero h).ne']
  rw [← hzero]
  have h (β : ℂ) : displacement α (exponentialVector β) = weylVector α β := by
    classical
    have he : exponentialVector β =
        Finsupp.linearCombination ℂ exponentialVector (Finsupp.single β (1 : ℂ)) := by
      simp only [Finsupp.linearCombination_single, one_smul]
    unfold displacement
    rw [he, LinearEquiv.extendOfIsometry_eq]
    simp only [LinearEquiv.refl_apply, Finsupp.linearCombination_single, one_smul]
  rw [h]
  apply lp.ext; funext j
  simp only [weylVector, mul_zero, sub_zero, add_zero, ← Complex.ofReal_neg,
    ← Complex.ofReal_exp, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, exponentialVector,
    exponentialCoeff, coherent, coherentCoeff]
  ring

/-- Every actual coherent density attains the all-input spectral lower bound. -/
theorem balanced_one_photon_coherent_entropy (α : ℂ) :
    spectralEntropy (densityReference
      (attenuator (1/2) balanced (pointMassEnvironment 1) (coherentDensity α))) =
    ENNReal.ofReal (Real.log 2) := by
  apply density_entropy_eq_log_two_of_square
  have hunit : ‖coherent α‖ = 1 := by
    rw [← displacement_vacuum, LinearIsometryEquiv.norm_map]
    simp [e, lp.norm_single]
  let P := attenuatorOperator (1/2) balanced (pointMassEnvironment 1)
    (pureDensity (coherent α) hunit)
  change P * P = ((1/2 : ℝ) : ℂ) • P
  have hP : P = LinearIsometryEquiv.conjStarAlgEquiv (displacement ((Real.sqrt (1/2 : ℝ) : ℂ) * α))
      (pureAttenuatorOperator (1/2) balanced (pointMassEnvironment 1) (e 0)) := by
    dsimp only [P]
    rw [attenuator_pureDensity_eq, ← displacement_vacuum]
    exact coherent_output_covariance (1/2) balanced (pointMassEnvironment 1) α
  rw [hP, ← map_mul, vacuum_pure_square, map_smul]

/-- The actual vacuum output minimizes spectral entropy over the entire density domain. -/
theorem balanced_one_photon_vacuum_minimizes (ρ : DensityOperator) :
    spectralEntropy (densityReference
      (attenuator (1/2) balanced (pointMassEnvironment 1) (fockDensity 0))) ≤
    spectralEntropy (densityReference
      (attenuator (1/2) balanced (pointMassEnvironment 1) ρ)) := by
  rw [balanced_one_photon_vacuum_entropy]
  exact balanced_one_photon_spectral_entropy_lower ρ

/-- Every coherent input minimizes the actual extended spectral entropy. -/
theorem balanced_one_photon_coherent_minimizes (α : ℂ) (ρ : DensityOperator) :
    spectralEntropy (densityReference
      (attenuator (1/2) balanced (pointMassEnvironment 1) (coherentDensity α))) ≤
    spectralEntropy (densityReference
      (attenuator (1/2) balanced (pointMassEnvironment 1) ρ)) := by
  rw [balanced_one_photon_coherent_entropy]
  exact balanced_one_photon_spectral_entropy_lower ρ

end D5.S3.Quantum.QuantumChannels.FockAttenuator.BalancedHalfCap
