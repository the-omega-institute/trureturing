/- GID: D5/S3/Quantum/Divergence/LiebOverlapResolventIntegralBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/LiebOverlapResolventIntegralBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Petz overlap loss controls the full weighted supported resolvent energy. -/

import D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
import D5.S3.Quantum.Recovery.PetzSpectralCoordinates
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

/-! Actual positive-power overlap and the full weighted resolvent energy.

proof_shape: content; admission_basis: escape-witness.
The proof identifies supported modular power moments with physical trace products
in the original eigenbases, including singular states, and cancels the common
nonintegrable tail before using finite sums of integrable positive-power kernels.
The pointwise resolvent inequality then supplies the actual full-axis budget.
Existing spectral and normalization suppliers are reused in place. No bounded
instance, numerical reduction, physical sharpness or literature novelty is claimed.
-/

noncomputable section
universe u v
open Matrix Set MeasureTheory Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Divergence.EntropyDefectInverseSqrtStability
open D5.S3.Quantum.Recovery.PetzSpectralCoordinates
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity

namespace D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget

private theorem trace_rank_one_product {n : Type*} [Fintype n]
    (x y : n → ℂ) :
    ((Matrix.vecMulVec x (star x) * Matrix.vecMulVec y (star y)).trace).re =
      ‖star y ⬝ᵥ x‖ ^ 2 := by
  classical
  have ht : (Matrix.vecMulVec x (star x) * Matrix.vecMulVec y (star y)).trace =
      (star x ⬝ᵥ y) * (star y ⬝ᵥ x) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec,
      dotProduct_smul, dotProduct_comm x (star y), smul_eq_mul]
  rw [ht, Matrix.star_dotProduct]
  have hz : star (star y ⬝ᵥ x) * (star y ⬝ᵥ x) =
      ((‖star y ⬝ᵥ x‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [RCLike.star_def, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_pow] using RCLike.conj_mul (star y ⬝ᵥ x)
  rw [hz, Complex.ofReal_re]

/-- The physical trace product and the supported modular power use exactly
the same original eigenvectors. This helper is consumed by the actual budget. -/
private theorem supported_power_moment {n : Type*} [Fintype n] [DecidableEq n]
    (R S : Matrix n n ℂ) (hR : R.PosSemidef) (hS : S.PosSemidef)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    let I := {i : n // 0 < hR.1.eigenvalues i}
    let J := {j : n // 0 < hS.1.eigenvalues j}
    let A : Matrix (J × I) (J × I) ℂ := Matrix.diagonal
      (fun ji => (hS.1.eigenvalues ji.1.1 / hR.1.eigenvalues ji.2.1 : ℝ))
    let ξ : J × I → ℂ := fun ji => (Real.sqrt (hR.1.eigenvalues ji.2.1) : ℂ) *
      (star (fun x => hS.1.eigenvectorBasis ji.1.1 x) ⬝ᵥ
        (fun x => hR.1.eigenvectorBasis ji.2.1 x))
    (star ξ ⬝ᵥ (cfc (fun x : ℝ => x ^ q) A *ᵥ ξ)).re =
      (cfc (fun x : ℝ => x ^ (1 - q)) R *
        cfc (fun x : ℝ => x ^ q) S).trace.re := by
  classical
  let I := {i : n // 0 < hR.1.eigenvalues i}
  let J := {j : n // 0 < hS.1.eigenvalues j}
  let r : I → ℝ := fun i => hR.1.eigenvalues i.1
  let s : J → ℝ := fun j => hS.1.eigenvalues j.1
  let u : I → n → ℂ := fun i x => hR.1.eigenvectorBasis i.1 x
  let v : J → n → ℂ := fun j x => hS.1.eigenvectorBasis j.1 x
  have hRexp := cfc_supported_sum R hR (fun x : ℝ => x ^ (1 - q))
    (Real.zero_rpow (by linarith : 1 - q ≠ 0))
  have hSexp := cfc_supported_sum S hS (fun x : ℝ => x ^ q)
    (Real.zero_rpow hq0.ne')
  have htrace :
      (cfc (fun x : ℝ => x ^ (1 - q)) R * cfc (fun x : ℝ => x ^ q) S).trace.re =
        ∑ i : I, ∑ j : J, r i ^ (1 - q) * s j ^ q * ‖star (v j) ⬝ᵥ u i‖ ^ 2 := by
    rw [hRexp, hSexp]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      Matrix.trace_sum, Matrix.trace_smul, Finset.smul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [trace_rank_one_product]
    dsimp only [r, s, u, v]
    ring
  rw [htrace]
  dsimp only
  rw [cfc_diagonal, diagonal_quadratic_form, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hr : 0 < r i := i.2
  have hs : 0 < s j := j.2
  have hc : (s j / r i) ^ q * r i = r i ^ (1 - q) * s j ^ q := by
    rw [Real.div_rpow hs.le hr.le, Real.rpow_sub hr, Real.rpow_one]
    ring
  simp only [r, s, u, v]
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt i.2.le]
  change (s j / r i) ^ q * (r i * ‖star (v j) ⬝ᵥ u i‖ ^ 2) = _
  rw [← mul_assoc, hc]

/-- A finite weighted gap is a difference of genuinely integrable positive-power
kernels. The two raw weighted resolvent sums are not integrated separately. -/
private theorem finite_power_resolvent_integral
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (p : ι → ℝ) (r : κ → ℝ) (u : ι → ℝ) (v : κ → ℝ)
    (hp : ∀ i, 0 < p i) (hr : ∀ j, 0 < r j)
    (hu : ∑ i, u i = 1) (hv : ∑ j, v j = 1) :
    IntegrableOn (fun t : ℝ => t ^ q *
      ((∑ i, (p i + t)⁻¹ * u i) - ∑ j, (r j + t)⁻¹ * v j)) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), t ^ q *
        ((∑ i, (p i + t)⁻¹ * u i) - ∑ j, (r j + t)⁻¹ * v j)) =
          (Real.pi / Real.sin (Real.pi * q)) *
            ((∑ j, (r j) ^ q * v j) - ∑ i, (p i) ^ q * u i) := by
  classical
  let F : ℝ → ℝ := fun t =>
    (∑ j, Real.rpowIntegrand₀₁ q t (r j) * v j) -
      ∑ i, Real.rpowIntegrand₀₁ q t (p i) * u i
  have hi (i : ι) : IntegrableOn
      (fun t : ℝ => Real.rpowIntegrand₀₁ q t (p i) * u i) (Ioi 0) :=
    (Real.integrableOn_rpowIntegrand₀₁_Ioi ⟨hq0, hq1⟩ (hp i).le).mul_const (u i)
  have hj (j : κ) : IntegrableOn
      (fun t : ℝ => Real.rpowIntegrand₀₁ q t (r j) * v j) (Ioi 0) :=
    (Real.integrableOn_rpowIntegrand₀₁_Ioi ⟨hq0, hq1⟩ (hr j).le).mul_const (v j)
  have hF : IntegrableOn F (Ioi (0 : ℝ)) :=
    (integrable_finsetSum Finset.univ (fun j _ => hj j)).sub
      (integrable_finsetSum Finset.univ (fun i _ => hi i))
  have hpoint (t : ℝ) (ht : 0 < t) : F t = t ^ q *
      ((∑ i, (p i + t)⁻¹ * u i) - ∑ j, (r j + t)⁻¹ * v j) := by
    have hk (x : ℝ) (hx : 0 < x) :
        Real.rpowIntegrand₀₁ q t x = t ^ (q - 1) - t ^ q * (x + t)⁻¹ := by
      rw [Real.rpowIntegrand₀₁_eq_pow_div ⟨hq0, hq1⟩ ht.le hx.le]
      have htq : t ^ q = t ^ (q - 1) * t := by
        rw [← Real.rpow_add_one ht.ne', sub_add_cancel]
      rw [htq]
      field_simp [(add_pos ht hx).ne', (add_pos hx ht).ne']
      ring
    have hpSum : (∑ i, Real.rpowIntegrand₀₁ q t (p i) * u i) =
        t ^ (q - 1) - t ^ q * ∑ i, (p i + t)⁻¹ * u i := by
      calc
        _ = ∑ i, (t ^ (q - 1) - t ^ q * (p i + t)⁻¹) * u i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hk _ (hp i)]
        _ = _ := by
          simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hu]
          ring
    have hrSum : (∑ j, Real.rpowIntegrand₀₁ q t (r j) * v j) =
        t ^ (q - 1) - t ^ q * ∑ j, (r j + t)⁻¹ * v j := by
      calc
        _ = ∑ j, (t ^ (q - 1) - t ^ q * (r j + t)⁻¹) * v j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hk _ (hr j)]
        _ = _ := by
          simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hv]
          ring
    dsimp only [F]
    rw [hpSum, hrSum]
    ring
  have hvF : (∫ t in Ioi (0 : ℝ), F t) =
      (Real.pi / Real.sin (Real.pi * q)) *
        ((∑ j, (r j) ^ q * v j) - ∑ i, (p i) ^ q * u i) := by
    dsimp only [F]
    rw [integral_sub (integrable_finsetSum Finset.univ (fun j _ => hj j))
      (integrable_finsetSum Finset.univ (fun i _ => hi i)),
      integral_finsetSum Finset.univ (fun j _ => hj j),
      integral_finsetSum Finset.univ (fun i _ => hi i)]
    have hip (i : ι) :
        (∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ q t (p i) * u i) =
          (p i) ^ q * (Real.pi / Real.sin (Real.pi * q)) * u i := by
      rw [integral_mul_const,
        Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const ⟨hq0, hq1⟩ (hp i).le,
        power_normalizer q ⟨hq0, hq1⟩]
    have hjr (j : κ) :
        (∫ t in Ioi (0 : ℝ), Real.rpowIntegrand₀₁ q t (r j) * v j) =
          (r j) ^ q * (Real.pi / Real.sin (Real.pi * q)) * v j := by
      rw [integral_mul_const,
        Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const ⟨hq0, hq1⟩ (hr j).le,
        power_normalizer q ⟨hq0, hq1⟩]
    simp_rw [hip, hjr]
    simp only [mul_sub, Finset.mul_sum]
    apply congrArg₂ (fun x y : ℝ => x - y)
    · apply Finset.sum_congr rfl
      intro j hj
      ring
    · apply Finset.sum_congr rfl
      intro i hi
      ring
  refine ⟨hF.congr_fun (fun t ht => hpoint t ht) measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi (fun t ht => hpoint t ht)]
  exact hvF

set_option maxHeartbeats 1000000 in
/-- The actual Petz/Lieb overlap deficit controls the full weighted resolvent
energy for all 0<q<1, retaining the original support and the genuine L2 norm. -/
theorem actual_lieb_overlap_resolvent_integral_budget
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (ρ σ : DensityState a) (support : SupportContained ρ σ)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    let M := supported_relative_modular_model Φ ρ σ support
    let w : ℝ → EuclideanSpace ℂ (M.data.J × M.data.I) := fun t => WithLp.toLp 2
      ((M.data.A + t • 1)⁻¹ *ᵥ M.data.ξ -
        M.data.V *ᵥ ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η))
    let inputOverlap := (cfc (fun x : ℝ => x ^ (1 - q)) M.data.R *
      cfc (fun x : ℝ => x ^ q) M.data.S).trace.re
    let outputOverlap := (cfc (fun x : ℝ => x ^ (1 - q)) M.data.T *
      cfc (fun x : ℝ => x ^ q) M.data.Q).trace.re
    IntegrableOn (fun t : ℝ => t ^ (q + 1) * ‖w t‖ ^ 2) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), t ^ (q + 1) * ‖w t‖ ^ 2) ≤
        (outputOverlap - inputOverlap) / (Real.sin (Real.pi * q) / Real.pi) := by
  classical
  let M := supported_relative_modular_model Φ ρ σ support
  let A := M.data.A
  let B := M.data.B
  let ξ := M.data.ξ
  let η := M.data.η
  let V := M.data.V
  let w : ℝ → EuclideanSpace ℂ (M.data.J × M.data.I) := fun t => WithLp.toLp 2
    ((A + t • 1)⁻¹ *ᵥ ξ - V *ᵥ ((B + t • 1)⁻¹ *ᵥ η))
  let u := fun i => ‖(star (M.hA.1.eigenvectorUnitary : Matrix (M.data.J × M.data.I) (M.data.J × M.data.I) ℂ) *ᵥ ξ) i‖ ^ 2
  let v := fun j => ‖(star (M.hB.1.eigenvectorUnitary : Matrix (M.data.L × M.data.K) (M.data.L × M.data.K) ℂ) *ᵥ η) j‖ ^ 2
  have expansionA (f : ℝ → ℝ) :
      (star ξ ⬝ᵥ (cfc f A *ᵥ ξ)).re = ∑ i, f (M.hA.1.eigenvalues i) * u i := by
    rw [show cfc f A = RHLinalg.specMap M.hA.1 f by rw [M.hA.1.cfc_eq]; rfl]
    exact RHLinalg.hermForm_specMap M.hA.1 f ξ
  have expansionB (f : ℝ → ℝ) :
      (star η ⬝ᵥ (cfc f B *ᵥ η)).re = ∑ j, f (M.hB.1.eigenvalues j) * v j := by
    rw [show cfc f B = RHLinalg.specMap M.hB.1 f by rw [M.hB.1.cfc_eq]; rfl]
    exact RHLinalg.hermForm_specMap M.hB.1 f η
  have hu : ∑ i, u i = 1 := by
    change (∑ i, ‖(star (M.hA.1.eigenvectorUnitary : Matrix (M.data.J × M.data.I) (M.data.J × M.data.I) ℂ) *ᵥ ξ) i‖ ^ 2) = 1
    rw [RHLinalg.sum_normSq_unitary_mulVec M.hA.1 ξ]
    exact M.normξ
  have hv : ∑ j, v j = 1 := by
    change (∑ j, ‖(star (M.hB.1.eigenvectorUnitary : Matrix (M.data.L × M.data.K) (M.data.L × M.data.K) ℂ) *ᵥ η) j‖ ^ 2) = 1
    rw [RHLinalg.sum_normSq_unitary_mulVec M.hB.1 η]
    exact M.normη
  let G : ℝ → ℝ := fun t =>
    (∑ i, (M.hA.1.eigenvalues i + t)⁻¹ * u i) -
      ∑ j, (M.hB.1.eigenvalues j + t)⁻¹ * v j
  have henergy (t : ℝ) (ht : 0 < t) : t * ‖w t‖ ^ 2 ≤ G t := by
    have saturation : (star (V *ᵥ η) ⬝ᵥ (V *ᵥ η)).re = (star η ⬝ᵥ η).re := by
      change (star (M.data.V *ᵥ M.data.η) ⬝ᵥ (M.data.V *ᵥ M.data.η)).re = _
      rw [M.mapsη, ← l2_norm_sq, ← l2_norm_sq,
        EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, M.normξ, M.normη]
    have he := (ResolventDefectRigidity.resolvent_defect_identity_and_bound
      A B M.hA.posSemidef M.hB.posSemidef V M.hVnorm M.hVA η saturation t ht).2.1
    have rA := expansionA (fun x => (x + t)⁻¹)
    have rB := expansionB (fun x => (x + t)⁻¹)
    rw [ResolventFunctionalRigidity.cfc_shift_inverse A M.hA.posSemidef t ht] at rA
    rw [ResolventFunctionalRigidity.cfc_shift_inverse B M.hB.posSemidef t ht] at rB
    dsimp only [G]
    rw [← rA, ← rB]
    simpa only [w, l2_norm_sq, V, η, M.mapsη] using he
  obtain ⟨hG, hGvalue⟩ := finite_power_resolvent_integral q hq0 hq1
    M.hA.1.eigenvalues M.hB.1.eigenvalues u v
    M.hA.eigenvalues_pos M.hB.eigenvalues_pos hu hv
  have hmomentA := supported_power_moment M.data.R M.data.S M.data.hR M.data.hS q hq0 hq1
  have hmomentB := supported_power_moment M.data.T M.data.Q M.data.hT M.data.hQ q hq0 hq1
  rw [← expansionA (fun x : ℝ => x ^ q), ← expansionB (fun x : ℝ => x ^ q),
    hmomentA, hmomentB] at hGvalue
  let E : ℝ → ℝ := fun t => t ^ (q + 1) * ‖w t‖ ^ 2
  obtain ⟨hOldE, _⟩ :=
    EntropyDefectResolventIntegralBudget.entropy_defect_resolvent_integral_budget Φ ρ σ support
  have hEm : AEStronglyMeasurable E (volume.restrict (Ioi (0 : ℝ))) := by
    have h := (Real.continuous_rpow_const hq0.le).aestronglyMeasurable.mul
      hOldE.aestronglyMeasurable
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change t ^ q * (t * (star (WithLp.ofLp (w t)) ⬝ᵥ WithLp.ofLp (w t)).re) = E t
    rw [← l2_norm_sq]
    change t ^ q * (t * ‖w t‖ ^ 2) = t ^ (q + 1) * ‖w t‖ ^ 2
    rw [Real.rpow_add_one ht.ne', mul_assoc]
  have hE0 (t : ℝ) (ht : 0 < t) : 0 ≤ E t := by
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (sq_nonneg _)
  have hEG (t : ℝ) (ht : 0 < t) : E t ≤ t ^ q * G t := by
    change t ^ (q + 1) * ‖w t‖ ^ 2 ≤ t ^ q * G t
    rw [Real.rpow_add_one ht.ne', mul_assoc]
    exact mul_le_mul_of_nonneg_left (henergy t ht) (Real.rpow_nonneg ht.le q)
  have hEi : IntegrableOn E (Ioi (0 : ℝ)) := by
    apply hG.mono' hEm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (hE0 t ht)]
    exact hEG t ht
  have hsin : 0 < Real.sin (Real.pi * q) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hq0)
      (by simpa using mul_lt_mul_of_pos_left hq1 Real.pi_pos)
  refine ⟨hEi, ?_⟩
  calc
    (∫ t in Ioi (0 : ℝ), E t) ≤ ∫ t in Ioi (0 : ℝ), t ^ q * G t :=
      integral_mono_ae hEi hG
        (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => hEG t ht))
    _ = _ := by
      rw [hGvalue]
      field_simp [Real.pi_ne_zero, hsin.ne']

end D5.S3.Quantum.Divergence.LiebOverlapResolventIntegralBudget
