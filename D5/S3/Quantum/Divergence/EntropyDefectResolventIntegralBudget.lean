/- GID: D5/S3/Quantum/Divergence/EntropyDefectResolventIntegralBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/EntropyDefectResolventIntegralBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual entropy loss bounds the full positive-axis supported resolvent energy integral. -/

import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
import D5.S3.Quantum.Divergence.ResolventFunctionalRigidity
import D5.S3.Weil.ZetaLinear.Sylvester
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Instances.Matrix

/-! Full positive-axis resolvent energy controlled by actual support-aware entropy loss. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v
open Matrix Filter MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI

namespace D5.S3.Quantum.Divergence.EntropyDefectResolventIntegralBudget

/-- The complete nonnegative resolvent gap is integrable, with exact log budget. -/
private theorem finite_log_resolvent_integral {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (q : κ → ℝ) (u : ι → ℝ) (v : κ → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hu : ∑ i, u i = 1) (hv : ∑ j, v j = 1)
    (hnonneg : ∀ t : ℝ, 0 < t →
      0 ≤ (∑ i, (p i + t)⁻¹ * u i) - ∑ j, (q j + t)⁻¹ * v j) :
    IntegrableOn (fun t : ℝ =>
      (∑ i, (p i + t)⁻¹ * u i) - ∑ j, (q j + t)⁻¹ * v j) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ),
        (∑ i, (p i + t)⁻¹ * u i) - ∑ j, (q j + t)⁻¹ * v j) =
      (∑ j, Real.log (q j) * v j) - ∑ i, Real.log (p i) * u i := by
  classical
  let F : ℝ → ℝ := fun t => (∑ i, Real.log (t + p i) * u i) -
    ∑ j, Real.log (t + q j) * v j
  let G : ℝ → ℝ := fun t => (∑ i, (p i + t)⁻¹ * u i) -
    ∑ j, (q j + t)⁻¹ * v j
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivAt F (G t) t := by
    have hdleft (i : ι) : HasDerivAt (fun x : ℝ => Real.log (x + p i) * u i)
        ((p i + t)⁻¹ * u i) t := by
      have h := (Real.hasDerivAt_log (ne_of_gt (add_pos_of_nonneg_of_pos ht (hp i)))).comp t
        ((hasDerivAt_id t).add_const (p i))
      simpa [add_comm] using h.mul_const (u i)
    have hdright (j : κ) : HasDerivAt (fun x : ℝ => Real.log (x + q j) * v j)
        ((q j + t)⁻¹ * v j) t := by
      have h := (Real.hasDerivAt_log (ne_of_gt (add_pos_of_nonneg_of_pos ht (hq j)))).comp t
        ((hasDerivAt_id t).add_const (q j))
      simpa [add_comm] using h.mul_const (v j)
    convert! (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hdleft i)).sub
      (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hdright j)) using 1
  have hlimit : Tendsto F atTop (𝓝 0) := by
    have hleft : Tendsto (fun t : ℝ => ∑ i, (Real.log (t + p i) - Real.log t) * u i)
        atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ
        (fun i _ => (Real.tendsto_log_comp_add_sub_log (p i)).mul_const (u i))
    have hright : Tendsto (fun t : ℝ => ∑ j, (Real.log (t + q j) - Real.log t) * v j)
        atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ
        (fun j _ => (Real.tendsto_log_comp_add_sub_log (q j)).mul_const (v j))
    have heq (t : ℝ) : F t =
        (∑ i, (Real.log (t + p i) - Real.log t) * u i) -
          ∑ j, (Real.log (t + q j) - Real.log t) * v j := by
      simp only [F, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hu, hv]
      ring
    simpa only [← heq, sub_self] using hleft.sub hright
  have hd' : ∀ t ∈ Ici (0 : ℝ), HasDerivAt F (G t) t :=
    fun t ht => hd t ht
  have hn' : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ G t :=
    fun t ht => hnonneg t ht
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd' hn' hlimit, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hd' hn' hlimit
  simpa only [F, G, zero_add, zero_sub, neg_sub] using h

theorem continuousAt_shift_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun s : ℝ => (A + s • (1 : Matrix ι ι ℂ))⁻¹) t := by
  let H := A + t • (1 : Matrix ι ι ℂ)
  have hH : H.PosDef :=
    Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul ht)
  have hdet : H.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit).ne_zero
  have hInv : ContinuousAt (fun X : Matrix ι ι ℂ => X⁻¹) H :=
    continuousAt_matrix_inv H (by
      simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet))
  exact hInv.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt

private theorem norm_form {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    (star x ⬝ᵥ x).re = ∑ i, ‖x i‖ ^ 2 := by
  classical
  simpa only [RHLinalg.hermForm, Matrix.one_mulVec, RCLike.re_to_complex] using
    RHLinalg.hermForm_one x

/-- Entropy loss pays for the actual full positive-axis resolvent error.
The physical density matrices may be singular; only their existing relative
modular support matrices are positive definite. No trace-distance is asserted. -/
theorem entropy_defect_resolvent_integral_budget
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (ρ σ : DensityState a) (support : SupportContained ρ σ) :
    let M := supported_relative_modular_model Φ ρ σ support
    let w : ℝ → (M.data.J × M.data.I → ℂ) := fun t =>
      (M.data.A + t • 1)⁻¹ *ᵥ M.data.ξ -
        M.data.V *ᵥ ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η)
    IntegrableOn (fun t : ℝ => t * (star (w t) ⬝ᵥ w t).re) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), t * (star (w t) ⬝ᵥ w t).re) ≤
        finiteTraceLogRelativeEntropy ρ σ -
          finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) := by
  classical
  let M := supported_relative_modular_model Φ ρ σ support
  let A := M.data.A
  let B := M.data.B
  let ξ := M.data.ξ
  let η := M.data.η
  let V := M.data.V
  let n := M.data.J × M.data.I
  let m := M.data.L × M.data.K
  let u : n → ℝ := fun i => ‖(star (M.hA.1.eigenvectorUnitary : Matrix n n ℂ) *ᵥ ξ) i‖ ^ 2
  let v : m → ℝ := fun j => ‖(star (M.hB.1.eigenvectorUnitary : Matrix m m ℂ) *ᵥ η) j‖ ^ 2
  have expansionA (g : ℝ → ℝ) :
      (star ξ ⬝ᵥ (cfc g A *ᵥ ξ)).re = ∑ i, g (M.hA.1.eigenvalues i) * u i := by
    have hs : cfc g A = RHLinalg.specMap M.hA.1 g := by rw [M.hA.1.cfc_eq]; rfl
    rw [hs]
    exact RHLinalg.hermForm_specMap M.hA.1 g ξ
  have expansionB (g : ℝ → ℝ) :
      (star η ⬝ᵥ (cfc g B *ᵥ η)).re = ∑ j, g (M.hB.1.eigenvalues j) * v j := by
    have hs : cfc g B = RHLinalg.specMap M.hB.1 g := by rw [M.hB.1.cfc_eq]; rfl
    rw [hs]
    exact RHLinalg.hermForm_specMap M.hB.1 g η
  have hu : ∑ i, u i = 1 := by
    change (∑ i, ‖(star (M.hA.1.eigenvectorUnitary : Matrix n n ℂ) *ᵥ ξ) i‖ ^ 2) = 1
    rw [RHLinalg.sum_normSq_unitary_mulVec M.hA.1 ξ]
    exact M.normξ
  have hv : ∑ j, v j = 1 := by
    change (∑ j, ‖(star (M.hB.1.eigenvectorUnitary : Matrix m m ℂ) *ᵥ η) j‖ ^ 2) = 1
    rw [RHLinalg.sum_normSq_unitary_mulVec M.hB.1 η]
    exact M.normη
  have saturation : (star (V *ᵥ η) ⬝ᵥ (V *ᵥ η)).re = (star η ⬝ᵥ η).re := by
    change (star (M.data.V *ᵥ M.data.η) ⬝ᵥ (M.data.V *ᵥ M.data.η)).re = _
    rw [M.mapsη, norm_form, norm_form, M.normξ, M.normη]
  have resolventA (s : ℝ) (hs : 0 < s) :
      (star ξ ⬝ᵥ ((A + s • 1)⁻¹ *ᵥ ξ)).re =
        ∑ i, (M.hA.1.eigenvalues i + s)⁻¹ * u i := by
    rw [← ResolventFunctionalRigidity.cfc_shift_inverse A M.hA.posSemidef s hs]
    exact expansionA _
  have resolventB (s : ℝ) (hs : 0 < s) :
      (star η ⬝ᵥ ((B + s • 1)⁻¹ *ᵥ η)).re =
        ∑ j, (M.hB.1.eigenvalues j + s)⁻¹ * v j := by
    rw [← ResolventFunctionalRigidity.cfc_shift_inverse B M.hB.posSemidef s hs]
    exact expansionB _
  have energy (s : ℝ) (hs : 0 < s) :
      s * (star ((A + s • 1)⁻¹ *ᵥ ξ - V *ᵥ ((B + s • 1)⁻¹ *ᵥ η)) ⬝ᵥ
        ((A + s • 1)⁻¹ *ᵥ ξ - V *ᵥ ((B + s • 1)⁻¹ *ᵥ η))).re ≤
        (∑ i, (M.hA.1.eigenvalues i + s)⁻¹ * u i) -
          ∑ j, (M.hB.1.eigenvalues j + s)⁻¹ * v j := by
    rw [← resolventA s hs, ← resolventB s hs]
    have he := (ResolventDefectRigidity.resolvent_defect_identity_and_bound
      A B M.hA.posSemidef M.hB.posSemidef V M.hVnorm M.hVA η saturation s hs).2.1
    simpa only [V, η, M.mapsη] using he
  have nn (x : M.data.J × M.data.I → ℂ) : 0 ≤ (star x ⬝ᵥ x).re := by
    rw [norm_form]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hnonneg (s : ℝ) (hs : 0 < s) :
      0 ≤ (∑ i, (M.hA.1.eigenvalues i + s)⁻¹ * u i) -
        ∑ j, (M.hB.1.eigenvalues j + s)⁻¹ * v j :=
    (mul_nonneg hs.le (nn _)).trans (energy s hs)
  obtain ⟨hGint, hGval⟩ := finite_log_resolvent_integral
    M.hA.1.eigenvalues M.hB.1.eigenvalues u v
    M.hA.eigenvalues_pos M.hB.eigenvalues_pos hu hv hnonneg
  have htrace : (star η ⬝ᵥ (cfc Real.log B *ᵥ η)).re -
      (star ξ ⬝ᵥ (cfc Real.log A *ᵥ ξ)).re =
      finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) := by
    rw [M.canonicalTraceR, M.canonicalTraceT]
    ring
  rw [← expansionA Real.log, ← expansionB Real.log, htrace] at hGval
  let w : ℝ → (M.data.J × M.data.I → ℂ) := fun t =>
    (A + t • 1)⁻¹ *ᵥ ξ - V *ᵥ ((B + t • 1)⁻¹ *ᵥ η)
  let E : ℝ → ℝ := fun t => t * (star (w t) ⬝ᵥ w t).re
  let G : ℝ → ℝ := fun t =>
    (∑ i, (M.hA.1.eigenvalues i + t)⁻¹ * u i) -
      ∑ j, (M.hB.1.eigenvalues j + t)⁻¹ * v j
  have hEcont : ContinuousOn E (Ioi (0 : ℝ)) := by
    intro t ht
    have hIA := continuousAt_shift_inverse A M.hA.posSemidef t ht
    have hIB := continuousAt_shift_inverse B M.hB.posSemidef t ht
    have hEc : ContinuousAt E t := by
      dsimp only [E, w, Matrix.mulVec, dotProduct]
      fun_prop
    exact hEc.continuousWithinAt
  have hE0 (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : 0 ≤ E t :=
    mul_nonneg ht.le (nn (w t))
  have hEG (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : E t ≤ G t :=
    energy t ht
  have hEint : IntegrableOn E (Ioi (0 : ℝ)) := by
    refine hGint.mono' (hEcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (hE0 t ht)]
    exact hEG t ht
  change IntegrableOn E (Ioi 0) ∧
    (∫ t in Ioi (0 : ℝ), E t) ≤
      finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)
  refine ⟨hEint, ?_⟩
  calc
    (∫ t in Ioi (0 : ℝ), E t) ≤ ∫ t in Ioi (0 : ℝ), G t :=
      integral_mono_ae hEint hGint
        (ae_restrict_of_forall_mem measurableSet_Ioi hEG)
    _ = _ := hGval

#print axioms entropy_defect_resolvent_integral_budget

end D5.S3.Quantum.Divergence.EntropyDefectResolventIntegralBudget
