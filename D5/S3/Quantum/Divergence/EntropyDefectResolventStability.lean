/- GID: D5/S3/Quantum/Divergence/EntropyDefectResolventStability
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/EntropyDefectResolventStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Supported quantum entropy loss controls quartic resolvent intertwining error. -/

import D5.S3.Quantum.Divergence.CanonicalRelativeModularModel
import D5.S3.Quantum.Divergence.ResolventFunctionalRigidity
import D5.S3.Weil.ZetaLinear.Sylvester
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Finite logarithmic calculus gives a quantitative bound on the actual supported model. -/

noncomputable section
universe u v
open Matrix Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Divergence.CanonicalChannelDPI

namespace D5.S3.Quantum.Divergence.EntropyDefectResolventStability

/-- A finite shifted-log gap controls its nonnegative resolvent derivative.
Only positivity of the spectral points and unit mass of the weights are used. -/
private theorem finite_log_resolvent_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (q : κ → ℝ) (u : ι → ℝ) (v : κ → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ j, 0 ≤ v j)
    (hu : ∑ i, u i = 1) (hv : ∑ j, v j = 1)
    (hnonneg : ∀ t : ℝ, 0 < t →
      0 ≤ (∑ i, (p i + t)⁻¹ * u i) - ∑ j, (q j + t)⁻¹ * v j)
    (t : ℝ) (ht : 0 < t) :
    t ^ 2 * ((∑ i, (p i + t)⁻¹ * u i) - ∑ j, (q j + t)⁻¹ * v j) ^ 2 ≤
      4 * ((∑ j, Real.log (q j) * v j) - ∑ i, Real.log (p i) * u i) := by
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
  have hm : MonotoneOn F (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (by intro t ht; simp only [interior_Ici, Set.mem_Ioi] at ht
          exact (hd t ht.le).hasDerivWithinAt)
      (by intro t ht; simp only [interior_Ici, Set.mem_Ioi] at ht
          exact hnonneg t ht)
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
  have hhi (s : ℝ) (hs : 0 ≤ s) : F s ≤ 0 :=
    ge_of_tendsto hlimit (by
      filter_upwards [eventually_ge_atTop s] with x hx
      exact hm hs (hs.trans hx) hx)
  have hlo : F 0 ≤ F t := hm (by simp) ht.le ht.le
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hlower (s : ℝ) (hs : t ≤ s) : G t - (s - t) / t ^ 2 ≤ G s := by
    have invdiff (r : ℝ) (hr : 0 < r) :
        (r + t)⁻¹ - (r + s)⁻¹ ≤ (s - t) / t ^ 2 := by
      have hrt : 0 < r + t := add_pos hr ht
      have hrs : 0 < r + s := by linarith
      calc
        (r + t)⁻¹ - (r + s)⁻¹ = (s - t) / ((r + t) * (r + s)) := by
          field_simp [ne_of_gt hrt, ne_of_gt hrs]
          <;> ring
        _ ≤ (s - t) / t ^ 2 := by
          apply div_le_div_of_nonneg_left (sub_nonneg.mpr hs) ht2
          nlinarith [mul_nonneg hr.le (show 0 ≤ s from ht.le.trans hs),
            mul_nonneg ht.le (sub_nonneg.mpr hs)]
    have hleft : (∑ i, (p i + t)⁻¹ * u i) -
        (∑ i, (p i + s)⁻¹ * u i) ≤ (s - t) / t ^ 2 := by
      calc
        _ = ∑ i, ((p i + t)⁻¹ - (p i + s)⁻¹) * u i := by
          simp only [sub_mul, Finset.sum_sub_distrib]
        _ ≤ ∑ i, ((s - t) / t ^ 2) * u i :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (invdiff (p i) (hp i)) (hu0 i))
        _ = (s - t) / t ^ 2 := by rw [← Finset.mul_sum, hu, mul_one]
    have hright : (∑ j, (q j + s)⁻¹ * v j) ≤ ∑ j, (q j + t)⁻¹ * v j := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ (hv0 j)
      exact inv_anti₀ (add_pos (hq j) ht) (by linarith)
    dsimp only [G]
    linarith
  let H : ℝ → ℝ := fun s => F s - G t * (s - t) + (s - t) ^ 2 / t ^ 2
  have hdH (s : ℝ) (hs : t ≤ s) :
      HasDerivAt H (G s - G t + 2 * (s - t) / t ^ 2) s := by
    have h := ((hd s (ht.le.trans hs)).sub
      (((hasDerivAt_id s).sub_const t).const_mul (G t))).add
      ((((hasDerivAt_id s).sub_const t).pow 2).div_const (t ^ 2))
    convert h using 1
    · rfl
    · simp
  have hmH : MonotoneOn H (Set.Ici t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici t)
      (fun s hs => (hdH s hs).continuousAt.continuousWithinAt)
      (by intro s hs; simp only [interior_Ici, Set.mem_Ioi] at hs
          exact (hdH s hs.le).hasDerivWithinAt)
      (by
        intro s hs
        simp only [interior_Ici, Set.mem_Ioi] at hs
        have h := hlower s hs.le
        have hn : 0 ≤ (s - t) / t ^ 2 := div_nonneg (by linarith) ht2.le
        rw [mul_div_assoc]
        linarith only [h, hn])
  have hGt : 0 ≤ G t := hnonneg t ht
  let h : ℝ := G t * t ^ 2 / 2
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hstep := hmH (show t ∈ Set.Ici t from by simp)
    (show t + h ∈ Set.Ici t from by
      simp only [Set.mem_Ici]
      exact le_add_of_nonneg_right hh)
    (le_add_of_nonneg_right hh)
  have hend := hhi (t + h) (by linarith)
  have hcancel : h ^ 2 / t ^ 2 = (G t) ^ 2 * t ^ 2 / 4 := by
    dsimp [h]
    field_simp [ne_of_gt ht]
    <;> ring
  have hprod : G t * h = (G t) ^ 2 * t ^ 2 / 2 := by dsimp [h]; ring
  simp only [H, sub_self, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
    sub_zero, add_zero, add_sub_cancel_left] at hstep
  rw [hcancel, hprod] at hstep
  have hresult : t ^ 2 * (G t) ^ 2 ≤ -4 * F 0 := by
    nlinarith only [hstep, hend, hlo]
  dsimp only [F] at hresult
  simp only [zero_add] at hresult
  change t ^ 2 * (G t) ^ 2 ≤ _
  linarith

private theorem norm_form {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    (star x ⬝ᵥ x).re = ∑ i, ‖x i‖ ^ 2 := by
  classical
  simpa only [RHLinalg.hermForm, Matrix.one_mulVec, RCLike.re_to_complex] using
    RHLinalg.hermForm_one x

/-- For the actual support-contained channel model, entropy loss controls the
square of the squared L2 resolvent-intertwining error at every positive shift.
The physical density matrices may be singular. -/
theorem entropy_defect_resolvent_stability
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (Φ : QuantumChannel a b) (ρ σ : DensityState a) (support : SupportContained ρ σ)
    (t : ℝ) (ht : 0 < t) :
    let M := supported_relative_modular_model Φ ρ σ support
    let w := (M.data.A + t • 1)⁻¹ *ᵥ M.data.ξ -
      M.data.V *ᵥ ((M.data.B + t • 1)⁻¹ *ᵥ M.data.η)
    t ^ 4 * ((star w ⬝ᵥ w).re) ^ 2 ≤
      4 * (finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ)) := by
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
  have hb := finite_log_resolvent_bound M.hA.1.eigenvalues M.hB.1.eigenvalues u v
    M.hA.eigenvalues_pos M.hB.eigenvalues_pos (fun _ => sq_nonneg _)
    (fun _ => sq_nonneg _) hu hv hnonneg t ht
  rw [← expansionA Real.log, ← expansionB Real.log] at hb
  have htrace : (star η ⬝ᵥ (cfc Real.log B *ᵥ η)).re -
      (star ξ ⬝ᵥ (cfc Real.log A *ᵥ ξ)).re =
      finiteTraceLogRelativeEntropy ρ σ -
        finiteTraceLogRelativeEntropy (Φ.mapState ρ) (Φ.mapState σ) := by
    rw [M.canonicalTraceR, M.canonicalTraceT]
    ring
  rw [htrace] at hb
  have he := energy t ht
  have hg := hnonneg t ht
  have hw := nn ((A + t • 1)⁻¹ *ᵥ ξ - V *ᵥ ((B + t • 1)⁻¹ *ᵥ η))
  have hsquare := mul_self_le_mul_self (mul_nonneg ht.le hw) he
  change t ^ 4 * _ ^ 2 ≤ _
  nlinarith only [hb, mul_le_mul_of_nonneg_left hsquare (sq_nonneg t)]

#print axioms entropy_defect_resolvent_stability

end D5.S3.Quantum.Divergence.EntropyDefectResolventStability
