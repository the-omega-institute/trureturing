/- GID: D5/S3/Quantum/Divergence/LogEqualityResolventRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/LogEqualityResolventRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equal logarithmic readouts force every positive resolvent defect to vanish. -/

import D5.S3.Quantum.Divergence.ResolventFunctionalRigidity
import D5.S3.Weil.ZetaLinear.Sylvester
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Matrix Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology

namespace D5.S3.Quantum.Divergence.LogEqualityResolventRigidity

/-- A positive-shift logarithmic readout has nonnegative derivative. Its
equal endpoint values, including the mass-cancelled limit at infinity,
therefore force all of those derivatives to vanish. -/
private theorem finite_log_equality_resolvents {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (q : κ → ℝ) (u : ι → ℝ) (v : κ → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hmass : ∑ i, u i = ∑ j, v j)
    (hlog : ∑ i, Real.log (p i) * u i = ∑ j, Real.log (q j) * v j)
    (hnonneg : ∀ t : ℝ, 0 < t →
      0 ≤ (∑ i, (p i + t)⁻¹ * u i) - ∑ j, (q j + t)⁻¹ * v j) :
    ∀ t : ℝ, 0 < t → (∑ i, (p i + t)⁻¹ * u i) -
      ∑ j, (q j + t)⁻¹ * v j = 0 := by
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
      rw [hmass]
      ring
    simpa only [← heq, sub_self] using hleft.sub hright
  have hz (t : ℝ) (ht : 0 ≤ t) : F t = 0 := by
    have hlo : 0 ≤ F t := by
      have h := hm (show (0 : ℝ) ∈ Set.Ici 0 from by simp) ht ht
      simpa only [F, zero_add, hlog, sub_self] using h
    have hhi : F t ≤ 0 := ge_of_tendsto hlimit (by
      filter_upwards [eventually_ge_atTop t] with x hx
      exact hm ht (ht.trans hx) hx)
    exact le_antisymm hhi hlo
  intro t ht
  have hevent : F =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    exact hz x hx.le
  exact (hd t ht.le).unique
    ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hevent)

private theorem norm_form {ι : Type*} [Fintype ι] (x : ι → ℂ) :
    (star x ⬝ᵥ x).re = ∑ i, ‖x i‖ ^ 2 := by
  classical
  simpa only [RHLinalg.hermForm, Matrix.one_mulVec, RCLike.re_to_complex] using
    RHLinalg.hermForm_one x

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Equality in the distinguished-vector logarithmic comparison implies
intertwining of every real finite spectral function. Positive definiteness
is required only on these relative modular support carriers. -/
theorem log_equality_forces_functional_intertwining
    (A : Matrix n n ℂ) (B : Matrix m m ℂ) (hA : A.PosDef) (hB : B.PosDef)
    (V : Matrix n m ℂ) (hV : Vᴴ * V ≤ 1) (hAB : Vᴴ * A * V ≤ B)
    (b : m → ℂ)
    (hb : (star (V *ᵥ b) ⬝ᵥ (V *ᵥ b)).re = (star b ⬝ᵥ b).re)
    (hlog : (star (V *ᵥ b) ⬝ᵥ (cfc Real.log A *ᵥ (V *ᵥ b))).re =
      (star b ⬝ᵥ (cfc Real.log B *ᵥ b)).re)
    (f : ℝ → ℝ) : cfc f A *ᵥ (V *ᵥ b) = V *ᵥ (cfc f B *ᵥ b) := by
  classical
  let a := V *ᵥ b
  let u : n → ℝ := fun i => ‖(star (hA.1.eigenvectorUnitary : Matrix n n ℂ) *ᵥ a) i‖ ^ 2
  let v : m → ℝ := fun j => ‖(star (hB.1.eigenvectorUnitary : Matrix m m ℂ) *ᵥ b) j‖ ^ 2
  have expansionA (g : ℝ → ℝ) :
      (star a ⬝ᵥ (cfc g A *ᵥ a)).re = ∑ i, g (hA.1.eigenvalues i) * u i := by
    have hs : cfc g A = RHLinalg.specMap hA.1 g := by rw [hA.1.cfc_eq]; rfl
    rw [hs]
    exact RHLinalg.hermForm_specMap hA.1 g a
  have expansionB (g : ℝ → ℝ) :
      (star b ⬝ᵥ (cfc g B *ᵥ b)).re = ∑ j, g (hB.1.eigenvalues j) * v j := by
    have hs : cfc g B = RHLinalg.specMap hB.1 g := by rw [hB.1.cfc_eq]; rfl
    rw [hs]
    exact RHLinalg.hermForm_specMap hB.1 g b
  have hmass : ∑ i, u i = ∑ j, v j := by
    change (∑ i, ‖(star (hA.1.eigenvectorUnitary : Matrix n n ℂ) *ᵥ a) i‖ ^ 2) = _
    rw [RHLinalg.sum_normSq_unitary_mulVec hA.1 a,
      RHLinalg.sum_normSq_unitary_mulVec hB.1 b, ← norm_form a, ← norm_form b]
    exact hb
  have hlogsum : ∑ i, Real.log (hA.1.eigenvalues i) * u i =
      ∑ j, Real.log (hB.1.eigenvalues j) * v j := by
    rw [← expansionA, ← expansionB]
    exact hlog
  have resolventA (t : ℝ) (ht : 0 < t) :
      (star a ⬝ᵥ ((A + t • (1 : Matrix n n ℂ))⁻¹ *ᵥ a)).re =
        ∑ i, (hA.1.eigenvalues i + t)⁻¹ * u i := by
    rw [← ResolventFunctionalRigidity.cfc_shift_inverse A hA.posSemidef t ht]
    exact expansionA _
  have resolventB (t : ℝ) (ht : 0 < t) :
      (star b ⬝ᵥ ((B + t • (1 : Matrix m m ℂ))⁻¹ *ᵥ b)).re =
        ∑ j, (hB.1.eigenvalues j + t)⁻¹ * v j := by
    rw [← ResolventFunctionalRigidity.cfc_shift_inverse B hB.posSemidef t ht]
    exact expansionB _
  have hnonneg (t : ℝ) (ht : 0 < t) :
      0 ≤ (∑ i, (hA.1.eigenvalues i + t)⁻¹ * u i) -
        ∑ j, (hB.1.eigenvalues j + t)⁻¹ * v j := by
    rw [← resolventA t ht, ← resolventB t ht]
    have hbound := (ResolventDefectRigidity.resolvent_defect_identity_and_bound
      A B hA.posSemidef hB.posSemidef V hV hAB b hb t ht).2.1
    have nn (x : n → ℂ) : 0 ≤ (star x ⬝ᵥ x).re := by
      rw [norm_form]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    exact (mul_nonneg ht.le (nn _)).trans hbound
  have hzero := finite_log_equality_resolvents hA.1.eigenvalues hB.1.eigenvalues u v
    hA.eigenvalues_pos hB.eigenvalues_pos hmass hlogsum hnonneg
  apply ResolventFunctionalRigidity.zero_resolvent_defects_force_functional_intertwining
    A B hA.posSemidef hB.posSemidef V hV hAB b hb _ f
  intro t ht
  rw [resolventA t ht, resolventB t ht]
  exact hzero t ht

#print axioms log_equality_forces_functional_intertwining

end D5.S3.Quantum.Divergence.LogEqualityResolventRigidity
