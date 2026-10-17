import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Abel

/-!
Transient source-only candidate for the unchanged finite-exceptional-value inverse problem.
Target pin: Lean v4.33.0; Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
This file has NOT been elaborated, compiled, kernel checked, or admitted.
Named helpers organize this candidate only; no non-bind-only witness is claimed.
-/

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology NNReal

namespace CFMPInverseAE

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The ambient function need only be continuous on the measurable target. -/
theorem measurableSet_affine_fiber {Ω : Set E} {G : E → E}
    (hΩ : MeasurableSet Ω) (hG : ContinuousOn G Ω) (c : E) :
    MeasurableSet {y | y ∈ Ω ∧ G y = y - c} := by
  have hdiff : ContinuousOn (fun y => G y - (y - c)) Ω :=
    hG.sub (continuous_id.sub continuous_const).continuousOn
  obtain ⟨Z, hZ, hZeq⟩ :=
    continuousOn_iff_isClosed.mp hdiff ({0} : Set E) isClosed_singleton
  have hset : {y | y ∈ Ω ∧ G y = y - c} = Z ∩ Ω := by
    calc
      {y | y ∈ Ω ∧ G y = y - c} =
          (fun y => G y - (y - c)) ⁻¹' ({0} : Set E) ∩ Ω := by
        ext y
        simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, mem_singleton_iff,
          sub_eq_zero, and_comm]
      _ = Z ∩ Ω := hZeq
  rw [hset]
  exact hZ.measurableSet.inter hΩ

variable [FiniteDimensional ℝ E]

/-- Affine equality on a measurable set plus a.e. actual differentiability gives
the actual identity derivative a.e. on that same set. The density supplier is
applied only after imposing actual differentiability at EVERY input point. -/
theorem ae_hasFDerivAt_id_of_affineOn (μ : Measure E) [IsAddHaarMeasure μ]
    {G : E → E} {S : Set E} (hS : MeasurableSet S) (c : E)
    (hEq : ∀ y ∈ S, G y = y - c)
    (hDiff : ∀ᵐ y ∂μ.restrict S, DifferentiableAt ℝ G y) :
    ∀ᵐ y ∂μ.restrict S, HasFDerivAt G (ContinuousLinearMap.id ℝ E) y := by
  -- Finite-dimensional real normed spaces are proper and hence complete.
  letI : CompleteSpace E := inferInstance
  let Q : Set E := {y | DifferentiableAt ℝ G y}
  let R : Set E := S ∩ Q
  have hQ : MeasurableSet Q := measurableSet_of_differentiableAt ℝ G
  have hR : MeasurableSet R := hS.inter hQ
  have hAll : ∀ y ∈ R, HasFDerivWithinAt G (fderiv ℝ G y) R y := by
    intro y hy
    exact (show DifferentiableAt ℝ G y from hy.2).hasFDerivAt.hasFDerivWithinAt
  have hApprox : ApproximatesLinearOn G (ContinuousLinearMap.id ℝ E) R 0 := by
    intro a ha b hb
    have hcancel :
        G a - G b - (ContinuousLinearMap.id ℝ E) (a - b) = 0 := by
      rw [hEq a ha.1, hEq b hb.1, ContinuousLinearMap.id_apply]
      abel
    rw [hcancel]
    simp
  have hNorm := hApprox.norm_fderiv_sub_le μ hR (fderiv ℝ G) hAll
  have hOnR :
      ∀ᵐ y ∂μ.restrict R, HasFDerivAt G (ContinuousLinearMap.id ℝ E) y := by
    filter_upwards [hNorm, ae_restrict_mem hR] with y hy hyR
    have hzero : fderiv ℝ G y - ContinuousLinearMap.id ℝ E = 0 :=
      nnnorm_eq_zero.mp (le_antisymm hy zero_le)
    have heq : fderiv ℝ G y = ContinuousLinearMap.id ℝ E := sub_eq_zero.mp hzero
    rw [← heq]
    exact (show DifferentiableAt ℝ G y from hyR.2).hasFDerivAt
  have hDiffAmbient : ∀ᵐ y ∂μ, y ∈ S → y ∈ Q :=
    (ae_restrict_iff' hS).mp hDiff
  have hRS : R =ᵐ[μ] S := by
    filter_upwards [hDiffAmbient] with y hy
    apply propext
    exact ⟨fun h => h.1, fun h => ⟨h, hy h⟩⟩
  have hMeasures : μ.restrict R = μ.restrict S := Measure.restrict_congr_set hRS
  rw [hMeasures] at hOnR
  exact hOnR

end Normed

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Elementary symmetry transfer from a symmetric operator to a right inverse.
No positive semidefiniteness, finite dimension, or linear equivalence is used. -/
theorem symmetric_of_symmetric_right_inverse {L B : E →L[ℝ] E}
    (hL : ∀ u v, inner ℝ (L u) v = inner ℝ u (L v))
    (hLB : L.comp B = ContinuousLinearMap.id ℝ E) :
    ∀ u v, inner ℝ (B u) v = inner ℝ u (B v) := by
  have happ (w : E) : L (B w) = w := by
    have hw := congrArg (fun T : E →L[ℝ] E => T w) hLB
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hw
  intro u v
  calc
    inner ℝ (B u) v = inner ℝ (B u) (L (B v)) := by rw [happ]
    _ = inner ℝ (L (B u)) (B v) := (hL (B u) (B v)).symm
    _ = inner ℝ u (B v) := by rw [happ]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Stronger core with arbitrary D and U, and with G unconstrained outside Ω.
The only derivative premise for F is actual symmetric differentiability on U. -/
theorem ae_symmetric_derivative_of_finite_exceptional_values
    (μ : Measure E) [IsAddHaarMeasure μ]
    {D Ω U : Set E} {F G : E → E} {K : ℝ≥0}
    (hΩ : IsOpen Ω) (hLip : LipschitzOnWith K G Ω)
    (hMaps : MapsTo G Ω D)
    (hInv : ∀ y ∈ Ω, G y + F (G y) = y)
    (hF : ∀ x ∈ U, ∃ A : E →L[ℝ] E,
      HasFDerivAt F A x ∧ ∀ u v, inner ℝ (A u) v = inner ℝ u (A v))
    (hFinite : (F '' (D \ U)).Finite) :
    ∀ᵐ y ∂μ.restrict Ω, ∃ B : E →L[ℝ] E,
      HasFDerivAt G B y ∧ ∀ u v, inner ℝ (B u) v = inner ℝ u (B v) := by
  classical
  have hDiff : ∀ᵐ y ∂μ.restrict Ω, DifferentiableAt ℝ G y := by
    filter_upwards [hLip.ae_differentiableWithinAt (μ := μ) hΩ.measurableSet,
      ae_restrict_mem hΩ.measurableSet] with y hy hyΩ
    exact hy.differentiableAt (hΩ.mem_nhds hyΩ)
  have hDiffAmbient : ∀ᵐ y ∂μ, y ∈ Ω → DifferentiableAt ℝ G y :=
    (ae_restrict_iff' hΩ.measurableSet).mp hDiff
  let S (c : E) : Set E := {y | y ∈ Ω ∧ G y = y - c}
  have hS (c : E) : MeasurableSet (S c) :=
    measurableSet_affine_fiber hΩ.measurableSet hLip.continuousOn c
  have hFiber (c : E) :
      ∀ᵐ y ∂μ, y ∈ S c → HasFDerivAt G (ContinuousLinearMap.id ℝ E) y := by
    apply (ae_restrict_iff' (hS c)).mp
    apply ae_hasFDerivAt_id_of_affineOn μ (hS c) c
    · intro y hy
      exact hy.2
    · apply (ae_restrict_iff' (hS c)).mpr
      filter_upwards [hDiffAmbient] with y hy hyS
      exact hy hyS.1
  have hFiniteEvent : ∀ᵐ y ∂μ, ∀ c ∈ F '' (D \ U),
      y ∈ S c → HasFDerivAt G (ContinuousLinearMap.id ℝ E) y :=
    hFinite.eventually_all.mpr (fun c _ => hFiber c)
  filter_upwards [ae_restrict_mem hΩ.measurableSet, hDiff,
    ae_restrict_of_ae hFiniteEvent] with y hyΩ hyDiff hyFinite
  by_cases hyGood : G y ∈ U
  · obtain ⟨A, hA, hASym⟩ := hF (G y) hyGood
    let B : E →L[ℝ] E := fderiv ℝ G y
    have hB : HasFDerivAt G B y := hyDiff.hasFDerivAt
    have hT : HasFDerivAt (fun x : E => x + F x)
        (ContinuousLinearMap.id ℝ E + A) (G y) :=
      (hasFDerivAt_id (G y)).add hA
    have hComp : HasFDerivAt (fun z : E => G z + F (G z))
        ((ContinuousLinearMap.id ℝ E + A).comp B) y := by
      simpa only [Function.comp_def] using hT.comp y hB
    have hEventual : (fun z : E => G z + F (G z)) =ᶠ[𝓝 y] id :=
      Filter.eventually_of_mem (hΩ.mem_nhds hyΩ) (fun z hz => hInv z hz)
    have hId : HasFDerivAt id ((ContinuousLinearMap.id ℝ E + A).comp B) y :=
      hComp.congr_of_eventuallyEq hEventual.symm
    have hLB : (ContinuousLinearMap.id ℝ E + A).comp B =
        ContinuousLinearMap.id ℝ E := hId.unique (hasFDerivAt_id y)
    have hLSym : ∀ u v, inner ℝ ((ContinuousLinearMap.id ℝ E + A) u) v =
        inner ℝ u ((ContinuousLinearMap.id ℝ E + A) v) := by
      intro u v
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
        inner_add_left, inner_add_right]
      rw [hASym u v]
    exact ⟨B, hB, symmetric_of_symmetric_right_inverse hLSym hLB⟩
  · have hc : F (G y) ∈ F '' (D \ U) :=
      ⟨G y, ⟨hMaps hyΩ, hyGood⟩, rfl⟩
    have hyS : y ∈ S (F (G y)) :=
      ⟨hyΩ, eq_sub_iff_add_eq.mpr (hInv y hyΩ)⟩
    refine ⟨ContinuousLinearMap.id ℝ E, hyFinite (F (G y)) hc hyS, ?_⟩
    intro u v
    rfl

/-- The original telescope, specialized to canonical finite-dimensional inner-product
volume. The homeomorphism and both ambient agreements identify the SAME inverse G.
The named unused premises are retained here only to match the requested original setting. -/
theorem original_inverse_ae_symmetric_derivative
    {D Ω U : Set E} {F G : E → E} {K : ℝ≥0}
    (_hD : IsOpen D) (hΩ : IsOpen Ω) (_hFContinuous : ContinuousOn F D)
    (e : D ≃ₜ Ω)
    (he : ∀ x : D, (e x : E) = (x : E) + F (x : E))
    (hG : ∀ y : Ω, G (y : E) = (e.symm y : E))
    (hLip : LipschitzOnWith K G Ω)
    (_hU : IsOpen U) (_hUD : U ⊆ D)
    (hF : ∀ x ∈ U, ∃ A : E →L[ℝ] E,
      HasFDerivAt F A x ∧
      (∀ u v, inner ℝ (A u) v = inner ℝ u (A v)) ∧
      ∀ v, 0 ≤ inner ℝ (A v) v)
    (hFinite : (F '' (D \ U)).Finite) :
    ∀ᵐ y ∂(volume : Measure E).restrict Ω, ∃ B : E →L[ℝ] E,
      HasFDerivAt G B y ∧ ∀ u v, inner ℝ (B u) v = inner ℝ u (B v) := by
  have hMaps : MapsTo G Ω D := by
    intro y hy
    rw [hG ⟨y, hy⟩]
    exact (e.symm ⟨y, hy⟩).property
  have hInv : ∀ y ∈ Ω, G y + F (G y) = y := by
    intro y hy
    let yΩ : Ω := ⟨y, hy⟩
    have hForward := he (e.symm yΩ)
    have hSame : (e (e.symm yΩ) : E) = y :=
      congrArg (fun z : Ω => (z : E)) (e.apply_symm_apply yΩ)
    calc
      G y + F (G y) = (e.symm yΩ : E) + F (e.symm yΩ : E) := by rw [hG yΩ]
      _ = (e (e.symm yΩ) : E) := hForward.symm
      _ = y := hSame
  apply ae_symmetric_derivative_of_finite_exceptional_values
    (volume : Measure E) hΩ hLip hMaps hInv
  · intro x hx
    obtain ⟨A, hA, hASym, _hPSD⟩ := hF x hx
    exact ⟨A, hA, hASym⟩
  · exact hFinite

end Inner

end CFMPInverseAE
