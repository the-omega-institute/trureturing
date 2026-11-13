/- GID: D5/S3/Analytic/ConvexBarrier/PartialMinimization
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/PartialMinimization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Analytic.ConvexBarrier.ScalarEnvelope

/-!
The concrete partial minimum supplier for an arbitrary scalar power-cone
LHSCB. All objects are constructed from `hF`; no minimizer, compactness,
stationarity, regularity, envelope, or self-concordance premise is added.

Mathematical attribution: Rui-Jin Zhang, Wenhao Fu and Yu-Hong Dai,
The optimal barrier parameter of the three-dimensional power cone,
arXiv:2611.06404v1, Lemma 3.1 and Theorem 3.5, printed pp. 6, 9.
This module is source only. No Lean process has run on this delivery.
It does not prove the separate Dikin/duality and curve-construction gaps.
-/

open Set Filter
open scoped Topology
open D5.S3.Geometry.PowerCone

namespace D5.S3.Analytic.ConvexBarrier

theorem minimizer_fiber_hessian_pos {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) :
    0 < hessian F (minimizerLift hF u) vertical vertical := by
  have hp : minimizerLift hF u ∈ coneInterior c := by
    simpa [minimizerLift] using (fiberMinimizer_spec hF hu).1
  rw [← hF.diagonal_two_eq_hessian hp vertical]
  exact hF.hessian_pos _ hp vertical (by simp [vertical])

/-- The derivative of the minimizer is the actual scalar inverse Hessian
block formula, not a hypothesis about the graph. -/
theorem fiberMinimizer_derivative {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) (h : Base) :
    fderiv ℝ (fiberMinimizer hF) u h =
      -hessian F (minimizerLift hF u) (h,0) vertical /
        hessian F (minimizerLift hF u) vertical vertical := by
  have hk := minimizer_fiber_hessian_pos hF hu
  have he := minimizer_hessian_orthogonal hF hu h
  have hv : minimizerTangent hF u h = (h,(0:ℝ)) +
      (fderiv ℝ (fiberMinimizer hF) u h) • vertical := by simp [vertical]
  rw [hv] at he
  simp only [hessian,map_add,map_smul,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul] at he
  apply (eq_div_iff hk.ne').mpr
  dsimp only [hessian]
  linarith

/-- The diagonal Schur complement, strictly positive for every nonzero base
direction by the lifted Hessian identity. -/
theorem partialMinimum_schur {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) (h : Base) :
    diagonal 2 quadrant (partialMinimum hF) u h =
      hessian F (minimizerLift hF u) (h,0) (h,0) -
        (hessian F (minimizerLift hF u) (h,0) vertical)^2 /
          hessian F (minimizerLift hF u) vertical vertical := by
  have hp : minimizerLift hF u ∈ coneInterior c := by
    simpa [minimizerLift] using (fiberMinimizer_spec hF hu).1
  rw [partialMinimum_second hF hu,
    hF.diagonal_two_eq_hessian hp]
  have hv : minimizerTangent hF u h = (h,(0:ℝ)) +
      (fderiv ℝ (fiberMinimizer hF) u h) • vertical := by simp [vertical]
  have hs := (hF.smooth.contDiffAt
    (hF.domain_open.mem_nhds (fiberMinimizer_spec hF hu).1)).isSymmSndFDerivAt (by norm_num)
  have hsym : hessian F (minimizerLift hF u) vertical (h,0) =
      hessian F (minimizerLift hF u) (h,0) vertical := hs vertical (h,0)
  simp only [hv,hessian,map_add,map_smul,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  change _ = hessian F (minimizerLift hF u) (h,0) (h,0) - _
  change fderiv ℝ (fderiv ℝ F) (minimizerLift hF u) vertical (h,0) = _ at hsym
  rw [hsym]
  simp only [fiberMinimizer_derivative hF hu]
  have hk := minimizer_fiber_hessian_pos hF hu
  dsimp only [hessian] at hk ⊢
  field_simp [hk.ne']
  <;> ring

theorem partialMinimum_hessian_pos {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) (h : Base) (hh : h ≠ 0) :
    0 < diagonal 2 quadrant (partialMinimum hF) u h := by
  rw [partialMinimum_second hF hu]
  apply hF.hessian_pos _ (fiberMinimizer_spec hF hu).1
  intro he
  exact hh (congrArg Prod.fst he)

theorem partialMinimum_self_concordant {c ν : ℝ} {F : ScalarPoint → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {u : Base} (hu : u ∈ quadrant) (h : Base) :
    |diagonal 3 quadrant (partialMinimum hF) u h| ≤
      2 * diagonal 2 quadrant (partialMinimum hF) u h *
        Real.sqrt (diagonal 2 quadrant (partialMinimum hF) u h) := by
  have hp : minimizerLift hF u ∈ coneInterior c := by
    simpa [minimizerLift] using (fiberMinimizer_spec hF hu).1
  simpa only [partialMinimum_third hF hu,partialMinimum_second hF hu] using
    hF.self_concordant _ hp (minimizerTangent hF u h)

/-- The actual arbitrary-barrier partial minimum is an LHSCB on the full
projected domain, with the original logarithmic homogeneity parameter. -/
theorem IsLHSCB.partialMinimum {c ν : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {F : ScalarPoint → ℝ} (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) :
    IsLHSCB ν quadrant quadrantBoundary (partialMinimum hF) := by
  refine ⟨hF.parameter,quadrant_isOpen,partialMinimum_smooth hF,?_,?_,?_,?_⟩
  · exact fun u hu h hh => partialMinimum_hessian_pos hF hu h hh
  · exact fun u hu h => partialMinimum_self_concordant hF hu h
  · exact fun u hu t ht => partialMinimum_homogeneous hF hu ht
  · exact fun b hb u hu hlim => partialMinimum_boundary_blowup hc hc1 hF hb u hu hlim

theorem partialMinimum_on_actual_projection {c ν : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {F : ScalarPoint → ℝ} (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) :
    IsLHSCB ν (interior (Prod.fst '' (closedCone c : Set ScalarPoint)))
      (frontier (Prod.fst '' (closedCone c : Set ScalarPoint))) (partialMinimum hF) := by
  simpa only [project_closed,← quadrant_eq_interior,← quadrantBoundary_eq_frontier] using
    IsLHSCB.partialMinimum hc hc1 hF

/-- F1 supplier. The minimum object, attained unique minimizer, C2 graph and
C3 LHSCB envelope are outputs of only the original `IsLHSCB` assumptions.
The derivative formulas are exported by `partialMinimum_first`,
`partialMinimum_second`, `partialMinimum_third`, `partialMinimum_schur`,
and `fiberMinimizer_derivative` from this import closure.
-/
theorem scalar_partial_minimization {c ν : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {F : ScalarPoint → ℝ} (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F) :
    IsLHSCB ν quadrant quadrantBoundary (partialMinimum hF) ∧
    ContDiffOn ℝ 2 (fiberMinimizer hF) quadrant ∧
    (∀ u ∈ quadrant,
      (u,fiberMinimizer hF u) ∈ coneInterior c ∧
      (∀ w : ℝ, (u,w) ∈ coneInterior c → partialMinimum hF u ≤ F (u,w)) ∧
      (∀ w : ℝ, (u,w) ∈ coneInterior c →
        (F (u,w) = partialMinimum hF u ↔ w = fiberMinimizer hF u))) := by
  refine ⟨IsLHSCB.partialMinimum hc hc1 hF,fiberMinimizer_smooth hF,?_⟩
  intro u hu
  obtain ⟨hp,hm⟩ := fiberMinimizer_spec hF hu
  refine ⟨hp,hm,?_⟩
  intro w hw
  constructor
  · intro he
    exact fiberMinimizer_unique hF hu hw (fun v hv => by
      change F (u,w) ≤ F (u,v)
      rw [he]
      exact hm v hv)
  · rintro rfl
    rfl

end D5.S3.Analytic.ConvexBarrier
