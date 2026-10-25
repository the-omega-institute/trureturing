import CFMPActualGlobalEnergy259Transient

noncomputable section
universe u260 v260
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped BigOperators Topology ContDiff Matrix
open D5.S3.Geometry.Hyperideal.FourCycleCurvature
open CFMPGenuineLengthNeighborhood435Transient (genuine)
open CFMPOriginalPhysicalEdge237Transient (sourceAngle)
open CFMPOriginalCovolumeNeighborhood251Transient
open CFMPGlobalGenuineCovolume256Transient
open CFMPActualPhysicalHessian258Transient
open CFMPActualGlobalEnergy259Transient

namespace CFMPActualGlobalHessian260Transient

def angleVector (a : Lengths) : Lengths := fun q => sourceAngle a q

theorem angleVector_hasFDerivAt (a : Lengths) (ha : genuine a) :
    HasFDerivAt angleVector (fderiv ℝ angleVector a) a := by
  have hs : ContDiffAt ℝ ∞ angleVector a := by
    apply contDiffAt_pi.mpr
    intro q
    exact CFMPOriginalGlobalSmoothCovolume103Transient.sourceAngle_smooth a ha q
  exact (hs.differentiableAt (by simp)).hasFDerivAt

theorem angleVector_matrix_actual
    (G : RealizationFamily) (hG : realizedFamily G)
    (a : Lengths) (ha : genuine a) (e f : Fin 6) :
    fderiv ℝ angleVector a (Pi.single f 1) e = physicalHessian G a e f := by
  have hc : HasFDerivAt (fun p : Lengths => sourceAngle p e)
      ((ContinuousLinearMap.proj e).comp (fderiv ℝ angleVector a)) a :=
    by
      convert! (hasFDerivAt_apply e (angleVector a)).comp a
        (angleVector_hasFDerivAt a ha) using 1 <;> rfl
  rw [physicalHessian_eq_sourceJacobian G hG a ha]
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply] using
    (congrArg (fun L : Lengths →L[ℝ] ℝ => L (Pi.single f 1)) hc.fderiv).symm

theorem angleVector_direction_actual
    (G : RealizationFamily) (hG : realizedFamily G)
    (a : Lengths) (ha : genuine a) (w : Lengths) (e : Fin 6) :
    fderiv ℝ angleVector a w e =
      ∑ f : Fin 6, w f * physicalHessian G a e f := by
  classical
  have hdecomp : w = ∑ f : Fin 6, w f • Pi.single f (1 : ℝ) := by
    ext q
    simp [Pi.single_apply]
  calc
    _ = fderiv ℝ angleVector a (∑ f : Fin 6, w f • Pi.single f (1 : ℝ)) e := by
      rw [← hdecomp]
    _ = ∑ f : Fin 6, w f * fderiv ℝ angleVector a (Pi.single f 1) e := by
      simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    _ = _ := by simp_rw [angleVector_matrix_actual G hG a ha]

variable {T : Type u260} {E : Type v260}
  [Fintype T] [Fintype E] [DecidableEq E]

def curvatureDifferential (s : Incidence T E) (p : E → ℝ) :
    (E → ℝ) →L[ℝ] (E → ℝ) :=
  ContinuousLinearMap.pi (fun e => -∑ o ∈ star s e,
    (ContinuousLinearMap.proj o.2).comp
      ((fderiv ℝ angleVector (localRead s o.1 p)).comp (localRead s o.1)))

theorem physicalCurvature_hasFDerivAt
    (s : Incidence T E) (p : E → ℝ) (hp : p ∈ globalGenuine s) :
    HasFDerivAt (physicalCurvature s) (curvatureDifferential s p) p := by
  classical
  have hocc (o : T × Fin 6) :
      HasFDerivAt (fun a : E → ℝ => sourceAngle (localRead s o.1 a) o.2)
        ((ContinuousLinearMap.proj o.2).comp
          ((fderiv ℝ angleVector (localRead s o.1 p)).comp (localRead s o.1))) p := by
    exact (hasFDerivAt_apply o.2 (angleVector (localRead s o.1 p))).comp p
      ((angleVector_hasFDerivAt _ (hp o.1)).comp p (localRead s o.1).hasFDerivAt)
  apply hasFDerivAt_pi.mpr
  intro e
  change HasFDerivAt
    (fun a : E → ℝ => 2 * Real.pi - ∑ o ∈ star s e,
      sourceAngle (localRead s o.1 a) o.2)
    (-∑ o ∈ star s e, (ContinuousLinearMap.proj o.2).comp
      ((fderiv ℝ angleVector (localRead s o.1 p)).comp (localRead s o.1))) p
  exact (HasFDerivAt.fun_sum (fun o _ => hocc o)).const_sub (2 * Real.pi)

theorem negative_curvature_bilinear_actual_pullback
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G)
    (p : E → ℝ) (hp : p ∈ globalGenuine s) (v w : E → ℝ) :
    -(∑ e : E, v e * (fderiv ℝ (physicalCurvature s) p w) e) =
      ∑ t : T, ∑ e : Fin 6, ∑ f : Fin 6,
        localRead s t v e * physicalHessian G (localRead s t p) e f *
          localRead s t w f := by
  classical
  have hcoord (e : E) : -(fderiv ℝ (physicalCurvature s) p w) e =
      ∑ o ∈ star s e, fderiv ℝ angleVector (localRead s o.1 p)
        (localRead s o.1 w) o.2 := by
    rw [(physicalCurvature_hasFDerivAt s p hp).fderiv]
    simp [curvatureDifferential]
  calc
    _ = ∑ e : E, v e * (-(fderiv ℝ (physicalCurvature s) p w) e) := by
      simp only [mul_neg,Finset.sum_neg_distrib]
    _ = ∑ e : E, (∑ o ∈ star s e,
        fderiv ℝ angleVector (localRead s o.1 p) (localRead s o.1 w) o.2) * v e := by
      simp_rw [hcoord]
      apply Finset.sum_congr rfl
      intro e _
      exact mul_comm _ _
    _ = ∑ t : T, ∑ e : Fin 6,
        fderiv ℝ angleVector (localRead s t p) (localRead s t w) e *
          localRead s t v e := by
      exact (occurrence_regroup s (fun o =>
        fderiv ℝ angleVector (localRead s o.1 p) (localRead s o.1 w) o.2) v).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro e _
      rw [angleVector_direction_actual G hG _ (hp t)]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro f _
      ring

theorem incidence_square_sum (s : Incidence T E) (v : E → ℝ) :
    (∑ t : T, ∑ q : Fin 6, (localRead s t v q)^2) =
      ∑ e : E, (degree s e : ℝ) * (v e)^2 := by
  classical
  calc
    _ = ∑ o : T × Fin 6, (v (source s o))^2 := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ e : E, ∑ o ∈ star s e, (v (source s o))^2 := by
      symm
      simpa only [D5.S3.Geometry.Hyperideal.FourCycleCurvature.star] using
        Finset.sum_fiberwise (Finset.univ : Finset (T × Fin 6))
          (source s) (fun o => (v (source s o))^2)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      calc
        (∑ o ∈ star s e, (v (source s o))^2) = ∑ _o ∈ star s e, (v e)^2 := by
          apply Finset.sum_congr rfl
          intro o ho
          rw [(Finset.mem_filter.mp ho).2]
        _ = _ := by simp [degree,nsmul_eq_mul]

theorem negative_curvature_degree_bounds
    (s : Incidence T E) (G : RealizationFamily) (hG : realizedFamily G)
    (p : E → ℝ) (hp : p ∈ globalGenuine s) (mu bound : ℝ)
    (hlocal : ∀ (t : T) (z : Lengths),
      mu * (∑ q : Fin 6, (z q)^2) ≤
        (∑ e : Fin 6, ∑ f : Fin 6, z e * physicalHessian G (localRead s t p) e f * z f) ∧
      (∑ e : Fin 6, ∑ f : Fin 6, z e * physicalHessian G (localRead s t p) e f * z f) ≤
        bound * (∑ q : Fin 6, (z q)^2))
    (v : E → ℝ) :
    mu * (∑ e : E, (degree s e : ℝ) * (v e)^2) ≤
      -(∑ e : E, v e * (fderiv ℝ (physicalCurvature s) p v) e) ∧
    -(∑ e : E, v e * (fderiv ℝ (physicalCurvature s) p v) e) ≤
      bound * (∑ e : E, (degree s e : ℝ) * (v e)^2) := by
  rw [negative_curvature_bilinear_actual_pullback s G hG p hp v v,
    ← incidence_square_sum s v]
  constructor
  · calc
      _ = ∑ t : T, mu * (∑ q : Fin 6, (localRead s t v q)^2) := by
        rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum (fun t _ => (hlocal t (localRead s t v)).1)
  · calc
      _ ≤ ∑ t : T, bound * (∑ q : Fin 6, (localRead s t v q)^2) :=
        Finset.sum_le_sum (fun t _ => (hlocal t (localRead s t v)).2)
      _ = _ := by rw [Finset.mul_sum]

end CFMPActualGlobalHessian260Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPActualGlobalHessian260Transient.physicalCurvature_hasFDerivAt,
      ``CFMPActualGlobalHessian260Transient.negative_curvature_bilinear_actual_pullback,
      ``CFMPActualGlobalHessian260Transient.incidence_square_sum,
      ``CFMPActualGlobalHessian260Transient.negative_curvature_degree_bounds] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP260 actual global Hessian theorem absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP260 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP260 CHECKED {name} axioms={axioms}"
