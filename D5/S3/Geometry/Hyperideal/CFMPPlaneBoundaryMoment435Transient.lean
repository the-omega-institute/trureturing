import D5.S3.Geometry.Hyperideal.CFMPPlaneDualConormal435Transient

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Matrix Interval BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open CFMPLorentzLiftSurface435Transient CFMPNativePullbackMetric435Transient
open CFMPSimplexDirection435Transient CFMPPlaneMomentDivergence435Transient
open CFMPPlaneEdgeCofactor435Transient CFMPPlaneDualConormal435Transient

namespace CFMPPlaneBoundaryMoment435Transient

theorem edgePoint_mem (e : Fin 3) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    edgePoint e r ∈ triangle 1 := by
  fin_cases e
  · change 0 ≤ (0 : ℝ) ∧ 0 ≤ r ∧ 0+r ≤ 1
    exact ⟨le_rfl,hr.1,by simpa using hr.2⟩
  · change 0 ≤ r ∧ 0 ≤ (0 : ℝ) ∧ r+0 ≤ 1
    exact ⟨hr.1,le_rfl,by simpa using hr.2⟩
  · change 0 ≤ 1-r ∧ 0 ≤ r ∧ 1-r+r ≤ 1
    exact ⟨by linarith [hr.2],hr.1,by linarith⟩

-- The two diagonal parametrizations in coordinate FTC describe the same closed edge.
theorem coordinate_boundary_moment (g : Fin 6 → ℝ) (a : Fin 3 → ℝ) (C : ℝ)
    (hq : ∀ z ∈ triangle 1, Q g z ≠ 0) :
    (∫ z in triangle 1, 2*C*moment g a z/(Q g z)^2) =
      ∑ e : Fin 3, ∫ r in (0 : ℝ)..1, referenceFlux g a C e r := by
  have hQ : Continuous (Q g) := by unfold Q;fun_prop
  have hX : ContinuousOn (fluxX g a C) (triangle 1) := by
    unfold fluxX
    exact (by fun_prop : Continuous (fun z : ℝ × ℝ => C*(a 1-a 0*z.1))).continuousOn.div
      hQ.continuousOn hq
  have hY : ContinuousOn (fluxY g a C) (triangle 1) := by
    unfold fluxY
    exact (by fun_prop : Continuous (fun z : ℝ × ℝ => C*(a 2-a 0*z.2))).continuousOn.div
      hQ.continuousOn hq
  have hc (e : Fin 3) : Continuous (edgePoint e) := by
    fin_cases e
    · change Continuous (fun r : ℝ => ((0 : ℝ),r))
      fun_prop
    · change Continuous (fun r : ℝ => (r,(0 : ℝ)))
      fun_prop
    · change Continuous (fun r : ℝ => (1-r,r))
      fun_prop
  have hiX (e : Fin 3) : IntervalIntegrable (fun r => fluxX g a C (edgePoint e r))
      volume (0 : ℝ) 1 :=
    (hX.comp' (hc e).continuousOn (fun r hr => edgePoint_mem e r hr)).intervalIntegrable_of_Icc
      (by norm_num)
  have hiY (e : Fin 3) : IntervalIntegrable (fun r => fluxY g a C (edgePoint e r))
      volume (0 : ℝ) 1 :=
    (hY.comp' (hc e).continuousOn (fun r hr => edgePoint_mem e r hr)).intervalIntegrable_of_Icc
      (by norm_num)
  have hAlt : IntervalIntegrable (fun r => fluxY g a C (r,1-r)) volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    apply hY.comp' (by fun_prop : Continuous (fun r : ℝ => (r,1-r))).continuousOn
    intro r hr
    exact ⟨hr.1,by linarith [hr.2],by linarith⟩
  have hdiag : (∫ r in (0 : ℝ)..1, fluxY g a C (r,1-r)) =
      ∫ r in (0 : ℝ)..1, fluxY g a C (1-r,r) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun r : ℝ => fluxY g a C (r,1-r)) (a := 0) (b := 1) 1
    calc
      _ = ∫ r in (0 : ℝ)..1, fluxY g a C (1-r,1-(1-r)) := by
        simpa only [sub_self,sub_zero] using h.symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro r hr
        change fluxY g a C (1-r,1-(1-r)) = fluxY g a C (1-r,r)
        rw [show (1 : ℝ)-(1-r)=r by ring]
  have hx2 := hiX 2
  have hx0 := hiX 0
  have hy2 := hiY 2
  have hy1 := hiY 1
  change IntervalIntegrable (fun r => fluxX g a C (1-r,r)) volume (0 : ℝ) 1 at hx2
  change IntervalIntegrable (fun r => fluxX g a C (0,r)) volume (0 : ℝ) 1 at hx0
  change IntervalIntegrable (fun r => fluxY g a C (1-r,r)) volume (0 : ℝ) 1 at hy2
  change IntervalIntegrable (fun r => fluxY g a C (r,0)) volume (0 : ℝ) 1 at hy1
  rw [triangle_moment g a C hq,intervalIntegral.integral_sub hx2 hx0,
    intervalIntegral.integral_sub hAlt hy1,hdiag]
  simp only [Fin.sum_univ_three]
  change _ = (∫ r in (0 : ℝ)..1, -fluxX g a C (0,r)) +
    (∫ r in (0 : ℝ)..1, -fluxY g a C (r,0)) +
    (∫ r in (0 : ℝ)..1, fluxX g a C (1-r,r)+fluxY g a C (1-r,r))
  rw [intervalIntegral.integral_neg,intervalIntegral.integral_neg,
    intervalIntegral.integral_add hx2 hy2]
  ring

def nativeSpeed (V0 b c : W) (e : Fin 3) (r : ℝ) : ℝ :=
  let Y := rawPoint V0 b c e r
  let D := rawTangent b c e
  Real.sqrt (dotProduct ((nativeMatrix Y).mulVec D) ((nativeMatrix Y).mulVec D) /
    (nativeMap Y 2)^2)

-- This joins coordinate FTC to the speed of the same actual native coordinate curve.
-- It does not identify the remaining coordinate area integral with native H2 measure.
theorem native_speed_boundary_moment (V0 b c : W)
    (hG : (gram (pairingEntries V0 b c)).det < 0) (a : Fin 3 → ℝ)
    (hq : ∀ z ∈ triangle 1, 0 < Q (pairingEntries V0 b c) z)
    (hd : ∀ e : Fin 3, ∀ r ∈ Icc (0 : ℝ) 1,
      delta (rawPoint V0 b c e r) ≠ 0) :
    (∫ z in triangle 1,
      2*Real.sqrt (-(gram (pairingEntries V0 b c)).det)*
        moment (pairingEntries V0 b c) a z/(Q (pairingEntries V0 b c) z)^2) =
      ∑ e : Fin 3, lorentz (basisPoint V0 b c a) (dualUnit V0 b c e) *
        (∫ r in (0 : ℝ)..1, nativeSpeed V0 b c e r) := by
  rw [coordinate_boundary_moment _ _ _ (fun z hz => (hq z hz).ne')]
  apply Finset.sum_congr rfl
  intro e he
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  have hri : r ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hr
  have hqr : 0 < radius (rawPoint V0 b c e r) := by
    rw [(raw_edge_pairings V0 b c e r).1]
    exact hq _ (edgePoint_mem e r hri)
  exact native_edge_flux V0 b c hG a e r hqr (hd e r hri)

end CFMPPlaneBoundaryMoment435Transient

run_cmd do
  let name := ``CFMPPlaneBoundaryMoment435Transient.native_speed_boundary_moment
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP395 native boundary moment absent from checked environment"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP395 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP395 CHECKED {name} axioms={axioms}"
