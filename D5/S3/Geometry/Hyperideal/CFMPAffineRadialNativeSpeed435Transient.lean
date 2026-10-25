import D5.S3.Geometry.Hyperideal.CFMPNativePullbackBridge435Transient

noncomputable section
set_option autoImplicit false
open scoped Matrix
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open CFMPNativePullbackMetric435Transient
open CFMPNativePullbackBridge435Transient

namespace CFMPAffineRadialNativeSpeed435Transient

-- Exact native metric speed of the affine radial parameter, including its endpoints.
theorem affine_native_squared_speed
    (Y Z : Fin 4 → ℝ) (a b chi r : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hchi : 1 < chi)
    (hYY : lorentz Y Y = -a^2) (hZZ : lorentz Z Z = -b^2)
    (hYZ : lorentz Y Z = -a*b*chi) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hd : delta ((1-r) • Y+r • Z) ≠ 0) :
    let U := (1-r) • Y+r • Z
    let v := Z-Y
    let Q := a^2*(1-r)^2+2*a*b*chi*r*(1-r)+b^2*r^2
    dotProduct ((nativeMatrix U).mulVec v) ((nativeMatrix U).mulVec v) /
        (nativeMap U 2)^2 =
      (a*b*Real.sqrt (chi^2-1)/Q)^2 := by
  let U := (1-r) • Y+r • Z
  let v := Z-Y
  let Q := a^2*(1-r)^2+2*a*b*chi*r*(1-r)+b^2*r^2
  have hZY : lorentz Z Y = -a*b*chi := by rw [lorentz_symm,hYZ]
  have hsum : 0 < a*(1-r)+b*r := by
    by_cases hz : r = 0
    · simpa [hz] using ha
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg ha.le (sub_nonneg.mpr hr.2))
        (mul_pos hb (lt_of_le_of_ne hr.1 (Ne.symm hz)))
  have hQ : 0 < Q := by
    have hchi0 : 0 ≤ chi-1 := sub_nonneg.mpr hchi.le
    have hn : 0 ≤ 2*a*b*(chi-1)*r*(1-r) :=
      mul_nonneg (mul_nonneg (by positivity) hr.1) (sub_nonneg.mpr hr.2)
    have he : Q = (a*(1-r)+b*r)^2+2*a*b*(chi-1)*r*(1-r) := by
      dsimp [Q]
      ring
    rw [he]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hsum) hn
  have hUU : radius U = Q := by
    dsimp only [radius,U]
    rw [lorentz_linear,hYY,hZZ,hYZ,hZY]
    dsimp [Q]
    ring
  have hv : v = (-1 : ℝ) • Y+(1 : ℝ) • Z := by
    ext i
    simp [v]
    ring
  have hvv : lorentz v v = -a^2-b^2+2*a*b*chi := by
    rw [hv,lorentz_linear Y Z Y Z (-1) 1 (-1) 1,hYY,hZZ,hYZ,hZY]
    ring
  have huv : lorentz U v = (1-r)*(a^2-a*b*chi)+r*(a*b*chi-b^2) := by
    rw [hv]
    dsimp only [U]
    rw [lorentz_linear Y Z Y Z (1-r) r (-1) 1,hYY,hZZ,hYZ,hZY]
    ring
  have hs : (Real.sqrt (chi^2-1))^2 = chi^2-1 :=
    Real.sq_sqrt (by nlinarith)
  change dotProduct ((nativeMatrix U).mulVec v) ((nativeMatrix U).mulVec v) /
    (nativeMap U 2)^2 = (a*b*Real.sqrt (chi^2-1)/Q)^2
  rw [coordinate_pullback_pairing U v v (hUU.symm ▸ hQ) hd,hUU,hvv,huv]
  rw [div_pow,mul_pow,mul_pow,hs]
  field_simp [hQ.ne']
  dsimp [Q]
  ring

end CFMPAffineRadialNativeSpeed435Transient

run_cmd do
  let name := ``CFMPAffineRadialNativeSpeed435Transient.affine_native_squared_speed
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError m!"CFMP458 missing declaration {name}"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP458 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP458 CHECKED {name} axioms={axioms}"
