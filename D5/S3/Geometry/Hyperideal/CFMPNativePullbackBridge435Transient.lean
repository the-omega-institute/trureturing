import D5.S3.Geometry.Hyperideal.CFMPNativePullbackMetric435Transient

noncomputable section
set_option autoImplicit false
open scoped Matrix
open D5.S3.Geometry.Hyperideal.LengthGramBody
open CFMPLorentzLiftSurface435Transient
open CFMPNativePullbackMetric435Transient

namespace CFMPNativePullbackBridge435Transient

theorem liftMatrix_nativeMap (U : W) (hU : 0 < radius U) (hd : delta U ≠ 0) :
    liftMatrix (nativeMap U) =
      !![delta U / Real.sqrt (radius U), 0, -U 0 * delta U / (Real.sqrt (radius U))^2;
         0, delta U / Real.sqrt (radius U), -U 1 * delta U / (Real.sqrt (radius U))^2;
         U 0 / Real.sqrt (radius U), U 1 / Real.sqrt (radius U), 1-U 2*delta U/(Real.sqrt (radius U))^2;
         U 0 / Real.sqrt (radius U), U 1 / Real.sqrt (radius U), 1-U 3*delta U/(Real.sqrt (radius U))^2] := by
  let s := Real.sqrt (radius U)
  let d := delta U
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hU).ne'
  have hd' : d ≠ 0 := hd
  have hsq : s^2 = -((U 0)^2+(U 1)^2+(U 2)^2-(U 3)^2) := by
    rw [Real.sq_sqrt hU.le]
    simp [radius, lorentz, Fin.sum_univ_four, pow_two]
    <;> ring
  have hquad2 : s^2-(U 0)^2-(U 1)^2+d^2 = 2*s^2-2*U 2*d := by
    dsimp [d, delta]
    nlinarith [hsq]
  have hquad3 : s^2-(U 0)^2-(U 1)^2-d^2 = 2*s^2-2*U 3*d := by
    dsimp [d, delta]
    nlinarith [hsq]
  have hc2 : ((nativeMap U 2)^2-(nativeMap U 0)^2-(nativeMap U 1)^2+1) /
      (2*(nativeMap U 2)^2) = 1-U 2*d/s^2 := by
    change ((s/d)^2-(U 0/d)^2-(U 1/d)^2+1)/(2*(s/d)^2) = _
    calc
      _ = (s^2-(U 0)^2-(U 1)^2+d^2)/(2*s^2) := by field_simp [hs,hd'] <;> ring
      _ = (2*s^2-2*U 2*d)/(2*s^2) := by rw [hquad2]
      _ = _ := by field_simp [hs] <;> ring
  have hc3 : ((nativeMap U 2)^2-(nativeMap U 0)^2-(nativeMap U 1)^2-1) /
      (2*(nativeMap U 2)^2) = 1-U 3*d/s^2 := by
    change ((s/d)^2-(U 0/d)^2-(U 1/d)^2-1)/(2*(s/d)^2) = _
    calc
      _ = (s^2-(U 0)^2-(U 1)^2-d^2)/(2*s^2) := by field_simp [hs,hd'] <;> ring
      _ = (2*s^2-2*U 3*d)/(2*s^2) := by rw [hquad3]
      _ = _ := by field_simp [hs] <;> ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [liftMatrix, hc2, hc3]
  all_goals try simp [nativeMap, Matrix.vecHead, Matrix.vecTail]
  all_goals change _ = _
  all_goals field_simp [show Real.sqrt (radius U) ≠ 0 from hs, hd]
  all_goals ring

theorem derivative_intertwining (U v : W) (hU : 0 < radius U) (hd : delta U ≠ 0) :
    (liftMatrix (nativeMap U)).mulVec ((nativeMatrix U).mulVec v) =
      normalizedTangent U v := by
  let s := Real.sqrt (radius U)
  let d := delta U
  let b := lorentz U v
  let e := v 3-v 2
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hU).ne'
  have hd' : d ≠ 0 := hd
  have hsq : s^2 = -((U 0)^2+(U 1)^2+(U 2)^2-(U 3)^2) := by
    rw [Real.sq_sqrt hU.le]
    simp [radius, lorentz, Fin.sum_univ_four, pow_two]
    <;> ring
  have hc2 : (U 0)^2+(U 1)^2+s^2-U 2*d=U 3*d := by
    dsimp [d,delta]
    nlinarith [hsq]
  have hc3 : (U 0)^2+(U 1)^2+s^2-U 3*d=U 2*d := by
    dsimp [d,delta]
    nlinarith [hsq]
  have hb : U 0*v 0+U 1*v 1-b = -U 2*v 2+U 3*v 3 := by
    dsimp [b,lorentz]
    simp [Fin.sum_univ_four]
    <;> ring
  have hN : (nativeMatrix U).mulVec v =
      ![v 0/d-U 0*e/d^2, v 1/d-U 1*e/d^2, -b/(s*d)-s*e/d^2] := by
    ext i
    fin_cases i <;> simp [nativeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    all_goals dsimp [s,d,b,e]
    all_goals field_simp [show Real.sqrt (radius U) ≠ 0 from hs, hd]
    all_goals try simp [lorentz, Fin.sum_univ_four]
    all_goals ring
  rw [liftMatrix_nativeMap U hU hd, hN]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, normalizedTangent]
    dsimp [s,d,b,e]
    field_simp [show Real.sqrt (radius U) ≠ 0 from hs, hd]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, normalizedTangent]
    dsimp [s,d,b,e]
    field_simp [show Real.sqrt (radius U) ≠ 0 from hs, hd]
    ring
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
    change U 0/s*(v 0/d-U 0*e/d^2)+U 1/s*(v 1/d-U 1*e/d^2)+
        (1-U 2*d/s^2)*(-b/(s*d)-s*e/d^2) = _
    calc
      _ = (U 0*v 0+U 1*v 1-b)/(s*d) -
          ((U 0)^2+(U 1)^2+s^2-U 2*d)*e/(s*d^2)+b*U 2/s^3 := by
        field_simp [hs,hd']; ring
      _ = (-U 2*v 2+U 3*v 3)/(s*d) - U 3*d*e/(s*d^2)+b*U 2/s^3 := by rw [hb,hc2]
      _ = _ := by
        change _ = s⁻¹*v 2+(b/s^3)*U 2
        dsimp [d,delta,e]
        field_simp [hs,show U 3-U 2 ≠ 0 from hd']; ring
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
    change U 0/s*(v 0/d-U 0*e/d^2)+U 1/s*(v 1/d-U 1*e/d^2)+
        (1-U 3*d/s^2)*(-b/(s*d)-s*e/d^2) = _
    calc
      _ = (U 0*v 0+U 1*v 1-b)/(s*d) -
          ((U 0)^2+(U 1)^2+s^2-U 3*d)*e/(s*d^2)+b*U 3/s^3 := by
        field_simp [hs,hd']; ring
      _ = (-U 2*v 2+U 3*v 3)/(s*d) - U 2*d*e/(s*d^2)+b*U 3/s^3 := by rw [hb,hc3]
      _ = _ := by
        change _ = s⁻¹*v 3+(b/s^3)*U 3
        dsimp [d,delta,e]
        field_simp [hs,show U 3-U 2 ≠ 0 from hd']; ring

theorem coordinate_pullback_pairing (U v w : W) (hU : 0 < radius U) (hd : delta U ≠ 0) :
    dotProduct ((nativeMatrix U).mulVec v) ((nativeMatrix U).mulVec w) /
        (nativeMap U 2)^2 =
      lorentz v w/radius U+lorentz U v*lorentz U w/(radius U)^2 := by
  have hs : Real.sqrt (radius U) ≠ 0 := (Real.sqrt_pos.mpr hU).ne'
  have hh : nativeMap U 2 ≠ 0 := div_ne_zero hs hd
  rw [← liftMatrix_lorentz (nativeMap U) _ _ hh,
    derivative_intertwining U v hU hd,derivative_intertwining U w hU hd]
  exact normalizedTangent_lorentz U v w hU

end CFMPNativePullbackBridge435Transient
