/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakParityTail/StripAlgebra
   generality: I
   mirror-B: none(waiver:private-consumed-implementation)
   mirror-E: none(waiver:private-consumed-implementation)
   anchors: [mathlib/module/Mathlib.Data.Rat.Defs]
   utility: none
   digest: Full-domain parity-tail physical source construction. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Model
import Lean.Elab.Tactic.Omega

/-!
The rational heads, moduli and terminal order come from the LowX model.
The parity-tail masks determine the six consumed strip sides through exact
polynomial identities and nonnegative corner interpolation.
The ordinary source is uxwv-parity-lattice-linear-tail-20261102.py,
SHA256 babbd52e84602a942b9aa943cf4ebeea4c3937450fc71f87bae3f031c558e275.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail

open scoped BigOperators
open private qHead qNewHead qModulus qTerminal
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Model

private def parityMask (u z h t alpha S : ℚ) : Fin 4 → Fin 4 → ℚ :=
  let x := u*z
  let q := h*t
  ![![alpha,0,(x-u-2)*q,0],
    ![0,0,u*q+(h-S)*t,u*(z/2-1)],
    ![x*h/2-1-alpha,0,0,0],
    ![0,z/2-1,2*q-1-(h-S)*t,u-1]]

private def parityMass (u z h t alpha S : ℚ) (isNew : Bool) (r : Fin 4) : ℚ :=
  ∑ j : Fin 4, parityMask u z h t alpha S r j *
    (if isNew then qNewHead z (u*z) h (h*t) j else qHead z (u*z) h (h*t) j)

private def parityPeak (u z h t alpha S : ℚ) (isNew : Bool) : Fin 4 → ℚ :=
  let m := parityMass u z h t alpha S isNew
  let n := qTerminal z (u*z) h (h*t) isNew
  let H := if isNew then qHead z (u*z) h (h*t) 0 else 0
  ![H+m 0,H+m 0+n 0+m 1,H+m 0+n 0+m 1+n 1+m 2,
    H+m 0+n 0+m 1+n 1+m 2+n 2+m 3]

-- These are scaled masses, with the selected equality already substituted.
-- There is no variable denominator and no certificate hypothesis.
private def stripScale (u z : ℚ) : ℚ := 8*u*(z+1)
private def selectorNumerator (u z h S delta : ℚ) : ℚ :=
  (u^2*z+1)*h+(u*z+1)*S-15*u*z/8+delta

private def scaledMass (u z h t S delta : ℚ) (isNew : Bool) : Fin 4 → ℚ :=
  let F := if isNew then qNewHead z (u*z) h (h*t) else qHead z (u*z) h (h*t)
  let C := stripScale u z
  let P := selectorNumerator u z h S delta
  ![4*P*F 0+C*((u*z-u-2)*(h*t)*F 2),
    C*((u*(h*t)+(h-S)*t)*F 2+u*(z/2-1)*F 3),
    C*((u*z*h/2-1)*F 0)-4*P*F 0,
    C*((z/2-1)*F 1+(2*(h*t)-1-(h-S)*t)*F 2+(u-1)*F 3)]

private def scaledPeak (u z h t S delta : ℚ) (isNew : Bool) : Fin 4 → ℚ :=
  let m := scaledMass u z h t S delta isNew
  let n := fun r => stripScale u z * qTerminal z (u*z) h (h*t) isNew r
  let H := if isNew then stripScale u z * qHead z (u*z) h (h*t) 0 else 0
  ![H+m 0,H+m 0+n 0+m 1,H+m 0+n 0+m 1+n 1+m 2,
    H+m 0+n 0+m 1+n 1+m 2+n 2+m 3]

private def stripGate (u z h t S delta : ℚ) : Fin 6 → ℚ :=
  let C := stripScale u z
  let n := qTerminal z (u*z) h (h*t) false
  let p := scaledPeak u z h t S delta false
  let v := scaledPeak u z h t S delta true
  let N := qModulus z (u*z) h (h*t) false
  ![p 0+C*n 0,p 1+C*n 1,p 2+C*n 2,C*N-v 0,C*N-v 1,C*N-v 2]

private theorem scaled_mass_eq (u z h t alpha S delta : ℚ)
    (hid : 2*u*(z+1)*alpha=selectorNumerator u z h S delta)
    (isNew : Bool) (r : Fin 4) :
    scaledMass u z h t S delta isNew r =
      stripScale u z * parityMass u z h t alpha S isNew r := by
  rw [scaledMass,←hid]
  cases isNew <;> fin_cases r <;>
    norm_num [parityMass,parityMask,stripScale,Fin.sum_univ_succ] <;> ring <;> simp

private theorem scaled_peak_eq (u z h t alpha S delta : ℚ)
    (hid : 2*u*(z+1)*alpha=selectorNumerator u z h S delta)
    (isNew : Bool) (r : Fin 4) :
    scaledPeak u z h t S delta isNew r =
      stripScale u z * parityPeak u z h t alpha S isNew r := by
  cases isNew <;> fin_cases r <;>
    simp only [scaledPeak,parityPeak,scaled_mass_eq u z h t alpha S delta hid,
      Bool.false_eq_true,↓reduceIte,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_succ,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply] <;> ring

-- Exact polynomial forms remove cancellations before the four corner substitutions.
private def polynomialGate (u z h t S delta : ℚ) : Fin 6 → ℚ :=
  ![
    (16*S*h*t*u^3*z^4 + 16*S*h*t*u^3*z^3 + 16*S*h*t*u^2*z^3 + 16*S*h*t*u^2*z^2 + 8*S*u^2*z^2 +
    16*S*u*z + 8*S + 16*delta*h*t*u^2*z^3 + 16*delta*h*t*u^2*z^2 + 8*delta*u*z + 8*delta +
    16*h^2*t*u^4*z^4 + 16*h^2*t*u^4*z^3 - 16*h^2*t*u^3*z^4 - 32*h^2*t*u^3*z^3 - 16*h^2*t*u^3*z^2
    - 16*h^2*t*u^2*z^3 - 16*h^2*t*u^2*z^2 - 30*h*t*u^3*z^4 - 30*h*t*u^3*z^3 + 16*h*t*u^2*z^3 +
    16*h*t*u^2*z^2 - 16*h*t*u^2*z - 16*h*t*u^2 - 32*h*t*u*z^2 - 64*h*t*u*z - 32*h*t*u +
    8*h*u^3*z^3 + 16*h*u^3*z^2 + 8*h*u^2*z^2 + 16*h*u^2*z + 8*h*u*z + 8*h - 15*u^2*z^2 + u*z +
    16*u)/2,
    (-16*S*t*u*z^2 - 32*S*t*u*z - 16*S*t*u + 8*S*u^2*z^2 + 16*S*u*z + 8*S + 16*delta*h*t*u^2*z^3 +
    16*delta*h*t*u^2*z^2 + 8*delta*u*z + 8*delta + 2*h*t*u^3*z^4 + 2*h*t*u^3*z^3 -
    32*h*t*u^3*z^2 - 32*h*t*u^3*z + 16*h*t*u^2*z^3 + 32*h*t*u^2*z^2 + 16*h*t*u^2*z -
    16*h*t*u*z^2 - 32*h*t*u*z - 16*h*t*u + 8*h*u^3*z^3 + 16*h*u^3*z^2 + 8*h*u^2*z^2 + 16*h*u^2*z
    + 8*h*u*z + 8*h + u^2*z^2 - 16*u^2 + 17*u*z + 32*u)/2,
    8*u*(z + 1)*(-S*h*t*u^2*z^3 - S*h*t*u*z^2 - S*t*z - S*t + h^2*t*u^2*z^3 - h^2*t*u*z^2 -
    2*h*t*u^2*z^2 - 2*h*t*u^2*z + 2*h*t*u*z^2 + 2*h*t*u*z - h*t*z - h*t + h*u^2*z^2 + h*u*z - u
    + 2),
    -16*S*h*t*u^3*z^4 - 16*S*h*t*u^3*z^3 - 16*S*h*t*u^2*z^3 - 16*S*h*t*u^2*z^2 - 8*S*u^2*z^2 -
    16*S*u*z - 8*S - 16*delta*h*t*u^2*z^3 - 16*delta*h*t*u^2*z^2 - 8*delta*u*z - 8*delta +
    16*h^2*t*u^3*z^4 + 32*h^2*t*u^3*z^3 + 16*h^2*t*u^3*z^2 + 16*h^2*t*u^2*z^3 + 16*h^2*t*u^2*z^2
    + 14*h*t*u^3*z^4 - 2*h*t*u^3*z^3 - 16*h*t*u^3*z^2 - 8*h*t*u^2*z^3 - 8*h*t*u^2*z^2 +
    8*h*t*u^2*z + 8*h*t*u^2 + 16*h*t*u*z^2 + 32*h*t*u*z + 16*h*t*u - 8*h*u^3*z^2 - 8*h*u^2*z -
    8*h*u*z - 8*h + 7*u^2*z^2 - 8*u^2*z - u*z - 16*u,
    8*S*t*u*z^2 + 16*S*t*u*z + 8*S*t*u - 8*S*u^2*z^2 - 16*S*u*z - 8*S - 16*delta*h*t*u^2*z^3 -
    16*delta*h*t*u^2*z^2 - 8*delta*u*z - 8*delta + 6*h*t*u^3*z^4 - 2*h*t*u^3*z^3 + 8*h*t*u^3*z^2
    + 16*h*t*u^3*z - 8*h*t*u^2*z^3 - 16*h*t*u^2*z^2 - 8*h*t*u^2*z + 8*h*t*u*z^2 + 16*h*t*u*z +
    8*h*t*u - 8*h*u^3*z^3 - 16*h*u^3*z^2 - 8*h*u^2*z^2 - 16*h*u^2*z - 8*h*u*z - 8*h + 3*u^2*z^2
    - 4*u^2*z + 8*u^2 - 9*u*z - 24*u,
    8*u*(z + 1)*(2*S*h*t*u^2*z^3 + 2*S*h*t*u*z^2 + S*t*z + S*t + 2*h^2*t*u*z^2 + 2*h*t*u^2*z^2 +
    2*h*t*u^2*z - h*t*u*z^2 - h*t*u*z + h*t*z + h*t - 2*h*u^2*z^2 - 2*h*u*z + u - 2)]

private theorem strip_gate_polynomial_eq (u z h t S delta : ℚ) (i : Fin 6) :
    stripGate u z h t S delta i = polynomialGate u z h t S delta i := by
  fin_cases i <;>
    norm_num [stripGate,scaledPeak,scaledMass,selectorNumerator,stripScale,
      qHead,qNewHead,qModulus,qTerminal,polynomialGate] <;> ring

set_option maxRecDepth 8192 in
private theorem polynomial_corner_0 (U Z H T : ℚ)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (highS highDelta : Bool) :
    0 ≤ polynomialGate (4+U) (16+Z) (2*(16+Z)+H) (1+T)
      (if highS then 7*(16+Z)/4 else 2)
      (if highDelta then 2*((4+U)-1) else 0) 0 := by
  cases highS <;> cases highDelta <;>
    dsimp [polynomialGate] <;> ring_nf <;> positivity

set_option maxRecDepth 8192 in
private theorem polynomial_corner_1 (U Z H T : ℚ)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (highS highDelta : Bool) :
    0 ≤ polynomialGate (4+U) (16+Z) (2*(16+Z)+H) (1+T)
      (if highS then 7*(16+Z)/4 else 2)
      (if highDelta then 2*((4+U)-1) else 0) 1 := by
  cases highS <;> cases highDelta <;>
    dsimp [polynomialGate] <;> ring_nf <;> positivity

set_option maxRecDepth 8192 in
private theorem polynomial_corner_2 (U Z H T : ℚ)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (highS highDelta : Bool) :
    0 ≤ polynomialGate (4+U) (16+Z) (2*(16+Z)+H) (1+T)
      (if highS then 7*(16+Z)/4 else 2)
      (if highDelta then 2*((4+U)-1) else 0) 2 := by
  cases highS <;> cases highDelta <;>
    dsimp [polynomialGate] <;> ring_nf <;> positivity

set_option maxRecDepth 8192 in
private theorem polynomial_corner_3 (U Z H T : ℚ)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (highS highDelta : Bool) :
    0 ≤ polynomialGate (4+U) (16+Z) (2*(16+Z)+H) (1+T)
      (if highS then 7*(16+Z)/4 else 2)
      (if highDelta then 2*((4+U)-1) else 0) 3 := by
  cases highS <;> cases highDelta <;>
    dsimp [polynomialGate] <;> ring_nf <;> positivity

set_option maxRecDepth 8192 in
private theorem polynomial_corner_4 (U Z H T : ℚ)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (highS highDelta : Bool) :
    0 ≤ polynomialGate (4+U) (16+Z) (2*(16+Z)+H) (1+T)
      (if highS then 7*(16+Z)/4 else 2)
      (if highDelta then 2*((4+U)-1) else 0) 4 := by
  cases highS <;> cases highDelta <;>
    dsimp [polynomialGate] <;> ring_nf <;> positivity

set_option maxRecDepth 8192 in
private theorem polynomial_corner_5 (U Z H T : ℚ)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (highS highDelta : Bool) :
    0 ≤ polynomialGate (4+U) (16+Z) (2*(16+Z)+H) (1+T)
      (if highS then 7*(16+Z)/4 else 2)
      (if highDelta then 2*((4+U)-1) else 0) 5 := by
  cases highS <;> cases highDelta <;>
    dsimp [polynomialGate] <;> ring_nf <;> positivity

-- The six sides on the entire nonnegative cone of increments.
private theorem strip_corners (U Z H T : ℚ)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (highS highDelta : Bool) (i : Fin 6) :
    0 ≤ stripGate (4+U) (16+Z) (2*(16+Z)+H) (1+T)
      (if highS then 7*(16+Z)/4 else 2)
      (if highDelta then 2*((4+U)-1) else 0) i := by
  rw [strip_gate_polynomial_eq]
  fin_cases i
  · exact polynomial_corner_0 U Z H T hU hZ hH hT highS highDelta
  · exact polynomial_corner_1 U Z H T hU hZ hH hT highS highDelta
  · exact polynomial_corner_2 U Z H T hU hZ hH hT highS highDelta
  · exact polynomial_corner_3 U Z H T hU hZ hH hT highS highDelta
  · exact polynomial_corner_4 U Z H T hU hZ hH hT highS highDelta
  · exact polynomial_corner_5 U Z H T hU hZ hH hT highS highDelta

-- Exact joint affinity in S and delta. In particular no S*delta term is hidden.
private theorem strip_rectangle_identity (u z h t S delta : ℚ) (i : Fin 6) :
    (7*z-8)*(2*(u-1))*stripGate u z h t S delta i =
      (7*z-4*S)*(2*(u-1)-delta)*stripGate u z h t 2 0 i +
      (4*S-8)*(2*(u-1)-delta)*stripGate u z h t (7*z/4) 0 i +
      (7*z-4*S)*delta*stripGate u z h t 2 (2*(u-1)) i +
      (4*S-8)*delta*stripGate u z h t (7*z/4) (2*(u-1)) i := by
  fin_cases i <;>
    norm_num [stripGate,scaledPeak,scaledMass,selectorNumerator,stripScale,
      qHead,qNewHead,qModulus,qTerminal] <;> ring

private theorem strip_gates (u z h t S delta : ℚ)
    (hu : 4 ≤ u) (hz : 16 ≤ z) (hh : 2*z ≤ h) (ht : 1 ≤ t)
    (hS : 2 ≤ S) (hS4 : 4*S ≤ 7*z)
    (hd0 : 0 ≤ delta) (hdJ : delta ≤ 2*(u-1)) (i : Fin 6) :
    0 ≤ stripGate u z h t S delta i := by
  have corner (p q : Bool) :
      0 ≤ stripGate u z h t (if p then 7*z/4 else 2)
        (if q then 2*(u-1) else 0) i := by
    have hc := strip_corners (u-4) (z-16) (h-2*z) (t-1)
      (by linarith) (by linarith) (by linarith) (by linarith) p q i
    simpa only [show (4:ℚ)+(u-4)=u by ring,
      show (16:ℚ)+(z-16)=z by ring,
      show 2*z+(h-2*z)=h by ring,show (1:ℚ)+(t-1)=t by ring] using hc
  have h00 := corner false false
  have h10 := corner true false
  have h01 := corner false true
  have h11 := corner true true
  simp only [Bool.false_eq_true,↓reduceIte] at h00 h10 h01 h11
  have hw0 : 0 ≤ 7*z-4*S := by linarith
  have hw1 : 0 ≤ 4*S-8 := by linarith
  have hv : 0 ≤ 2*(u-1)-delta := by linarith
  have hsum := add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg hw0 hv) h00)
    (mul_nonneg (mul_nonneg hw1 hv) h10))
    (mul_nonneg (mul_nonneg hw0 hd0) h01))
    (mul_nonneg (mul_nonneg hw1 hd0) h11)
  rw [←strip_rectangle_identity u z h t S delta i] at hsum
  have hden : 0 < (7*z-8)*(2*(u-1)) :=
    mul_pos (by linarith) (by linarith)
  exact (mul_nonneg_iff_of_pos_left hden).mp (by simpa only [mul_assoc] using hsum)

/-- The three exact old seams and three exact enlarged upper peaks.
The selector equation and rectangle bounds are consumed, not assumed outputs. -/
private theorem six_strip_sides (u z h t alpha S delta : ℚ)
    (hu : 4 ≤ u) (hz : 16 ≤ z) (hh : 2*z ≤ h) (ht : 1 ≤ t)
    (hS : 2 ≤ S) (hS4 : 4*S ≤ 7*z)
    (hd0 : 0 ≤ delta) (hdJ : delta ≤ 2*(u-1))
    (hid : 2*u*(z+1)*alpha=selectorNumerator u z h S delta) :
    (∀ r : Fin 4, r.val < 3 → 0 ≤ parityPeak u z h t alpha S false r +
      qTerminal z (u*z) h (h*t) false r) ∧
    (∀ r : Fin 4, r.val < 3 → parityPeak u z h t alpha S true r ≤
      qModulus z (u*z) h (h*t) false) := by
  have hC : 0 < stripScale u z := by dsimp [stripScale]; positivity
  have hg := strip_gates u z h t S delta hu hz hh ht hS hS4 hd0 hdJ
  constructor
  · intro r hr
    have hv := hg ⟨r.val,by omega⟩
    have he : stripGate u z h t S delta ⟨r.val,by omega⟩ =
        stripScale u z*(parityPeak u z h t alpha S false r+
          qTerminal z (u*z) h (h*t) false r) := by
      fin_cases r <;> norm_num at hr
      all_goals simp [stripGate,scaled_peak_eq u z h t alpha S delta hid] <;> ring
    rw [he] at hv
    exact (mul_nonneg_iff_of_pos_left hC).mp hv
  · intro r hr
    have hv := hg ⟨r.val+3,by omega⟩
    have he : stripGate u z h t S delta ⟨r.val+3,by omega⟩ =
        stripScale u z*(qModulus z (u*z) h (h*t) false-
          parityPeak u z h t alpha S true r) := by
      fin_cases r <;> norm_num at hr
      all_goals simp [stripGate,scaled_peak_eq u z h t alpha S delta hid] <;> ring
    rw [he] at hv
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hC).mp hv)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakParityTail
