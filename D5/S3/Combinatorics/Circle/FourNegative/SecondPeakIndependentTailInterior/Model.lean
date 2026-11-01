/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Model
   generality: I
   mirror-B: none(waiver:owning-blueprint-scribe)
   mirror-E: none(waiver:private-consumed-model)
   anchors: [mathlib/module/Mathlib.Data.Rat.Defs]
   utility: none
   digest: Actual rational packet seams and peak slacks for the UXWV order. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Parameters
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior

open scoped BigOperators

private def qHead (z w t rho : ℚ) : Fin 4 → ℚ :=
  let x := 8*t*z*w
  let y := 16*t*z*w*rho
  ![x*(y*(z+1)+1)+1, w*(x*(y+1)+1)+1,
    w*z*(x+1)+z+1, y*(w*z+z+1)+1]
private def qNewHead (z w t rho : ℚ) : Fin 4 → ℚ :=
  let A := qHead z w t rho
  let y := 16*t*z*w*rho
  ![2*A 0, 2*A 1-1, 2*A 2-z-1, 2*A 3-y*(z+1)-1]
private def qMask (z w t rho u P h0 h2 : ℚ) : Fin 4 → Fin 4 → ℚ :=
  let x := 8*t*z*w
  let y := 16*t*z*w*rho
  let D0 := t*(w+3*z+2)
  let D1 := t*z*w
  ![![u,z/2-1,h0,D0], ![3*w/8-u-1,0,0,D1],
    ![w/8,0,h2,x/2-1-D0-D1-P], ![0,0,y/2-1-h0-h2,P]]
private def qMass (z w t rho u P h0 h2 : ℚ) (row bank : Fin 4) : ℚ :=
  ∑ chain : Fin 4, qMask z w t rho u P h0 h2 bank chain *
    (if row = 0 then qHead z w t rho chain else qNewHead z w t rho chain)
private def qNegative (z w t rho : ℚ) (row bank : Fin 4) : ℚ :=
  let N := (8*t*z*w)*(16*t*z*w*rho)*z*w-1
  let A := qHead z w t rho
  let B := qNewHead z w t rho
  if row = 0 then ![(A 1-N)/2,(A 0-N)/2,(A 3-N)/2,(A 2-N)/2] bank
  else ![(B 1-(2*N+1))/2,(A 0-(2*N+1))/2,
    (B 3-(2*N+1))/2,(B 2-(2*N+1))/2] bank
private def qPeak (z w t rho u P h0 h2 : ℚ) (row bank : Fin 4) : ℚ :=
  let m := qMass z w t rho u P h0 h2 row
  let n := qNegative z w t rho row
  let e := if row = 0 then 0 else qHead z w t rho 0
  ![e+m 0,e+m 0+n 0+m 1,e+m 0+n 0+m 1+n 1+m 2,
    e+m 0+n 0+m 1+n 1+m 2+n 2+m 3] bank
private def qExpr (z w t rho u P h0 h2 : ℚ)
    (row kind bank : Fin 4) : ℚ :=
  let peak := qPeak z w t rho u P h0 h2 row bank
  let N := (8*t*z*w)*(16*t*z*w*rho)*z*w-1
  if kind = 0 then peak + qNegative z w t rho row bank
  else (if row = 0 then (N-1)/2 else N) - peak

private def chartExpr (mode : Fin 2) (Z V T R : ℚ) (row kind bank : Fin 4) : ℚ :=
  let z := if mode = 0 then 4 else Z+8
  let w := 4*z*(V+1)
  let t := T+1
  let rho := R+1
  let u := if mode = 0 then 2*(V+1)-1 else 2*(V+1)
  qExpr z w t rho u 1 (rho-1) (3*rho) row kind bank

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
