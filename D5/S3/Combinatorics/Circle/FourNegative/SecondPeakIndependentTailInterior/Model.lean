/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Model
   generality: I
   mirror-B: none(waiver:owning-blueprint-scribe)
   mirror-E: none(waiver:private-consumed-model)
   anchors: [mathlib/module/Mathlib.Data.Rat.Defs]
   utility: none
   digest: Actual rational packet seams and peak slacks for the UXWV order. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Parameters
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Batteries.Tactic.OpenPrivate
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
open scoped BigOperators

private def qHead (z w t rho : ℚ) : Fin 4 → ℚ :=
  let x := t*z*w
  let y := 2*t*z*w*rho
  ![x*(y*(z+1)+1)+1, w*(x*(y+1)+1)+1,
    w*z*(x+1)+z+1, y*(w*z+z+1)+1]
private def qNewHead (z w t rho : ℚ) : Fin 4 → ℚ :=
  let A := qHead z w t rho
  let y := 2*t*z*w*rho
  ![2*A 0, 2*A 1-1, 2*A 2-z-1, 2*A 3-y*(z+1)-1]
private def qMask (z w t rho u D0 W0 : ℚ) : Fin 4 → Fin 4 → ℚ :=
  let x := t*z*w
  let y := 2*t*z*w*rho
  let D1 := x/8
  ![![u,z/2-1,W0,D0], ![3*w/8-u-1,0,0,D1],
    ![w/8,0,4*rho-1-W0,x/2-2-D0-D1], ![0,0,y/2-4*rho,1]]
private def qMass (z w t rho u D0 W0 : ℚ) (row bank : Fin 4) : ℚ :=
  ∑ chain : Fin 4, qMask z w t rho u D0 W0 bank chain *
    (if row = 0 then qHead z w t rho chain else qNewHead z w t rho chain)
private def qNegative (z w t rho : ℚ) (row bank : Fin 4) : ℚ :=
  let N := (t*z*w)*(2*t*z*w*rho)*z*w-1
  let A := qHead z w t rho
  let B := qNewHead z w t rho
  if row = 0 then ![(A 1-N)/2,(A 0-N)/2,(A 3-N)/2,(A 2-N)/2] bank
  else ![(B 1-(2*N+1))/2,(A 0-(2*N+1))/2,
    (B 3-(2*N+1))/2,(B 2-(2*N+1))/2] bank
private def qPeak (z w t rho u D0 W0 : ℚ) (row bank : Fin 4) : ℚ :=
  let m := qMass z w t rho u D0 W0 row
  let n := qNegative z w t rho row
  let e := if row = 0 then 0 else qHead z w t rho 0
  ![e+m 0,e+m 0+n 0+m 1,e+m 0+n 0+m 1+n 1+m 2,
    e+m 0+n 0+m 1+n 1+m 2+n 2+m 3] bank
private def qExpr (z w t rho u D0 W0 : ℚ)
    (row kind bank : Fin 4) : ℚ :=
  let peak := qPeak z w t rho u D0 W0 row bank
  let N := (t*z*w)*(2*t*z*w*rho)*z*w-1
  if kind = 0 then peak + qNegative z w t rho row bank
  else (if row = 0 then (N-1)/2 else N) - peak

private def evenChartExpr (mode endpoint : Fin 2) (Z V T R : ℚ)
    (row kind bank : Fin 4) : ℚ :=
  let z := if mode = 0 then 4 else Z+8
  let w := 4*z*(V+1)
  let t := T+1
  let rho := R+1
  let K : ℚ := if endpoint = 0 then 1 else 4
  let u := if mode = 0 then 2*(V+1)-1 else 2*(V+1)
  qExpr z w (2*t) rho u (t*(w+3*z+2)/4-(K-1)/2) (K*rho-1) row kind bank

private def boundaryChartExpr (mode : Fin 3) (endpoint : Fin 2) (Z V R : ℚ)
    (row kind bank : Fin 4) : ℚ :=
  let z := if mode = 0 then 4 else if mode = 1 then 8 else Z+16
  let w := 4*z*(V+1)
  let rho := R+1
  let eps : ℚ := if endpoint = 0 then 0 else 1/2
  let u := if mode = 0 then 2*(V+1)-1 else 2*(V+1)
  let D0 := if mode = 0 then w/8 else if mode = 1 then w/8+2 else (w+3*z)/8
  let W0 := if mode = 0 then 4*rho-1 else
    (if mode = 1 then 7/2 else 3/2)*rho-1-eps
  qExpr z w 1 rho u D0 W0 row kind bank

private theorem qExpr_affine (z w t rho u D0 D1 W0 W1 h : ℚ)
    (row kind bank : Fin 4) :
    qExpr z w t rho u ((1-h)*D0+h*D1) ((1-h)*W0+h*W1) row kind bank =
    (1-h)*qExpr z w t rho u D0 W0 row kind bank +
      h*qExpr z w t rho u D1 W1 row kind bank := by
  fin_cases row <;> fin_cases kind <;> fin_cases bank <;>
    norm_num [qExpr,qPeak,qNegative,qMass,qMask,qHead,qNewHead,Fin.sum_univ_succ] <;> ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
