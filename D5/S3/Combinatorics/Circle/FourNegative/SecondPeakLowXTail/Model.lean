/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLowXTail/Model
   generality: I
   mirror-B: none(waiver:private-consumed-implementation)
   mirror-E: none(waiver:private-consumed-implementation)
   anchors: [mathlib/module/Mathlib.Data.Rat.Defs]
   utility: none
   digest: Exact rational heads, masks, terminal values and six low-X margins. -/
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail

open scoped BigOperators

-- Source: uxwv-b-above-d-low-x-20261102.py, raw_expressions().
-- Attribution follows that sealed source: Pro's earlier seed/discrepancy;
-- caller's gap extension, collision rule, affine/chord argument and low-block exchange.
-- Coordinates are rational here. The physical dyadic parameter lift is external.
private def qHead (z x h q : ℚ) : Fin 4 → ℚ :=
  let w := h*x
  let y := 2*x*q
  ![1+x+x*y+x*y*z, 1+w+w*x+w*x*y,
    1+z+w*z+w*z*x, 1+y+y*z+y*w*z]

private def qNewHead (z x h q : ℚ) : Fin 4 → ℚ :=
  let A := qHead z x h q
  let y := 2*x*q
  ![2*A 0, 2*A 1-1, 2*A 2-z-1, 2*A 3-y*(z+1)-1]

private def qModulus (z x h q : ℚ) (isNew : Bool) : ℚ :=
  let P := x*(2*x*q)*z*(h*x)
  if isNew then 2*P-1 else P-1

-- Banks are ordered as in raw_expressions(); columns are U,V,W,X.
-- E = x/(2*z^2), D = x/4, S = h*x/(2*z); E=1 is included.
private def qMask (z x h q r e : ℚ) : Fin 4 → Fin 4 → ℚ :=
  let E := x/(2*z^2)
  let D := x/4
  let S := h*x/(2*z)
  ![![0,z/4,0,D-E], ![S-1,z/4-1,r,D],
    ![h*x/2-S,0,2*q-1-r-e,E-1], ![0,0,x*q-2*q+e,0]]

private def qMass (z x h q r e : ℚ) (isNew : Bool) (bank : Fin 4) : ℚ :=
  ∑ chain : Fin 4, qMask z x h q r e bank chain *
    (if isNew then qNewHead z x h q chain else qHead z x h q chain)

-- Terminals U,X,W,V. The new X terminal uses the OLD head A.
private def qTerminal (z x h q : ℚ) (isNew : Bool) : Fin 4 → ℚ :=
  let A := qHead z x h q
  let B := qNewHead z x h q
  let M := qModulus z x h q isNew
  if isNew then ![(B 1-M)/2,(A 0-M)/2,(B 3-M)/2,(B 2-M)/2]
  else ![(A 1-M)/2,(A 0-M)/2,(A 3-M)/2,(A 2-M)/2]

private def qPeak (z x h q r e : ℚ) (isNew : Bool) : Fin 4 → ℚ :=
  let m := qMass z x h q r e isNew
  let n := qTerminal z x h q isNew
  let start := if isNew then qHead z x h q 0 else 0
  ![start+m 0, start+m 0+n 0+m 1, start+m 0+n 0+m 1+n 1+m 2,
    start+m 0+n 0+m 1+n 1+m 2+n 2+m 3]

private def qSeam (z x h q r e : ℚ) (isNew : Bool) (bank : Fin 4) : ℚ :=
  qPeak z x h q r e isNew bank + qTerminal z x h q isNew bank

private def qSlack (z x h q r e : ℚ) (isNew : Bool) (bank : Fin 4) : ℚ :=
  (qModulus z x h q isNew-1)/2 - qPeak z x h q r e isNew bank

-- The six live margins: three old lower seams and the first three new upper peaks.
-- The last new peak and the opposite sides are supplied by physical comparisons.
private def margin (z x h q r e : ℚ) : Fin 6 → ℚ :=
  ![qSeam z x h q r e false 0, qSeam z x h q r e false 1,
    qSeam z x h q r e false 2, qSlack z x h q r e true 0,
    qSlack z x h q r e true 1, qSlack z x h q r e true 2]

private def smallTZero (z x h t : ℚ) (i : Fin 6) : ℚ :=
  margin z x h (h*t) 0 0 i

private def smallTPositive (z x e h : ℚ) (i : Fin 6) : ℚ :=
  margin z x h (x*e/4) 0 e i

private def largeTZero (z x h u beta : ℚ) (i : Fin 6) : ℚ :=
  margin z x h (h*z^2*u/2) (beta*u) 0 i

private def largeTPositive (z x e h beta : ℚ) (i : Fin 6) : ℚ :=
  margin z x h (x*e/4) (beta*x*e/(2*h*z^2)) e i

private def cap (z x e : ℚ) : ℚ := x*e/(2*z^2)

-- The coefficient of h^2 in second is -bend, for both collision choices.
private def bend (z x : ℚ) : ℚ := x*(x+1)*(z^2-z+1)/z

private def second (z x e h beta : ℚ) : ℚ :=
  h * largeTPositive z x e h beta 4

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail
