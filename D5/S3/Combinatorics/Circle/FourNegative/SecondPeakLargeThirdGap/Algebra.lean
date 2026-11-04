/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/Algebra
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Exact four-chain and independent dyadic polynomial expressions. -/
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Batteries.Tactic.OpenPrivate
import Lean.Elab.Tactic.Omega

/-! Exact four-chain and independent dyadic polynomial expressions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap

private def DD (y z : ℤ) : ℤ := y*(z+1)+1
private def AA (x y z : ℤ) : ℤ := x*DD y z+1
private def BB (x y t : ℤ) : ℤ := x*t*(y+1)+t+1
private def LL (x z t : ℤ) : ℤ := x*z*t+z*t+z+1
private def MM (y z t : ℤ) : ℤ := t*y*z+DD y z
private def NN (x y z t : ℤ) : ℤ := x*y*z*t-1
private def BBn (x y t : ℤ) : ℤ := 2*BB x y t-1
private def LLn (x z t : ℤ) : ℤ := 2*LL x z t-z-1
private def MMn (y z t : ℤ) : ℤ := 2*MM y z t-DD y z
private def EE (x y z t : ℤ) : ℤ :=
  2*NN x y z t-MM y z t-(t-1)*AA x y z
private def KK (x y z t : ℤ) : ℤ :=
  LL x z t*(AA x y z-DD y z-2)-EE x y z t*(z+1)
private def JJ (x y z t lam : ℤ) : ℤ :=
  LL x z t*(AA x y z-1)-2*lam*LL x z t*LLn x z t-KK x y z t

private def dyadicT (x R : ℤ) : ℤ := 2*x*R
private def dyadicZ (x R Z : ℤ) : ℤ := 2*x*dyadicT x R*Z
private def dyadicY (x R Z lam : ℤ) : ℤ := 2*dyadicZ x R Z*lam

/-- The order is fixed here and consumed, without omissions, by Selection. -/
private def gate (i : Fin 14) (x R Z lam : ℤ) : ℤ :=
  let t := dyadicT x R
  let z := dyadicZ x R Z
  let y := dyadicY x R Z lam
  let A := AA x y z
  let B := BB x y t
  let L := LL x z t
  let M := MM y z t
  let Bn := BBn x y t
  let Ln := LLn x z t
  let Mn := MMn y z t
  ![B+M-2*A, 2*B-2*A+Mn-1, 2*A-B-1, 2*A-2*B,
    EE x y z t, 2*lam*L*(z-1)-EE x y z t, A-1-2*lam*L,
    KK x y z t, JJ x y z t lam, B-lam*L, Bn-lam*Ln,
    2*lam*L-B-1, 2*lam*Ln-Bn-1, NN x y z t-A] i

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
