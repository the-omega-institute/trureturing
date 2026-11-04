/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/Algebra
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact original equal-tail heads and division-free scaled seam windows. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

/-! Exact equal-tail polynomial windows. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail

private def A (x p s : ℤ) : ℤ := 1+x+x*(2*s*p*x)+x*(2*s*p*x)*(p*x)
private def B (x p s : ℤ) : ℤ := 1+p*x+x*(p*x)+x*(2*s*p*x)*(p*x)
private def L (x p : ℤ) : ℤ := 1+p*x+(p*x)^2+x*(p*x)^2
private def K (x p s : ℤ) : ℤ := 1+2*s*p*x+(2*s*p*x)*(p*x)+(2*s*p*x)*(p*x)^2
private def SU (x p s : ℤ) : ℤ := 2*B x p s-1
private def SV (x p : ℤ) : ℤ := 2*L x p-1-p*x
private def SW (x p s : ℤ) : ℤ := 2*K x p s-(1+2*s*p*x+(2*s*p*x)*(p*x))

/-- Four times each doubled seam, followed by four times its exact head slack.
The mask and V arguments are scaled by four so no truncated division occurs. -/
private def scaledGates (x p s alpha m4 v4 j4 eps : ℤ) : Fin 12 → ℤ :=
  let e1 := 8*(alpha+1)*K x p s-2*s*(m4+4)*L x p
  let e2 := 8*A x p s+2*v4*B x p s-2*s*(j4+4)*L x p
  let e3 := (2*v4+8)*B x p s-2*s*(j4+4)*L x p
  let f1 := 8*eps*A x p s+8*(alpha+1)*SW x p s-2*s*(m4+4)*SV x p
  let f2 := 16*A x p s+2*v4*SU x p s-2*s*(j4+4)*SV x p
  let f3 := (2*v4+8)*SU x p s-2*s*(j4+4)*SV x p
  ![e1,4*(K x p s-1)-e1,e2,4*(A x p s-1)-e2,
    e3,4*(B x p s-1)-e3,f1,4*(SW x p s-1)-f1,
    f2,4*(A x p s-1)-f2,f3,4*(SU x p s-1)-f3]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
