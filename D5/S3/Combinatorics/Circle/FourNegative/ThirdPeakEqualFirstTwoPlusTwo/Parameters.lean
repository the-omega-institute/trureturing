/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualFirstTwoPlusTwo/Parameters
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Polynomial heads and packet windows for original equal first two gaps and third gap d+2. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

/-! The two variables are the original powers
`x = 2^a` and `t = 2^d`, with `b=a` and `c=d+2`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo

private def A (x t : ℤ) : ℤ := 4*t*x^2+x^2+x+1
private def B (x t : ℤ) : ℤ := t*x^2+t*x+t+1
private def L (x t : ℤ) : ℤ := 4*t^2*x+4*t^2+4*t+1
private def K (x t : ℤ) : ℤ := 4*t^2*x+4*t*x+x+1
private def SU (x t : ℤ) : ℤ := 2*B x t-1
private def SV (x t : ℤ) : ℤ := 2*L x t-1-4*t
private def SW (x t : ℤ) : ℤ := 2*K x t-1-x-4*t*x
private def E (x t : ℤ) : ℤ := 4*B x t-A x t
private def H1 (x t u : ℤ) : ℤ := B x t+L x t-2*(1+u)*A x t
private def H2 (x t u : ℤ) : ℤ := B x t-L x t+2*K x t-2*(1+u)*A x t
private def J1 (x t u : ℤ) : ℤ := SU x t+SV x t-4*(1+u)*A x t
private def J2 (x t u : ℤ) : ℤ := SU x t-SV x t+2*SW x t-4*(1+u)*A x t
private def D (x t u v : ℤ) : ℤ := (2*v+1)*B x t-L x t-2*u*A x t
private def T (x t u v : ℤ) : ℤ := 2*D x t u v+4*t-2*v
private def window (s h : ℤ) : Prop := 0≤s ∧ s≤h-1
private def firstTwo (x t u : ℤ) : Prop :=
  window (H1 x t u) (L x t) ∧ window (H2 x t u) (K x t) ∧
  window (J1 x t u) (SV x t) ∧ window (J2 x t u) (SW x t)
private def windows (x t u v : ℤ) : Prop :=
  firstTwo x t u ∧ window (D x t u v) (A x t) ∧ window (T x t u v) (A x t)

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
