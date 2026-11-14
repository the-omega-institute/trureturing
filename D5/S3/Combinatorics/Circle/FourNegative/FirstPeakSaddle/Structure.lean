/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Structure
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:private-consumed-full-saddle-implementation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Native capacities, bit inclusion and twelve paired physical seams. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
import Mathlib.Data.Nat.Bitwise

/-! This private interface contains actual natural masks.
Native supplies arithmetic existence in six exhaustive regions.
Field order is s,r,h,v. Gate arguments are t,z,x,y,s,r,h,v, all integers. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators

private def gate (t z x y s r h v : ℤ) : Fin 12 → ℤ :=
  let D := y*(z+1)+1
  let A := x*D+1
  let B := x*t*(y+1)+t+1
  let L := x*z*t+z*t+z+1
  let M := t*y*z+D
  let Bn := 2*B-1
  let Ln := 2*L-z-1
  let Mn := 2*M-D
  let E1 := (t-2*v)*A-2*s*M+2*h*L
  let F1 := 2*((t-1-2*v)*A-s*Mn+h*Ln)
  let E2 := B+L-2*v*A-2*r*M+2*h*L
  let F2 := Bn+Ln-4*v*A-2*r*Mn+2*h*Ln
  let E3 := 2*(h+1)*L-2*M
  let F3 := 2*((h+1)*Ln-Mn)
  ![E1,A-1-E1,F1,A-1-F1,E2,L-1-E2,F2,Ln-1-F2,
    E3,B-1-E3,F3,Bn-1-F3]

private structure JointChoice (a b c d : ℕ) where
  s : ℕ
  r : ℕ
  h : ℕ
  v : ℕ
  bounds : 1≤r ∧ r≤s ∧ s≤2^(a-1) ∧ v<2^(d-1) ∧ h<2^(b-1)
  submask : ∀ e<a-1, (r-1).testBit e=true → (s-1).testBit e=true
  good : ∀ i : Fin 12, 0≤gate (2^d) (2^c) (2^a) (2^b) s r h v i

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle
