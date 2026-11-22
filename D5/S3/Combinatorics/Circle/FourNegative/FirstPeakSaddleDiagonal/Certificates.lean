/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/Certificates
   generality: I
   mirror-B: none(waiver:private-consumed-full-saddle-implementation)
   mirror-E: none(waiver:private-consumed-full-saddle-implementation)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Integer margin definitions for the diagonal saddle charts. -/
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! The strict and equality certificates use the same scaled, boundary, rectangle, and gate margins. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal

private def D (y z : ℤ) : ℤ := y*(z+1)+1
private def A (x y z : ℤ) : ℤ := x*D y z+1
private def B (x y t : ℤ) : ℤ := x*t*(y+1)+t+1
private def L (x z t : ℤ) : ℤ := x*z*t+z*t+z+1
private def M (y z t : ℤ) : ℤ := t*y*z+D y z
private def Bn (x y t : ℤ) : ℤ := 2*B x y t-1
private def Ln (x z t : ℤ) : ℤ := 2*L x z t-z-1
private def Mn (y z t : ℤ) : ℤ := 2*M y z t-D y z
private def grain (K J : ℤ) : ℤ := 4*K*J
private def reserve (K J t : ℤ) : ℤ := 2*K*J*t-grain K J
private def C (x y z t g : ℤ) : ℤ := A x y z+L x z t-2*g*M y z t
private def E0 (K J m t h r : ℤ) : ℤ :=
  let g := grain K J
  t*A (g*t) (2*K*t) (g*m)-2*reserve K J t*M (2*K*t) (g*m) t
    -2*r*M (2*K*t) (g*m) t+2*h*L (g*t) (g*m) t
private def H0 (K J m t h r : ℤ) : ℤ :=
  let g := grain K J
  t*A (g*t) (2*K*t) (g*m)-2*reserve K J t*M (2*K*t) (g*m) t
    -r*Mn (2*K*t) (g*m) t+h*Ln (g*t) (g*m) t
private def pivot (K J m t h r : ℤ) : ℤ :=
  t+grain K J*m-1+2*m*(2*J*h-r)

private def scaledMargin (K J m t lo hi h r : ℤ) : Fin 4 → ℤ :=
  let g := grain K J
  let z := g*m
  let aa := A (g*t) (2*K*t) z
  let ll := L (g*t) z t
  let cc := C (g*t) (2*K*t) z t g
  let re := (z+1)*E0 K J m t h r-aa*pivot K J m t h r
  let rh := (z+1)*H0 K J m t h r-aa*pivot K J m t h r
  ![aa*lo+re+(z+1)*cc, (z+1)*(aa-1)-aa*hi-re,
    aa*lo+rh-(z+1)*(aa-reserve K J t*D (2*K*t) z),
    (z+1)*(ll-cc)-aa*hi-rh]

private def rectangleMargin (x y z t g q s r h v : ℤ) : Fin 4 → ℤ :=
  let e := (t-2*v)*A x y z-2*s*M y z t+2*h*L x z t
  let hh := e+r*D y z-h*(z+1)
  let cc := C x y z t g
  ![e+cc,A x y z-1-e,hh-A x y z+q*D y z,L x z t-cc-hh]

private def boundaryMargin (K J m : ℤ) : Fin 4 → ℤ :=
  let g := grain K J
  let z := g*m
  rectangleMargin (g*(2*z)) (2*K*(2*z)) z (2*z) g
    (reserve K J (2*z)) (reserve K J (2*z)+g) g 0 0

private def gateMargin (x y z t s r h v : ℤ) : Fin 12 → ℤ :=
  let aa := A x y z
  let bb := B x y t
  let ll := L x z t
  let mm := M y z t
  let bn := Bn x y t
  let ln := Ln x z t
  let mn := Mn y z t
  let e1 := (t-2*v)*aa-2*s*mm+2*h*ll
  let f1 := 2*((t-1-2*v)*aa-s*mn+h*ln)
  let e2 := bb+ll-2*v*aa-2*r*mm+2*h*ll
  let f2 := bn+ln-4*v*aa-2*r*mn+2*h*ln
  let e3 := 2*(h+1)*ll-2*mm
  let f3 := 2*((h+1)*ln-mn)
  ![e1,aa-1-e1,f1,aa-1-f1,e2,ll-1-e2,f2,ln-1-f2,
    e3,bb-1-e3,f3,bn-1-f3]

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal
