/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstTwoMaxPlusOne/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-arithmetic-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-arithmetic)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Two exhaustive unbounded polynomial charts for the physical max-plus-one boundary. -/
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule

/-! These estimates concern arbitrary parameters in two infinite charts. They
are neither a bounded enumeration nor a checker or a numerical reduction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoMaxPlusOne
open private Gates
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule

private def Bounds (x z s r p q : ℤ) : Prop :=
  let A := x*x*z+x*x+x+1
  let B := 2*z*(x*x+x+1)+1
  let L := 2*z*z*(x+1)+z+1
  let M := 2*x*z*z+x*z+x+1
  let Bp := 2*B-1
  let Lp := 2*L-1-z
  let Mp := 2*M-1-x-x*z
  Gates (x*x*z*z-1) ((z-2)*A) (B-z*A)
    ((s-1)*L+A+p*B) (M-s*L) ((r-1-p-q)*B) (L-r*B)
    ((s-1)*M+q*B) (A-s*M) ∧
  Gates (2*x*x*z*z-1) ((z-2)*(2*A)) (Bp-z*(2*A))
    ((s-1)*Lp+2*A+p*Bp) (Mp-s*Lp) ((r-1-p-q)*Bp) (Lp-r*Bp)
    ((s-1)*Mp+q*Bp+A) (A-s*Mp)

set_option maxHeartbeats 2000000 in
private theorem small_chart (s q : ℤ) (hq : 1 ≤ q) (hs : 2*q ≤ s) :
    Bounds (2*s) (2*(2*s)*q) s ((2*s)*q) 0 q := by
  obtain ⟨h, hh, rfl⟩ : ∃ h : ℤ, 0 ≤ h ∧ s=2*q+h := ⟨s-2*q, by omega, by ring⟩
  obtain ⟨j, hj, rfl⟩ : ∃ j : ℤ, 0 ≤ j ∧ q=j+1 := ⟨q-1, by omega, by ring⟩
  dsimp only [Bounds, Gates]
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  all_goals first | (apply sub_nonneg.mp; ring_nf; positivity) | ring

set_option maxHeartbeats 2000000 in
private theorem large_chart (s p : ℤ) (hs : 2 ≤ s) (hp : 1 ≤ p) :
    Bounds (2*s) ((2*s)^2*p) s (2*s^2*p) p (s*p) := by
  obtain ⟨h, hh, rfl⟩ : ∃ h : ℤ, 0 ≤ h ∧ s=h+2 := ⟨s-2, by omega, by ring⟩
  obtain ⟨j, hj, rfl⟩ : ∃ j : ℤ, 0 ≤ j ∧ p=j+1 := ⟨p-1, by omega, by ring⟩
  dsimp only [Bounds, Gates]
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  all_goals first | (apply sub_nonneg.mp; ring_nf; positivity) | ring

end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoMaxPlusOne
