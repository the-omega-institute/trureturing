/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/Algebra
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakAdjacentTail/Algebra
   mirror-E: none(waiver:adjacent-tail-physical-source)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Exact adjacent-tail heads, stocks, residuals and integer ceilings. -/
import Mathlib.Tactic


set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail

private def A (x z q : ℚ) : ℚ := 1+x+x*(q*z)+x*(q*z)*z
private def B (x z q : ℚ) : ℚ := 1+2*z+2*x*z+2*x*(q*z)*z
private def L (x z : ℚ) : ℚ := 1+z+2*z^2*(1+x)
private def K (z q : ℚ) : ℚ := 1+q*z+(q*z)*z+2*(q*z)*z^2
private def SU (x z q : ℚ) : ℚ := 2*B x z q-1
private def SV (x z : ℚ) : ℚ := 2*L x z-1-z
private def SW (z q : ℚ) : ℚ := 2*K z q-(1+q*z+(q*z)*z)
private def E (x z q v m : ℚ) : ℚ := (v+1)*B x z q-K z q+m*L x z
private def F (x z q v m : ℚ) : ℚ := (v+1)*SU x z q-SW z q+m*SV x z

/-- The seven common sides, on the larger continuous q>=4 domain. -/
private def Common (x z q : ℚ) : Prop :=
  0 ≤ B x z q-A x z q-1 ∧ 0 ≤ 2*A x z q-B x z q-1 ∧
  0 ≤ B x z q-L x z ∧ 0 ≤ K z q-1-2*(B x z q-L x z) ∧
  0 ≤ SW z q-1-2*(SU x z q-SV x z) ∧
  0 ≤ K z q-B x z q-1 ∧ 0 ≤ (q*z/2-1)*L x z-(K z q-B x z q)

/-- The nine nontrivial residual sides for q=8. V stock is handled separately. -/
private def Residual (x z q v m : ℚ) : Prop :=
  0 ≤ m ∧ 0 ≤ q*z/2-1-m ∧
  0 ≤ E x z q v m ∧ 0 ≤ L x z-1-E x z q v m ∧
  0 ≤ A x z q-1-2*E x z q v m ∧
  0 ≤ F x z q v m ∧ 0 ≤ A x z q-1-2*F x z q v m ∧
  0 ≤ K z q-1-2*((v+1)*B x z q-L x z) ∧
  0 ≤ SW z q-1-2*((v+1)*SU x z q-SV x z)

private def StocksAndResidual (x z q v m : ℚ) : Prop :=
  0 ≤ v ∧ 0 ≤ z/2-1-v ∧ Residual x z q v m

private def HighResidual (z m : ℚ) : Prop :=
  0 ≤ m ∧ 0 ≤ 8*z-1-m ∧
  0 ≤ E 4 z 16 0 m ∧ 0 ≤ L 4 z-1-E 4 z 16 0 m ∧
  0 ≤ A 4 z 16-1-2*E 4 z 16 0 m ∧
  0 ≤ F 4 z 16 0 m ∧ 0 ≤ A 4 z 16-1-2*F 4 z 16 0 m

/-- These are the actual old/new postterminal windows, in U,X,W,V order. -/
private def Windows (x z q v m : ℚ) : Prop :=
  (0 ≤ 2*(B x z q-A x z q) ∧ 2*(B x z q-A x z q) ≤ B x z q-1) ∧
  (0 ≤ 2*(SU x z q-2*A x z q) ∧ 2*(SU x z q-2*A x z q) ≤ SU x z q-1) ∧
  (0 ≤ 2*E x z q v m ∧ 2*E x z q v m ≤ A x z q-1) ∧
  (0 ≤ 2*F x z q v m ∧ 2*F x z q v m ≤ A x z q-1) ∧
  (0 ≤ 2*((v+1)*B x z q-L x z) ∧
    2*((v+1)*B x z q-L x z) ≤ K z q-1) ∧
  (0 ≤ 2*((v+1)*SU x z q-SV x z) ∧
    2*((v+1)*SU x z q-SV x z) ≤ SW z q-1)

private theorem residual_identity (x z q v m : ℚ) :
    F x z q v m=2*E x z q v m+(q*z-m)*(z+1)-v := by
  dsimp [F,E,SU,SV,SW,A,B,L,K]
  ring

private theorem heads_positive (x z q : ℚ) (hx : 4 ≤ x) (hz : 2*x ≤ z) (hq : 4 ≤ q) :
    0 < A x z q ∧ 0 < B x z q ∧ 0 < L x z ∧
    0 < K z q ∧ 0 < SU x z q ∧ 0 < SV x z ∧ 0 < SW z q := by
  have hx0 : 0 ≤ x := by linarith
  have hz0 : 0 ≤ z := by linarith
  have hq0 : 0 ≤ q := by linarith
  dsimp [A,B,L,K,SU,SV,SW]
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · ring_nf; positivity
  constructor <;> ring_nf <;> positivity

private theorem windows_of_residual (x z q v m : ℚ)
    (hx : 4 ≤ x) (hz : 2*x ≤ z) (hq : 4 ≤ q)
    (hc : Common x z q) (hv : 0 ≤ v) (hr : Residual x z q v m) :
    Windows x z q v m := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := hc
  obtain ⟨hm,hmc,he,hec,heo,hf,hfo,h3o,h3n⟩ := hr
  obtain ⟨hA,hB,hL,hK,hSU,hSV,hSW⟩ := heads_positive x z q hx hz hq
  have hvB : 0 ≤ v*B x z q := mul_nonneg hv hB.le
  have hvSU : 0 ≤ v*SU x z q := mul_nonneg hv hSU.le
  dsimp [Windows]
  dsimp [SU,SV] at *
  refine ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,
    ⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,
    ⟨by nlinarith,by linarith⟩,⟨by nlinarith,by linarith⟩⟩

/-- Integer ceiling is the least integer making the old residual nonnegative. -/
private def ceilDiv (D LL : ℤ) : ℤ := -((-D)/LL)

private theorem ceilDiv_spec (D LL : ℤ) (hL : 0 < LL) :
    0 ≤ ceilDiv D LL*LL-D ∧ ceilDiv D LL*LL-D ≤ LL-1 := by
  have h0 := Int.emod_nonneg (-D) (ne_of_gt hL)
  have h1 := Int.emod_lt_of_pos (-D) hL
  have he := Int.emod_add_mul_ediv (-D) LL
  dsimp [ceilDiv]
  constructor <;> nlinarith

private theorem ceilDiv_stock (D LL stock : ℤ) (hL : 0 < LL)
    (hD : 0 < D) (hs : D ≤ stock*LL) :
    1 ≤ ceilDiv D LL ∧ ceilDiv D LL ≤ stock := by
  obtain ⟨he,hec⟩ := ceilDiv_spec D LL hL
  constructor
  · by_contra hn
    have hn' : ceilDiv D LL ≤ 0 := by omega
    nlinarith
  · by_contra hn
    have hn' : stock+1 ≤ ceilDiv D LL := by omega
    nlinarith

private def residueRepresentative (x u : ℚ) (negative : Bool) : ℚ :=
  if negative then x+1-u else u

private def chooseM3 (x z u : ℚ) (negative : Bool) : ℚ :=
  (8*z-residueRepresentative x u negative)/(x+1)-
    (if negative then (if u≤8 then 6 else 7) else 7)

private def chooseV2 (x u : ℚ) (negative : Bool) : ℚ :=
  if negative then (if u≤4 then x/8+(if u=4 then 1 else 0) else 0)
  else if u=1 then x/8-1 else if u=2 then x/8 else x/8-u/4

private def chooseM2 (x z u : ℚ) (negative : Bool) : ℚ :=
  (4*z-residueRepresentative x u negative)/(x+1)-4*chooseV2 x u negative-
    (if negative then (if u≤4 then 2 else 3) else 3)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
