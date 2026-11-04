/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/Rounding
   generality: I
   mirror-B: none(waiver:physical-construction-component)
   mirror-E: none(waiver:physical-construction-component)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Signed ceiling, complete low-bit predecessor and parity-adjusted remainder. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.LowBits

/-! UNCOMPILED. The integer ceiling accepts negative numerators.
The existing signed-ceiling source in SecondPeakParityTail imports the unreachable
Mathlib.Data.Int.DivMod; this source uses the reachable physical import closure. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD

private def ceilInt (n d : ℤ) : ℤ := -((-n)/d)

private theorem ceiling_bounds (n d : ℤ) (hd : 0<d) :
    n≤d*ceilInt n d ∧ d*ceilInt n d<n+d := by
  have h0:=Int.emod_nonneg (-n) (ne_of_gt hd)
  have h1:=Int.emod_lt_of_pos (-n) hd
  have he:=Int.emod_add_mul_ediv (-n) d
  dsimp only [ceilInt]
  constructor <;> nlinarith only [h0,h1,he]

private def chooseM (K B L D : ℤ) : ℤ := D*ceilInt (K-B+L) (D*L)-1

private theorem ceiling_M (K B L D : ℤ) (hL : 0<L) (hD : 0<D) (hKB : B<K) :
    let M:=chooseM K B L D
    0≤M ∧ 0≤B-K+M*L ∧ B-K+M*L<D*L ∧
      1≤ceilInt (K-B+L) (D*L) := by
  have hd:=mul_pos hD hL
  have hh:=ceiling_bounds (K-B+L) (D*L) hd
  have hc : 1≤ceilInt (K-B+L) (D*L) := by
    by_contra hn
    have hz : ceilInt (K-B+L) (D*L)≤0 := by omega
    have := mul_nonpos_of_nonneg_of_nonpos hd.le hz
    nlinarith
  dsimp [chooseM]
  have hm : 0≤D*ceilInt (K-B+L) (D*L)-1 := by
    have := mul_le_mul_of_nonneg_left hc hD.le
    nlinarith
  exact ⟨hm,by nlinarith only [hh.1],by nlinarith only [hh.2],hc⟩

private theorem ceiling_M_bits (K B L : ℤ) (s : ℕ)
    (hL : 0<L) (hKB : B<K) (m : ℕ) (hm : m<2^s) :
    Submask m (chooseM K B L ((2:ℤ)^s)).toNat := by
  let c:=ceilInt (K-B+L) ((2:ℤ)^s*L)
  have hD : (0:ℤ)<2^s := by positivity
  have hb:=ceiling_M K B L (2^s) hL hD hKB
  have hc : 1≤c := hb.2.2.2
  have hcN : 1≤c.toNat := by omega
  have hcZ : (c.toNat:ℤ)=c := Int.toNat_of_nonneg (by omega)
  have hcast : ((2^s*c.toNat-1:ℕ):ℤ)=chooseM K B L ((2:ℤ)^s) := by
    rw [Nat.cast_sub (by have := Nat.two_pow_pos s; nlinarith)]
    push_cast
    rw [hcZ]
    rfl
  have he : (chooseM K B L ((2:ℤ)^s)).toNat=2^s*c.toNat-1 := by omega
  rw [he]
  exact submask_predecessor s c.toNat m hcN hm

private def parityJ (F C e : ℤ) : ℤ :=
  e%2+2*ceilInt (F-(e%2)*C) (2*C)

private theorem parity_remainder (F C e : ℤ) (hF : 0<F) (hC : 0<C) :
    let j:=parityJ F C e
    0<j ∧ 0≤j*C-F ∧ j*C-F<2*C ∧ (e+j)%2=0 := by
  have hh:=ceiling_bounds (F-(e%2)*C) (2*C) (by omega)
  have hj : 0<parityJ F C e := by
    by_contra hn
    have hz : parityJ F C e≤0 := by omega
    have := mul_nonpos_of_nonpos_of_nonneg hz hC.le
    dsimp [parityJ] at *
    nlinarith
  dsimp [parityJ] at *
  exact ⟨hj,by nlinarith only [hh.1],by nlinarith only [hh.2],by omega⟩

private theorem parity_standard_cap (F C e p : ℤ)
    (hF : 0<F) (hC : 0<C) (htail : 2*F<(p-4)*C) :
    2*parityJ F C e<p := by
  have hh:=parity_remainder F C e hF hC
  by_contra hn
  have hm : 0≤(2*parityJ F C e-p)*C :=
    mul_nonneg (by omega) hC.le
  nlinarith only [hh.2.2.1,htail,hm]

/-- The strict odd rounding at p=x/2 uses the parity of p/2. -/
private theorem parity_odd_cap (F C p : ℤ)
    (hF : 0<F) (hC : 0<C) (hp : 4∣p)
    (htail : F<(p/2-1)*C) : 2*parityJ F C 1<p := by
  have hh:=parity_remainder F C 1 hF hC
  obtain ⟨u,hu⟩:=hp
  have hupper : parityJ F C 1<p/2+1 := by
    by_contra hn
    have hm : 0≤(parityJ F C 1-(p/2+1))*C := mul_nonneg (by omega) hC.le
    nlinarith only [htail,hh.2.2.1,hm]
  have hjodd : parityJ F C 1%2=1 := by dsimp [parityJ]; omega
  omega

/-- The exact paired first remainder is integral before any conversion to a mask. -/
private theorem first_remainder_identity (A L K p q h e j : ℤ)
    (hparity : (e+j)%2=0) :
    2*((p*q-(e+j)/2)*A+(h*j)*L-K)=
      j*(2*h*L-A)-(2*K-(2*p*q-e)*A) := by
  have he : 2*((e+j)/2)=e+j := by omega
  linear_combination -A*he

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
