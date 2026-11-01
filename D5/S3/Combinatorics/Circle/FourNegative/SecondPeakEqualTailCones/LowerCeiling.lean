/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/LowerCeiling
   generality: I
   mirror-B: none(waiver:private-consumed-native-ceiling)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Safe natural ceiling, unbounded power coordinates and exact W complement. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowerPolynomial
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Native
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
open private heads newHeads row_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Source
open private F E all_ones_xor
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Native
open private lowerPolynomial lower_polynomials
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowerPolynomial

-- For positive integer t,d this is ceil(t/d), using only a natural division.
private def ceilMask (t d : ℤ) : ℕ := (t+d-1).toNat / d.toNat
private def lowerC (a b s : ℕ) : ℕ :=
  ceilMask (heads (2^a) (2^b) (2^s) 3-heads (2^a) (2^b) (2^s) 2)
    (2*heads (2^a) (2^b) (2^s) 2)

private theorem ceilMask_bounds (t d : ℤ) (ht : 1≤t) (hd : 1≤d) :
    t≤d*(ceilMask t d:ℤ) ∧ d*(ceilMask t d:ℤ)≤t+d-1 := by
  have hn : 0≤t+d-1 := by omega
  have hd0 : 0≤d := by omega
  have hdc : (d.toNat:ℤ)=d := Int.toNat_of_nonneg hd0
  have hnc : ((t+d-1).toNat:ℤ)=t+d-1 := Int.toNat_of_nonneg hn
  have hdp : 0<d.toNat := by omega
  have he := Nat.div_add_mod (t+d-1).toNat d.toNat
  have hr := Nat.mod_lt (t+d-1).toNat hdp
  have heZ : (d.toNat:ℤ)*((t+d-1).toNat/d.toNat:ℕ)+
      ((t+d-1).toNat%d.toNat:ℕ)=((t+d-1).toNat:ℤ) := by
    exact_mod_cast he
  have hrZ : (((t+d-1).toNat%d.toNat:ℕ):ℤ)<(d.toNat:ℤ) := by exact_mod_cast hr
  have hr0 : (0:ℤ)≤((t+d-1).toNat%d.toNat:ℕ) := by positivity
  rw [hdc,hnc] at heZ
  rw [hdc] at hrZ
  dsimp only [ceilMask]
  constructor <;> omega

-- These are NATURAL differences, cast only after their subtraction bounds.
-- The boundary b=2*s+1 has w=0, so it needs no separate endpoint or hypothesis.
private theorem lower_coordinates (a b s : ℕ) (ha : 2≤a)
    (has : a+1≤s) (hb : 2*s+1≤b) :
    ∃ u v w : ℕ,
      (2:ℤ)^a=4+(u:ℤ) ∧
      (2:ℤ)^s=2*(4+(u:ℤ))+(v:ℤ) ∧
      (2:ℤ)^b=2*(2*(4+(u:ℤ))+(v:ℤ))^2+(w:ℤ) := by
  have hx : 4≤(2:ℕ)^a := by
    have h := Nat.pow_le_pow_right Nat.zero_lt_two ha
    norm_num at h ⊢
    exact h
  have hz : 2*(2:ℕ)^a≤2^s := by
    have h := Nat.pow_le_pow_right Nat.zero_lt_two has
    simpa only [pow_succ,Nat.mul_comm] using h
  have hy : 2*(2:ℕ)^s*(2:ℕ)^s≤2^b := by
    have h := Nat.pow_le_pow_right Nat.zero_lt_two hb
    have he : (2:ℕ)^(2*s+1)=2*2^s*2^s := by
      rw [show 2*s+1=s+s+1 by omega]
      simp only [pow_add]
      ring
    rwa [he] at h
  refine ⟨2^a-4,2^s-2*2^a,2^b-2*2^s*2^s,?_,?_,?_⟩
  · rw [Nat.cast_sub hx]
    push_cast
    ring
  · rw [Nat.cast_sub hx,Nat.cast_sub hz]
    push_cast
    ring
  · rw [Nat.cast_sub hx,Nat.cast_sub hz,Nat.cast_sub hy]
    push_cast
    ring

private theorem lower_polynomial_powers (a b s : ℕ) (ha : 2≤a)
    (has : a+1≤s) (hb : 2*s+1≤b) :
    ∀ i, 0<lowerPolynomial (2^a) (2^b) (2^s) i := by
  obtain ⟨u,v,w,hx,hz,hy⟩ := lower_coordinates a b s ha has hb
  rw [hx,hy,hz]
  exact lower_polynomials u v w (by positivity) (by positivity) (by positivity)

private theorem lower_rounding_capacity (a b s : ℕ) (hs : 2≤s)
    (ha : 2≤a) (has : a+1≤s) (hb : 2*s+1≤b) :
    (heads (2^a) (2^b) (2^s) 3-heads (2^a) (2^b) (2^s) 2 ≤
        2*heads (2^a) (2^b) (2^s) 2*(lowerC a b s:ℤ) ∧
      2*heads (2^a) (2^b) (2^s) 2*(lowerC a b s:ℤ) ≤
        heads (2^a) (2^b) (2^s) 3+heads (2^a) (2^b) (2^s) 2-1) ∧
    lowerC a b s≤F b := by
  let L := heads (2^a) (2^b) (2^s) 2
  let M := heads (2^a) (2^b) (2^s) 3
  have hL : 1≤L := ((row_bounds a b s ha (by omega) hs).1 2).1
  have hP := lower_polynomial_powers a b s ha has hb
  have hp12 : 0<M-L := hP 11
  have hp13 : 0<L*((2:ℤ)^b-3)-M+1 := hP 12
  have hc : M-L≤2*L*(lowerC a b s:ℤ) ∧
      2*L*(lowerC a b s:ℤ)≤M+L-1 := by
    have h := ceilMask_bounds (M-L) (2*L) (by omega) (by omega)
    change M-L≤2*L*(lowerC a b s:ℤ) ∧ _ at h
    constructor <;> linarith [h.1,h.2]
  have half : (2:ℤ)^b=2*(2:ℤ)^(b-1) := by
    conv_lhs => rw [show b=(b-1)+1 by omega,pow_succ]
    ring
  have hf : (F b:ℤ)=(2:ℤ)^(b-1)-1 := by
    simp only [F,Nat.cast_sub Nat.one_le_two_pow,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  have hcap : (lowerC a b s:ℤ)≤(F b:ℤ) := by
    by_contra hbad
    have hstep : (F b:ℤ)+1≤(lowerC a b s:ℤ) := by omega
    have hmul := mul_le_mul_of_nonneg_left hstep (show 0≤2*L by omega)
    rw [half] at hp13
    rw [hf] at hmul
    nlinarith only [hc.2,hp13,hmul,hL]
  exact ⟨hc,by exact_mod_cast hcap⟩

private theorem lower_mask_facts (a b s : ℕ) (hs : 2≤s)
    (ha : 2≤a) (has : a+1≤s) (hb : 2*s+1≤b) :
    lowerC a b s<2^(b-1) ∧ (F b ^^^ lowerC a b s)<2^(b-1) ∧
    F b ^^^ lowerC a b s=F b-lowerC a b s ∧
    ((F b ^^^ lowerC a b s:ℕ):ℤ)=(F b:ℤ)-(lowerC a b s:ℤ) := by
  have hc := (lower_rounding_capacity a b s hs ha has hb).2
  have he := all_ones_xor (b-1) (lowerC a b s) hc
  change F b ^^^ lowerC a b s=F b-lowerC a b s at he
  have hf : F b<2^(b-1) := by
    dsimp [F]
    exact Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  refine ⟨lt_of_le_of_lt hc hf,?_,he,?_⟩
  · rw [he]
    omega
  · rw [he,Nat.cast_sub hc]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
