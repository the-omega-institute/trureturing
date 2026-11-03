/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/IntegerCertificates
   generality: I
   mirror-B: none(waiver:physical-construction-component)
   mirror-E: none(waiver:physical-construction-component)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Integer interpretations of the universal rational coefficient proofs. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.PolynomialCertificates1
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.PolynomialCertificates2
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.PolynomialCertificates3
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.PolynomialCertificates4

/-! UNCOMPILED. All wrappers are consumed by the actual selector. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD

private theorem int_base_K_gt_B (x p q h : ℤ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) : 0<K x p q h-B x p q h := by
  have hxQ : 4≤(x:ℚ) := by exact_mod_cast hx
  have hpQ : 4≤(p:ℚ) := by exact_mod_cast hp
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hr:=base_K_gt_B (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_base_C_positive (x p q h : ℤ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) : 0<C x p q h := by
  have hxQ : 4≤(x:ℚ) := by exact_mod_cast hx
  have hpQ : 4≤(p:ℚ) := by exact_mod_cast hp
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hr:=base_C_positive (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_base_second_slack (x p q h : ℤ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) : 0<B x p q h-h*p*L x p q-Y x p q h*(Z x q+1) := by
  have hxQ : 4≤(x:ℚ) := by exact_mod_cast hx
  have hpQ : 4≤(p:ℚ) := by exact_mod_cast hp
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hr:=base_second_slack (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_base_M_stock (x p q h : ℤ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) : 0<(Y x p q h-h*p)*L x p q-2*K x p q h+2*B x p q h := by
  have hxQ : 4≤(x:ℚ) := by exact_mod_cast hx
  have hpQ : 4≤(p:ℚ) := by exact_mod_cast hp
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hr:=base_M_stock (x:ℚ) p q h hxQ hpQ hqQ hhQ
  have hr2:=mul_pos (by norm_num : (0:ℚ)<2) hr
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr2 ⊢
  ring_nf at hr2 ⊢
  exact_mod_cast hr2

private theorem int_base_S3_lower (x p q h : ℤ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) : 0<2*B x p q h-2*L x p q := by
  have hxQ : 4≤(x:ℚ) := by exact_mod_cast hx
  have hpQ : 4≤(p:ℚ) := by exact_mod_cast hp
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hr:=base_S3_lower (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_base_S3_upper (x p q h : ℤ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) : 0<K x p q h-1-2*B x p q h+2*L x p q := by
  have hxQ : 4≤(x:ℚ) := by exact_mod_cast hx
  have hpQ : 4≤(p:ℚ) := by exact_mod_cast hp
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hr:=base_S3_upper (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_base_T3_lower (x p q h : ℤ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) : 0<2*SU x p q h-2*SV x p q := by
  have hxQ : 4≤(x:ℚ) := by exact_mod_cast hx
  have hpQ : 4≤(p:ℚ) := by exact_mod_cast hp
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hr:=base_T3_lower (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_base_T3_upper (x p q h : ℤ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) : 0<SW x p q h-1-2*SU x p q h+2*SV x p q := by
  have hxQ : 4≤(x:ℚ) := by exact_mod_cast hx
  have hpQ : 4≤(p:ℚ) := by exact_mod_cast hp
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hr:=base_T3_upper (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_base_F2_positive (x p q h : ℤ)
    (hx : 4≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) : 0<2*x*K x p q h-(2*p*q*x-2*p)*A x p q h := by
  have hxQ : 4≤(x:ℚ) := by exact_mod_cast hx
  have hpQ : 4≤(p:ℚ) := by exact_mod_cast hp
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hr:=base_F2_positive (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_first_large (x p q h : ℤ)
    (hx : 8≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) : 0<A x p q h-4*C x p q h-2*Y x p q h*(Z x q+1)-2 := by
  have hxQ : 8≤(x:ℚ) := by exact_mod_cast hx
  have hpQ : 4≤(p:ℚ) := by exact_mod_cast hp
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hr:=first_large (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_first_small_R_lower (x p q h : ℤ)
    (hx : 4*p≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) : 0<p*q*A x p q h-K x p q h := by
  have hxQ : 4*p≤(x:ℚ) := by exact_mod_cast hx
  have hpQ : 4≤(p:ℚ) := by exact_mod_cast hp
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hr:=first_small_R_lower (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_first_small_T1_upper (x p q h : ℤ)
    (hx : 4*p≤x) (hp : 4≤p) (hq : 2≤q) (hh : 1≤h) : 0<A x p q h-1-4*(p*q*A x p q h-K x p q h)-2*Y x p q h*(Z x q+1)-2 := by
  have hxQ : 4*p≤(x:ℚ) := by exact_mod_cast hx
  have hpQ : 4≤(p:ℚ) := by exact_mod_cast hp
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hr:=first_small_T1_upper (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_tail_R32 (x p q h : ℤ)
    (hx : 32≤x) (hp : 2*p≥x) (hq : 2≤q) (hh : 1≤h) :
    0<x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h) := by
  have hxQ : 32≤(x:ℚ) := by exact_mod_cast hx
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hpQ : (x:ℚ)/2≤(p:ℚ) := by
    have hp' : 2*(p:ℚ)≥(x:ℚ) := by exact_mod_cast hp
    linarith
  have hr:=tail_R32 (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_tail_R8 (x p q h : ℤ)
    (hx : 8≤x) (hp : p≥4*x) (hq : 2≤q) (hh : 1≤h) :
    0<x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h) := by
  have hxQ : 8≤(x:ℚ) := by exact_mod_cast hx
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hpQ : 4*(x:ℚ)≤(p:ℚ) := by
    have hp' : 4*(x:ℚ)≤(p:ℚ) := by exact_mod_cast hp
    linarith
  have hr:=tail_R8 (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_tail_R8q4 (x p q h : ℤ)
    (hx : 8≤x) (hp : p≥2*x) (hq : 4≤q) (hh : 1≤h) :
    0<x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h) := by
  have hxQ : 8≤(x:ℚ) := by exact_mod_cast hx
  have hqQ : 4≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hpQ : 2*(x:ℚ)≤(p:ℚ) := by
    have hp' : 2*(x:ℚ)≤(p:ℚ) := by exact_mod_cast hp
    linarith
  have hr:=tail_R8q4 (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_tail_R16 (x p q h : ℤ)
    (hx : 16≤x) (hp : p≥2*x) (hq : 2≤q) (hh : 1≤h) :
    0<x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h) := by
  have hxQ : 16≤(x:ℚ) := by exact_mod_cast hx
  have hqQ : 2≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hpQ : 2*(x:ℚ)≤(p:ℚ) := by
    have hp' : 2*(x:ℚ)≤(p:ℚ) := by exact_mod_cast hp
    linarith
  have hr:=tail_R16 (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_tail_R16q4 (x p q h : ℤ)
    (hx : 16≤x) (hp : p≥x) (hq : 4≤q) (hh : 1≤h) :
    0<x*(p-4)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h) := by
  have hxQ : 16≤(x:ℚ) := by exact_mod_cast hx
  have hqQ : 4≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hpQ : (x:ℚ)≤(p:ℚ) := by
    have hp' : (x:ℚ)≤(p:ℚ) := by exact_mod_cast hp
    linarith
  have hr:=tail_R16q4 (x:ℚ) p q h hxQ hpQ hqQ hhQ
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr ⊢
  ring_nf at hr ⊢
  exact_mod_cast hr

private theorem int_tail_R16odd (x p q h : ℤ)
    (hx : 16≤x) (hp : 2*p=x) (hq : 8≤q) (hh : 1≤h) :
    0<x*(p-2)*C x p q h-2*(2*x*K x p q h-(2*p*q*x-2*p)*A x p q h) := by
  have hxQ : 16≤(x:ℚ) := by exact_mod_cast hx
  have hqQ : 8≤(q:ℚ) := by exact_mod_cast hq
  have hhQ : 1≤(h:ℚ) := by exact_mod_cast hh
  have hp' : 2*(p:ℚ)=(x:ℚ) := by exact_mod_cast hp
  have hpQ : (p:ℚ)=(x:ℚ)/2 := by linarith
  have hr:=tail_R16odd (x:ℚ) p q h hxQ hpQ hqQ hhQ
  have hr2:=mul_pos (by norm_num : (0:ℚ)<2) hr
  dsimp [A,B,L,K,SU,SV,SW,C,Y,Z,T] at hr2 ⊢
  ring_nf at hr2 ⊢
  exact_mod_cast hr2

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
