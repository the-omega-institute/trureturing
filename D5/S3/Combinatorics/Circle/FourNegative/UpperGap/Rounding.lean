/- GID: D5/S3/Combinatorics/Circle/FourNegative/UpperGap/Rounding
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-integer-allocation-bounds)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod.Lemmas]
   utility: none
   digest: Integer floor and ceiling bounds used by the two rounded boundary chambers. -/
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.SourceMasses

/-! Uncompiled preparation source. All divisions in these lemmas are integer
Euclidean divisions; no real rounding or favorable-subset premise is used. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.UpperGap

private theorem multiple_floor_seam (A H B : ℤ) (hA : 0<A) (hH : 0<H) :
    let n := H*((B-1)/(H*A))
    1 ≤ B-n*A ∧ B-n*A ≤ H*A ∧ n*A ≤ B-1 := by
  let n := H*((B-1)/(H*A))
  have hden : 0<H*A := mul_pos hH hA
  have h0 := Int.emod_nonneg (B-1) (ne_of_gt hden)
  have h1 := Int.emod_lt_of_pos (B-1) hden
  have he := Int.ediv_add_emod (B-1) (H*A)
  have hrem : B-n*A=(B-1)%(H*A)+1 := by
    dsimp [n]
    nlinarith only [he]
  change 1 ≤ B-n*A ∧ B-n*A ≤ H*A ∧ n*A ≤ B-1
  rw [hrem]
  omega

private theorem multiple_floor_peak (A H B : ℤ)
    (hA : 0<A) (hH : 0<H) (hbuffer : 2*(H*A) ≤ B-1) :
    let n := H*((B-1)/(H*A))
    0 ≤ B-n*A ∧ 0 ≤ (2*B-1)-2*n*A ∧ 0 ≤ 2*n*A-B-1 := by
  have h := multiple_floor_seam A H B hA hH
  dsimp only at h ⊢
  rcases h with ⟨hlo,hhi,_⟩
  refine ⟨by linarith, ?_, ?_⟩ <;> nlinarith

private theorem multiple_floor_positive (A H B : ℤ)
    (hA : 0<A) (hH : 0<H) (hlower : H*A ≤ B-1) :
    H ≤ H*((B-1)/(H*A)) := by
  have hden : 0<H*A := mul_pos hH hA
  have h0 := Int.emod_nonneg (B-1) (ne_of_gt hden)
  have h1 := Int.emod_lt_of_pos (B-1) hden
  have he := Int.ediv_add_emod (B-1) (H*A)
  have hquot : 1 ≤ (B-1)/(H*A) := by
    by_contra hh
    have hq : (B-1)/(H*A) ≤ 0 := by omega
    have hmul := mul_nonpos_of_nonpos_of_nonneg hq hden.le
    nlinarith
  nlinarith

private theorem first_mask_capacity (A C Y n : ℤ)
    (hA : 0<A) (hY : 0<Y) (hsep : 2*C<A)
    (hbudget : n*A ≤ 2*Y*C) : n<Y := by
  by_contra hh
  have hn : Y≤n := by omega
  have hmul := mul_le_mul_of_nonneg_right hn hA.le
  have hgap := mul_pos hY (sub_pos.mpr hsep)
  nlinarith

private theorem positive_ceiling (q K : ℤ) (hq : 1≤q) (hK : 1≤K) :
    let w := (q+K-1)/K
    1≤w ∧ q≤K*w ∧ K*w<q+K := by
  let w := (q+K-1)/K
  have h0 := Int.emod_nonneg (q+K-1) (by omega : K≠0)
  have h1 := Int.emod_lt_of_pos (q+K-1) (by omega : 0<K)
  have he := Int.ediv_add_emod (q+K-1) K
  have hrem : K*w+(q+K-1)%K=q+K-1 := by
    dsimp [w]
    nlinarith only [he]
  have hlo : q≤K*w := by omega
  have hhi : K*w<q+K := by omega
  have hw : 1≤w := by
    by_contra hh
    have hw0 : w≤0 := by omega
    have hmul := mul_nonpos_of_nonneg_of_nonpos (by omega : 0≤K) hw0
    omega
  exact ⟨hw,hlo,hhi⟩

private theorem ceiling_capacity (q K C : ℤ)
    (hq : 1≤q) (hK : 1≤K) (hcap : q≤K*C) :
    (q+K-1)/K≤C := by
  have h := positive_ceiling q K hq hK
  dsimp only at h
  by_contra hh
  have hw : C+1≤(q+K-1)/K := by omega
  have hmul := mul_le_mul_of_nonneg_left hw (by omega : 0≤K)
  nlinarith

-- The old peak is controlled by the lower ceiling bound. The new seam is
-- controlled by the strict upper ceiling bound and the independently proved
-- rounding buffer. The old seam then follows from its positive charge.
private theorem rounded_last_packet (A L M z h : ℤ)
    (hL : 1≤L) (hz : 4≤z) (hh : 1≤h)
    (hq : 1≤M+1-2*A)
    (hcap : M+1-2*A≤(2*h-2)*L)
    (hbuffer : 0≤M-(2*h*z+2*h+1)-1-2*L) :
    let D := 2*h*z+2*h+1
    let w := (M+1-2*A+2*L-1)/(2*L)
    1≤w ∧ w≤h-1 ∧
    0≤M-A-w*L ∧
    0≤(2*M-D)-2*A-w*(2*L-z-1) ∧
    0≤2*A+2*w*L-M-1 ∧
    0<D-w*(z+1) := by
  let D := 2*h*z+2*h+1
  let w := (M+1-2*A+2*L-1)/(2*L)
  have hr := positive_ceiling (M+1-2*A) (2*L) hq (by omega)
  have hc : w≤h-1 := by
    apply ceiling_capacity (M+1-2*A) (2*L) (h-1) hq (by omega)
    nlinarith only [hcap]
  change 1≤w ∧ M+1-2*A≤2*L*w ∧ 2*L*w<M+1-2*A+2*L at hr
  have hsub := mul_le_mul_of_nonneg_right hc (by omega : 0≤z+1)
  have hhz : 0≤h*(z+1) := mul_nonneg (by omega) (by omega)
  have hE : 0<D-w*(z+1) := by dsimp [D]; nlinarith
  have hwz : 0≤w*(z+1) := mul_nonneg (by omega) (by omega)
  have hT : 0≤(2*M-D)-2*A-w*(2*L-z-1) := by
    dsimp [D]
    nlinarith only [hr.2.2,hbuffer,hwz]
  refine ⟨hr.1,hc,?_,hT,?_,hE⟩
  · nlinarith only [hT,hE]
  · nlinarith only [hr.2.1]

end D5.S3.Combinatorics.Circle.FourNegative.UpperGap
