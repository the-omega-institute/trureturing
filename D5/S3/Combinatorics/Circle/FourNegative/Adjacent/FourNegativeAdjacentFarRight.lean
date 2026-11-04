/- GID: D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentFarRight
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentFarRight
   mirror-E: none(waiver:no-public-declarations)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: A ceiling-selected physical mask for the large second paired gap. -/
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentSource

/-! A literal last-ear construction when the second radix is at least four times the first. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentFarRight
open SourceWidth PeriodicShortening RunFirstEarTransport
open private label lift_order marked_word ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private Gates four_strip from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule
open private coefficient_bounds chains from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentSource
open private mask_labels mask_labels_mem mask_labels_bound mask_labels_sum
  from D5.S3.Combinatorics.Circle.ThreeBitSource

private theorem ceiling_multiple (R B T : ℤ) (hR : 0 < R) (hB : 0 < B)
    (hT : R ≤ T * B) :
    ∃ h : ℕ, 1 ≤ h ∧ (h : ℤ) ≤ T ∧ R ≤ h * B ∧ h * B < R + B := by
  let d := (R - 1) / B
  have hd : 0 ≤ d := Int.ediv_nonneg (by omega) hB.le
  have he := Int.emod_add_mul_ediv (R - 1) B
  have hr0 := Int.emod_nonneg (R - 1) (ne_of_gt hB)
  have hrB := Int.emod_lt_of_pos (R - 1) hB
  have hh : 0 ≤ d + 1 := by omega
  change (R - 1) % B + B * d = R - 1 at he
  have hbnds : R ≤ (d+1)*B ∧ (d+1)*B < R+B := by
    constructor <;> nlinarith
  have hdT : d+1 ≤ T := by
    by_contra h
    have hhT : T+1 ≤ d+1 := by omega
    have hm := mul_le_mul_of_nonneg_right hhT hB.le
    nlinarith
  have hc : ((d+1).toNat : ℤ) = d+1 := Int.toNat_of_nonneg hh
  refine ⟨(d+1).toNat, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (show (1 : ℤ) ≤ ((d+1).toNat : ℤ) by rw [hc]; omega)
  · rw [hc]; exact hdT
  · rw [hc]; exact hbnds.1
  · rw [hc]; exact hbnds.2

set_option maxHeartbeats 1200000 in
-- Coupled source identities and prefix bounds expand independent dyadic products.
private theorem arithmetic (a b : ℤ) (ha : 2 ≤ a) (hb : 4*a ≤ b) :
    let x := 2*a
    let y := 2*b
    let N := x^2*y^2-1
    let A := 1+x+x^2+x^2*y
    let B := 1+y+x*y+x^2*y
    let L := 1+y+y^2+x*y^2
    let M := 1+x+x*y+x*y^2
    let e := 1+x+x*y
    let GV := 2*B-1
    let GW := 2*L-1-y
    let GX := 2*M-e
    let R := b+2*b^2+4*a*b^2-2*a-4*a^2-8*a^2*b
    0 < R ∧ R ≤ (b-1)*B ∧
    ∀ h : ℕ, 1 ≤ h → (h : ℤ) ≤ b-1 → R ≤ h*B → h*B < R+B →
    Gates (N/2) ((b-1)*A) (-(N-B)/2) ((b-1-h)*B) (-(N-L)/2)
      ((a-1)*L) (-(N-M)/2) ((a-1)*M+h*B) (-(N-A)/2) ∧
    Gates N ((b-1)*(2*A)) (-((2*N+1)-GV)/2) ((b-1-h)*GV) (-((2*N+1)-GW)/2)
      ((a-1)*GW) (-((2*N+1)-GX)/2) ((a-1)*GX+h*GV+A) (-((2*N+1)-A)/2) := by
  dsimp only
  let u := a-2
  let v := b-4*a
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have ea : a=u+2 := by dsimp [u]; ring
  have eb : b=4*(u+2)+v := by dsimp [u,v]; ring
  have hR : 0 < b+2*b^2+4*a*b^2-2*a-4*a^2-8*a^2*b := by
    rw [ea,eb]; ring_nf; positivity
  have hT : b+2*b^2+4*a*b^2-2*a-4*a^2-8*a^2*b ≤
      (b-1)*(1+2*b+(2*a)*(2*b)+(2*a)^2*(2*b)) := by
    have hm : 0 ≤ (b-1)*(1+2*b+(2*a)*(2*b)+(2*a)^2*(2*b)) -
        (b+2*b^2+4*a*b^2-2*a-4*a^2-8*a^2*b) := by
      rw [ea,eb]; ring_nf; positivity
    linarith
  refine ⟨hR,hT,?_⟩
  intro h hh hhb hlow hhigh
  have margins :
      0 < (1+2*b+(2*a)*(2*b)+(2*a)^2*(2*b)) - (1+2*a+(2*a)^2+(2*a)^2*(2*b)) ∧
      0 < (1+2*b+(2*b)^2+(2*a)*(2*b)^2) - (1+2*a+(2*a)*(2*b)+(2*a)*(2*b)^2) ∧
      0 < 2*(1+2*a+(2*a)^2+(2*a)^2*(2*b))-1-(1+2*b+(2*a)*(2*b)+(2*a)^2*(2*b)) ∧
      0 < 2*(1+2*a+(2*a)*(2*b)+(2*a)*(2*b)^2) -
        (1+2*b+(2*b)^2+(2*a)*(2*b)^2) -
        2*(1+2*b+(2*a)*(2*b)+(2*a)^2*(2*b)) - (1+2*a+(2*a)*(2*b))-1 := by
    rw [ea,eb]; ring_nf
    exact ⟨by positivity,by positivity,by positivity,by positivity⟩
  obtain ⟨cA,cB,cL,cM,cGV,cGW,cGX⟩ := coefficient_bounds (2*a) (2*b) (by omega) (by omega)
  have hh0 : (0 : ℤ) ≤ h := by positivity
  have hab : 2*b ≤ a*b := by
    have hb0 : 0 ≤ b := by omega
    nlinarith only [mul_nonneg (show 0 ≤ a-2 by omega) hb0]
  dsimp only [Gates]
  have hCdiv : ((2*a)^2*(2*b)^2-1)/2 = 8*a^2*b^2 - 1 := by clear * - a b; ring_nf; omega
  have hd0 : -(((2*a)^2*(2*b)^2-1)-(1+2*b+(2*a)*(2*b)+(2*a)^2*(2*b)))/2 = -8*a^2*b^2 + 4*a^2*b + 2*a*b + b + 1 := by clear * - a b; ring_nf; omega
  have hd1 : -(((2*a)^2*(2*b)^2-1)-(1+2*b+(2*b)^2+(2*a)*(2*b)^2))/2 = -8*a^2*b^2 + 4*a*b^2 + 2*b^2 + b + 1 := by clear * - a b; ring_nf; omega
  have hd2 : -(((2*a)^2*(2*b)^2-1)-(1+2*a+(2*a)*(2*b)+(2*a)*(2*b)^2))/2 = -8*a^2*b^2 + 4*a*b^2 + 2*a*b + a + 1 := by clear * - a b; ring_nf; omega
  have hd3 : -(((2*a)^2*(2*b)^2-1)-(1+2*a+(2*a)^2+(2*a)^2*(2*b)))/2 = -8*a^2*b^2 + 4*a^2*b + 2*a^2 + a + 1 := by clear * - a b; ring_nf; omega
  have he0 : -((2*((2*a)^2*(2*b)^2-1)+1)-(2*(1+2*b+(2*a)*(2*b)+(2*a)^2*(2*b))-1))/2 = -16*a^2*b^2 + 8*a^2*b + 4*a*b + 2*b + 1 := by clear * - a b; ring_nf; omega
  have he1 : -((2*((2*a)^2*(2*b)^2-1)+1)-(2*(1+2*b+(2*b)^2+(2*a)*(2*b)^2)-1-2*b))/2 = -16*a^2*b^2 + 8*a*b^2 + 4*b^2 + b + 1 := by clear * - a b; ring_nf; omega
  have he2 : -((2*((2*a)^2*(2*b)^2-1)+1)-(2*(1+2*a+(2*a)*(2*b)+(2*a)*(2*b)^2)-(1+2*a+(2*a)*(2*b))))/2 = -16*a^2*b^2 + 8*a*b^2 + 2*a*b + a + 1 := by clear * - a b; ring_nf; omega
  have he3 : -((2*((2*a)^2*(2*b)^2-1)+1)-(1+2*a+(2*a)^2+(2*a)^2*(2*b)))/2 = -16*a^2*b^2 + 4*a^2*b + 2*a^2 + a + 1 := by clear * - a b; ring_nf; omega
  simp only [hCdiv,hd0,hd1,hd2,hd3,he0,he1,he2,he3]
  ring_nf at hlow hhigh margins cA cB cL cM cGV cGW cGX hab ⊢
  clear hCdiv hd0 hd1 hd2 hd3 he0 he1 he2 he3 hR hT
  clear hu hv ea eb u v
  repeat' constructor
  all_goals first
    | rfl
    | linarith only [ha,hb,hh0,hhb,hlow,hhigh,margins.1,margins.2.1,
        margins.2.2.1,margins.2.2.2,cA.1,cA.2,cB.1,cB.2,cL.1,cL.2,
        cM.1,cM.2,cGV,cGW,cGX,hab]

set_option maxHeartbeats 1600000 in
-- Coupled source identities and prefix bounds expand independent dyadic products.
private theorem far_right (r s : ℕ) (hr : 2 ≤ r) (hs : r+2 ≤ s) :
    ∃ sigma : List (Fin (2*r+2*s)), ∃ j : ℕ, j ≤ 2*r+2*s ∧
      OriginalOrder (2*r+2*s) (1+2^r+2^(2*r)+2^(2*r+s)) sigma ∧
      OriginalOrder (2*r+2*s+1) (2*(1+2^r+2^(2*r)+2^(2*r+s)))
        (earWord (2*r+2*s) sigma j) := by
  classical
  let a : ℤ := 2^(r-1)
  let b : ℤ := 2^(s-1)
  let x := 2*a
  let y := 2*b
  let k := 2*r+2*s
  let N := modulus k
  let A := 1+x+x^2+x^2*y
  let B := 1+y+x*y+x^2*y
  let L := 1+y+y^2+x*y^2
  let M := 1+x+x*y+x*y^2
  let e := 1+x+x*y
  let GV := 2*B-1
  let GW := 2*L-1-y
  let GX := 2*M-e
  let R := b+2*b^2+4*a*b^2-2*a-4*a^2-8*a^2*b
  let t : ℕ := 1+2^r+2^(2*r)+2^(2*r+s)
  let f := fun i : ℕ => centered N ((2 : ℤ)^i*A)
  let g := fun i : ℕ => centered (modulus (k+1)) ((2 : ℤ)^i*(2*A))
  have ha : 2 ≤ a := by
    simpa only [a,pow_one] using pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (show 1 ≤ r-1 by omega)
  have hb : 4*a ≤ b := by
    have he : (2 : ℤ)^(r+1) = 4*a := by
      rw [show r+1=(r-1)+2 by omega,pow_add]; norm_num; dsimp [a]; ring
    rw [←he]
    exact pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (by omega)
  have hx : (2 : ℤ)^r=x := by
    dsimp [x,a]
    conv_lhs => rw [show r=(r-1)+1 by omega,pow_succ]
    ring
  have hy : (2 : ℤ)^s=y := by
    dsimp [y,b]
    conv_lhs => rw [show s=(s-1)+1 by omega,pow_succ]
    ring
  have hN : N=x^2*y^2-1 := by
    dsimp [N,k,modulus]
    rw [show 2*r+2*s=r+r+(s+s) by omega]
    simp only [pow_add,hx,hy]; ring
  have hNN : modulus (k+1)=2*N+1 := by dsimp [N,modulus]; rw [pow_succ]; ring
  have ht : (t : ℤ)=A := by
    dsimp only [t,A]
    push_cast
    rw [show 2*r=r+r by omega]
    simp only [pow_add,hx,hy]; ring
  obtain ⟨hR,hT,hgates⟩ := arithmetic a b ha hb
  change 0<R at hR
  change R ≤ (b-1)*B at hT
  obtain ⟨h,hh,hhb,hlow,hhigh⟩ := ceiling_multiple R B (b-1) hR
    (by
      have ha0 : 0 ≤ a := by omega
      have hb0 : 0 ≤ b := by omega
      dsimp [B,x,y]
      positivity) hT
  have hmask : h < 2^(s-1) := by
    have he : (h : ℤ)<(2 : ℤ)^(s-1) := by change (h : ℤ)<b; omega
    exact_mod_cast he
  have gate := hgates h hh hhb hlow hhigh
  change Gates ((x^2*y^2-1)/2) ((b-1)*A) (-(x^2*y^2-1-B)/2) ((b-1-h)*B) (-(x^2*y^2-1-L)/2)
      ((a-1)*L) (-(x^2*y^2-1-M)/2) ((a-1)*M+h*B) (-(x^2*y^2-1-A)/2) ∧
    Gates (x^2*y^2-1) ((b-1)*(2*A)) (-((2*(x^2*y^2-1)+1)-GV)/2)
      ((b-1-h)*GV) (-((2*(x^2*y^2-1)+1)-GW)/2)
      ((a-1)*GW) (-((2*(x^2*y^2-1)+1)-GX)/2)
      ((a-1)*GX+h*GV+A) (-((2*(x^2*y^2-1)+1)-A)/2) at gate
  rw [←hN] at gate
  obtain ⟨hU,hV,hW,hX,hU',hV',hW',hX',hear⟩ := chains r s hr (by omega)
  simp only [hx,hy] at hU hV hW hX hU' hV' hW' hX' hear
  change ∀ i<s, f i = if i+1<s then 2^i*A else -(N-B)/2 at hU
  change ∀ i<s, f (s+i) = if i+1<s then 2^i*B else -(N-L)/2 at hV
  change ∀ i<r, f (2*s+i) = if i+1<r then 2^i*L else -(N-M)/2 at hW
  change ∀ i<r, f (2*s+r+i) = if i+1<r then 2^i*M else -(N-A)/2 at hX
  change ∀ i<s, g i = if i+1<s then 2^i*(2*A) else -(modulus (k+1)-GV)/2 at hU'
  change ∀ i<s, g (s+i) = if i+1<s then 2^i*GV else -(modulus (k+1)-GW)/2 at hV'
  change ∀ i<r, g (2*s+i) = if i+1<r then 2^i*GW else -(modulus (k+1)-GX)/2 at hW'
  change ∀ i<r, g (2*s+r+i) = if i+1<r then 2^i*GX else -(modulus (k+1)-A)/2 at hX'
  change g k=A at hear
  let U := List.range (s-1)
  let V := List.range' s (s-1)
  let W := List.range' (2*s) (r-1)
  let X := List.range' (2*s+r) (r-1)
  let H := mask_labels (s-1) s h hmask
  let Vhi := H.toList
  let Vlo := (V.toFinset \ H).toList
  let u := s-1
  let v := 2*s-1
  let w := 2*s+r-1
  let z := k-1
  have posU (i : ℕ) (hi : i<s-1) : f i=2^i*A ∧ g i=2^i*(2*A) := by
    rw [hU i (by omega),hU' i (by omega),ite_eq_left (by omega),ite_eq_left (by omega)]
    exact ⟨rfl,rfl⟩
  have posV (i : ℕ) (hi : i<s-1) : f (s+i)=2^i*B ∧ g (s+i)=2^i*GV := by
    rw [hV i (by omega),hV' i (by omega),ite_eq_left (by omega),ite_eq_left (by omega)]
    exact ⟨rfl,rfl⟩
  have posW (i : ℕ) (hi : i<r-1) : f (2*s+i)=2^i*L ∧ g (2*s+i)=2^i*GW := by
    rw [hW i (by omega),hW' i (by omega),ite_eq_left (by omega),ite_eq_left (by omega)]
    exact ⟨rfl,rfl⟩
  have posX (i : ℕ) (hi : i<r-1) : f (2*s+r+i)=2^i*M ∧ g (2*s+r+i)=2^i*GX := by
    rw [hX i (by omega),hX' i (by omega),ite_eq_left (by omega),ite_eq_left (by omega)]
    exact ⟨rfl,rfl⟩
  have negU : f u=-(N-B)/2 ∧ g u=-(modulus (k+1)-GV)/2 := by
    simpa only [u,ite_eq_right (by omega : ¬s-1+1<s)] using
      And.intro (hU (s-1) (by omega)) (hU' (s-1) (by omega))
  have negV : f v=-(N-L)/2 ∧ g v=-(modulus (k+1)-GW)/2 := by
    simpa only [show s+(s-1)=v by dsimp [v]; omega,ite_eq_right (by omega : ¬s-1+1<s)] using
      And.intro (hV (s-1) (by omega)) (hV' (s-1) (by omega))
  have negW : f w=-(N-M)/2 ∧ g w=-(modulus (k+1)-GX)/2 := by
    simpa only [show 2*s+(r-1)=w by dsimp [w]; omega,ite_eq_right (by omega : ¬r-1+1<r)] using
      And.intro (hW (r-1) (by omega)) (hW' (r-1) (by omega))
  have negX : f z=-(N-A)/2 ∧ g z=-(modulus (k+1)-A)/2 := by
    simpa only [show 2*s+r+(r-1)=z by dsimp [z,k]; omega,ite_eq_right (by omega : ¬r-1+1<r)] using
      And.intro (hX (r-1) (by omega)) (hX' (r-1) (by omega))
  have hH : H ⊆ V.toFinset := by
    intro i hi
    have hi' := mask_labels_bound hi
    apply List.mem_toFinset.mpr
    apply List.mem_range'.mpr
    exact ⟨i-s,by omega,by omega⟩
  have split : (Vlo++Vhi).Perm V := by
    have hd : List.Disjoint Vlo Vhi := by
      intro i hi hj
      exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hi)).2 (Finset.mem_toList.mp hj)
    apply (List.perm_ext_iff_of_nodup
      ((V.toFinset \ H).nodup_toList.append H.nodup_toList hd)
      (by dsimp [V]; exact List.nodup_range')).mpr
    intro i
    have hhH : i∈H → i∈V.toFinset := fun hi => hH hi
    simp only [Vlo,Vhi,List.mem_append,Finset.mem_toList,Finset.mem_sdiff]
    rw [←List.mem_toFinset]
    tauto
  have sumU : (U.map f).sum=(b-1)*A ∧ (U.map g).sum=(b-1)*(2*A) := by
    constructor
    · simpa only [U,List.range_eq_range',Nat.zero_add,b] using ladder_sum f 0 (s-1) A (fun i hi => by simpa using (posU i hi).1)
    · simpa only [U,List.range_eq_range',Nat.zero_add,b] using ladder_sum g 0 (s-1) (2*A) (fun i hi => by simpa using (posU i hi).2)
  have sumV : (V.map f).sum=(b-1)*B ∧ (V.map g).sum=(b-1)*GV :=
    ⟨ladder_sum f s (s-1) B (fun i hi => (posV i hi).1),ladder_sum g s (s-1) GV (fun i hi => (posV i hi).2)⟩
  have sumW : (W.map f).sum=(a-1)*L ∧ (W.map g).sum=(a-1)*GW :=
    ⟨ladder_sum f (2*s) (r-1) L (fun i hi => (posW i hi).1),ladder_sum g (2*s) (r-1) GW (fun i hi => (posW i hi).2)⟩
  have sumX : (X.map f).sum=(a-1)*M ∧ (X.map g).sum=(a-1)*GX :=
    ⟨ladder_sum f (2*s+r) (r-1) M (fun i hi => (posX i hi).1),ladder_sum g (2*s+r) (r-1) GX (fun i hi => (posX i hi).2)⟩
  have sumHi : (Vhi.map f).sum=h*B ∧ (Vhi.map g).sum=h*GV := by
    have hsum (F : Finset ℕ) (f : ℕ → ℤ) : (F.toList.map f).sum=∑ i∈F,f i := by
      change ((F.toList : Multiset ℕ).map f).sum = _
      rw [Finset.coe_toList]; rfl
    constructor
    · rw [hsum]; exact mask_labels_sum (s-1) s h hmask f B (fun i hi => (posV i hi).1)
    · rw [hsum]; exact mask_labels_sum (s-1) s h hmask g GV (fun i hi => (posV i hi).2)
  have sumLo : (Vlo.map f).sum=(b-1-h)*B ∧ (Vlo.map g).sum=(b-1-h)*GV := by
    have hf := (split.map f).sum_eq
    have hg := (split.map g).sum_eq
    simp only [List.map_append,List.sum_append,sumV.1,sumV.2,sumHi.1,sumHi.2] at hf hg
    constructor <;> nlinarith only [hf,hg]
  obtain ⟨cA,cB,cL,cM,cGV,cGW,cGX⟩ := coefficient_bounds x y (by dsimp [x]; omega) (by dsimp [y]; omega)
  change 0<A ∧ 2*A<x^2*y^2-1 at cA
  change 0<B ∧ 2*B<x^2*y^2-1 at cB
  change 0<L ∧ 2*L<x^2*y^2-1 at cL
  change 0<M ∧ 2*M<x^2*y^2-1 at cM
  change 0<GV at cGV
  change 0<GW at cGW
  change 0<GX at cGX
  have up : ∀ i∈U, 0≤f i ∧ 0≤g i := by
    intro i hi
    rw [(posU i (List.mem_range.mp hi)).1,(posU i (List.mem_range.mp hi)).2]
    constructor <;> positivity
  have vp : ∀ i∈V, 0≤f i ∧ 0≤g i := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hi
    simp only [Nat.one_mul]
    rw [(posV j hj).1,(posV j hj).2]; constructor <;> positivity
  have wp : ∀ i∈W, 0≤f i ∧ 0≤g i := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hi
    simp only [Nat.one_mul]
    rw [(posW j hj).1,(posW j hj).2]; constructor <;> positivity
  have xp : ∀ i∈X, 0≤f i ∧ 0≤g i := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hi
    simp only [Nat.one_mul]
    rw [(posX j hj).1,(posX j hj).2]; constructor <;> positivity
  have lop : ∀ i∈Vlo, 0≤f i ∧ 0≤g i := by
    intro i hi
    exact vp i (split.mem_iff.mp (List.mem_append_left Vhi hi))
  have hip : ∀ i∈Vhi, 0≤f i ∧ 0≤g i := by
    intro i hi
    exact vp i (split.mem_iff.mp (List.mem_append_right Vlo hi))
  let F := X++Vhi
  let pre := U++[u]++Vlo++[v]++W++[w]++F
  let word := pre++[z]
  have fpos : ∀ i∈F,0≤f i ∧ 0≤g i := by
    intro i hi; rcases List.mem_append.mp hi with hi|hi
    · exact xp i hi
    · exact hip i hi
  have inventory : (U++[u]++V++[v]++W++[w]++X++[z]) = List.range k := by
    have hUall : U++[u]=List.range s := by
      simpa only [U,u,Nat.succ_eq_add_one,show s-1+1=s by omega] using (List.range_succ (n:=s-1)).symm
    have hVall : V++[v]=List.range' s s := by
      simpa only [V,v,show s+(s-1)=2*s-1 by omega,show s-1+1=s by omega] using
        (List.range'_1_concat (s:=s) (n:=s-1)).symm
    have hWall : W++[w]=List.range' (2*s) r := by
      simpa only [W,w,show 2*s+(r-1)=2*s+r-1 by omega,show r-1+1=r by omega] using
        (List.range'_1_concat (s:=2*s) (n:=r-1)).symm
    have hXall : X++[z]=List.range' (2*s+r) r := by
      simpa only [X,z,k,show 2*s+r+(r-1)=2*r+2*s-1 by omega,show r-1+1=r by omega] using
        (List.range'_1_concat (s:=2*s+r) (n:=r-1)).symm
    have h1 := List.range'_append_1 (s:=0) (m:=s) (n:=s)
    have h2 := List.range'_append_1 (s:=0) (m:=2*s) (n:=r)
    have h3 := List.range'_append_1 (s:=0) (m:=2*s+r) (n:=r)
    simp only [Nat.zero_add,show s+s=2*s by omega] at h1 h2 h3
    calc
      _ = (U++[u])++(V++[v])++(W++[w])++(X++[z]) := by simp only [List.append_assoc]
      _ = _ := by
        rw [hUall,hVall,hWall,hXall,List.range_eq_range',h1,h2,h3]
        rw [show 2*s+r+r=k by dsimp [k]; omega,←List.range_eq_range']
  have hp : word.Perm (List.range k) := by
    rw [←inventory]
    apply Multiset.coe_eq_coe.mp
    have hsplit : (Vlo : Multiset ℕ)+(Vhi : Multiset ℕ)=(V : Multiset ℕ) := by
      simpa only [←Multiset.coe_add] using Multiset.coe_eq_coe.mpr split
    simp only [word,pre,F,←Multiset.coe_add]
    rw [←hsplit]
    ac_rfl
  have gatesOld : Gates (N/2) (U.map f).sum (f u) (Vlo.map f).sum (f v)
      (W.map f).sum (f w) (F.map f).sum (f z) := by
    simp only [F,List.map_append,List.sum_append,sumU.1,sumLo.1,sumW.1,sumX.1,sumHi.1,
      negU.1,negV.1,negW.1,negX.1]
    exact gate.1
  have gatesNew : Gates N (U.map g).sum (g u) (Vlo.map g).sum (g v)
      (W.map g).sum (g w) ((F++[k]).map g).sum (g z) := by
    simp only [F,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,
      sumU.2,sumLo.2,sumW.2,sumX.2,sumHi.2,hear,negU.2,negV.2,negW.2,negX.2,hNN]
    exact gate.2
  have oldstrip : InStrip f (N/2) 0 word := by
    simpa only [word,pre,List.append_assoc] using
      four_strip f (N/2) U Vlo W F u v w z (fun i hi => (up i hi).1)
        (fun i hi => (lop i hi).1) (fun i hi => (wp i hi).1) (fun i hi => (fpos i hi).1) gatesOld
  have newstrip : InStrip g N 0 (pre++[k]++[z]) := by
    simpa only [pre,List.append_assoc] using
      four_strip g N U Vlo W (F++[k]) u v w z (fun i hi => (up i hi).2)
        (fun i hi => (lop i hi).2) (fun i hi => (wp i hi).2)
        (by intro i hi; rcases List.mem_append.mp hi with hi|hi
            · exact (fpos i hi).2
            · rw [List.mem_singleton.mp hi,hear]; exact cA.1.le) gatesNew
  have hp' : (pre++[k]++[z]).Perm (List.range (k+1)) := by
    rw [List.range_succ]
    apply List.Perm.trans (l₂:=word++[k])
    · apply Multiset.coe_eq_coe.mp
      simp only [word,←Multiset.coe_add]; ac_rfl
    · exact hp.append_right [k]
  have hz : ((List.range k).map f).sum=0 := by
    simpa only [f,N,←ht] using ThreeNegativeEqualOuterSourceBridge.source_zero k t (by dsimp [k]; omega)
  have hz' : ((List.range (k+1)).map g).sum=0 := by
    have he : ((2*t : ℕ) : ℤ)=2*A := by push_cast; rw [ht]
    simpa only [g,←he] using ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*t) (by dsimp [k]; omega)
  have hcut : pre.length = k-1 := by
    have hh := hp.length_eq
    simp only [word,List.length_append,List.length_singleton,List.length_range] at hh
    omega
  refine ⟨word.map (label k (by dsimp [k]; omega)),k-1,by dsimp [k]; omega,?_,?_⟩
  · exact lift_order k t (by dsimp [k]; omega) word hp
      (by simpa only [f,N,←ht] using oldstrip) (by simpa only [f,N,←ht] using hz)
  · rw [marked_word k (k-1) (by dsimp [k]; omega) pre [z] hcut (by simpa only [word] using hp)]
    have he : ((2*t : ℕ) : ℤ)=2*A := by push_cast; rw [ht]
    simpa only [List.append_assoc,List.singleton_append] using
      (lift_order (k+1) (2*t) (by dsimp [k]; omega) (pre++[k]++[z]) hp'
      (by have hh : modulus (k+1)/2=N := by omega
          simpa only [g,he,hh] using newstrip)
      (by simpa only [g,he] using hz'))

end D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentFarRight
