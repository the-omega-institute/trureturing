/- GID: D5/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentFarLeft
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/Adjacent/FourNegativeAdjacentFarLeft
   mirror-E: none(waiver:no-public-declarations)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Disjoint low and high physical X masks for the large first paired gap. -/
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentSource

/-! Coupled polynomial peak bounds for the two large-first-radix regimes. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentFarLeft
open SourceWidth PeriodicShortening RunFirstEarTransport
open private label lift_order marked_word ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private coefficient_bounds chains from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentSource
open private Gates four_strip from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule

set_option maxHeartbeats 1600000 in
-- Coupled source identities and prefix bounds expand independent dyadic products.
private theorem small_arithmetic (c b : ℤ) (hc : 2 ≤ c) (hb : c ≤ b) :
    let x := 4*c*b
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
    Gates (N/2) ((x/2-1)*L) (-(N-M)/2) (1*M+(b-1)*A) (-(N-B)/2)
      ((x/2-(2*c))*M) (-(N-A)/2) (((2*c)-1-1)*M+(b-1)*B) (-(N-L)/2) ∧
    Gates N ((x/2-1)*GW) (-((2*N+1)-GX)/2) (1*GX+(b-1)*(2*A)) (-((2*N+1)-GV)/2)
      ((x/2-(2*c))*GX+A) (-((2*N+1)-A)/2) (((2*c)-1-1)*GX+(b-1)*GV) (-((2*N+1)-GW)/2) := by
  dsimp only [Gates]
  have hxdiv : (4*c*b)/2 = 2*b*c := by ring_nf; omega
  have hcdiv : ((4*c*b)^2*(2*b)^2-1)/2 = 32*b^4*c^2 - 1 := by ring_nf; omega
  have hd0 : -(((4*c*b)^2*(2*b)^2-1)-(1+(4*c*b)+(4*c*b)*(2*b)+(4*c*b)*(2*b)^2))/2 = -32*b^4*c^2 + 8*b^3*c + 4*b^2*c + 2*b*c + 1 := by ring_nf; omega
  have hd1 : -(((4*c*b)^2*(2*b)^2-1)-(1+(2*b)+(4*c*b)*(2*b)+(4*c*b)^2*(2*b)))/2 = -32*b^4*c^2 + 16*b^3*c^2 + 4*b^2*c + b + 1 := by ring_nf; omega
  have hd2 : -(((4*c*b)^2*(2*b)^2-1)-(1+(4*c*b)+(4*c*b)^2+(4*c*b)^2*(2*b)))/2 = -32*b^4*c^2 + 16*b^3*c^2 + 8*b^2*c^2 + 2*b*c + 1 := by ring_nf; omega
  have hd3 : -(((4*c*b)^2*(2*b)^2-1)-(1+(2*b)+(2*b)^2+(4*c*b)*(2*b)^2))/2 = -32*b^4*c^2 + 8*b^3*c + 2*b^2 + b + 1 := by ring_nf; omega
  have he0 : -((2*((4*c*b)^2*(2*b)^2-1)+1)-(2*(1+(4*c*b)+(4*c*b)*(2*b)+(4*c*b)*(2*b)^2)-(1+(4*c*b)+(4*c*b)*(2*b))))/2 = -64*b^4*c^2 + 16*b^3*c + 4*b^2*c + 2*b*c + 1 := by ring_nf; omega
  have he1 : -((2*((4*c*b)^2*(2*b)^2-1)+1)-(2*(1+(2*b)+(4*c*b)*(2*b)+(4*c*b)^2*(2*b))-1))/2 = -64*b^4*c^2 + 32*b^3*c^2 + 8*b^2*c + 2*b + 1 := by ring_nf; omega
  have he2 : -((2*((4*c*b)^2*(2*b)^2-1)+1)-(1+(4*c*b)+(4*c*b)^2+(4*c*b)^2*(2*b)))/2 = -64*b^4*c^2 + 16*b^3*c^2 + 8*b^2*c^2 + 2*b*c + 1 := by ring_nf; omega
  have he3 : -((2*((4*c*b)^2*(2*b)^2-1)+1)-(2*(1+(2*b)+(2*b)^2+(4*c*b)*(2*b)^2)-1-(2*b)))/2 = -64*b^4*c^2 + 16*b^3*c + 4*b^2 + b + 1 := by ring_nf; omega
  simp only [hxdiv,hcdiv,hd0,hd1,hd2,hd3,he0,he1,he2,he3]
  let u := c-2
  let v := b-c
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have ec : c=u+2 := by dsimp [u]; ring
  have eb : b=u+2+v := by dsimp [u,v]; ring
  simp only [ec,eb]
  ring_nf
  repeat' constructor
  all_goals first
    | rfl
    | apply le_of_sub_nonneg
      ring_nf
      positivity

set_option maxHeartbeats 1600000 in
-- Coupled source identities and prefix bounds expand independent dyadic products.
private theorem large_arithmetic (p b : ℤ) (hp : 1 ≤ p) (hb : 2 ≤ b) :
    let x := 4*p*b^2
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
    Gates (N/2) ((x/2-1)*L) (-(N-M)/2) (p*M+(b-1)*A) (-(N-B)/2)
      ((x/2-(2*p*b))*M) (-(N-A)/2) (((2*p*b)-p-1)*M+(b-1)*B) (-(N-L)/2) ∧
    Gates N ((x/2-1)*GW) (-((2*N+1)-GX)/2) (p*GX+(b-1)*(2*A)) (-((2*N+1)-GV)/2)
      ((x/2-(2*p*b))*GX+A) (-((2*N+1)-A)/2) (((2*p*b)-p-1)*GX+(b-1)*GV) (-((2*N+1)-GW)/2) := by
  dsimp only [Gates]
  have hxdiv : (4*p*b^2)/2 = 2*b^2*p := by ring_nf; omega
  have hcdiv : ((4*p*b^2)^2*(2*b)^2-1)/2 = 32*b^6*p^2 - 1 := by ring_nf; omega
  have hd0 : -(((4*p*b^2)^2*(2*b)^2-1)-(1+(4*p*b^2)+(4*p*b^2)*(2*b)+(4*p*b^2)*(2*b)^2))/2 = -32*b^6*p^2 + 8*b^4*p + 4*b^3*p + 2*b^2*p + 1 := by ring_nf; omega
  have hd1 : -(((4*p*b^2)^2*(2*b)^2-1)-(1+(2*b)+(4*p*b^2)*(2*b)+(4*p*b^2)^2*(2*b)))/2 = -32*b^6*p^2 + 16*b^5*p^2 + 4*b^3*p + b + 1 := by ring_nf; omega
  have hd2 : -(((4*p*b^2)^2*(2*b)^2-1)-(1+(4*p*b^2)+(4*p*b^2)^2+(4*p*b^2)^2*(2*b)))/2 = -32*b^6*p^2 + 16*b^5*p^2 + 8*b^4*p^2 + 2*b^2*p + 1 := by ring_nf; omega
  have hd3 : -(((4*p*b^2)^2*(2*b)^2-1)-(1+(2*b)+(2*b)^2+(4*p*b^2)*(2*b)^2))/2 = -32*b^6*p^2 + 8*b^4*p + 2*b^2 + b + 1 := by ring_nf; omega
  have he0 : -((2*((4*p*b^2)^2*(2*b)^2-1)+1)-(2*(1+(4*p*b^2)+(4*p*b^2)*(2*b)+(4*p*b^2)*(2*b)^2)-(1+(4*p*b^2)+(4*p*b^2)*(2*b))))/2 = -64*b^6*p^2 + 16*b^4*p + 4*b^3*p + 2*b^2*p + 1 := by ring_nf; omega
  have he1 : -((2*((4*p*b^2)^2*(2*b)^2-1)+1)-(2*(1+(2*b)+(4*p*b^2)*(2*b)+(4*p*b^2)^2*(2*b))-1))/2 = -64*b^6*p^2 + 32*b^5*p^2 + 8*b^3*p + 2*b + 1 := by ring_nf; omega
  have he2 : -((2*((4*p*b^2)^2*(2*b)^2-1)+1)-(1+(4*p*b^2)+(4*p*b^2)^2+(4*p*b^2)^2*(2*b)))/2 = -64*b^6*p^2 + 16*b^5*p^2 + 8*b^4*p^2 + 2*b^2*p + 1 := by ring_nf; omega
  have he3 : -((2*((4*p*b^2)^2*(2*b)^2-1)+1)-(2*(1+(2*b)+(2*b)^2+(4*p*b^2)*(2*b)^2)-1-(2*b)))/2 = -64*b^6*p^2 + 16*b^4*p + 4*b^2 + b + 1 := by ring_nf; omega
  simp only [hxdiv,hcdiv,hd0,hd1,hd2,hd3,he0,he1,he2,he3]
  let u := p-1
  let v := b-2
  have hu : 0 ≤ u := by dsimp [u]; omega
  have hv : 0 ≤ v := by dsimp [v]; omega
  have ep : p=u+1 := by dsimp [u]; ring
  have eb : b=v+2 := by dsimp [v]; ring
  simp only [ep,eb]
  ring_nf
  repeat' constructor
  all_goals first
    | rfl
    | apply le_of_sub_nonneg
      ring_nf
      positivity

set_option maxHeartbeats 2400000 in
-- Coupled source identities and prefix bounds expand independent dyadic products.
private theorem symbolic (r s : ℕ) (hs : 2 ≤ s) (hr : s+2 ≤ r) :
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
  let T : ℤ := 2^(r-s)
  let p : ℤ := 2^(r-2*s)
  let t : ℕ := 1+2^r+2^(2*r)+2^(2*r+s)
  let f := fun i : ℕ => centered N ((2 : ℤ)^i*A)
  let g := fun i : ℕ => centered (modulus (k+1)) ((2 : ℤ)^i*(2*A))
  have ha : 2 ≤ a := by
    simpa only [a,pow_one] using pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (show 1 ≤ r-1 by omega)
  have hb : 2 ≤ b := by
    simpa only [b,pow_one] using pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (show 1 ≤ s-1 by omega)
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
  have hhalf : x/2=a := by dsimp [x]; omega
  have haT : a=b*T := by
    dsimp [a,b,T]
    rw [show r-1=(s-1)+(r-s) by omega,pow_add]
  have gate :
      Gates (N/2) ((a-1)*L) (-(N-M)/2) (p*M+(b-1)*A) (-(N-B)/2)
        ((a-T)*M) (-(N-A)/2) ((T-p-1)*M+(b-1)*B) (-(N-L)/2) ∧
      Gates N ((a-1)*GW) (-((2*N+1)-GX)/2) (p*GX+(b-1)*(2*A)) (-((2*N+1)-GV)/2)
        ((a-T)*GX+A) (-((2*N+1)-A)/2) ((T-p-1)*GX+(b-1)*GV) (-((2*N+1)-GW)/2) := by
    rw [hN]
    by_cases hreg : r ≤ 2*s
    · let c : ℤ := 2^(r-s-1)
      have hc : 2 ≤ c := by
        simpa only [c,pow_one] using pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (show 1 ≤ r-s-1 by omega)
      have hcb : c ≤ b := pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) (by omega)
      have hcT : 2*c=T := by
        dsimp [c,T]
        conv_rhs => rw [show r-s=(r-s-1)+1 by omega,pow_succ]
        ring
      have hcx : 4*c*b=x := by dsimp [x]; rw [haT,←hcT]; ring
      have hp : p=1 := by dsimp [p]; rw [show r-2*s=0 by omega]; norm_num
      rw [hp]
      simpa only [hcx,hcT,hhalf,one_mul] using small_arithmetic c b hc hcb
    · have hp : 1 ≤ p := by
        dsimp [p]
        exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2^(r-2*s))
      have hpx : 4*p*b^2=x := by
        dsimp only [p,b]
        rw [←hx]
        conv_rhs => rw [show r=(r-2*s)+(s-1)+(s-1)+2 by omega]
        simp only [pow_add,pow_succ]; ring
      have hpT : 2*p*b=T := by
        dsimp only [p,b,T]
        conv_rhs => rw [show r-s=(r-2*s)+(s-1)+1 by omega]
        simp only [pow_add,pow_succ]; ring
      simpa only [hpx,hpT,hhalf] using large_arithmetic p b hp hb
  obtain ⟨hU,hV,hW,hX,hU',hV',hW',hX',hear⟩ := chains r s (by omega) hs
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
  let off := 2*s+r
  let Xlow := List.range' off (r-s)
  let Xone := [off+(r-2*s)]
  let Xrest := Xlow.erase (off+(r-2*s))
  let Xhigh := List.range' (off+(r-s)) (s-1)
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
  have hmem : off+(r-2*s) ∈ Xlow := by
    apply List.mem_range'.mpr
    exact ⟨r-2*s,by omega,by omega⟩
  have split : (Xone++Xrest).Perm Xlow := by
    simpa only [Xone,List.singleton_append] using (List.perm_cons_erase hmem).symm
  have sumU : (U.map f).sum=(b-1)*A ∧ (U.map g).sum=(b-1)*(2*A) := by
    constructor
    · simpa only [U,List.range_eq_range',Nat.zero_add,b] using ladder_sum f 0 (s-1) A (fun i hi => by simpa using (posU i hi).1)
    · simpa only [U,List.range_eq_range',Nat.zero_add,b] using ladder_sum g 0 (s-1) (2*A) (fun i hi => by simpa using (posU i hi).2)
  have sumV : (V.map f).sum=(b-1)*B ∧ (V.map g).sum=(b-1)*GV :=
    ⟨ladder_sum f s (s-1) B (fun i hi => (posV i hi).1),ladder_sum g s (s-1) GV (fun i hi => (posV i hi).2)⟩
  have sumW : (W.map f).sum=(a-1)*L ∧ (W.map g).sum=(a-1)*GW :=
    ⟨ladder_sum f (2*s) (r-1) L (fun i hi => (posW i hi).1),ladder_sum g (2*s) (r-1) GW (fun i hi => (posW i hi).2)⟩
  have sumLow : (Xlow.map f).sum=(T-1)*M ∧ (Xlow.map g).sum=(T-1)*GX :=
    ⟨ladder_sum f off (r-s) M (fun i hi => (posX i (by omega)).1),
      ladder_sum g off (r-s) GX (fun i hi => (posX i (by omega)).2)⟩
  have sumOne : (Xone.map f).sum=p*M ∧ (Xone.map g).sum=p*GX := by
    simpa only [Xone,List.map_singleton,List.sum_singleton,p] using posX (r-2*s) (by omega)
  have posHigh (i : ℕ) (hi : i<s-1) :
      f (off+(r-s)+i)=2^i*(T*M) ∧ g (off+(r-s)+i)=2^i*(T*GX) := by
    rw [show off+(r-s)+i=2*s+r+((r-s)+i) by dsimp [off]; omega,
      (posX ((r-s)+i) (by omega)).1,(posX ((r-s)+i) (by omega)).2,pow_add]
    dsimp only [T]
    constructor <;> ring
  have sumHigh : (Xhigh.map f).sum=(a-T)*M ∧ (Xhigh.map g).sum=(a-T)*GX := by
    have hf := ladder_sum f (off+(r-s)) (s-1) (T*M) (fun i hi => (posHigh i hi).1)
    have hg := ladder_sum g (off+(r-s)) (s-1) (T*GX) (fun i hi => (posHigh i hi).2)
    change (Xhigh.map f).sum=(b-1)*(T*M) at hf
    change (Xhigh.map g).sum=(b-1)*(T*GX) at hg
    rw [hf,hg,haT]; constructor <;> ring
  have sumRest : (Xrest.map f).sum=(T-p-1)*M ∧ (Xrest.map g).sum=(T-p-1)*GX := by
    have hf := (split.map f).sum_eq
    have hg := (split.map g).sum_eq
    simp only [List.map_append,List.sum_append,sumLow.1,sumLow.2,sumOne.1,sumOne.2] at hf hg
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
  have lp : ∀ i∈Xlow,0≤f i ∧ 0≤g i := by
    intro i hi; obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hi
    simp only [Nat.one_mul]
    rw [(posX j (by omega)).1,(posX j (by omega)).2]; constructor <;> positivity
  have op : ∀ i∈Xone,0≤f i ∧ 0≤g i := by
    intro i hi; exact lp i (split.mem_iff.mp (List.mem_append_left Xrest hi))
  have rp : ∀ i∈Xrest,0≤f i ∧ 0≤g i := by
    intro i hi; exact lp i (split.mem_iff.mp (List.mem_append_right Xone hi))
  have hpHigh : ∀ i∈Xhigh,0≤f i ∧ 0≤g i := by
    intro i hi; obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp hi
    simp only [Nat.one_mul]
    rw [(posHigh j hj).1,(posHigh j hj).2]
    have hT : 0≤T := by dsimp [T]; positivity
    constructor <;> positivity
  let F2 := Xone++U
  let F4 := Xrest++V
  let pre := W++[w]++F2++[u]++Xhigh
  let post := [z]++F4++[v]
  let word := pre++post
  have p2 : ∀ i∈F2,0≤f i ∧ 0≤g i := by
    intro i hi; rcases List.mem_append.mp hi with hi|hi
    · exact op i hi
    · exact up i hi
  have p4 : ∀ i∈F4,0≤f i ∧ 0≤g i := by
    intro i hi; rcases List.mem_append.mp hi with hi|hi
    · exact rp i hi
    · exact vp i hi
  have inventory : U++[u]++V++[v]++W++[w]++Xlow++Xhigh++[z]=List.range k := by
    have hUall : U++[u]=List.range s := by
      simpa only [U,u,Nat.succ_eq_add_one,show s-1+1=s by omega] using (List.range_succ (n:=s-1)).symm
    have hVall : V++[v]=List.range' s s := by
      simpa only [V,v,show s+(s-1)=2*s-1 by omega,show s-1+1=s by omega] using
        (List.range'_1_concat (s:=s) (n:=s-1)).symm
    have hWall : W++[w]=List.range' (2*s) r := by
      simpa only [W,w,show 2*s+(r-1)=2*s+r-1 by omega,show r-1+1=r by omega] using
        (List.range'_1_concat (s:=2*s) (n:=r-1)).symm
    have hXsplit : Xlow++Xhigh=List.range' off (r-1) := by
      simpa only [Xlow,Xhigh,show r-s+(s-1)=r-1 by omega] using
        (List.range'_append_1 (s:=off) (m:=r-s) (n:=s-1))
    have hXall : Xlow++Xhigh++[z]=List.range' (2*s+r) r := by
      rw [hXsplit]
      simpa only [off,z,k,show 2*s+r+(r-1)=2*r+2*s-1 by omega,show r-1+1=r by omega] using
        (List.range'_1_concat (s:=2*s+r) (n:=r-1)).symm
    have h1 := List.range'_append_1 (s:=0) (m:=s) (n:=s)
    have h2 := List.range'_append_1 (s:=0) (m:=2*s) (n:=r)
    have h3 := List.range'_append_1 (s:=0) (m:=2*s+r) (n:=r)
    simp only [Nat.zero_add,show s+s=2*s by omega] at h1 h2 h3
    calc
      _ = (U++[u])++(V++[v])++(W++[w])++(Xlow++Xhigh++[z]) := by simp only [List.append_assoc]
      _ = _ := by
        rw [hUall,hVall,hWall,hXall,List.range_eq_range',h1,h2,h3]
        rw [show 2*s+r+r=k by dsimp [k]; omega,←List.range_eq_range']
  have hp : word.Perm (List.range k) := by
    rw [←inventory]
    apply Multiset.coe_eq_coe.mp
    have hsplit : (Xone : Multiset ℕ)+(Xrest : Multiset ℕ)=(Xlow : Multiset ℕ) := by
      simpa only [←Multiset.coe_add] using Multiset.coe_eq_coe.mpr split
    simp only [word,pre,post,F2,F4,←Multiset.coe_add]
    rw [←hsplit]
    ac_rfl
  have gatesOld : Gates (N/2) (W.map f).sum (f w) (F2.map f).sum (f u)
      (Xhigh.map f).sum (f z) (F4.map f).sum (f v) := by
    simp only [F2,F4,List.map_append,List.sum_append,sumW.1,sumOne.1,sumU.1,sumHigh.1,sumRest.1,sumV.1,
      negW.1,negU.1,negX.1,negV.1]
    exact gate.1
  have gatesNew : Gates N (W.map g).sum (g w) (F2.map g).sum (g u)
      ((Xhigh++[k]).map g).sum (g z) (F4.map g).sum (g v) := by
    simp only [F2,F4,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,
      sumW.2,sumOne.2,sumU.2,sumHigh.2,sumRest.2,sumV.2,hear,negW.2,negU.2,negX.2,negV.2,hNN]
    exact gate.2
  have oldstrip : InStrip f (N/2) 0 word := by
    simpa only [word,pre,post,List.append_assoc] using
      four_strip f (N/2) W F2 Xhigh F4 w u z v (fun i hi => (wp i hi).1)
        (fun i hi => (p2 i hi).1) (fun i hi => (hpHigh i hi).1) (fun i hi => (p4 i hi).1) gatesOld
  have newstrip : InStrip g N 0 (pre++[k]++post) := by
    simpa only [pre,post,List.append_assoc] using
      four_strip g N W F2 (Xhigh++[k]) F4 w u z v (fun i hi => (wp i hi).2)
        (fun i hi => (p2 i hi).2)
        (by intro i hi; rcases List.mem_append.mp hi with hi|hi
            · exact (hpHigh i hi).2
            · rw [List.mem_singleton.mp hi,hear]; exact cA.1.le)
        (fun i hi => (p4 i hi).2) gatesNew
  have hp' : (pre++[k]++post).Perm (List.range (k+1)) := by
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
  have cut : pre.length=r+2*s := by simp only [pre,F2,W,Xone,U,Xhigh,List.length_append,List.length_singleton,List.length_range,List.length_range']; omega
  refine ⟨word.map (label k (by dsimp [k]; omega)),r+2*s,by omega,?_,?_⟩
  · exact lift_order k t (by dsimp [k]; omega) word hp
      (by simpa only [f,N,←ht] using oldstrip) (by simpa only [f,N,←ht] using hz)
  · rw [marked_word k (r+2*s) (by dsimp [k]; omega) pre post cut (by simpa only [word] using hp)]
    have he : ((2*t : ℕ) : ℤ)=2*A := by push_cast; rw [ht]
    simpa only [List.append_assoc,List.singleton_append] using
      (lift_order (k+1) (2*t) (by dsimp [k]; omega) (pre++[k]++post) hp'
      (by have hh : modulus (k+1)/2=N := by omega
          simpa only [g,he,hh] using newstrip)
      (by simpa only [g,he] using hz'))

end D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentFarLeft
