/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/EqualGaps
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/EqualGaps
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: A literal first-ear physical construction for all equal first-three gaps. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.EqualGapsArithmetic
import D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift

/-! One withheld physical U occurrence gives both complete prefix strips. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.EqualGaps
open SourceWidth PeriodicShortening RunFirstEarTransport
open private source_table from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable
open private endpoints from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.EqualGapsArithmetic
open private Gates four_strip
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule
open private negative_step
  from D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
open private label lift_order marked_word ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

private theorem reserve_inventory (a d s : ℕ) (ha : 2 ≤ a) (hd : a + 2 ≤ d)
    (hs : s=d-a-1) :
    let U := List.range s ++ List.range' (s+1) (a-1)
    (U ++ [d-1] ++ List.range' d (a-1) ++ [d+a-1] ++
      List.range' (d+a) (a-1) ++ [d+a+a-1] ++
      ([s] ++ List.range' (d+a+a) (a-1)) ++ [d+a+a+a-1]).Perm
        (List.range (a+a+a+d)) := by
  dsimp only
  have hsplit : List.range s ++ [s] ++ List.range' (s+1) (a-1) = List.range (d-1) := by
    rw [← List.range_succ]
    simp only [List.range_eq_range']
    simpa only [Nat.zero_add, show s+1+(a-1)=d-1 by omega] using
      List.range'_append_1 (s:=0) (m:=s+1) (n:=a-1)
  have hu : ((List.range s ++ List.range' (s+1) (a-1)) ++ [s]).Perm
      (List.range (d-1)) := by
    rw [← hsplit]
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl
  have merge (o n : ℕ) (hn : 1 ≤ n) :
      List.range' o (n-1) ++ [o+n-1] = List.range' o n := by
    simpa only [show o+(n-1)=o+n-1 by omega, show n-1+1=n by omega] using
      (List.range'_1_concat (s:=o) (n:=n-1)).symm
  have hall : (List.range (d-1) ++ [d-1]) ++
      (List.range' d (a-1) ++ [d+a-1]) ++
      (List.range' (d+a) (a-1) ++ [d+a+a-1]) ++
      (List.range' (d+a+a) (a-1) ++ [d+a+a+a-1]) = List.range (a+a+a+d) := by
    rw [← List.range_succ, show (d-1).succ=d by omega,
      merge d a (by omega), merge (d+a) a (by omega), merge (d+a+a) a (by omega)]
    simp only [List.range_eq_range']
    have h1 := List.range'_append_1 (s:=0) (m:=d) (n:=a)
    have h2 := List.range'_append_1 (s:=0) (m:=d+a) (n:=a)
    have h3 := List.range'_append_1 (s:=0) (m:=d+a+a) (n:=a)
    simp only [Nat.zero_add] at h1 h2 h3
    rw [h1,h2,h3]
    congr 1; omega
  have hreorder :
      ((List.range s ++ List.range' (s+1) (a-1)) ++ [d-1] ++
        List.range' d (a-1) ++ [d+a-1] ++ List.range' (d+a) (a-1) ++ [d+a+a-1] ++
        ([s] ++ List.range' (d+a+a) (a-1)) ++ [d+a+a+a-1]).Perm
      ((((List.range s ++ List.range' (s+1) (a-1)) ++ [s]) ++ [d-1]) ++
        (List.range' d (a-1) ++ [d+a-1]) ++ (List.range' (d+a) (a-1) ++ [d+a+a-1]) ++
        (List.range' (d+a+a) (a-1) ++ [d+a+a+a-1])) := by
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl
  exact hreorder.trans (by rw [←hall]; exact (((hu.append_right [d-1]).append_right _).append_right _).append_right _)

set_option maxHeartbeats 1600000 in
-- The complete physical inventory, masses and both prefix strips are elaborated together.
/-- An explicit physical single-bit reserve, with the literal ear at cut zero.
The first three gaps coincide; the fourth gap is arbitrary above a+2. -/
theorem actualSource_equal_gaps_first_ear (a d : ℕ) (ha : 2 ≤ a) (hd : a + 2 ≤ d) :
    ∃ sigma : List (Fin (a+a+a+d)),
      OriginalOrder (a+a+a+d) (1+2^a+2^(a+a)+2^(a+a+a)) sigma ∧
      OriginalOrder (a+a+a+d+1) (2*(1+2^a+2^(a+a)+2^(a+a+a)))
        (earWord (a+a+a+d) sigma 0) := by
  let k := a+a+a+d
  let seed := 1+2^a+2^(a+a)+2^(a+a+a)
  let s := d-a-1
  let R : ℤ := 2^a
  let T : ℤ := 2^d
  let p : ℤ := 2^(a-1)
  let l : ℤ := 2^s
  let u : ℤ := 2^(d-1)
  let C := 1+R+R*R
  let A := R*R*R+C
  let B := T*C+1
  let V := T*(R*(1+R))+1+R
  let W := T*(R*R)+1+R+R*R
  let GV := 2*B-1
  let GW := 2*V-1-R
  let GX := 2*W-1-R-R*R
  let N := R*R*R*T-1
  let f := fun i : ℕ => centered N ((2 : ℤ)^i*A)
  let g := fun i : ℕ => centered (2*N+1) ((2 : ℤ)^i*(2*A))
  have hp : 2 ≤ p := by simpa [p] using pow_le_pow_right₀ (by decide : (1:ℤ)≤2) (show 1≤a-1 by omega)
  have hl : 2 ≤ l := by simpa [l] using pow_le_pow_right₀ (by decide : (1:ℤ)≤2) (show 1≤s by dsimp [s]; omega)
  have hR : R=2*p := by
    dsimp [R,p]
    calc
      (2:ℤ)^a=2^((a-1)+1) := by congr 1; omega
      _=2*2^(a-1) := by rw [pow_succ]; ring
  have hT : T=2*u := by
    dsimp [T,u]
    calc
      (2:ℤ)^d=2^((d-1)+1) := by congr 1; omega
      _=2*2^(d-1) := by rw [pow_succ]; ring
  have hu : u=R*l := by dsimp [u,R,l]; rw [←pow_add]; congr 1; dsimp [s]; omega
  have hN : N=2*(R^4*l)-1 := by dsimp [N]; rw [hT,hu]; ring
  have hhalf : N/2=R^4*l-1 := by omega
  obtain ⟨hA,hB,hV,hW,huf,hvf,hwf,hxf,hug,hvg,hwg,hxg,hfresh⟩ :=
    source_table a a a d ha ha ha (by omega)
  change 1≤A ∧ A<N at hA
  change 1≤B ∧ B<N at hB
  change 1≤V ∧ V<N at hV
  change 1≤W ∧ W<N at hW
  change ∀ i<d, f i=if i+1<d then 2^i*A else -(N-B)/2 at huf
  change ∀ i<a, f (d+i)=if i+1<a then 2^i*B else -(N-V)/2 at hvf
  change ∀ i<a, f (d+a+i)=if i+1<a then 2^i*V else -(N-W)/2 at hwf
  change ∀ i<a, f (d+a+a+i)=if i+1<a then 2^i*W else -(N-A)/2 at hxf
  change ∀ i<d, g i=if i+1<d then 2^i*(2*A) else -((2*N+1)-GV)/2 at hug
  change ∀ i<a, g (d+i)=if i+1<a then 2^i*GV else -((2*N+1)-GW)/2 at hvg
  change ∀ i<a, g (d+a+i)=if i+1<a then 2^i*GW else -((2*N+1)-GX)/2 at hwg
  change ∀ i<a, g (d+a+a+i)=if i+1<a then 2^i*GX else -((2*N+1)-A)/2 at hxg
  have hear : g k=A := by simpa only [show d+a+a+a=k by dsimp [k]; omega] using hfresh
  have posU (i : ℕ) (hi : i<d-1) : f i=2^i*A ∧ g i=2^i*(2*A) :=
    ⟨(huf i (by omega)).trans (ite_eq_left (by omega)),(hug i (by omega)).trans (ite_eq_left (by omega))⟩
  have posV (i : ℕ) (hi : i<a-1) : f (d+i)=2^i*B ∧ g (d+i)=2^i*GV :=
    ⟨(hvf i (by omega)).trans (ite_eq_left (by omega)),(hvg i (by omega)).trans (ite_eq_left (by omega))⟩
  have posW (i : ℕ) (hi : i<a-1) : f (d+a+i)=2^i*V ∧ g (d+a+i)=2^i*GW :=
    ⟨(hwf i (by omega)).trans (ite_eq_left (by omega)),(hwg i (by omega)).trans (ite_eq_left (by omega))⟩
  have posX (i : ℕ) (hi : i<a-1) : f (d+a+a+i)=2^i*W ∧ g (d+a+a+i)=2^i*GX :=
    ⟨(hxf i (by omega)).trans (ite_eq_left (by omega)),(hxg i (by omega)).trans (ite_eq_left (by omega))⟩
  have rels : 2*u*A=N+B ∧ 2*p*B=N+V ∧ 2*p*V=N+W ∧ 2*p*W=N+A := by
    dsimp [N,A,B,V,W,C]; rw [hT,hR]; refine ⟨?_,?_,?_,?_⟩ <;> ring
  have grels : 2*u*(2*A)=2*N+1+GV ∧ 2*p*GV=2*N+1+GW ∧
      2*p*GW=2*N+1+GX ∧ 2*p*GX=2*N+1+A := by
    dsimp [N,A,B,V,W,C,GV,GW,GX]; rw [hT,hR]; refine ⟨?_,?_,?_,?_⟩ <;> ring
  have negU : f (d-1)=B-u*A ∧ g (d-1)=GV-u*(2*A) := by
    have hf:=huf (d-1) (by omega); have hg:=hug (d-1) (by omega)
    rw [ite_eq_right (by omega),negative_step N A B u rels.1] at hf
    rw [ite_eq_right (by omega),negative_step (2*N+1) (2*A) GV u grels.1] at hg
    exact ⟨hf,hg⟩
  have negV : f (d+a-1)=V-p*B ∧ g (d+a-1)=GW-p*GV := by
    have hf:=hvf (a-1) (by omega); have hg:=hvg (a-1) (by omega)
    rw [ite_eq_right (by omega),negative_step N B V p rels.2.1] at hf
    rw [ite_eq_right (by omega),negative_step (2*N+1) GV GW p grels.2.1] at hg
    simpa only [show d+(a-1)=d+a-1 by omega] using And.intro hf hg
  have negW : f (d+a+a-1)=W-p*V ∧ g (d+a+a-1)=GX-p*GW := by
    have hf:=hwf (a-1) (by omega); have hg:=hwg (a-1) (by omega)
    rw [ite_eq_right (by omega),negative_step N V W p rels.2.2.1] at hf
    rw [ite_eq_right (by omega),negative_step (2*N+1) GW GX p grels.2.2.1] at hg
    simpa only [show d+a+(a-1)=d+a+a-1 by omega] using And.intro hf hg
  have negX : f (d+a+a+a-1)=A-p*W ∧ g (d+a+a+a-1)=A-p*GX := by
    have hf:=hxf (a-1) (by omega); have hg:=hxg (a-1) (by omega)
    rw [ite_eq_right (by omega),negative_step N W A p rels.2.2.2] at hf
    rw [ite_eq_right (by omega),negative_step (2*N+1) GX A p grels.2.2.2] at hg
    simpa only [show d+a+a+(a-1)=d+a+a+a-1 by omega] using And.intro hf hg
  let P1 := List.range s ++ List.range' (s+1) (a-1)
  let P2 := List.range' d (a-1)
  let P3 := List.range' (d+a) (a-1)
  let P4 := [s] ++ List.range' (d+a+a) (a-1)
  have hUp : (P1++[s]).Perm (List.range (d-1)) := by
    have he : List.range s ++ [s] ++ List.range' (s+1) (a-1)=List.range (d-1) := by
      rw [←List.range_succ]
      simp only [Nat.succ_eq_add_one,List.range_eq_range']
      simpa only [Nat.zero_add,show s+1+(a-1)=d-1 by dsimp [s]; omega] using
        List.range'_append_1 (s:=0) (m:=s+1) (n:=a-1)
    rw [←he]
    apply Multiset.coe_eq_coe.mp
    simp only [P1,←Multiset.coe_add]; ac_rfl
  have hmassU : (P1.map f).sum=(u-1-l)*A ∧ (P1.map g).sum=2*(u-1-l)*A := by
    have hf:=(hUp.map f).sum_eq
    have hg:=(hUp.map g).sum_eq
    have hs:=posU s (by dsimp [s]; omega)
    have hsf:=ladder_sum f 0 (d-1) A (by intro i hi; simpa using (posU i hi).1)
    have hsg:=ladder_sum g 0 (d-1) (2*A) (by intro i hi; simpa using (posU i hi).2)
    simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton] at hf hg
    rw [←List.range_eq_range'] at hsf hsg
    change _=(u-1)*A at hsf
    change _=(u-1)*(2*A) at hsg
    change f s=l*A ∧ g s=l*(2*A) at hs
    rw [hs.1,hsf] at hf; rw [hs.2,hsg] at hg
    constructor <;> linarith
  have hmassV : (P2.map f).sum=(p-1)*B ∧ (P2.map g).sum=(p-1)*GV :=
    ⟨ladder_sum f d (a-1) B (by intro i hi; exact (posV i hi).1),
     ladder_sum g d (a-1) GV (by intro i hi; exact (posV i hi).2)⟩
  have hmassW : (P3.map f).sum=(p-1)*V ∧ (P3.map g).sum=(p-1)*GW :=
    ⟨ladder_sum f (d+a) (a-1) V (by intro i hi; exact (posW i hi).1),
     ladder_sum g (d+a) (a-1) GW (by intro i hi; exact (posW i hi).2)⟩
  have hmassX : (P4.map f).sum=l*A+(p-1)*W ∧ (P4.map g).sum=2*l*A+(p-1)*GX := by
    have hs:=posU s (by dsimp [s]; omega)
    have hf:=ladder_sum f (d+a+a) (a-1) W (by intro i hi; exact (posX i hi).1)
    have hg:=ladder_sum g (d+a+a) (a-1) GX (by intro i hi; exact (posX i hi).2)
    simp only [P4,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,hs.1,hs.2,hf,hg]
    exact ⟨rfl,by ring⟩
  have hpositive : 0≤A ∧ 0≤B ∧ 0≤V ∧ 0≤W ∧ 0≤GV ∧ 0≤GW ∧ 0≤GX := by
    dsimp [A,B,V,W,C,GV,GW,GX]; rw [hR,hT]; refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> ring_nf <;> positivity
  have pos1 (h : ℕ→ℤ) (H : ℤ) (hH : 0≤H)
      (hh : ∀ i<d-1, h i=2^i*H) : ∀ i∈P1, 0≤h i := by
    intro i hi
    have hi' : i<d-1 := List.mem_range.mp (hUp.mem_iff.mp (List.mem_append_left _ hi))
    rw [hh i hi']; positivity
  have posblock (h : ℕ→ℤ) (H : ℤ) (o : ℕ) (hH : 0≤H)
      (hh : ∀ i<a-1, h (o+i)=2^i*H) : ∀ i∈List.range' o (a-1), 0≤h i := by
    intro i hi
    have hi':=List.mem_range'.mp hi
    have he : i=o+(i-o) := by omega
    rw [he,hh (i-o) (by omega)]; positivity
  have pos4 (h : ℕ→ℤ) (H : ℤ) (hH : 0≤H) (hs : 0≤h s)
      (hh : ∀ i<a-1, h (d+a+a+i)=2^i*H) : ∀ i∈P4, 0≤h i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · simpa only [List.mem_singleton.mp hi] using hs
    · exact posblock h H (d+a+a) hH hh i hi
  have hgates : Gates (N/2) (P1.map f).sum (f (d-1)) (P2.map f).sum (f (d+a-1))
      (P3.map f).sum (f (d+a+a-1)) (P4.map f).sum (f (d+a+a+a-1)) ∧
      Gates N (([k]++P1).map g).sum (g (d-1)) (P2.map g).sum (g (d+a-1))
      (P3.map g).sum (g (d+a+a-1)) (P4.map g).sum (g (d+a+a+a-1)) := by
    rw [hmassU.1,hmassV.1,hmassW.1,hmassX.1,negU.1,negV.1,negW.1,negX.1,
      List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,hear,
      hmassU.2,hmassV.2,hmassW.2,hmassX.2,negU.2,negV.2,negW.2,negX.2,hhalf,hN]
    convert endpoints p l hp hl using 3 <;> simp only [A,B,V,W,C,GV,GW,GX,hu,hT,hR] <;> ring
  let word := P1++[d-1]++P2++[d+a-1]++P3++[d+a+a-1]++P4++[d+a+a+a-1]
  have hold : InStrip f (N/2) 0 word := by
    exact four_strip f (N/2) P1 P2 P3 P4 (d-1) (d+a-1) (d+a+a-1) (d+a+a+a-1)
      (pos1 f A hpositive.1 (by intro i hi; exact (posU i hi).1))
      (posblock f B d hpositive.2.1 (by intro i hi; exact (posV i hi).1))
      (posblock f V (d+a) hpositive.2.2.1 (by intro i hi; exact (posW i hi).1))
      (pos4 f W hpositive.2.2.2.1 (by rw [(posU s (by dsimp [s];omega)).1]; positivity)
        (by intro i hi; exact (posX i hi).1)) hgates.1
  have hnew : InStrip g N 0 ([k]++word) := by
    have posg : ∀ i∈[k]++P1, 0≤g i := by
      intro i hi; rcases List.mem_append.mp hi with hi|hi
      · rw [List.mem_singleton.mp hi,hear]; exact hpositive.1
      · exact pos1 g (2*A) (by positivity) (by intro i hi;exact (posU i hi).2) i hi
    simpa only [word,List.append_assoc] using
      four_strip g N ([k]++P1) P2 P3 P4 (d-1) (d+a-1) (d+a+a-1) (d+a+a+a-1)
        posg (posblock g GV d hpositive.2.2.2.2.1 (by intro i hi; exact (posV i hi).2))
        (posblock g GW (d+a) hpositive.2.2.2.2.2.1 (by intro i hi; exact (posW i hi).2))
        (pos4 g GX hpositive.2.2.2.2.2.2 (by rw [(posU s (by dsimp [s];omega)).2]; positivity)
          (by intro i hi;exact (posX i hi).2)) hgates.2
  have hperm : word.Perm (List.range k) := reserve_inventory a d s ha hd rfl
  have hmod : modulus k=N := by
    dsimp [modulus,k,N,R,T]
    simp only [pow_add]
  have hmod' : modulus (k+1)=2*N+1 := by dsimp [modulus]; rw [pow_succ]; rw [←hmod]; dsimp [modulus]; ring
  have hseed : (seed:ℤ)=A := by
    dsimp [seed,A,C,R]
    simp only [pow_add]; ring
  have hk : 0<k := by dsimp [k];omega
  have old : OriginalOrder k seed (word.map (label k hk)) := by
    apply lift_order k seed hk word hperm
    · simpa only [f,hmod,hseed] using hold
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero k seed (by dsimp [k];omega)
  have newperm : ([k]++word).Perm (List.range (k+1)) := by
    have hp:= (List.perm_append_singleton k word).symm
    have hr : List.range k++[k]=List.range (k+1) := by simpa only [Nat.succ_eq_add_one] using (List.range_succ (n:=k)).symm
    exact hp.trans ((hperm.append_right [k]).trans (List.Perm.of_eq hr))
  have new : OriginalOrder (k+1) (2*seed) (([k]++word).map (label (k+1) (by omega))) := by
    apply lift_order (k+1) (2*seed) (by omega) ([k]++word) newperm
    · have hhalf' : (2*N+1)/2=N := by omega
      simpa only [g,hmod',Nat.cast_mul,Nat.cast_ofNat,hseed,hhalf'] using hnew
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*seed) (by dsimp [k];omega)
  refine ⟨word.map (label k hk),old,?_⟩
  rw [show earWord k (word.map (label k hk)) 0=([k]++word).map (label (k+1) (by omega)) by
    simpa using marked_word k 0 hk [] word rfl hperm]
  exact new
end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.EqualGaps
