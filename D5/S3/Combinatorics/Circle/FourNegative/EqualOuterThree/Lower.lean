/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualOuterThree/Lower
   generality: I
   mirror-B: none(waiver:private-consumed-construction-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-construction)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Consumed lower construction for the complete equal-outer-three family. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree.LowerArithmetic
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
import D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift

/-! The lower physical construction, consumed by the full family endpoint. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree
open SourceWidth PeriodicShortening RunFirstEarTransport
open private source_table
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable
open private new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private endpoints
  from D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree.LowerArithmetic
open private Gates four_strip
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule
open private negative_step
  from D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
open private label lift_order marked_word ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

private theorem pow_step (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ)^n = 2 * 2^(n-1) := by
  calc
    (2 : ℤ)^n = 2^((n-1)+1) := by congr 1; omega
    _ = 2 * 2^(n-1) := by rw [pow_succ]; ring

private theorem inventory (s b h : ℕ) (hb : 2 ≤ b) (hs : b+2 ≤ s)
    (hh : h=s-b-1) :
    let T := List.range' s h
    let R := List.range' (s+h) (s-h-1)
    (List.range' (2*s+b) (s-1) ++ [3*s+b-1] ++
      List.range (s-1) ++ [s-1] ++ R ++ [2*s-1] ++
      (List.range' (2*s) (b-1) ++ T) ++ [2*s+b-1]).Perm
      (List.range (3*s+b)) := by
  dsimp only
  have hT : List.range' s h ++ List.range' (s+h) (s-h-1) =
      List.range' s (s-1) := by
    simpa only [show h+(s-h-1)=s-1 by omega] using
      (List.range'_append_1 (s:=s) (m:=h) (n:=s-h-1))
  have hTR : List.range' s h ++ List.range' (s+h) (s-h-1) ++ [2*s-1] =
      List.range' s s := by
    rw [hT]
    simpa only [show s+(s-1)=2*s-1 by omega, show s-1+1=s by omega] using
      (List.range'_1_concat (s:=s) (n:=s-1)).symm
  have hU : List.range (s-1) ++ [s-1] = List.range s := by
    simpa only [Nat.succ_eq_add_one,show s-1+1=s by omega] using (List.range_succ (n:=s-1)).symm
  have hW : List.range' (2*s) (b-1) ++ [2*s+b-1] =
      List.range' (2*s) b := by
    simpa only [show 2*s+(b-1)=2*s+b-1 by omega, show b-1+1=b by omega] using
      (List.range'_1_concat (s:=2*s) (n:=b-1)).symm
  have hX : List.range' (2*s+b) (s-1) ++ [3*s+b-1] =
      List.range' (2*s+b) s := by
    simpa only [show 2*s+b+(s-1)=3*s+b-1 by omega, show s-1+1=s by omega] using
      (List.range'_1_concat (s:=2*s+b) (n:=s-1)).symm
  have hall : List.range s ++ List.range' s s ++ List.range' (2*s) b ++
      List.range' (2*s+b) s = List.range (3*s+b) := by
    simp only [List.range_eq_range']
    have h1 := List.range'_append_1 (s:=0) (m:=s) (n:=s)
    have h2 := List.range'_append_1 (s:=0) (m:=2*s) (n:=b)
    have h3 := List.range'_append_1 (s:=0) (m:=2*s+b) (n:=s)
    simp only [Nat.zero_add] at h1 h2 h3
    rw [h1,show s+s=2*s by omega,h2,h3]
    congr 1 <;> omega
  have hreorder :
      (List.range' (2*s+b) (s-1) ++ [3*s+b-1] ++
        List.range (s-1) ++ [s-1] ++
        (List.range' (s+h) (s-h-1)) ++ [2*s-1] ++
        (List.range' (2*s) (b-1) ++ List.range' s h) ++ [2*s+b-1]).Perm
      ((List.range (s-1) ++ [s-1]) ++
        (List.range' s h ++ List.range' (s+h) (s-h-1) ++ [2*s-1]) ++
        (List.range' (2*s) (b-1) ++ [2*s+b-1]) ++
        (List.range' (2*s+b) (s-1) ++ [3*s+b-1])) := by
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl
  apply hreorder.trans
  rw [hU, hTR, hW, hX]
  exact List.Perm.of_eq hall

set_option maxHeartbeats 3200000 in
/- The complete lower physical witness.  The theorem is private because its
   ordinary family endpoint is consumed by the subsequent same-tree endpoint. -/
private theorem actual_lower (s b : ℕ) (hb : 2 ≤ b) (hs : b+2 ≤ s) :
    ∃ sigma : List (Fin (s+s+b+s)),
      OriginalOrder (s+s+b+s) (1+2^s+2^(s+b)+2^(2*s+b)) sigma ∧
      OriginalOrder (s+s+b+s+1) (2*(1+2^s+2^(s+b)+2^(2*s+b)))
        (earWord (s+s+b+s) sigma 0) := by
  let k := s+s+b+s
  let seed := 1+2^s+2^(s+b)+2^(2*s+b)
  let h := s-b-1
  let m : ℤ := 2^h
  let r : ℤ := 2^(b-1)
  let y : ℤ := 2^b
  let q : ℤ := 2^s
  let A : ℤ := q*y*q+(1+q+q*y)
  let B : ℤ := q*(1+q+q*y)+1
  let L : ℤ := q*(q*(1+q))+1+q
  let M : ℤ := q*(y*q)+1+y+y*q
  let Bn : ℤ := 2*B-1
  let Ln : ℤ := 2*L-1-q
  let Mn : ℤ := 2*M-1-y-y*q
  let p : ℤ := m-1
  let N : ℤ := q*y*q*q-1
  let f := fun i : ℕ => centered N ((2 : ℤ)^i*A)
  let g := fun i : ℕ => centered (2*N+1) ((2 : ℤ)^i*(2*A))
  have hh : 1 ≤ h := by dsimp [h]; omega
  have hm : 2 ≤ m := by
    dsimp [m]
    simpa using pow_le_pow_right₀ (by decide : (1:ℤ)≤2) hh
  have hr : 2 ≤ r := by
    dsimp [r]
    simpa using pow_le_pow_right₀ (by decide : (1:ℤ)≤2) (show 1≤b-1 by omega)
  have hy : y=2*r := pow_step b (by omega)
  have hq : q=2*y*m := by
    change (2:ℤ)^s=2*2^b*2^h
    calc
      (2:ℤ)^s=2^((b+1)+h) := by congr 1; dsimp [h]; omega
      _=2*2^b*2^h := by rw [pow_add,pow_succ]; ring
  have hqh : q=2*(2*r*m) := by rw [hq,hy]; ring
  have hpowS : (2:ℤ)^(s-1)=2*r*m := by
    have hhq := pow_step s (by omega)
    rw [show (2:ℤ)^s=q by rfl, hq, hy] at hhq
    nlinarith only [hhq]
  have hN : N=2*(64*r^4*m^3)-1 := by
    dsimp [N]
    rw [hq,hy]
    ring
  have hhalf : N/2=64*r^4*m^3-1 := by rw [hN]; omega
  obtain ⟨hA,hB,hL,hM,huf,hvf,hwf,hxf,hug,hvg,hwg,hxg,hfresh⟩ :=
    source_table s b s s (by omega) hb (by omega) (by omega)
  simp only [show s+s=2*s by omega] at hwf hxf hwg hxg hfresh
  change 1≤A ∧ A<N at hA
  change 1≤B ∧ B<N at hB
  change 1≤L ∧ L<N at hL
  change 1≤M ∧ M<N at hM
  change ∀ i<s, f i=if i+1<s then 2^i*A else -(N-B)/2 at huf
  change ∀ i<s, f (s+i)=if i+1<s then 2^i*B else -(N-L)/2 at hvf
  change ∀ i<b, f (2*s+i)=if i+1<b then 2^i*L else -(N-M)/2 at hwf
  change ∀ i<s, f (2*s+b+i)=if i+1<s then 2^i*M else -(N-A)/2 at hxf
  change ∀ i<s, g i=if i+1<s then 2^i*(2*A) else -((2*N+1)-Bn)/2 at hug
  change ∀ i<s, g (s+i)=if i+1<s then 2^i*Bn else -((2*N+1)-Ln)/2 at hvg
  change ∀ i<b, g (2*s+i)=if i+1<b then 2^i*Ln else -((2*N+1)-Mn)/2 at hwg
  change ∀ i<s, g (2*s+b+i)=if i+1<s then 2^i*Mn else -((2*N+1)-A)/2 at hxg
  have hear : g k=A := by
    simpa only [show 2*s+b+s=k by dsimp [k]; omega] using hfresh
  have hbase := new_base_bounds s b s s (by omega) hb (by omega) (by omega)
  have hBn : 0≤Bn := by have h:=hbase 1; change 1≤Bn ∧ Bn<2*N+1 at h; omega
  have hLn : 0≤Ln := by have h:=hbase 2; change 1≤2*L-(1+q) ∧ 2*L-(1+q)<2*N+1 at h; dsimp only [Ln]; omega
  have hMn : 0≤Mn := by have h:=hbase 3; change 1≤2*M-(1+y+y*q) ∧ 2*M-(1+y+y*q)<2*N+1 at h; dsimp only [Mn]; omega
  have posU (i : ℕ) (hi : i<s-1) : f i=2^i*A ∧ g i=2^i*(2*A) :=
    ⟨(huf i (by omega)).trans (ite_eq_left (by omega)),
      (hug i (by omega)).trans (ite_eq_left (by omega))⟩
  have posV (i : ℕ) (hi : i<s-1) : f (s+i)=2^i*B ∧ g (s+i)=2^i*Bn :=
    ⟨(hvf i (by omega)).trans (ite_eq_left (by omega)),
      (hvg i (by omega)).trans (ite_eq_left (by omega))⟩
  have posWchain (i : ℕ) (hi : i<b-1) : f (2*s+i)=2^i*L ∧ g (2*s+i)=2^i*Ln :=
    ⟨(hwf i (by omega)).trans (ite_eq_left (by omega)),
      (hwg i (by omega)).trans (ite_eq_left (by omega))⟩
  have posX (i : ℕ) (hi : i<s-1) : f (2*s+b+i)=2^i*M ∧ g (2*s+b+i)=2^i*Mn :=
    ⟨(hxf i (by omega)).trans (ite_eq_left (by omega)),
      (hxg i (by omega)).trans (ite_eq_left (by omega))⟩
  have rels : q*A=N+B ∧ q*B=N+L ∧ y*L=N+M ∧ q*M=N+A := by
    dsimp [q,y,N,A,B,L,M]; constructor; ring
    constructor; ring
    constructor <;> ring
  have grels : q*(2*A)=2*N+1+Bn ∧ q*Bn=2*N+1+Ln ∧
      y*Ln=2*N+1+Mn ∧ q*Mn=2*N+1+A := by
    dsimp [q,y,N,A,B,L,M,Bn,Ln,Mn]; constructor; ring
    constructor; ring
    constructor <;> ring
  have negU : f (s-1)=B-(2*r*m)*A ∧ g (s-1)=Bn-(2*r*m)*(2*A) := by
    have hf:=huf (s-1) (by omega); have hg:=hug (s-1) (by omega)
    rw [ite_eq_right (by omega),negative_step N A B (2*r*m) (by simpa only [hqh] using rels.1)] at hf
    rw [ite_eq_right (by omega),negative_step (2*N+1) (2*A) Bn (2*r*m)
      (by simpa only [hqh] using grels.1)] at hg
    exact ⟨hf,hg⟩
  have negV : f (2*s-1)=L-(2*r*m)*B ∧ g (2*s-1)=Ln-(2*r*m)*Bn := by
    have hf:=hvf (s-1) (by omega); have hg:=hvg (s-1) (by omega)
    rw [ite_eq_right (by omega),negative_step N B L (2*r*m) (by simpa only [hqh] using rels.2.1)] at hf
    rw [ite_eq_right (by omega),negative_step (2*N+1) Bn Ln (2*r*m)
      (by simpa only [hqh] using grels.2.1)] at hg
    simpa only [show s+(s-1)=2*s-1 by omega] using And.intro hf hg
  have negW : f (2*s+b-1)=M-r*L ∧ g (2*s+b-1)=Mn-r*Ln := by
    have hf:=hwf (b-1) (by omega); have hg:=hwg (b-1) (by omega)
    rw [ite_eq_right (by omega),negative_step N L M r (by simpa [hy] using rels.2.2.1)] at hf
    rw [ite_eq_right (by omega),negative_step (2*N+1) Ln Mn r
      (by simpa [hy] using grels.2.2.1)] at hg
    simpa only [show 2*s+(b-1)=2*s+b-1 by omega] using And.intro hf hg
  have negX : f (3*s+b-1)=A-(2*r*m)*M ∧ g (3*s+b-1)=A-(2*r*m)*Mn := by
    have hf:=hxf (s-1) (by omega); have hg:=hxg (s-1) (by omega)
    rw [ite_eq_right (by omega),negative_step N M A (2*r*m) (by simpa only [hqh] using rels.2.2.2)] at hf
    rw [ite_eq_right (by omega),negative_step (2*N+1) Mn A (2*r*m)
      (by simpa only [hqh] using grels.2.2.2)] at hg
    simpa only [show 2*s+b+(s-1)=3*s+b-1 by omega] using And.intro hf hg
  let T := List.range' s h
  let R := List.range' (s+h) (s-h-1)
  let PX := List.range' (2*s+b) (s-1)
  let PU := List.range (s-1)
  let PW := List.range' (2*s) (b-1)
  have hTR : (T++R).Perm (List.range' s (s-1)) := by
    apply List.Perm.of_eq
    simpa only [T,R,show h+(s-h-1)=s-1 by omega] using
      (List.range'_append_1 (s:=s) (m:=h) (n:=s-h-1))
  have hmassX : (PX.map f).sum=(2*r*m-1)*M ∧ (PX.map g).sum=(2*r*m-1)*Mn := by
    have hf := ladder_sum f (2*s+b) (s-1) M
      (by intro i hi; exact (posX i hi).1)
    have hg := ladder_sum g (2*s+b) (s-1) Mn
      (by intro i hi; exact (posX i hi).2)
    rw [hpowS] at hf hg
    constructor
    · simpa only [PX] using hf
    · simpa only [PX] using hg
  have hmassU : (PU.map f).sum=(2*r*m-1)*A ∧ (PU.map g).sum=(2*r*m-1)*(2*A) := by
    have hf := ladder_sum f 0 (s-1) A
      (by intro i hi; simpa using (posU i hi).1)
    have hg := ladder_sum g 0 (s-1) (2*A)
      (by intro i hi; simpa using (posU i hi).2)
    rw [←List.range_eq_range'] at hf hg
    rw [hpowS] at hf hg
    constructor
    · simpa only [PU] using hf
    · simpa only [PU] using hg
  have hmassT : (T.map f).sum=p*B ∧ (T.map g).sum=p*Bn := by
    constructor
    · simpa only [T,p,m] using ladder_sum f s h B (by intro i hi; exact (posV i (by dsimp [h] at hi; omega)).1)
    · simpa only [T,p,m] using ladder_sum g s h Bn (by intro i hi; exact (posV i (by dsimp [h] at hi; omega)).2)
  have hmassVR : (R.map f).sum=(2*r*m-1-p)*B ∧ (R.map g).sum=(2*r*m-1-p)*Bn := by
    have hf := (hTR.map f).sum_eq
    have hg := (hTR.map g).sum_eq
    have ht := hmassT
    have hvf0 := ladder_sum f s (s-1) B (by intro i hi; exact (posV i hi).1)
    have hvg0 := ladder_sum g s (s-1) Bn (by intro i hi; exact (posV i hi).2)
    simp only [List.map_append,List.sum_append] at hf hg
    rw [ht.1] at hf; rw [ht.2] at hg
    rw [hpowS] at hvf0 hvg0
    constructor <;> nlinarith only [hf,hg,hvf0,hvg0]
  have hmassW : ((PW++T).map f).sum=(r-1)*L+p*B ∧
      ((PW++T).map g).sum=(r-1)*Ln+p*Bn := by
    have hwf0 := ladder_sum f (2*s) (b-1) L (by intro i hi; exact (posWchain i hi).1)
    have hwg0 := ladder_sum g (2*s) (b-1) Ln (by intro i hi; exact (posWchain i hi).2)
    simp only [PW,List.map_append,List.sum_append,hmassT.1,hmassT.2]
    rw [show (2:ℤ)^(b-1)=r by rfl] at hwf0 hwg0
    constructor <;> linarith only [hwf0,hwg0]
  have hpositive : 0≤A ∧ 0≤B ∧ 0≤L ∧ 0≤M ∧ 0≤Bn ∧ 0≤Ln ∧ 0≤Mn := by
    have h := (show 1≤A ∧ A<N from hA)
    exact ⟨by omega,by omega,by omega,by omega,hBn,hLn,hMn⟩
  have posblock (z : ℕ → ℤ) (H : ℤ) (o n : ℕ) (hH : 0≤H)
      (hh : ∀ i<n,z (o+i)=2^i*H) : ∀ i∈List.range' o n, 0≤z i := by
    intro i hi
    have hi' := List.mem_range'_1.mp hi
    rw [show i=o+(i-o) by omega,hh (i-o) (by omega)]
    positivity
  have posPX := posblock f M (2*s+b) (s-1) hpositive.2.2.2.1
    (by intro i hi; exact (posX i hi).1)
  have posPXn := posblock g Mn (2*s+b) (s-1) hpositive.2.2.2.2.2.2
    (by intro i hi; exact (posX i hi).2)
  have posPU : ∀ i∈PU,0≤f i := by
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [(posU i (by omega)).1]; positivity
  have posPUn : ∀ i∈PU,0≤g i := by
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [(posU i (by omega)).2]; positivity
  have posR : ∀ i∈R,0≤f i := by
    intro i hi
    have hi' := List.mem_range'_1.mp hi
    rw [show i=s+(i-s) by omega]
    rw [(posV (i-s) (by dsimp [R,h] at hi'; omega)).1]; positivity
  have posRn : ∀ i∈R,0≤g i := by
    intro i hi
    have hi' := List.mem_range'_1.mp hi
    rw [show i=s+(i-s) by omega]
    rw [(posV (i-s) (by dsimp [R,h] at hi'; omega)).2]; positivity
  have posWbank : ∀ i∈PW++T,0≤f i := by
    intro i hi; rcases List.mem_append.mp hi with hi|hi
    · exact posblock f L (2*s) (b-1) hpositive.2.2.1 (by intro j hj; exact (posWchain j hj).1) i hi
    · have hi' := List.mem_range'_1.mp hi
      rw [show i=s+(i-s) by omega]
      rw [(posV (i-s) (by dsimp only [h] at hi'; omega)).1]
      positivity
  have posWbankn : ∀ i∈PW++T,0≤g i := by
    intro i hi; rcases List.mem_append.mp hi with hi|hi
    · exact posblock g Ln (2*s) (b-1) hLn (by intro j hj; exact (posWchain j hj).2) i hi
    · have hi' := List.mem_range'_1.mp hi
      rw [show i=s+(i-s) by omega]
      rw [(posV (i-s) (by dsimp only [h] at hi'; omega)).2]
      positivity
  have hgates : Gates (N/2) (PX.map f).sum (f (3*s+b-1))
      (PU.map f).sum (f (s-1)) (R.map f).sum (f (2*s-1))
      ((PW++T).map f).sum (f (2*s+b-1)) ∧
      Gates N (([k]++PX).map g).sum (g (3*s+b-1))
      (PU.map g).sum (g (s-1)) (R.map g).sum (g (2*s-1))
      ((PW++T).map g).sum (g (2*s+b-1)) := by
    rw [hmassX.1,hmassU.1,hmassVR.1,hmassW.1,
      negX.1,negU.1,negV.1,negW.1,
      List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,hear,
      hmassX.2,hmassU.2,hmassVR.2,hmassW.2,
      negX.2,negU.2,negV.2,negW.2,hhalf]
    convert endpoints r m hr hm using 3 <;>
      simp only [A,B,L,M,Bn,Ln,Mn,p,N,k,hq,hy] <;> ring
  let word := PX++[3*s+b-1]++PU++[s-1]++R++[2*s-1]++(PW++T)++[2*s+b-1]
  have hold : InStrip f (N/2) 0 word := by
    exact four_strip f (N/2) PX PU R (PW++T)
      (3*s+b-1) (s-1) (2*s-1) (2*s+b-1)
      posPX posPU posR posWbank hgates.1
  have hnew : InStrip g N 0 ([k]++word) := by
    have hfirst : ∀ i∈[k]++PX,0≤g i := by
      intro i hi; rcases List.mem_append.mp hi with hi|hi
      · rw [List.mem_singleton.mp hi,hear]; omega
      · exact posPXn i hi
    simpa only [word,List.append_assoc] using
      four_strip g N ([k]++PX) PU R (PW++T)
        (3*s+b-1) (s-1) (2*s-1) (2*s+b-1)
        hfirst posPUn posRn posWbankn hgates.2
  have hperm : word.Perm (List.range k) := by
    simpa only [word,show 3*s+b=k by dsimp [k]; omega] using inventory s b h hb hs rfl
  have hmod : modulus k=N := by
    dsimp [modulus,k,N,q,y]
    simp only [pow_add]
    ring
  have hmod' : modulus (k+1)=2*N+1 := by
    have he : modulus (k+1)=2*modulus k+1 := by
      dsimp only [modulus]; rw [pow_succ]; ring
    rw [he,hmod]
  have hseed : (seed:ℤ)=A := by
    dsimp [seed,A,q,y]
    push_cast
    rw [show 2*s+b=(s+b)+s by omega]
    simp only [pow_add]
    ring
  have hk : 0<k := by dsimp [k]; omega
  have old : OriginalOrder k seed (word.map (label k hk)) := by
    apply lift_order k seed hk word hperm
    · simpa only [f,hmod,hseed] using hold
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero k seed (by dsimp [k]; omega)
  have newperm : ([k]++word).Perm (List.range (k+1)) := by
    have hp := (List.perm_append_singleton k word).symm
    have hrange : List.range k++[k]=List.range (k+1) := by
      simpa only [Nat.succ_eq_add_one] using (List.range_succ (n:=k)).symm
    exact hp.trans ((hperm.append_right [k]).trans (List.Perm.of_eq hrange))
  have new : OriginalOrder (k+1) (2*seed)
      (([k]++word).map (label (k+1) (by omega))) := by
    apply lift_order (k+1) (2*seed) (by omega) ([k]++word) newperm
    · have hhalf' : (2*N+1)/2=N := by omega
      simpa only [g,hmod',Nat.cast_mul,Nat.cast_ofNat,hseed,hhalf'] using hnew
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*seed)
        (by dsimp [k]; omega)
  refine ⟨word.map (label k hk),old,?_⟩
  rw [show earWord k (word.map (label k hk)) 0 =
      ([k]++word).map (label (k+1) (by omega)) by
    simpa using marked_word k 0 hk [] word rfl hperm]
  exact new

#print axioms actual_lower
end D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree
