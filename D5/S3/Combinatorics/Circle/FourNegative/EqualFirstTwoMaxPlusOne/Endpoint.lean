/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstTwoMaxPlusOne/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EqualFirstTwoMaxPlusOne/Endpoint
   mirror-E: none(waiver:source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: A physical joint order at the full independent equal-first-two max-plus-one boundary. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoMaxPlusOne.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
import D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift

/-! An unbounded construction on original labels, with one literal last cut.
The caller supplied the redistribution U,W,V,X. No finite control is a premise. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoMaxPlusOne
open SourceWidth PeriodicShortening RunFirstEarTransport
open private Bounds small_chart large_chart
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoMaxPlusOne.Arithmetic
open private source_table
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable
open private new_base_bounds base newBase sourceMod
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
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

private theorem inventory (u c v : ℕ) (hu : 2 ≤ u) (hc : u < c)
    (R T : List ℕ)
    (hV : (R++T++[c+1+v]).Perm (List.range' (c+1) (c-1))) :
    (List.range' 1 (c-1) ++ [c] ++
      (List.range' (c+1+c) (u-1) ++ [0] ++ T) ++ [c+1+c+u-1] ++
      R ++ [c+1+c-1] ++
      (List.range' (c+1+c+u) (u-1) ++ [c+1+v]) ++ [c+1+c+u+u-1]).Perm
      (List.range (u+u+c+(c+1))) := by
  have merge (o n : ℕ) (hn : 1 ≤ n) :
      List.range' o (n-1) ++ [o+n-1] = List.range' o n := by
    simpa only [show o+(n-1)=o+n-1 by omega, show n-1+1=n by omega] using
      (List.range'_1_concat (s:=o) (n:=n-1)).symm
  have hU : (List.range' 1 (c-1) ++ [0]).Perm (List.range c) := by
    apply List.perm_append_comm.trans
    apply List.Perm.of_eq
    simpa only [List.range'_one, Nat.zero_add, show 1+(c-1)=c by omega,
      List.range_eq_range'] using (List.range'_append_1 (s:=0) (m:=1) (n:=c-1))
  have hreorder :
      (List.range' 1 (c-1) ++ [c] ++
        (List.range' (c+1+c) (u-1) ++ [0] ++ T) ++ [c+1+c+u-1] ++
        R ++ [c+1+c-1] ++
        (List.range' (c+1+c+u) (u-1) ++ [c+1+v]) ++ [c+1+c+u+u-1]).Perm
      (((List.range' 1 (c-1) ++ [0]) ++ [c]) ++
        ((R++T++[c+1+v]) ++ [c+1+c-1]) ++
        (List.range' (c+1+c) (u-1) ++ [c+1+c+u-1]) ++
        (List.range' (c+1+c+u) (u-1) ++ [c+1+c+u+u-1])) := by
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl
  apply hreorder.trans
  have hblocks := (((hU.append_right [c]).append (hV.append_right [c+1+c-1])).append
      (List.Perm.refl (List.range' (c+1+c) (u-1) ++ [c+1+c+u-1]))).append
      (List.Perm.refl (List.range' (c+1+c+u) (u-1) ++ [c+1+c+u+u-1]))
  apply hblocks.trans
  apply List.Perm.of_eq
  rw [← List.range_succ, show c.succ=c+1 by omega,
    merge (c+1) c (by omega), merge (c+1+c) u (by omega),
    merge (c+1+c+u) u (by omega), List.range_eq_range']
  have h1 := List.range'_append_1 (s:=0) (m:=c+1) (n:=c)
  have h2 := List.range'_append_1 (s:=0) (m:=c+1+c) (n:=u)
  have h3 := List.range'_append_1 (s:=0) (m:=c+1+c+u) (n:=u)
  simp only [Nat.zero_add] at h1 h2 h3
  rw [h1,h2,h3]
  rw [List.range_eq_range']
  congr 1
  omega

set_option maxHeartbeats 2400000 in
private theorem physical (u c v : ℕ) (p : ℤ) (T R : List ℕ)
    (hu : 2 ≤ u) (hc : u < c) (hv : v=c-u-1)
    (hsplit : (R++T++[c+1+v]).Perm (List.range' (c+1) (c-1)))
    (hweight : ∀ (h : ℕ → ℤ) (H : ℤ),
      (∀ i<c-1, h (c+1+i)=2^i*H) → (T.map h).sum=p*H)
    (hend : Bounds (2^u) (2^c) (2^(u-1)) (2^(c-1)) p (2^v)) :
    ∃ sigma : List (Fin (u+u+c+(c+1))),
      OriginalOrder (u+u+c+(c+1)) (1+2^u+2^(u+u)+2^(u+u+c)) sigma ∧
      OriginalOrder (u+u+c+(c+1)+1) (2*(1+2^u+2^(u+u)+2^(u+u+c)))
        (earWord (u+u+c+(c+1)) sigma (u+u+c+(c+1)-1)) := by
  let d := c+1
  let k := u+u+c+d
  let seed := 1+2^u+2^(u+u)+2^(u+u+c)
  let x : ℤ := 2^u
  let z : ℤ := 2^c
  let t : ℤ := 2^d
  let s : ℤ := 2^(u-1)
  let r : ℤ := 2^(c-1)
  let q : ℤ := 2^v
  let A := x*x*z+(1+x+x*x)
  let B := t*(1+x+x*x)+1
  let L := t*(z*(1+x))+1+z
  let M := t*(x*z)+1+x+x*z
  let Bp := 2*B-1
  let Lp := 2*L-1-z
  let Mp := 2*M-1-x-x*z
  let N := x*x*z*t-1
  let f := fun i : ℕ => centered N ((2 : ℤ)^i*A)
  let g := fun i : ℕ => centered (2*N+1) ((2 : ℤ)^i*(2*A))
  have hx : x=2*s := pow_step u (by omega)
  have hz : z=2*r := pow_step c (by omega)
  have ht : t=2*z := by dsimp [t,d,z]; rw [pow_succ]; ring
  have hN : N=2*(x*x*z*z)-1 := by dsimp [N]; rw [ht]; ring
  have hhalf : N/2=x*x*z*z-1 := by omega
  obtain ⟨hA,hB,hL,hM,huf,hvf,hwf,hxf,hug,hvg,hwg,hxg,hfresh⟩ :=
    source_table u u c d hu hu (by omega) (by dsimp [d]; omega)
  change 1≤A ∧ A<N at hA
  change 1≤B ∧ B<N at hB
  change 1≤L ∧ L<N at hL
  change 1≤M ∧ M<N at hM
  change ∀ i<d, f i=if i+1<d then 2^i*A else -(N-B)/2 at huf
  change ∀ i<c, f (d+i)=if i+1<c then 2^i*B else -(N-L)/2 at hvf
  change ∀ i<u, f (d+c+i)=if i+1<u then 2^i*L else -(N-M)/2 at hwf
  change ∀ i<u, f (d+c+u+i)=if i+1<u then 2^i*M else -(N-A)/2 at hxf
  change ∀ i<d, g i=if i+1<d then 2^i*(2*A) else -((2*N+1)-Bp)/2 at hug
  change ∀ i<c, g (d+i)=if i+1<c then 2^i*Bp else -((2*N+1)-Lp)/2 at hvg
  change ∀ i<u, g (d+c+i)=if i+1<u then 2^i*Lp else -((2*N+1)-Mp)/2 at hwg
  change ∀ i<u, g (d+c+u+i)=if i+1<u then 2^i*Mp else -((2*N+1)-A)/2 at hxg
  have hear : g k=A := by
    simpa only [show d+c+u+u=k by dsimp [k]; omega] using hfresh
  have hbnew := new_base_bounds u u c d hu hu (by omega) (by dsimp [d]; omega)
  have hBp : 0≤Bp := by have h:=hbnew 1; change 1≤Bp ∧ Bp<2*N+1 at h; omega
  have hLp : 0≤Lp := by
    have h := (hbnew 2).1
    change 1≤2*L-(1+z) at h
    dsimp only [Lp]; omega
  have hMp : 0≤Mp := by
    have h := (hbnew 3).1
    change 1≤2*M-(1+x+x*z) at h
    dsimp only [Mp]; omega
  have posU (i : ℕ) (hi : i<d-1) : f i=2^i*A ∧ g i=2^i*(2*A) :=
    ⟨(huf i (by omega)).trans (ite_eq_left (by omega)),
     (hug i (by omega)).trans (ite_eq_left (by omega))⟩
  have posV (i : ℕ) (hi : i<c-1) : f (d+i)=2^i*B ∧ g (d+i)=2^i*Bp :=
    ⟨(hvf i (by omega)).trans (ite_eq_left (by omega)),
     (hvg i (by omega)).trans (ite_eq_left (by omega))⟩
  have posW (i : ℕ) (hi : i<u-1) : f (d+c+i)=2^i*L ∧ g (d+c+i)=2^i*Lp :=
    ⟨(hwf i (by omega)).trans (ite_eq_left (by omega)),
     (hwg i (by omega)).trans (ite_eq_left (by omega))⟩
  have posX (i : ℕ) (hi : i<u-1) : f (d+c+u+i)=2^i*M ∧ g (d+c+u+i)=2^i*Mp :=
    ⟨(hxf i (by omega)).trans (ite_eq_left (by omega)),
     (hxg i (by omega)).trans (ite_eq_left (by omega))⟩
  have rels : 2*z*A=N+B ∧ 2*r*B=N+L ∧ 2*s*L=N+M ∧ 2*s*M=N+A := by
    dsimp [N,A,B,L,M]; rw [ht,hx,hz]; refine ⟨?_,?_,?_,?_⟩ <;> ring
  have grels : 2*z*(2*A)=2*N+1+Bp ∧ 2*r*Bp=2*N+1+Lp ∧
      2*s*Lp=2*N+1+Mp ∧ 2*s*Mp=2*N+1+A := by
    dsimp [N,A,B,L,M,Bp,Lp,Mp]; rw [ht,hx,hz]; refine ⟨?_,?_,?_,?_⟩ <;> ring
  have negU : f (d-1)=B-z*A ∧ g (d-1)=Bp-z*(2*A) := by
    have hf:=huf (d-1) (by omega); have hg:=hug (d-1) (by omega)
    rw [ite_eq_right (by omega),negative_step N A B z rels.1] at hf
    rw [ite_eq_right (by omega),negative_step (2*N+1) (2*A) Bp z grels.1] at hg
    exact ⟨hf,hg⟩
  have negV : f (d+c-1)=L-r*B ∧ g (d+c-1)=Lp-r*Bp := by
    have hf:=hvf (c-1) (by omega); have hg:=hvg (c-1) (by omega)
    rw [ite_eq_right (by omega),negative_step N B L r rels.2.1] at hf
    rw [ite_eq_right (by omega),negative_step (2*N+1) Bp Lp r grels.2.1] at hg
    simpa only [show d+(c-1)=d+c-1 by omega] using And.intro hf hg
  have negW : f (d+c+u-1)=M-s*L ∧ g (d+c+u-1)=Mp-s*Lp := by
    have hf:=hwf (u-1) (by omega); have hg:=hwg (u-1) (by omega)
    rw [ite_eq_right (by omega),negative_step N L M s rels.2.2.1] at hf
    rw [ite_eq_right (by omega),negative_step (2*N+1) Lp Mp s grels.2.2.1] at hg
    simpa only [show d+c+(u-1)=d+c+u-1 by omega] using And.intro hf hg
  have negX : f (d+c+u+u-1)=A-s*M ∧ g (d+c+u+u-1)=A-s*Mp := by
    have hf:=hxf (u-1) (by omega); have hg:=hxg (u-1) (by omega)
    rw [ite_eq_right (by omega),negative_step N M A s rels.2.2.2] at hf
    rw [ite_eq_right (by omega),negative_step (2*N+1) Mp A s grels.2.2.2] at hg
    simpa only [show d+c+u+(u-1)=d+c+u+u-1 by omega] using And.intro hf hg
  let P1 := List.range' 1 (c-1)
  let P2 := List.range' (d+c) (u-1) ++ [0] ++ T
  let P3 := R
  let P4 := List.range' (d+c+u) (u-1) ++ [d+v]
  have hUp : (P1++[0]).Perm (List.range (d-1)) := by
    apply List.perm_append_comm.trans
    apply List.Perm.of_eq
    simpa only [P1,d,List.range'_one,Nat.zero_add,
      show 1+(c-1)=c by omega, show c+1-1=c by omega, List.range_eq_range'] using
      (List.range'_append_1 (s:=0) (m:=1) (n:=c-1))
  have hmassU : (P1.map f).sum=(z-2)*A ∧ (P1.map g).sum=(z-2)*(2*A) := by
    have hf:=(hUp.map f).sum_eq; have hg:=(hUp.map g).sum_eq
    have h0:=posU 0 (by dsimp [d]; omega)
    have hsf:=ladder_sum f 0 (d-1) A (by intro i hi; simpa using (posU i hi).1)
    have hsg:=ladder_sum g 0 (d-1) (2*A) (by intro i hi; simpa using (posU i hi).2)
    rw [←List.range_eq_range'] at hsf hsg
    change _=(z-1)*A at hsf
    change _=(z-1)*(2*A) at hsg
    simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton] at hf hg
    simp only [pow_zero,one_mul] at h0
    rw [h0.1,hsf] at hf; rw [h0.2,hsg] at hg
    constructor <;> nlinarith only [hf,hg]
  have hmassT : (T.map f).sum=p*B ∧ (T.map g).sum=p*Bp :=
    ⟨hweight f B (by intro i hi;exact (posV i hi).1),
     hweight g Bp (by intro i hi;exact (posV i hi).2)⟩
  have hq := posV v (by omega)
  change f (d+v)=q*B ∧ g (d+v)=q*Bp at hq
  have hmassR : (P3.map f).sum=(r-1-p-q)*B ∧ (P3.map g).sum=(r-1-p-q)*Bp := by
    have hf:=(hsplit.map f).sum_eq; have hg:=(hsplit.map g).sum_eq
    have hsf:=ladder_sum f d (c-1) B (by intro i hi;exact (posV i hi).1)
    have hsg:=ladder_sum g d (c-1) Bp (by intro i hi;exact (posV i hi).2)
    simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton] at hf hg
    rw [hmassT.1,hq.1,hsf] at hf
    rw [hmassT.2,hq.2,hsg] at hg
    constructor <;> nlinarith only [hf,hg]
  have hmassW := ladder_sum f (d+c) (u-1) L (by intro i hi;exact (posW i hi).1)
  have hmassWp := ladder_sum g (d+c) (u-1) Lp (by intro i hi;exact (posW i hi).2)
  have hmassX := ladder_sum f (d+c+u) (u-1) M (by intro i hi;exact (posX i hi).1)
  have hmassXp := ladder_sum g (d+c+u) (u-1) Mp (by intro i hi;exact (posX i hi).2)
  have h0 := posU 0 (by dsimp [d];omega)
  simp only [pow_zero,one_mul] at h0
  have hmass2 : (P2.map f).sum=(s-1)*L+A+p*B ∧
      (P2.map g).sum=(s-1)*Lp+2*A+p*Bp := by
    simp only [P2,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,
      hmassW,hmassWp,h0.1,h0.2,hmassT.1,hmassT.2]
    exact ⟨rfl,rfl⟩
  have hmass4 : (P4.map f).sum=(s-1)*M+q*B ∧
      ((P4++[k]).map g).sum=(s-1)*Mp+q*Bp+A := by
    simp only [P4,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,
      hmassX,hmassXp,hq.1,hq.2,hear]
    exact ⟨rfl,rfl⟩
  have posblock (h : ℕ→ℤ) (H : ℤ) (o n : ℕ) (hH : 0≤H)
      (hh : ∀ i<n, h (o+i)=2^i*H) : ∀ i∈List.range' o n, 0≤h i := by
    intro i hi
    have hi':=List.mem_range'.mp hi
    rw [show i=o+(i-o) by omega,hh (i-o) (by omega)]
    positivity
  have posVall (h : ℕ→ℤ) (H : ℤ) (hH : 0≤H)
      (hh : ∀ i<c-1, h (d+i)=2^i*H) : ∀ i∈R++T++[d+v],0≤h i := by
    intro i hi
    exact posblock h H d (c-1) hH hh i (hsplit.mem_iff.mp hi)
  have positive (h : ℕ→ℤ) (HU HV HW HX : ℤ)
      (hHU : 0≤HU) (hHV : 0≤HV) (hHW : 0≤HW) (hHX : 0≤HX)
      (hU : ∀ i<d-1,h i=2^i*HU) (hV : ∀ i<c-1,h (d+i)=2^i*HV)
      (hW : ∀ i<u-1,h (d+c+i)=2^i*HW) (hX : ∀ i<u-1,h (d+c+u+i)=2^i*HX) :
      (∀i∈P1,0≤h i) ∧ (∀i∈P2,0≤h i) ∧ (∀i∈P3,0≤h i) ∧ (∀i∈P4,0≤h i) := by
    have hVall:=posVall h HV hHV hV
    have hzero : 0≤h 0 := by rw [hU 0 (by dsimp [d];omega)]; simpa using hHU
    refine ⟨?_,?_,?_,?_⟩
    · intro i hi
      have hb:=List.mem_range'.mp hi
      rw [hU i (by dsimp [d];omega)]
      positivity
    · intro i hi
      rcases List.mem_append.mp hi with hi|hi
      · rcases List.mem_append.mp hi with hi|hi
        · exact posblock h HW (d+c) (u-1) hHW hW i hi
        · simpa only [List.mem_singleton.mp hi] using hzero
      · exact hVall i (by simp only [List.mem_append];exact Or.inl (Or.inr hi))
    · intro i hi; exact hVall i (by simp only [List.mem_append];exact Or.inl (Or.inl hi))
    · intro i hi
      rcases List.mem_append.mp hi with hi|hi
      · exact posblock h HX (d+c+u) (u-1) hHX hX i hi
      · exact hVall i (List.mem_append_right _ hi)
  have posf := positive f A B L M (by omega) (by omega) (by omega) (by omega)
    (fun i hi=>(posU i hi).1) (fun i hi=>(posV i hi).1)
    (fun i hi=>(posW i hi).1) (fun i hi=>(posX i hi).1)
  have posg := positive g (2*A) Bp Lp Mp (by omega) hBp hLp hMp
    (fun i hi=>(posU i hi).2) (fun i hi=>(posV i hi).2)
    (fun i hi=>(posW i hi).2) (fun i hi=>(posX i hi).2)
  have hgates : Gates (N/2) (P1.map f).sum (f (d-1)) (P2.map f).sum (f (d+c+u-1))
      (P3.map f).sum (f (d+c-1)) (P4.map f).sum (f (d+c+u+u-1)) ∧
      Gates N (P1.map g).sum (g (d-1)) (P2.map g).sum (g (d+c+u-1))
      (P3.map g).sum (g (d+c-1)) ((P4++[k]).map g).sum (g (d+c+u+u-1)) := by
    rw [hmassU.1,hmassU.2,hmass2.1,hmass2.2,hmassR.1,hmassR.2,
      hmass4.1,hmass4.2,negU.1,negU.2,negW.1,negW.2,negV.1,negV.2,negX.1,negX.2,hhalf]
    dsimp only [Bounds] at hend
    convert hend using 3 <;> (try dsimp [N,A,B,L,M,Bp,Lp,Mp]) <;> (try rw [ht]) <;> ring
  let pre := P1++[d-1]++P2++[d+c+u-1]++P3++[d+c-1]++P4
  let last := d+c+u+u-1
  have hold : InStrip f (N/2) 0 (pre++[last]) := by
    exact four_strip f (N/2) P1 P2 P3 P4 (d-1) (d+c+u-1) (d+c-1) last
      posf.1 posf.2.1 posf.2.2.1 posf.2.2.2 hgates.1
  have hnew : InStrip g N 0 (pre++[k,last]) := by
    have hp4 : ∀i∈P4++[k],0≤g i := by
      intro i hi; rcases List.mem_append.mp hi with hi|hi
      · exact posg.2.2.2 i hi
      · rw [List.mem_singleton.mp hi,hear];omega
    simpa only [pre,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
      four_strip g N P1 P2 P3 (P4++[k]) (d-1) (d+c+u-1) (d+c-1) last
        posg.1 posg.2.1 posg.2.2.1 hp4 hgates.2
  have hperm : (pre++[last]).Perm (List.range k) := inventory u c v hu hc R T hsplit
  have hmod : modulus k=N := by dsimp [modulus,k,N,x,z,t];ring
  have hmod' : modulus (k+1)=2*N+1 := by dsimp [modulus];rw [pow_succ];rw [←hmod];dsimp [modulus];ring
  have hseed : (seed:ℤ)=A := by dsimp [seed,A,x,z];push_cast;ring
  have hk : 0<k := by dsimp [k,d];omega
  have old : OriginalOrder k seed ((pre++[last]).map (label k hk)) := by
    apply lift_order k seed hk (pre++[last]) hperm
    · simpa only [f,hmod,hseed] using hold
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero k seed (by dsimp [k,d];omega)
  have newperm : (pre++[k,last]).Perm (List.range (k+1)) := by
    have hp : (pre++[k,last]).Perm ((pre++[last])++[k]) := by
      apply Multiset.coe_eq_coe.mp
      simp only [←Multiset.coe_add]
      ac_rfl
    exact hp.trans (by simpa only [List.range_succ] using hperm.append_right [k])
  have new : OriginalOrder (k+1) (2*seed) ((pre++[k,last]).map (label (k+1) (by omega))) := by
    apply lift_order (k+1) (2*seed) (by omega) (pre++[k,last]) newperm
    · have hhalf' : (2*N+1)/2=N := by omega
      simpa only [g,hmod',Nat.cast_mul,Nat.cast_ofNat,hseed,hhalf'] using hnew
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*seed) (by dsimp [k,d];omega)
  have hlen : pre.length=k-1 := by have hh:=hperm.length_eq;simp only [List.length_append,List.length_singleton,List.length_range] at hh;omega
  refine ⟨(pre++[last]).map (label k hk),old,?_⟩
  rw [marked_word k (k-1) hk pre [last] hlen hperm]
  exact new

/-- One physical permutation works for both actual sources at every independent
u≥2 and c>u, with d=c+1 and the literal cut k-1. -/
theorem actualSource_equal_first_two_max_plus_one_joint_lift (u c : ℕ)
    (hu : 2 ≤ u) (hc : u < c) :
    ∃ sigma : List (Fin (u+u+c+(c+1))),
      OriginalOrder (u+u+c+(c+1)) (1+2^u+2^(u+u)+2^(u+u+c)) sigma ∧
      OriginalOrder (u+u+c+(c+1)+1) (2*(1+2^u+2^(u+u)+2^(u+u+c)))
        (earWord (u+u+c+(c+1)) sigma (u+u+c+(c+1)-1)) := by
  let v := c-u-1
  let V := List.range' (c+1) (c-1)
  let R0 := V.erase (c+1+v)
  let s : ℤ := 2^(u-1)
  let q : ℤ := 2^v
  have hvsum : v+(u+1)=c := by dsimp [v];omega
  have hv : v<c-1 := by omega
  have hmem : c+1+v ∈ V := by
    rw [List.mem_range']
    exact ⟨v, hv, by simp⟩
  have hsplit0 : (R0++[c+1+v]).Perm V :=
    List.perm_append_comm.trans (List.perm_cons_erase hmem).symm
  have hx : (2:ℤ)^u=2*s := pow_step u (by omega)
  have hq : 1≤q := one_le_pow₀ (by decide)
  by_cases hsmall : c<2*u
  · have hs : 2*q≤s := by
      have h := pow_le_pow_right₀ (by decide : (1:ℤ)≤2) (show v+1≤u-1 by dsimp [v];omega)
      simpa only [pow_succ,mul_comm] using h
    have hz : (2:ℤ)^c=2*(2*s)*q := by
      rw [←hx]
      have he : c=u+v+1 := by dsimp [v];omega
      rw [he,pow_succ,pow_add]
      dsimp [q];ring
    have hr : (2:ℤ)^(c-1)=(2*s)*q := by
      rw [←hx,←pow_add]
      congr 1;dsimp [v];omega
    apply physical u c v 0 [] R0 hu hc rfl
    · simpa only [List.append_nil] using hsplit0
    · intro h H hh;simp
    · rw [hx,hz,hr]
      exact small_chart s q hq hs
  · let w := c-2*u
    let p : ℤ := 2^w
    let R := R0.erase (c+1+w)
    have hw : w<v := by dsimp [w,v];omega
    have hcu : 2*u ≤ c := by omega
    have hwsub : w+2*u=c := by dsimp [w]; exact Nat.sub_add_cancel hcu
    have hwm : c+1+w ∈ R0 := by
      apply (List.mem_erase_of_ne (by omega : c+1+w≠c+1+v)).mpr
      rw [List.mem_range']
      exact ⟨w, by omega, by simp⟩
    have hs : 2≤s := by
      simpa [s] using pow_le_pow_right₀ (by decide : (1:ℤ)≤2) (show 1≤u-1 by omega)
    have hp : 1≤p := one_le_pow₀ (by decide)
    have hqp : q=s*p := by
      dsimp [q,s,p]
      rw [←pow_add]
      congr 1;dsimp [v,w];omega
    have hz : (2:ℤ)^c=(2*s)^2*p := by
      rw [←hx]
      dsimp [p]
      rw [←pow_mul,←pow_add]
      congr 1;dsimp [w];omega
    have hr : (2:ℤ)^(c-1)=2*s^2*p := by
      have he := pow_step c (by omega)
      rw [hz] at he
      nlinarith only [he]
    apply physical u c v p [c+1+w] R hu hc rfl
    · exact ((List.perm_append_comm.trans (List.perm_cons_erase hwm).symm).append_right [c+1+v]).trans hsplit0
    · intro h H hh
      simpa only [List.map_singleton,List.sum_singleton] using hh w (by omega)
    · rw [hx,hz,hr]
      change Bounds (2*s) ((2*s)^2*p) s (2*s^2*p) p q
      rw [hqp]
      exact large_chart s p hs hp

#print axioms actualSource_equal_first_two_max_plus_one_joint_lift
end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoMaxPlusOne
