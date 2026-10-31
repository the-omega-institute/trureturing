/-! Complete physical upper witnesses for gaps `(s,b,s,s)`, `s ≥ 2`,
`b ≥ s+2`.  The masks are literal label lists; the theorem returns the
old/new `InStrip` witness consumed by the later full-family assembly.
-/
import D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree.UpperArithmetic
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Transport
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree

open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private UpperBounds upperGates chart_s_ge_three chart_s_two_large chart_corner
  from D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree
open private source_table
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable
open private base newBase sourceMod new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private insertAt_add
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private four_strip
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule
open private label lift_order marked_word ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

private def size (s b : ℕ) : ℕ := s + b + s + s
private def seed (s b : ℕ) : ℕ := 1 + 2^s + 2^(s+b) + 2^(2*s+b)

private theorem pow_step (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ)^n = 2 * 2^(n-1) := by
  calc
    (2 : ℤ)^n = 2^((n-1)+1) := by congr 1; omega
    _ = 2 * 2^(n-1) := by rw [pow_succ]; ring

private theorem inventory (s b : ℕ) (R T : List ℕ)
    (hs : 2 ≤ s) (hb : s + 2 ≤ b)
    (hW : (R ++ T).Perm (List.range' (2*s) (b-1))) :
    (R ++ [2*s+b-1] ++ List.range (s-1) ++ [s-1] ++
      List.range' (2*s+b) (s-1) ++ [size s b-1] ++
      (List.range' s (s-1) ++ T) ++ [2*s-1]).Perm (List.range (size s b)) := by
  have hW' : (R ++ [2*s+b-1] ++ T).Perm (List.range' (2*s) b) := by
    have h := hW.append_right [2*s+b-1]
    have hc : List.range' (2*s) (b-1) ++ [2*s+b-1] = List.range' (2*s) b := by
      simpa only [show 2*s+(b-1)=2*s+b-1 by omega, show (b-1)+1=b by omega]
        using (List.range'_1_concat (s:=2*s) (n:=b-1)).symm
    rw [← hc] at h
    apply h.trans
    apply List.Perm.of_eq
    simp only [List.append_assoc]
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl
  have hU : List.range (s-1) ++ [s-1] = List.range s := by
    simpa only [show s-1+1=s by omega] using (List.range_succ (n:=s-1)).symm
  have hX : List.range' (2*s+b) (s-1) ++ [size s b-1] =
      List.range' (2*s+b) s := by
    dsimp [size]
    simpa only [show 2*s+b+(s-1)=s+b+s+s-1 by omega,
      show (s-1)+1=s by omega] using
      (List.range'_1_concat (s:=2*s+b) (n:=s-1)).symm
  have hAll : List.range s ++ List.range' s (s-1) ++ [2*s-1] ++
      List.range' (2*s) b ++ List.range' (2*s+b) s = List.range (size s b) := by
    rw [List.range_eq_range']
    have h1 := List.range'_append_1 (s:=0) (m:=s) (n:=s-1)
    have h0 : List.range' 0 (2*s-1) ++ [2*s-1] = List.range' 0 (2*s) := by
      simpa only [Nat.zero_add] using
        (List.range'_1_concat (s:=0) (n:=2*s-1)).symm
    have h2 := List.range'_append_1 (s:=0) (m:=2*s) (n:=b)
    have h3 := List.range'_append_1 (s:=0) (m:=2*s+b) (n:=s)
    simp only [Nat.zero_add] at h1 h2 h3
    rw [h1]
    rw [show s+(s-1)=2*s-1 by omega, h0]
    rw [h2]
    rw [h3]
    congr 1
    dsimp [size]
    omega
  have hcanon :
      (List.range (s-1) ++ [s-1]) ++
        (List.range' s (s-1) ++ [2*s-1]) ++
        List.range' (2*s) b ++
        (List.range' (2*s+b) (s-1) ++ [size s b-1]) =
      List.range (size s b) := by
    rw [hU, hX]
    exact hAll
  have hreshape :
      (R ++ [2*s+b-1] ++ List.range (s-1) ++ [s-1] ++
        List.range' (2*s+b) (s-1) ++ [size s b-1] ++
        (List.range' s (s-1) ++ T) ++ [2*s-1]).Perm
      ((List.range (s-1) ++ [s-1]) ++
        (List.range' s (s-1) ++ [2*s-1]) ++
        (R ++ [2*s+b-1] ++ T) ++
        (List.range' (2*s+b) (s-1) ++ [size s b-1])) := by
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl
  have hreplace :
      ((List.range (s-1) ++ [s-1]) ++
        (List.range' s (s-1) ++ [2*s-1]) ++
        (R ++ [2*s+b-1] ++ T) ++
        (List.range' (2*s+b) (s-1) ++ [size s b-1])).Perm
      ((List.range (s-1) ++ [s-1]) ++
        (List.range' s (s-1) ++ [2*s-1]) ++
        List.range' (2*s) b ++
        (List.range' (2*s+b) (s-1) ++ [size s b-1])) := by
    simpa only [List.append_assoc] using
      (List.Perm.refl (List.range (s-1) ++ [s-1])).append
        ((List.Perm.refl (List.range' s (s-1) ++ [2*s-1])).append
          (hW'.append (List.Perm.refl (List.range' (2*s+b) (s-1) ++ [size s b-1]))))
  exact hreshape.trans (hreplace.trans (List.Perm.of_eq hcanon))

set_option maxHeartbeats 2400000 in
private theorem physical (s b : ℕ) (v : ℤ) (R T : List ℕ)
    (hs : 2 ≤ s) (hb : s + 2 ≤ b)
    (hW : (R ++ T).Perm (List.range' (2*s) (b-1)))
    (hweight : ∀ (h : ℕ → ℤ) (H : ℤ),
      (∀ i < b-1, h (2*s+i) = 2^i*H) →
      (T.map h).sum = (v-1)*H)
    (hend : UpperBounds (2^s) (2^b) (2^(s-1)) v) :
    ∃ l : List ℕ, l.Perm (List.range (size s b)) ∧
      InStrip (fun i => centered (sourceMod s b s s)
        ((2 : ℤ)^i * base s b s s 0)) (sourceMod s b s s / 2) 0 l ∧
      ∃ j : ℕ, j ≤ size s b ∧
        InStrip (fun i => centered (2*sourceMod s b s s+1)
          ((2 : ℤ)^i * (2*base s b s s 0))) (sourceMod s b s s) 0
          (insertAt (size s b) l j) := by
  let k := size s b
  let A := base s b s s 0
  let B := base s b s s 1
  let L := base s b s s 2
  let M := base s b s s 3
  let N := sourceMod s b s s
  let Bn := 2*B-1
  let Ln := 2*L-(2^s)-1
  let Mn := 2*M-1-(2^b)-(2^s)*(2^b)
  let f := fun i : ℕ => centered N ((2 : ℤ)^i*A)
  let g := fun i : ℕ => centered (2*N+1) ((2 : ℤ)^i*(2*A))
  obtain ⟨hA,hB,hL,hM,huf,hvf,hwf,hxf,hug,hvg,hwg,hxg,hfresh⟩ :=
    source_table s b s s hs hb hs hs
  change 1 ≤ A ∧ A < N at hA
  change 1 ≤ B ∧ B < N at hB
  change 1 ≤ L ∧ L < N at hL
  change 1 ≤ M ∧ M < N at hM
  change ∀ i<s, f i=if i+1<s then 2^i*A else -(N-B)/2 at huf
  change ∀ i<s, f (s+i)=if i+1<s then 2^i*B else -(N-L)/2 at hvf
  change ∀ i<b, f (2*s+i)=if i+1<b then 2^i*L else -(N-M)/2 at hwf
  change ∀ i<s, f (2*s+b+i)=if i+1<s then 2^i*M else -(N-A)/2 at hxf
  change ∀ i<s, g i=if i+1<s then 2^i*(2*A) else -((2*N+1)-Bn)/2 at hug
  change ∀ i<s, g (s+i)=if i+1<s then 2^i*Bn else -((2*N+1)-Ln)/2 at hvg
  change ∀ i<b, g (2*s+i)=if i+1<b then 2^i*Ln else -((2*N+1)-Mn)/2 at hwg
  change ∀ i<s, g (2*s+b+i)=if i+1<s then 2^i*Mn else -((2*N+1)-A)/2 at hxg
  have hfresh' : g k = A := by simpa [k] using hfresh
  have hnb := new_base_bounds s b s s hs hb hs hs
  have hnewB : 0 ≤ Bn := by
    have h := hnb 1
    change 1 ≤ Bn ∧ Bn < 2*N+1 at h
    omega
  have hnewL : 0 ≤ Ln := by
    have h := hnb 2
    change 1 ≤ Ln ∧ Ln < 2*N+1 at h
    omega
  have hnewM : 0 ≤ Mn := by
    have h := hnb 3
    change 1 ≤ Mn ∧ Mn < 2*N+1 at h
    omega
  have posU (i : ℕ) (hi : i<s-1) : f i=2^i*A ∧ g i=2^i*(2*A) :=
    ⟨(huf i (by omega)).trans (ite_eq_left (by omega)),
     (hug i (by omega)).trans (ite_eq_left (by omega))⟩
  have posV (i : ℕ) (hi : i<s-1) : f (s+i)=2^i*B ∧ g (s+i)=2^i*Bn :=
    ⟨(hvf i (by omega)).trans (ite_eq_left (by omega)),
     (hvg i (by omega)).trans (ite_eq_left (by omega))⟩
  have posW (i : ℕ) (hi : i<b-1) : f (2*s+i)=2^i*L ∧ g (2*s+i)=2^i*Ln :=
    ⟨(hwf i (by omega)).trans (ite_eq_left (by omega)),
     (hwg i (by omega)).trans (ite_eq_left (by omega))⟩
  have posX (i : ℕ) (hi : i<s-1) : f (2*s+b+i)=2^i*M ∧ g (2*s+b+i)=2^i*Mn :=
    ⟨(hxf i (by omega)).trans (ite_eq_left (by omega)),
     (hxg i (by omega)).trans (ite_eq_left (by omega))⟩
  let P1 := R
  let P2 := List.range (s-1)
  let P3 := List.range' (2*s+b) (s-1)
  let P4 := List.range' s (s-1) ++ T
  let wneg := 2*s+b-1
  let uneg := s-1
  let xneg := k-1
  let vneg := 2*s-1
  have hRmass : (P1.map f).sum=(2^(b-1)-v)*L ∧
      (P1.map g).sum=(2^(b-1)-v)*Ln := by
    have hf := (hW.map f).sum_eq
    have hg := (hW.map g).sum_eq
    have hsf := ladder_sum f (2*s) (b-1) L
      (by intro i hi; exact posW i hi)
    have hsg := ladder_sum g (2*s) (b-1) Ln
      (by intro i hi; exact posW i hi)
    have ht := hweight f L (by intro i hi; exact (posW i hi).1)
    have ht' := hweight g Ln (by intro i hi; exact (posW i hi).2)
    simp only [List.map_append,List.sum_append] at hf hg
    rw [ht,ht',hsf,hsg] at hf hg
    constructor <;> nlinarith only [hf,hg]
  have hP2 : (P2.map f).sum=(2^(s-1)-1)*A ∧
      (P2.map g).sum=(2^(s-1)-1)*(2*A) := by
    have hf := ladder_sum f 0 (s-1) A (by intro i hi; exact (posU i hi).1)
    have hg := ladder_sum g 0 (s-1) (2*A) (by intro i hi; exact (posU i hi).2)
    simpa [P2] using And.intro hf hg
  have hP3 : (P3.map f).sum=(2^(s-1)-1)*M ∧
      (P3.map g).sum=(2^(s-1)-1)*Mn := by
    have hf := ladder_sum f (2*s+b) (s-1) M
      (by intro i hi; exact (posX i hi).1)
    have hg := ladder_sum g (2*s+b) (s-1) Mn
      (by intro i hi; exact (posX i hi).2)
    simpa [P3] using And.intro hf hg
  have hP4 : (P4.map f).sum=(2^(s-1)-1)*B+(v-1)*L ∧
      (P4.map g).sum=(2^(s-1)-1)*Bn+(v-1)*Ln := by
    have hvf' := ladder_sum f s (s-1) B (by intro i hi; exact (posV i hi).1)
    have hvg' := ladder_sum g s (s-1) Bn (by intro i hi; exact (posV i hi).2)
    have ht := hweight f L (by intro i hi; exact (posW i hi).1)
    have ht' := hweight g Ln (by intro i hi; exact (posW i hi).2)
    simp only [P4,List.map_append,List.sum_append,List.map_append] 
    rw [hvf',hvg',ht,ht']
  have hnegW : f wneg=-(N-M)/2 ∧ g wneg=-((2*N+1)-Mn)/2 := by
    simpa [wneg] using And.intro (hwf (b-1) (by omega)) (hwg (b-1) (by omega))
  have hnegU : f uneg=-(N-B)/2 ∧ g uneg=-((2*N+1)-Bn)/2 := by
    simpa [uneg] using And.intro (huf (s-1) (by omega)) (hug (s-1) (by omega))
  have hnegX : f xneg=-(N-A)/2 ∧ g xneg=-((2*N+1)-A)/2 := by
    simpa [xneg,k,size] using And.intro (hxf (s-1) (by omega)) (hxg (s-1) (by omega))
  have hnegV : f vneg=-(N-L)/2 ∧ g vneg=-((2*N+1)-Ln)/2 := by
    simpa [vneg] using And.intro (hvf (s-1) (by omega)) (hvg (s-1) (by omega))
  have hpowq : (2^s : ℤ) = 2*(2^(s-1)) := pow_step s (by omega)
  have hpowy : (2^b : ℤ) = 2*(2^(b-1)) := pow_step b (by omega)
  have hgates :
      upperGates (N/2) (P1.map f).sum (f wneg)
        (P2.map f).sum (f uneg) (P3.map f).sum (f xneg)
        (P4.map f).sum (f vneg) ∧
      upperGates N (P1.map g).sum (g wneg)
        (P2.map g).sum (g uneg) (([k]++P3).map g).sum (g xneg)
        (P4.map g).sum (g vneg) := by
    rw [hRmass.1,hP2.1,hP3.1,hP4.1,hRmass.2,hP2.2,hP3.2,hP4.2,
      hnegW.1,hnegU.1,hnegX.1,hnegV.1,hnegW.2,hnegU.2,hnegX.2,hnegV.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,zero_add,hfresh']
    have hh := hend
    dsimp only [UpperBounds] at hh
    convert hh using 3 <;> (try dsimp [N,A,B,L,M,Bn,Ln,Mn]) <;>
      (try rw [hpowq,hpowy]) <;> ring
  have hpold : ∀ i ∈ P1, 0≤f i := by
    intro i hi
    have hm := hW.mem_iff.mp (List.mem_append_left T hi)
    obtain ⟨t, ht, heq⟩ := List.mem_range'.mp hm
    subst i
    simpa only [show 2*s+t=2*s+t by rfl] using (posW t ht).1.le
  have hpoldU : ∀ i ∈ P2, 0≤f i := by
    intro i hi; exact (posU i (List.mem_range.mp hi)).1.le
  have hpoldX : ∀ i ∈ P3, 0≤f i := by
    intro i hi
    simpa only [show i=2*s+b+(i-(2*s+b)) by omega] using
      (posX (i-(2*s+b)) (by omega)).1.le
  have hpoldV : ∀ i ∈ P4, 0≤f i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · simpa only [show i=s+(i-s) by omega] using (posV (i-s) (by omega)).1.le
    · have hm := hW.mem_iff.mp (List.mem_append_right R hi)
      obtain ⟨t, ht, heq⟩ := List.mem_range'.mp hm
      subst i
      simpa only [show 2*s+t=2*s+t by rfl] using (posW t ht).1.le
  have hpnew : ∀ i ∈ P1, 0≤g i := by
    intro i hi
    have hm := hW.mem_iff.mp (List.mem_append_left T hi)
    obtain ⟨t, ht, heq⟩ := List.mem_range'.mp hm
    subst i
    simpa only [show 2*s+t=2*s+t by rfl] using (posW t ht).2.le
  have hpnewU : ∀ i ∈ P2, 0≤g i := by
    intro i hi; exact (posU i (List.mem_range.mp hi)).2.le
  have hpnewX : ∀ i ∈ [k]++P3, 0≤g i := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl|hi
    · exact hA.le
    · simpa only [show i=2*s+b+(i-(2*s+b)) by omega] using
        (posX (i-(2*s+b)) (by omega)).2.le
  have hpnewV : ∀ i ∈ P4, 0≤g i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · simpa only [show i=s+(i-s) by omega] using (posV (i-s) (by omega)).2.le
    · have hm := hW.mem_iff.mp (List.mem_append_right R hi)
      obtain ⟨t, ht, heq⟩ := List.mem_range'.mp hm
      subst i
      simpa only [show 2*s+t=2*s+t by rfl] using (posW t ht).2.le
  let oldWord := P1++[wneg]++P2++[uneg]++P3++[xneg]++P4++[vneg]
  let newWord := P1++[wneg]++P2++[uneg]++[k]++P3++[xneg]++P4++[vneg]
  have hperm : oldWord.Perm (List.range k) := by
    simpa [oldWord,P1,P2,P3,P4,wneg,uneg,xneg,vneg] using inventory s b R T hs hb hW
  have hold : InStrip f (N/2) 0 oldWord := by
    exact four_strip f (N/2) P1 P2 P3 P4 wneg uneg xneg vneg
      hpold hpoldU hpoldX hpoldV hgates.1
  have hnew : InStrip g N 0 newWord := by
    have hnewMass : ((([k]++P3).map g).sum) = A + (P3.map g).sum := by
      simp [List.map_cons,List.sum_cons,List.sum_nil,hfresh']
    simpa [newWord,List.append_assoc,hnewMass] using
      (four_strip g N P1 P2 ([k]++P3) P4 wneg uneg xneg vneg
        hpnew hpnewU hpnewX hpnewV hgates.2)
  have hlen : oldWord.length = k := by
    have hh := hperm.length_eq
    simpa [oldWord] using hh
  let j := P1.length + 1 + P2.length + 1
  have hj : j ≤ k := by dsimp [j]; omega
  have hinsert : insertAt k oldWord j = newWord := by
    let pre := P1++[wneg]++P2++[uneg]
    let post := P3++[xneg]++P4++[vneg]
    have he : oldWord = pre ++ post := by rfl
    have hj' : pre.length = j := by simp [pre,j]
    have hj0 : j = pre.length + 0 := by simp [hj']
    rw [he, hj0, insertAt_add]
    simp [pre,post,insertAt]
  refine ⟨oldWord,hperm,?_,j,hj,?_⟩
  · simpa [f,N,A] using hold
  · simpa [g,N,A,hinsert] using hnew

private theorem actual_of_physical (s b : ℕ) (l : List ℕ) (j : ℕ)
    (hp : l.Perm (List.range (size s b))) (hj : j ≤ size s b)
    (hold : InStrip (fun i => centered (sourceMod s b s s)
      ((2 : ℤ)^i * base s b s s 0)) (sourceMod s b s s / 2) 0 l)
    (hnew : InStrip (fun i => centered (2*sourceMod s b s s+1)
      ((2 : ℤ)^i * (2*base s b s s 0))) (sourceMod s b s s) 0
      (insertAt (size s b) l j)) :
    OriginalOrder (size s b) (seed s b) (l.map (label (size s b) (by
      dsimp [size]; omega))) ∧
    OriginalOrder (size s b + 1) (2*seed s b)
      (earWord (size s b) (l.map (label (size s b) (by
        dsimp [size]; omega))) j) := by
  let k := size s b
  let A := base s b s s 0
  let N := sourceMod s b s s
  have hk : 0 < k := by dsimp [k,size]; omega
  have hmod : modulus k = N := by
    dsimp [k,N,size,modulus,sourceMod]
    ring
  have hmod' : modulus (k+1) = 2*N+1 := by
    dsimp [k,N,size,modulus,sourceMod]
    ring
  have hseed : (seed s b : ℤ) = A := by
    dsimp [seed,A,base]
    push_cast
    ring
  have old : OriginalOrder k (seed s b)
      (l.map (label k hk)) := by
    apply lift_order k (seed s b) hk l hp
    · simpa [hmod,hseed] using hold
    · simpa [hmod,hseed] using
        (ThreeNegativeEqualOuterSourceBridge.source_zero k (seed s b) hk)
  let pre := l.take j
  let post := l.drop j
  have hlen : l.length = k := by
    simpa using hp.length_eq
  have hprelen : pre.length = j := by
    dsimp [pre]
    rw [List.length_take, Nat.min_eq_left]
    exact hj
  have hnewperm : (pre ++ k :: post).Perm (List.range (k+1)) := by
    have he : pre ++ post = l := List.take_append_drop j l
    have h1 : (pre ++ k :: post).Perm (l ++ [k]) := by
      rw [← he]
      apply Multiset.coe_eq_coe.mp
      simp only [← Multiset.coe_add]
      ac_rfl
    exact h1.trans (by simpa [List.range_succ] using hp.append_right [k])
  have new : OriginalOrder (k+1) (2*seed s b)
      ((pre ++ k :: post).map (label (k+1) (by omega))) := by
    apply lift_order (k+1) (2*seed s b) (by omega) (pre ++ k :: post) hnewperm
    · simpa [hmod',hseed,insertAt,pre,post] using hnew
    · simpa [hmod',hseed] using
        (ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*seed s b) (by omega))
  have hpr : (pre ++ post).Perm (List.range k) := by
    rw [List.take_append_drop]
    exact hp
  refine ⟨old, ?_⟩
  rw [marked_word k j hk pre post hprelen hpr]
  exact new

private def wMask (s b : ℕ) : List ℕ :=
  List.range' (2*s) (b-s-2) ++ [2*s+(b-s-2)+1]
private def wRest (s b : ℕ) : List ℕ :=
  [2*s+(b-s-2)] ++ List.range' (2*s+(b-s-2)+2) (s-1)
private def wMaskCorner : List ℕ := [5]
private def wRestCorner : List ℕ := [4,6]
private def wMaskTwo (b : ℕ) : List ℕ :=
  List.range' 4 (b-5) ++ [4+(b-5)+2]
private def wRestTwo (b : ℕ) : List ℕ :=
  List.range' (4+(b-5)) 2 ++ List.range' (4+(b-5)+3) 1

private theorem mask_partition_s_ge_three (s b : ℕ) (hs : 3 ≤ s)
    (hb : s+2 ≤ b) :
    (wRest s b ++ wMask s b).Perm (List.range' (2*s) (b-1)) := by
  dsimp [wRest,wMask]
  let h := b-s-2
  have h0 : List.range' (2*s) h ++ [2*s+h] = List.range' (2*s) (h+1) := by
    simpa using (List.range'_1_concat (s:=2*s) (n:=h)).symm
  have h1 : List.range' (2*s) (h+1) ++ [2*s+h+1] =
      List.range' (2*s) (h+2) := by
    simpa [show 2*s+(h+1)=2*s+h+1 by omega] using
      (List.range'_1_concat (s:=2*s) (n:=h+1)).symm
  have h2 : List.range' (2*s) (h+2) ++ List.range' (2*s+h+2) (s-1) =
      List.range' (2*s) (h+s+1) := by
    simpa using (List.range'_append_1 (s:=2*s) (m:=h+2) (n:=s-1)).symm
  have hlen : h+s+1=b-1 := by dsimp [h]; omega
  rw [← hlen, ← h2, ← h1, ← h0]
  apply Multiset.coe_eq_coe.mp
  simp only [← Multiset.coe_add]
  ac_rfl

private theorem mask_partition_corner :
    (wRestCorner ++ wMaskCorner).Perm (List.range' 4 3) := by decide

private theorem mask_partition_two (b : ℕ) (hb : 5 ≤ b) :
    (wRestTwo b ++ wMaskTwo b).Perm (List.range' 4 (b-1)) := by
  dsimp [wRestTwo,wMaskTwo]
  let h := b-5
  have h0 : List.range' 4 h ++ List.range' (4+h) 2 =
      List.range' 4 (h+2) := by
    simpa using (List.range'_append_1 (s:=4) (m:=h) (n:=2)).symm
  have h1 : List.range' 4 (h+2) ++ [4+h+2] = List.range' 4 (h+3) := by
    simpa using (List.range'_1_concat (s:=4) (n:=h+2)).symm
  have h2 : List.range' 4 (h+3) ++ [4+h+3] = List.range' 4 (h+4) := by
    simpa using (List.range'_1_concat (s:=4) (n:=h+3)).symm
  have hlen : h+4=b-1 := by dsimp [h]; omega
  rw [← hlen, ← h2, ← h1, ← h0]
  apply Multiset.coe_eq_coe.mp
  simp only [← Multiset.coe_add]
  ac_rfl

private theorem weight_s_ge_three (s b : ℕ) (hs : 3 ≤ s) (hb : s+2 ≤ b)
    (h : ℕ → ℤ) (H : ℤ)
    (hh : ∀ i < b-1, h (2*s+i)=2^i*H) :
    ((wMask s b).map h).sum = (3*2^(b-s-2)-1)*H := by
  dsimp [wMask]
  rw [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
  rw [ladder_sum h (2*s) (b-s-2) H (by intro i hi; exact hh i (by omega))]
  rw [hh (b-s-2+1) (by omega)]
  have : (2:ℤ)^(b-s-2+1) = 2*2^(b-s-2) := by rw [pow_succ]
  rw [this]
  ring

private theorem weight_corner (h : ℕ → ℤ) (H : ℤ)
    (hh : ∀ i < 3, h (4+i)=2^i*H) :
    ((wMaskCorner.map h).sum) = 2*H := by
  simp [wMaskCorner,hh]

private theorem weight_two (b : ℕ) (hb : 5 ≤ b)
    (h : ℕ → ℤ) (H : ℤ)
    (hh : ∀ i < b-1, h (4+i)=2^i*H) :
    ((wMaskTwo b).map h).sum = (5*2^(b-5)-1)*H := by
  dsimp [wMaskTwo]
  rw [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
  rw [ladder_sum h 4 (b-5) H (by intro i hi; exact hh i (by omega))]
  rw [hh (b-5+2) (by omega)]
  rw [show (2:ℤ)^(b-5+2)=4*2^(b-5) by rw [pow_add]; norm_num; ring]
  ring

private theorem upper_s_ge_three (s b : ℕ) (hs : 3 ≤ s) (hb : s+2 ≤ b) :
    ∃ l : List ℕ, l.Perm (List.range (size s b)) ∧
      InStrip (fun i => centered (sourceMod s b s s)
        ((2 : ℤ)^i * base s b s s 0)) (sourceMod s b s s / 2) 0 l ∧
      ∃ j : ℕ, j ≤ size s b ∧
        InStrip (fun i => centered (2*sourceMod s b s s+1)
          ((2 : ℤ)^i * (2*base s b s s 0))) (sourceMod s b s s) 0
          (insertAt (size s b) l j) := by
  let h := b-s-2
  let m := 2^h
  let v := 3*m
  have hh : 0 ≤ h := by dsimp [h]; omega
  have hm : 1 ≤ m := by dsimp [m]; positivity
  have hq : (2:ℤ)^s = 2*(2:ℤ)^(s-1) := pow_step s (by omega)
  have hy : (2:ℤ)^b = 8*(2:ℤ)^(s-1)*(2:ℤ)^h := by
    dsimp [h]
    rw [show b=s+2+(b-s-2) by omega, pow_add, pow_add, pow_add]
    norm_num
    ring
  have hbnd : UpperBounds (2^s) (2^b) (2^(s-1)) v := by
    have hc := chart_s_ge_three (2^(s-1):ℤ) (2^h:ℤ) (by
      have : (8:ℤ) ≤ 2^s := by exact pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith [hq]) (by positivity)
    simpa [v,m,h,show (2:ℤ)^s=2*(2:ℤ)^(s-1) by exact hq,
      show (2:ℤ)^b=8*(2:ℤ)^(s-1)*(2:ℤ)^h by exact hy] using hc
  apply physical s b (v : ℤ) (wRest s b) (wMask s b) (by omega) hb
    (mask_partition_s_ge_three s b hs hb)
    (by intro H K hh; simpa [v,m] using weight_s_ge_three s b hs hb H K hh) hbnd

private theorem upper_s_two_four :
    ∃ l : List ℕ, l.Perm (List.range (size 2 4)) ∧
      InStrip (fun i => centered (sourceMod 2 4 2 2)
        ((2 : ℤ)^i * base 2 4 2 2 0)) (sourceMod 2 4 2 2 / 2) 0 l ∧
      ∃ j : ℕ, j ≤ size 2 4 ∧
        InStrip (fun i => centered (2*sourceMod 2 4 2 2+1)
          ((2 : ℤ)^i * (2*base 2 4 2 2 0))) (sourceMod 2 4 2 2) 0
          (insertAt (size 2 4) l j) := by
  apply physical 2 4 3 wRestCorner wMaskCorner (by omega) (by omega)
    mask_partition_corner
  · intro h H hh; simpa [wMaskCorner] using weight_corner h H hh
  · simpa [show (2:ℤ)^2=4 by norm_num, show (2:ℤ)^4=16 by norm_num,
      show (2:ℤ)^(2-1)=2 by norm_num] using chart_corner

private theorem upper_s_two_large (b : ℕ) (hb : 5 ≤ b) :
    ∃ l : List ℕ, l.Perm (List.range (size 2 b)) ∧
      InStrip (fun i => centered (sourceMod 2 b 2 2)
        ((2 : ℤ)^i * base 2 b 2 2 0)) (sourceMod 2 b 2 2 / 2) 0 l ∧
      ∃ j : ℕ, j ≤ size 2 b ∧
        InStrip (fun i => centered (2*sourceMod 2 b 2 2+1)
          ((2 : ℤ)^i * (2*base 2 b 2 2 0))) (sourceMod 2 b 2 2) 0
          (insertAt (size 2 b) l j) := by
  let h := b-5
  let m := 2^h
  let v := 5*m
  have hh : 0 ≤ h := by dsimp [h]; omega
  have hm : 1 ≤ m := by dsimp [m]; positivity
  have hy : (2:ℤ)^b = 32*(2:ℤ)^h := by
    dsimp [h]; rw [show b=5+h by omega, pow_add]; norm_num; ring
  have hbnd : UpperBounds (2^2) (2^b) (2^(2-1)) v := by
    have hc := chart_s_two_large (2^h:ℤ) (by positivity)
    simpa [v,m,h,hy,show (2:ℤ)^2=4 by norm_num,
      show (2:ℤ)^(2-1)=2 by norm_num] using hc
  apply physical 2 b (v : ℤ) (wRestTwo b) (wMaskTwo b) (by omega) (by omega)
    (mask_partition_two b hb)
    (by intro H K hh; simpa [v,m] using weight_two b hb H K hh) hbnd

private theorem upper_actual_s_ge_three (s b : ℕ) (hs : 3 ≤ s) (hb : s+2 ≤ b) :
    ∃ sigma : List (Fin (size s b)),
      OriginalOrder (size s b) (seed s b) sigma ∧
      ∃ j : ℕ, j ≤ size s b ∧
        OriginalOrder (size s b + 1) (2*seed s b)
          (earWord (size s b) sigma j) := by
  rcases upper_s_ge_three s b hs hb with ⟨l,hp,hold,j,hj,hnew⟩
  let sigma := l.map (label (size s b) (by dsimp [size]; omega))
  have hsigma := actual_of_physical s b l j hp hj hold hnew
  exact ⟨sigma, hsigma.1, j, hj, hsigma.2⟩

private theorem upper_actual_s_two_four :
    ∃ sigma : List (Fin (size 2 4)),
      OriginalOrder (size 2 4) (seed 2 4) sigma ∧
      ∃ j : ℕ, j ≤ size 2 4 ∧
        OriginalOrder (size 2 4 + 1) (2*seed 2 4)
          (earWord (size 2 4) sigma j) := by
  rcases upper_s_two_four with ⟨l,hp,hold,j,hj,hnew⟩
  let sigma := l.map (label (size 2 4) (by dsimp [size]; omega))
  have hsigma := actual_of_physical 2 4 l j hp hj hold hnew
  exact ⟨sigma, hsigma.1, j, hj, hsigma.2⟩

private theorem upper_actual_s_two_large (b : ℕ) (hb : 5 ≤ b) :
    ∃ sigma : List (Fin (size 2 b)),
      OriginalOrder (size 2 b) (seed 2 b) sigma ∧
      ∃ j : ℕ, j ≤ size 2 b ∧
        OriginalOrder (size 2 b + 1) (2*seed 2 b)
          (earWord (size 2 b) sigma j) := by
  rcases upper_s_two_large b hb with ⟨l,hp,hold,j,hj,hnew⟩
  let sigma := l.map (label (size 2 b) (by dsimp [size]; omega))
  have hsigma := actual_of_physical 2 b l j hp hj hold hnew
  exact ⟨sigma, hsigma.1, j, hj, hsigma.2⟩

end D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree
