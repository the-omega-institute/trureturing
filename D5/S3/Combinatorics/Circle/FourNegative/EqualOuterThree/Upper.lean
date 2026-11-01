/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualOuterThree/Upper
   generality: I
   mirror-B: none(waiver:private-consumed-construction-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-construction)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Consumed upper construction for the complete equal-outer-three family. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree.UpperArithmetic
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule
import D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift

/-! The three upper physical charts, consumed by the full family endpoint. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree

open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private UpperBounds chart_s_ge_three chart_s_two_large chart_corner
  from D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree.UpperArithmetic
open private source_table
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable
open private base newBase sourceMod new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private insertAt_add
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private Gates four_strip
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule
open private negative_step
  from D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
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
    rw [hc] at h
    have hswap : (R ++ [2*s+b-1] ++ T).Perm ((R++T)++[2*s+b-1]) := by
      apply Multiset.coe_eq_coe.mp
      simp only [← Multiset.coe_add]
      ac_rfl
    exact hswap.trans h
  have hU : List.range (s-1) ++ [s-1] = List.range s := by
    simpa only [Nat.succ_eq_add_one,show s-1+1=s by omega] using (List.range_succ (n:=s-1)).symm
  have hX : List.range' (2*s+b) (s-1) ++ [size s b-1] =
      List.range' (2*s+b) s := by
    dsimp [size]
    simpa only [show 2*s+b+(s-1)=s+b+s+s-1 by omega,
      show (s-1)+1=s by omega] using
      (List.range'_1_concat (s:=2*s+b) (n:=s-1)).symm
  have hAll : List.range s ++ List.range' s (s-1) ++ [2*s-1] ++
      List.range' (2*s) b ++ List.range' (2*s+b) s = List.range (size s b) := by
    simp only [List.range_eq_range']
    have h1 := List.range'_append_1 (s:=0) (m:=s) (n:=s-1)
    have h0 : List.range' 0 (2*s-1) ++ [2*s-1] = List.range' 0 (2*s) := by
      simpa only [Nat.zero_add, show 2*s-1+1=2*s by omega] using
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
    simpa only [List.append_assoc] using hAll
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
    (hend : UpperBounds (2^s) (2^b) (2^(s-1)) (2^(b-1)) v) :
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
  let Ln := 2*L-1-(2^s)
  let Mn := 2*M-1-(2^b)-(2^b)*(2^s)
  let f := fun i : ℕ => centered N ((2 : ℤ)^i*A)
  let g := fun i : ℕ => centered (2*N+1) ((2 : ℤ)^i*(2*A))
  obtain ⟨hA,hB,hL,hM,huf,hvf,hwf,hxf,hug,hvg,hwg,hxg,hfresh⟩ :=
    source_table s b s s hs (by omega) hs hs
  simp only [show s+s=2*s by omega] at hwf hxf hwg hxg hfresh
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
  have hfresh' : g k = A := by
    simpa only [g,N,A,base,sourceMod,Matrix.cons_val_zero,
      show 2*s+b+s=k by dsimp [k,size]; omega] using hfresh
  have hnb := new_base_bounds s b s s hs (by omega) hs hs
  have hnewB : 0 ≤ Bn := by
    have h := hnb 1
    change 1 ≤ Bn ∧ Bn < 2*N+1 at h
    omega
  have hnewL : 0 ≤ Ln := by
    have h := hnb 2
    change 1 ≤ 2*L-(1+(2:ℤ)^s) ∧ 2*L-(1+(2:ℤ)^s) < 2*N+1 at h
    dsimp only [Ln]; omega
  have hnewM : 0 ≤ Mn := by
    have h := hnb 3
    change 1 ≤ 2*M-(1+(2:ℤ)^b+(2:ℤ)^b*2^s) ∧
      2*M-(1+(2:ℤ)^b+(2:ℤ)^b*2^s) < 2*N+1 at h
    dsimp only [Mn]; omega
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
      (by intro i hi; exact (posW i hi).1)
    have hsg := ladder_sum g (2*s) (b-1) Ln
      (by intro i hi; exact (posW i hi).2)
    have ht := hweight f L (by intro i hi; exact (posW i hi).1)
    have ht' := hweight g Ln (by intro i hi; exact (posW i hi).2)
    simp only [List.map_append,List.sum_append] at hf hg
    rw [ht,hsf] at hf
    rw [ht',hsg] at hg
    constructor <;> nlinarith only [hf,hg]
  have hP2 : (P2.map f).sum=(2^(s-1)-1)*A ∧
      (P2.map g).sum=(2^(s-1)-1)*(2*A) := by
    have hf := ladder_sum f 0 (s-1) A (by intro i hi; simpa using (posU i hi).1)
    have hg := ladder_sum g 0 (s-1) (2*A) (by intro i hi; simpa using (posU i hi).2)
    simpa only [P2, ← List.range_eq_range'] using And.intro hf hg
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
    exact ⟨rfl,rfl⟩
  have hpowq : (2^s : ℤ) = 2*(2^(s-1)) := pow_step s (by omega)
  have hpowy : (2^b : ℤ) = 2*(2^(b-1)) := pow_step b (by omega)
  have rels : (2:ℤ)^s*A=N+B ∧ (2:ℤ)^s*B=N+L ∧
      (2:ℤ)^b*L=N+M ∧ (2:ℤ)^s*M=N+A := by
    dsimp [A,B,L,M,N,base,sourceMod]
    constructor; ring
    constructor; ring
    constructor <;> ring
  have grels : (2:ℤ)^s*(2*A)=2*N+1+Bn ∧ (2:ℤ)^s*Bn=2*N+1+Ln ∧
      (2:ℤ)^b*Ln=2*N+1+Mn ∧ (2:ℤ)^s*Mn=2*N+1+A := by
    dsimp [Bn,Ln,Mn,A,B,L,M,N,base,sourceMod]
    constructor; ring
    constructor; ring
    constructor <;> ring
  have hnegW : f wneg=M-2^(b-1)*L ∧
      g wneg=Mn-2^(b-1)*Ln := by
    have hf := hwf (b-1) (by omega)
    have hg := hwg (b-1) (by omega)
    rw [ite_eq_right (by omega), negative_step N L M (2^(b-1))
      (by rw [← hpowy]; exact rels.2.2.1)] at hf
    rw [ite_eq_right (by omega), negative_step (2*N+1) Ln Mn (2^(b-1))
      (by rw [← hpowy]; exact grels.2.2.1)] at hg
    simpa only [show 2*s+(b-1)=wneg by dsimp [wneg]; omega] using And.intro hf hg
  have hnegU : f uneg=B-2^(s-1)*A ∧
      g uneg=Bn-2^(s-1)*(2*A) := by
    have hf := huf (s-1) (by omega)
    have hg := hug (s-1) (by omega)
    rw [ite_eq_right (by omega), negative_step N A B (2^(s-1))
      (by rw [← hpowq]; exact rels.1)] at hf
    rw [ite_eq_right (by omega), negative_step (2*N+1) (2*A) Bn (2^(s-1))
      (by rw [← hpowq]; exact grels.1)] at hg
    simpa only [uneg] using And.intro hf hg
  have hnegX : f xneg=A-2^(s-1)*M ∧
      g xneg=A-2^(s-1)*Mn := by
    have hf := hxf (s-1) (by omega)
    have hg := hxg (s-1) (by omega)
    rw [ite_eq_right (by omega), negative_step N M A (2^(s-1))
      (by rw [← hpowq]; exact rels.2.2.2)] at hf
    rw [ite_eq_right (by omega), negative_step (2*N+1) Mn A (2^(s-1))
      (by rw [← hpowq]; exact grels.2.2.2)] at hg
    simpa only [show 2*s+b+(s-1)=xneg by dsimp [xneg,k,size]; omega] using And.intro hf hg
  have hnegV : f vneg=L-2^(s-1)*B ∧
      g vneg=Ln-2^(s-1)*Bn := by
    have hf := hvf (s-1) (by omega)
    have hg := hvg (s-1) (by omega)
    rw [ite_eq_right (by omega), negative_step N B L (2^(s-1))
      (by rw [← hpowq]; exact rels.2.1)] at hf
    rw [ite_eq_right (by omega), negative_step (2*N+1) Bn Ln (2^(s-1))
      (by rw [← hpowq]; exact grels.2.1)] at hg
    simpa only [show s+(s-1)=vneg by dsimp [vneg]; omega] using And.intro hf hg
  have hhalf : N/2=((2:ℤ)^s)^3*2^(b-1)-1 := by
    have hn : N=2*(((2:ℤ)^s)^3*2^(b-1))-1 := by
      dsimp [N,sourceMod]
      rw [hpowy]
      ring
    omega
  have hgates :
      Gates (N/2) (P1.map f).sum (f wneg)
        (P2.map f).sum (f uneg) (P3.map f).sum (f xneg)
        (P4.map f).sum (f vneg) ∧
      Gates N (P1.map g).sum (g wneg)
        (P2.map g).sum (g uneg) (([k]++P3).map g).sum (g xneg)
        (P4.map g).sum (g vneg) := by
    rw [hRmass.1,hP2.1,hP3.1,hP4.1,hRmass.2,hP2.2,hP4.2,
      hnegW.1,hnegU.1,hnegX.1,hnegV.1,hnegW.2,hnegU.2,hnegX.2,hnegV.2]
    simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,hfresh',hP3.2]
    have hh := hend
    dsimp only [UpperBounds] at hh
    rw [hhalf]
    convert hh using 2 <;> dsimp [N,A,B,L,M,Bn,Ln,Mn,base,sourceMod] <;>
      (try rw [hpowy]) <;> ring
  have posblock (z : ℕ → ℤ) (H : ℤ) (o n : ℕ) (hH : 0≤H)
      (hh : ∀ i<n,z (o+i)=2^i*H) : ∀ i∈List.range' o n, 0≤z i := by
    intro i hi
    have hi' := List.mem_range'_1.mp hi
    rw [show i=o+(i-o) by omega,hh (i-o) (by omega)]
    positivity
  have hAf : 0≤A := by omega
  have hBf : 0≤B := by omega
  have hLf : 0≤L := by omega
  have hMf : 0≤M := by omega
  have hpold : ∀ i ∈ P1, 0≤f i := by
    intro i hi
    exact posblock f L (2*s) (b-1) hLf (by intro j hj; exact (posW j hj).1)
      i (hW.mem_iff.mp (List.mem_append_left T hi))
  have hpoldU : ∀ i ∈ P2, 0≤f i := by
    intro i hi
    rw [(posU i (List.mem_range.mp hi)).1]
    positivity
  have hpoldX : ∀ i ∈ P3, 0≤f i :=
    posblock f M (2*s+b) (s-1) hMf (by intro j hj; exact (posX j hj).1)
  have hpoldV : ∀ i ∈ P4, 0≤f i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact posblock f B s (s-1) hBf (by intro j hj; exact (posV j hj).1) i hi
    · exact posblock f L (2*s) (b-1) hLf (by intro j hj; exact (posW j hj).1)
        i (hW.mem_iff.mp (List.mem_append_right R hi))
  have hpnew : ∀ i ∈ P1, 0≤g i := by
    intro i hi
    exact posblock g Ln (2*s) (b-1) hnewL (by intro j hj; exact (posW j hj).2)
      i (hW.mem_iff.mp (List.mem_append_left T hi))
  have hpnewU : ∀ i ∈ P2, 0≤g i := by
    intro i hi
    rw [(posU i (List.mem_range.mp hi)).2]
    positivity
  have hpnewX : ∀ i ∈ [k]++P3, 0≤g i := by
    intro i hi
    rcases List.mem_cons.mp hi with hi|hi
    · rw [hi,hfresh']; exact hAf
    · exact posblock g Mn (2*s+b) (s-1) hnewM (by intro j hj; exact (posX j hj).2) i hi
  have hpnewV : ∀ i ∈ P4, 0≤g i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact posblock g Bn s (s-1) hnewB (by intro j hj; exact (posV j hj).2) i hi
    · exact posblock g Ln (2*s) (b-1) hnewL (by intro j hj; exact (posW j hj).2)
        i (hW.mem_iff.mp (List.mem_append_right R hi))
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
    simpa only [List.length_range] using hperm.length_eq
  let j := P1.length + 1 + P2.length + 1
  have hj : j ≤ k := by
    have hh := hlen
    simp only [oldWord,List.length_append,List.length_singleton] at hh
    dsimp [j]; omega
  have hinsert : insertAt k oldWord j = newWord := by
    let pre := P1++[wneg]++P2++[uneg]
    let post := P3++[xneg]++P4++[vneg]
    have he : oldWord = pre ++ post := by simp only [oldWord,pre,post,List.append_assoc]
    have hj' : pre.length = j := by
      dsimp [pre,j]
      simp only [List.length_append,List.length_singleton] <;> omega
    have hj0 : j = pre.length + 0 := by simp [hj']
    rw [he, hj0, insertAt_add]
    simp [pre,post,insertAt,newWord,List.append_assoc]
  refine ⟨oldWord,hperm,?_,j,hj,?_⟩
  · simpa [f,N,A] using hold
  · change InStrip g N 0 (insertAt k oldWord j)
    rw [hinsert]
    exact hnew

private theorem actual_of_physical (s b : ℕ) (hs : 2≤s) (l : List ℕ) (j : ℕ)
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
    simp only [pow_add] <;> ring
  have hmod' : modulus (k+1) = 2*N+1 := by
    dsimp [k,N,size,modulus,sourceMod]
    simp only [pow_add] <;> ring
  have hseed : (seed s b : ℤ) = A := by
    dsimp [seed,A,base]
    push_cast
    rw [show 2*s+b=(s+b)+s by omega]
    simp only [pow_add] <;> ring
  have old : OriginalOrder k (seed s b)
      (l.map (label k hk)) := by
    apply lift_order k (seed s b) hk l hp
    · simpa [hmod,hseed] using hold
    · simpa [hmod,hseed] using
        (ThreeNegativeEqualOuterSourceBridge.source_zero k (seed s b) (by dsimp [k,size]; omega))
  let pre := l.take j
  let post := l.drop j
  have hlen : l.length = k := by
    simpa using hp.length_eq
  have hprelen : pre.length = j := by
    dsimp [pre]
    rw [List.length_take, Nat.min_eq_left (by omega)]
  have hnewperm : (pre ++ k :: post).Perm (List.range (k+1)) := by
    have he : pre ++ post = l := List.take_append_drop j l
    have h1 : (pre ++ k :: post).Perm (l ++ [k]) := by
      rw [← he, ← List.singleton_append]
      apply Multiset.coe_eq_coe.mp
      simp only [← Multiset.coe_add]
      ac_rfl
    exact h1.trans (by simpa only [List.range_succ] using hp.append_right [k])
  have new : OriginalOrder (k+1) (2*seed s b)
      ((pre ++ k :: post).map (label (k+1) (by omega))) := by
    apply lift_order (k+1) (2*seed s b) (by omega) (pre ++ k :: post) hnewperm
    · have hhalf' : (2*N+1)/2=N := by omega
      simpa only [hmod',Nat.cast_mul,Nat.cast_ofNat,hseed,hhalf',insertAt,pre,post] using hnew
    · simpa [hmod',hseed] using
        (ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*seed s b) (by dsimp [k,size]; omega))
  have hpr : (pre ++ post).Perm (List.range k) := by
    rw [List.take_append_drop]
    exact hp
  refine ⟨old, ?_⟩
  have he : l=pre++post := (List.take_append_drop j l).symm
  rw [he,marked_word k j hk pre post hprelen hpr]
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
    simpa only [show h+2+(s-1)=h+s+1 by omega, show 2*s+(h+2)=2*s+h+2 by omega] using
      (List.range'_append_1 (s:=2*s) (m:=h+2) (n:=s-1))
  have hlen : h+s+1=b-1 := by dsimp [h]; omega
  rw [← hlen, ← h2, ← h1, ← h0]
  try simp only [List.range'_one]
  apply Multiset.coe_eq_coe.mp
  simp only [← Multiset.coe_add, ← Multiset.cons_coe, ← Multiset.singleton_add,
    Multiset.coe_nil, add_zero]
  dsimp only [h]
  ac_rfl

private theorem mask_partition_corner :
    (wRestCorner ++ wMaskCorner).Perm (List.range' 4 3) := by decide

private theorem mask_partition_two (b : ℕ) (hb : 5 ≤ b) :
    (wRestTwo b ++ wMaskTwo b).Perm (List.range' 4 (b-1)) := by
  dsimp [wRestTwo,wMaskTwo]
  let h := b-5
  have h0 : List.range' 4 h ++ List.range' (4+h) 2 =
      List.range' 4 (h+2) := by
    simpa using (List.range'_append_1 (s:=4) (m:=h) (n:=2))
  have h1 : List.range' 4 (h+2) ++ [4+h+2] = List.range' 4 (h+3) := by
    simpa only [show h+2+1=h+3 by omega,show 4+(h+2)=4+h+2 by omega] using (List.range'_1_concat (s:=4) (n:=h+2)).symm
  have h2 : List.range' 4 (h+3) ++ [4+h+3] = List.range' 4 (h+4) := by
    simpa only [show h+3+1=h+4 by omega,show 4+(h+3)=4+h+3 by omega] using (List.range'_1_concat (s:=4) (n:=h+3)).symm
  have hlen : h+4=b-1 := by dsimp [h]; omega
  rw [← hlen, ← h2, ← h1, ← h0]
  try simp only [List.range'_one]
  apply Multiset.coe_eq_coe.mp
  simp only [← Multiset.coe_add]
  dsimp only [h]
  simp only [Nat.add_assoc]
  ac_rfl

private theorem weight_s_ge_three (s b : ℕ) (hs : 3 ≤ s) (hb : s+2 ≤ b)
    (h : ℕ → ℤ) (H : ℤ)
    (hh : ∀ i < b-1, h (2*s+i)=2^i*H) :
    ((wMask s b).map h).sum = (3*2^(b-s-2)-1)*H := by
  dsimp [wMask]
  rw [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
  rw [ladder_sum h (2*s) (b-s-2) H (by intro i hi; exact hh i (by omega))]
  rw [show 2*s+(b-s-2)+1=2*s+(b-s-2+1) by omega,hh (b-s-2+1) (by omega)]
  have : (2:ℤ)^(b-s-2+1) = 2*2^(b-s-2) := by rw [pow_succ]; ring
  rw [this]
  ring

private theorem weight_corner (h : ℕ → ℤ) (H : ℤ)
    (hh : ∀ i < 3, h (4+i)=2^i*H) :
    ((wMaskCorner.map h).sum) = 2*H := by
  simpa only [wMaskCorner,List.map_singleton,List.sum_singleton,show 4+1=5 by omega,pow_one] using hh 1 (by omega)

private theorem weight_two (b : ℕ) (hb : 5 ≤ b)
    (h : ℕ → ℤ) (H : ℤ)
    (hh : ∀ i < b-1, h (4+i)=2^i*H) :
    ((wMaskTwo b).map h).sum = (5*2^(b-5)-1)*H := by
  dsimp [wMaskTwo]
  rw [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
  rw [ladder_sum h 4 (b-5) H (by intro i hi; exact hh i (by omega))]
  rw [show 4+(b-5)+2=4+(b-5+2) by omega,hh (b-5+2) (by omega)]
  rw [show (2:ℤ)^(b-5+2)=4*2^(b-5) by rw [pow_add]; norm_num <;> ring]
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
  let m : ℤ := 2^h
  let v : ℤ := 3*m
  have hm : 1 ≤ m := by
    dsimp only [m]
    simpa using pow_le_pow_right₀ (by decide : (1:ℤ)≤2) (show 0≤h by omega)
  have hq : (2:ℤ)^s = 2*(2:ℤ)^(s-1) := pow_step s (by omega)
  have hy : (2:ℤ)^b = 8*(2:ℤ)^(s-1)*(2:ℤ)^h := by
    calc
      (2:ℤ)^b=2^((s+2)+h) := by congr 1; dsimp [h]; omega
      _=8*(2:ℤ)^(s-1)*(2:ℤ)^h := by rw [pow_add,pow_add,hq]; norm_num <;> ring
  have hbnd : UpperBounds (2^s) (2^b) (2^(s-1)) (2^(b-1)) v := by
    have hc := chart_s_ge_three (2^(s-1):ℤ) (2^h:ℤ) (by
      have : (8:ℤ) ≤ 2^s := by
        simpa using pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 3≤s by omega)
      nlinarith [hq]) hm
    simpa only [v,m,show (2:ℤ)^s=2*(2:ℤ)^(s-1) by exact hq,
      show (2:ℤ)^b=8*(2:ℤ)^(s-1)*(2:ℤ)^h by exact hy,
      show (2:ℤ)^(b-1)=4*(2:ℤ)^(s-1)*(2:ℤ)^h by
        have hy2 := pow_step b (by omega); rw [hy] at hy2; nlinarith only [hy2]] using hc
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
      show (2:ℤ)^(2-1)=2 by norm_num, show (2:ℤ)^(4-1)=8 by norm_num] using chart_corner

private theorem upper_s_two_large (b : ℕ) (hb : 5 ≤ b) :
    ∃ l : List ℕ, l.Perm (List.range (size 2 b)) ∧
      InStrip (fun i => centered (sourceMod 2 b 2 2)
        ((2 : ℤ)^i * base 2 b 2 2 0)) (sourceMod 2 b 2 2 / 2) 0 l ∧
      ∃ j : ℕ, j ≤ size 2 b ∧
        InStrip (fun i => centered (2*sourceMod 2 b 2 2+1)
          ((2 : ℤ)^i * (2*base 2 b 2 2 0))) (sourceMod 2 b 2 2) 0
          (insertAt (size 2 b) l j) := by
  let h := b-5
  let m : ℤ := 2^h
  let v : ℤ := 5*m
  have hm : 1 ≤ m := by
    dsimp only [m]
    simpa using pow_le_pow_right₀ (by decide : (1:ℤ)≤2) (show 0≤h by omega)
  have hy : (2:ℤ)^b = 32*(2:ℤ)^h := by
    calc
      (2:ℤ)^b=2^(5+h) := by congr 1; dsimp [h]; omega
      _=32*2^h := by rw [pow_add]; norm_num
  have hbnd : UpperBounds (2^2) (2^b) (2^(2-1)) (2^(b-1)) v := by
    have hc := chart_s_two_large (2^h:ℤ) hm
    simpa only [v,m,hy,show (2:ℤ)^2=4 by norm_num,
      show (2:ℤ)^(2-1)=2 by norm_num,
      show (2:ℤ)^(b-1)=16*(2:ℤ)^h by
        have hy2 := pow_step b (by omega); rw [hy] at hy2; nlinarith only [hy2]] using hc
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
  have hsigma := actual_of_physical s b (by omega) l j hp hj hold hnew
  exact ⟨sigma, hsigma.1, j, hj, hsigma.2⟩

private theorem upper_actual_s_two_four :
    ∃ sigma : List (Fin (size 2 4)),
      OriginalOrder (size 2 4) (seed 2 4) sigma ∧
      ∃ j : ℕ, j ≤ size 2 4 ∧
        OriginalOrder (size 2 4 + 1) (2*seed 2 4)
          (earWord (size 2 4) sigma j) := by
  rcases upper_s_two_four with ⟨l,hp,hold,j,hj,hnew⟩
  let sigma := l.map (label (size 2 4) (by dsimp [size]; omega))
  have hsigma := actual_of_physical 2 4 (by omega) l j hp hj hold hnew
  exact ⟨sigma, hsigma.1, j, hj, hsigma.2⟩

private theorem upper_actual_s_two_large (b : ℕ) (hb : 5 ≤ b) :
    ∃ sigma : List (Fin (size 2 b)),
      OriginalOrder (size 2 b) (seed 2 b) sigma ∧
      ∃ j : ℕ, j ≤ size 2 b ∧
        OriginalOrder (size 2 b + 1) (2*seed 2 b)
          (earWord (size 2 b) sigma j) := by
  rcases upper_s_two_large b hb with ⟨l,hp,hold,j,hj,hnew⟩
  let sigma := l.map (label (size 2 b) (by dsimp [size]; omega))
  have hsigma := actual_of_physical 2 b (by omega) l j hp hj hold hnew
  exact ⟨sigma, hsigma.1, j, hj, hsigma.2⟩

end D5.S3.Combinatorics.Circle.FourNegative.EqualOuterThree
