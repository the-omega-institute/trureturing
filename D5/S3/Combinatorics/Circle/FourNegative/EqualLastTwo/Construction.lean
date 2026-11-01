/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualLastTwo/Construction
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Consumed physical partitions, reconstruction and the large-gap joint plan. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo.Schedule
/-! Exact physical construction and doubled packet checks. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo
open SourceWidth PeriodicShortening RunFirstEarTransport
open private rank amplitude delta heads newHeads successor newSuccessor start length f g N
  source source_numeric shift image_Ico image_range bankLarge bankAdjacent
  largeP largeQ largeR largeG adjacentP adjacentQ adjacentR adjacentG
  corner2P corner2Q corner2R corner2G corner3P corner3Q corner3R corner3G
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo.Source
open private four_perm from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private Checks from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Arithmetic
open private checks_strip from D5.S3.Combinatorics.Circle.FourNegative.EqualLastThreeUpper.Physical
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private size negatives source_signs sourceMod chain_values from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private finish toList_sum large_mass adjacent_mass corner_two_mass corner_three_mass
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo.Schedule
open private large_checks adjacent_checks corner_two_checks corner_three_checks
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo.Arithmetic

private theorem large_partition (a b d : ℕ) (hd : 2 ≤ d) (hb : d+2 ≤ b) (ha : b < a) :
    let k := a+b+d+d
    ((largeP a b d).toList ++ (k-1) :: (largeQ a b d).toList ++ (d-1) ::
      (largeR a b d).toList ++ (2*d-1) :: (largeG a b d).toList ++ [2*d+b-1]).Perm (List.range k) := by
  classical
  let k := a+b+d+d
  let P := largeP a b d
  let Q := largeQ a b d
  let R := largeR a b d
  let G := Finset.range k \ (P ∪ Q ∪ R ∪ {k-1,d-1,2*d-1,2*d+b-1})
  have hP : ∀ i ∈ P, i < k ∧ i ≠ k-1 ∧ i ≠ d-1 ∧ i ≠ 2*d-1 ∧ i ≠ 2*d+b-1 := by
    intro i hi; simp [P,largeP,largeQ,largeR,largeG,bankLarge,shift,image_Ico,image_range,k] at hi ⊢; omega
  have hQ : ∀ i ∈ Q, i < k ∧ i ≠ k-1 ∧ i ≠ d-1 ∧ i ≠ 2*d-1 ∧ i ≠ 2*d+b-1 := by
    intro i hi; simp [Q,largeP,largeQ,largeR,largeG,bankLarge,shift,image_Ico,image_range,k] at hi ⊢; omega
  have hR : ∀ i ∈ R, i < k ∧ i ≠ k-1 ∧ i ≠ d-1 ∧ i ≠ 2*d-1 ∧ i ≠ 2*d+b-1 := by
    intro i hi; simp [R,largeP,largeQ,largeR,largeG,bankLarge,shift,image_Ico,image_range,k] at hi ⊢; omega
  have hPQ : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [P,Q,largeP,largeQ,largeR,largeG,bankLarge,shift,image_Ico,image_range] at hi hj; omega
  have hPR : Disjoint P R := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [P,R,largeP,largeQ,largeR,largeG,bankLarge,shift,image_Ico,image_range] at hi hj; omega
  have hQR : Disjoint Q R := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [Q,R,largeP,largeQ,largeR,largeG,bankLarge,shift,image_Ico,image_range] at hi hj; omega
  have hn : ([k-1,d-1,2*d-1,2*d+b-1]:List ℕ).Nodup := by simp [k]; omega
  have hbound : ∀ i ∈ ([k-1,d-1,2*d-1,2*d+b-1]:List ℕ), i < k := by
    intro i hi; simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> dsimp [k] <;> omega
  have hp := four_perm k (k-1) (d-1) (2*d-1) (2*d+b-1) P Q R hP hQ hR hPQ hPR hQR hn hbound
  have hG : G=largeG a b d := by
    ext i; simp [G,P,Q,R,largeP,largeQ,largeR,largeG,bankLarge,shift,image_Ico,image_range,k]; omega
  dsimp only at hp ⊢
  simpa only [←hG] using hp

private theorem adjacent_partition (a d : ℕ) (hd : 2 ≤ d) (ha : d+4 ≤ a) :
    let k := a+(d+1)+d+d
    ((adjacentP a d).toList ++ (k-1) :: (adjacentQ a d).toList ++ (d-1) ::
      (adjacentR a d).toList ++ (2*d-1) :: (adjacentG a d).toList ++ [3*d]).Perm (List.range k) := by
  classical
  let k := a+(d+1)+d+d
  let P := adjacentP a d
  let Q := adjacentQ a d
  let R := adjacentR a d
  let G := Finset.range k \ (P ∪ Q ∪ R ∪ {k-1,d-1,2*d-1,3*d})
  have hP : ∀ i ∈ P, i < k ∧ i ≠ k-1 ∧ i ≠ d-1 ∧ i ≠ 2*d-1 ∧ i ≠ 3*d := by
    intro i hi; simp [P,adjacentP,adjacentQ,adjacentR,adjacentG,bankAdjacent,shift,image_Ico,image_range,k] at hi ⊢; omega
  have hQ : ∀ i ∈ Q, i < k ∧ i ≠ k-1 ∧ i ≠ d-1 ∧ i ≠ 2*d-1 ∧ i ≠ 3*d := by
    intro i hi; simp [Q,adjacentP,adjacentQ,adjacentR,adjacentG,bankAdjacent,shift,image_Ico,image_range,k] at hi ⊢; omega
  have hR : ∀ i ∈ R, i < k ∧ i ≠ k-1 ∧ i ≠ d-1 ∧ i ≠ 2*d-1 ∧ i ≠ 3*d := by
    intro i hi; simp [R,adjacentP,adjacentQ,adjacentR,adjacentG,bankAdjacent,shift,image_Ico,image_range,k] at hi ⊢; omega
  have hPQ : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [P,Q,adjacentP,adjacentQ,adjacentR,adjacentG,bankAdjacent,shift,image_Ico,image_range] at hi hj; omega
  have hPR : Disjoint P R := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [P,R,adjacentP,adjacentQ,adjacentR,adjacentG,bankAdjacent,shift,image_Ico,image_range] at hi hj; omega
  have hQR : Disjoint Q R := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [Q,R,adjacentP,adjacentQ,adjacentR,adjacentG,bankAdjacent,shift,image_Ico,image_range] at hi hj; omega
  have hn : ([k-1,d-1,2*d-1,3*d]:List ℕ).Nodup := by simp [k]; omega
  have hbound : ∀ i ∈ ([k-1,d-1,2*d-1,3*d]:List ℕ), i < k := by
    intro i hi; simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> dsimp [k] <;> omega
  have hp := four_perm k (k-1) (d-1) (2*d-1) (3*d) P Q R hP hQ hR hPQ hPR hQR hn hbound
  have hG : G=adjacentG a d := by
    ext i; simp [G,P,Q,R,adjacentP,adjacentQ,adjacentR,adjacentG,bankAdjacent,shift,image_Ico,image_range,k]; omega
  dsimp only at hp ⊢
  simpa only [←hG] using hp

private theorem corner_two_partition (d : ℕ) (hd : 2 ≤ d) :
    let k := 4*d+3
    ((corner2P d).toList ++ (d-1) :: (corner2Q d).toList ++ (2*d-1) ::
      (corner2R d).toList ++ (k-1) :: (corner2G d).toList ++ [3*d]).Perm (List.range k) := by
  classical
  let k := 4*d+3
  let P := corner2P d
  let Q := corner2Q d
  let R := corner2R d
  let G := Finset.range k \ (P ∪ Q ∪ R ∪ {d-1,2*d-1,k-1,3*d})
  have hP : ∀ i ∈ P, i < k ∧ i ≠ d-1 ∧ i ≠ 2*d-1 ∧ i ≠ k-1 ∧ i ≠ 3*d := by
    intro i hi; simp [P,corner2P,corner2Q,corner2R,corner2G,shift,image_Ico,image_range,k] at hi ⊢; omega
  have hQ : ∀ i ∈ Q, i < k ∧ i ≠ d-1 ∧ i ≠ 2*d-1 ∧ i ≠ k-1 ∧ i ≠ 3*d := by
    intro i hi; simp [Q,corner2P,corner2Q,corner2R,corner2G,shift,image_Ico,image_range,k] at hi ⊢; omega
  have hR : ∀ i ∈ R, i < k ∧ i ≠ d-1 ∧ i ≠ 2*d-1 ∧ i ≠ k-1 ∧ i ≠ 3*d := by
    intro i hi; simp [R,corner2P,corner2Q,corner2R,corner2G,shift,image_Ico,image_range,k] at hi ⊢; omega
  have hPQ : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [P,Q,corner2P,corner2Q,corner2R,corner2G,shift,image_Ico,image_range] at hi hj; omega
  have hPR : Disjoint P R := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [P,R,corner2P,corner2Q,corner2R,corner2G,shift,image_Ico,image_range] at hi hj; omega
  have hQR : Disjoint Q R := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [Q,R,corner2P,corner2Q,corner2R,corner2G,shift,image_Ico,image_range] at hi hj; omega
  have hn : ([d-1,2*d-1,k-1,3*d]:List ℕ).Nodup := by simp [k]; omega
  have hbound : ∀ i ∈ ([d-1,2*d-1,k-1,3*d]:List ℕ), i < k := by
    intro i hi; simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> dsimp [k] <;> omega
  have hp := four_perm k (d-1) (2*d-1) (k-1) (3*d) P Q R hP hQ hR hPQ hPR hQR hn hbound
  have hG : G=corner2G d := by
    ext i; simp [G,P,Q,R,corner2P,corner2Q,corner2R,corner2G,shift,image_Ico,image_range,k]; omega
  dsimp only at hp ⊢
  simpa only [←hG] using hp

private theorem corner_three_partition (d : ℕ) (hd : 2 ≤ d) :
    let k := 4*d+4
    ((corner3P d).toList ++ (k-1) :: (corner3Q d).toList ++ (2*d-1) ::
      (corner3R d).toList ++ (d-1) :: (corner3G d).toList ++ [3*d]).Perm (List.range k) := by
  classical
  let k := 4*d+4
  let P := corner3P d
  let Q := corner3Q d
  let R := corner3R d
  let G := Finset.range k \ (P ∪ Q ∪ R ∪ {k-1,2*d-1,d-1,3*d})
  have hP : ∀ i ∈ P, i < k ∧ i ≠ k-1 ∧ i ≠ 2*d-1 ∧ i ≠ d-1 ∧ i ≠ 3*d := by
    intro i hi; simp [P,corner3P,corner3Q,corner3R,corner3G,shift,image_Ico,image_range,k] at hi ⊢; omega
  have hQ : ∀ i ∈ Q, i < k ∧ i ≠ k-1 ∧ i ≠ 2*d-1 ∧ i ≠ d-1 ∧ i ≠ 3*d := by
    intro i hi; simp [Q,corner3P,corner3Q,corner3R,corner3G,shift,image_Ico,image_range,k] at hi ⊢; omega
  have hR : ∀ i ∈ R, i < k ∧ i ≠ k-1 ∧ i ≠ 2*d-1 ∧ i ≠ d-1 ∧ i ≠ 3*d := by
    intro i hi; simp [R,corner3P,corner3Q,corner3R,corner3G,shift,image_Ico,image_range,k] at hi ⊢; omega
  have hPQ : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [P,Q,corner3P,corner3Q,corner3R,corner3G,shift,image_Ico,image_range] at hi hj; omega
  have hPR : Disjoint P R := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [P,R,corner3P,corner3Q,corner3R,corner3G,shift,image_Ico,image_range] at hi hj; omega
  have hQR : Disjoint Q R := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; simp [Q,R,corner3P,corner3Q,corner3R,corner3G,shift,image_Ico,image_range] at hi hj; omega
  have hn : ([k-1,2*d-1,d-1,3*d]:List ℕ).Nodup := by simp [k]; omega
  have hbound : ∀ i ∈ ([k-1,2*d-1,d-1,3*d]:List ℕ), i < k := by
    intro i hi; simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> dsimp [k] <;> omega
  have hp := four_perm k (k-1) (2*d-1) (d-1) (3*d) P Q R hP hQ hR hPQ hPR hQR hn hbound
  have hG : G=corner3G d := by
    ext i; simp [G,P,Q,R,corner3P,corner3Q,corner3R,corner3G,shift,image_Ico,image_range,k]; omega
  dsimp only at hp ⊢
  simpa only [←hG] using hp

private theorem positive_label (a b d : ℕ) (hd : 2 ≤ d) (hb : d < b) (ha : b < a)
    (i : ℕ) (hi : i < rank a b d) (hn : i ∉ negatives a b d d) :
    0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
  have hs := source_signs a b d d (by omega) (by omega) hd hd i hi
  rw [if_neg hn] at hs
  exact ⟨hs.1.le,hs.2.le⟩

private theorem negative_label (a b d : ℕ) (hd : 2 ≤ d) (hb : d < b) (ha : b < a)
    (i : ℕ) (hi : i < rank a b d) (hn : i ∈ negatives a b d d) :
    f a b d i ≤ 0 ∧ g a b d i ≤ 0 := by
  have hs := source_signs a b d d (by omega) (by omega) hd hd i hi
  rw [if_pos hn] at hs
  exact ⟨hs.1.le,hs.2.le⟩

private theorem physical_plan (a b d : ℕ) (hd : 2 ≤ d) (hb : d < b) (ha : b < a)
    (bs bsn : List (List ℕ × ℕ)) (cut : ℕ) (pre post : List ℕ)
    (hc : pre.length=cut) (hword : blocksWord bs=pre++post)
    (hnewword : blocksWord bsn=pre++rank a b d::post)
    (hperm : (blocksWord bs).Perm (List.range (rank a b d)))
    (hC : 0 ≤ N a b d/2) (hD : 0 ≤ N a b d)
    (hp : ∀ B ∈ bs, ∀ i ∈ B.1, 0 ≤ f a b d i)
    (hpn : ∀ B ∈ bsn, ∀ i ∈ B.1, 0 ≤ g a b d i)
    (hn : ∀ B ∈ bs, f a b d B.2 ≤ 0)
    (hnn : ∀ B ∈ bsn, g a b d B.2 ≤ 0)
    (oldchecks : Checks (2*(N a b d/2)) 0
      (bs.map (fun B => (2*(B.1.map (f a b d)).sum,2*f a b d B.2))))
    (newchecks : Checks (2*N a b d) 0
      (bsn.map (fun B => (2*(B.1.map (g a b d)).sum,2*g a b d B.2)))) :
    ∃ sigma : List (Fin (rank a b d)), cut ≤ rank a b d ∧
      OriginalOrder (rank a b d) (amplitude a b d) sigma ∧
      OriginalOrder (rank a b d+1) (2*amplitude a b d)
        (earWord (rank a b d) sigma cut) := by
  apply finish a b d hd hb ha cut pre post hc (by simpa only [hword] using hperm)
  · simpa only [hword] using checks_strip (f a b d) (N a b d/2) bs hC hp hn oldchecks
  · simpa only [hnewword] using checks_strip (g a b d) (N a b d) bsn hD hpn hnn newchecks

-- The physical partition and both source rows are checked together.
set_option maxHeartbeats 2400000 in
private theorem large_plan (a b d : ℕ) (hd : 2 ≤ d) (hb : d+2 ≤ b) (ha : b < a) :
    ∃ sigma : List (Fin (rank (a) (b) d)), d ≤ rank (a) (b) d ∧
      OriginalOrder (rank (a) (b) d) (amplitude (a) (b) d) sigma ∧
      OriginalOrder (rank (a) (b) d+1) (2*amplitude (a) (b) d)
        (earWord (rank (a) (b) d) sigma (d)) := by
  classical
  have hdb : d < b := by omega
  have hba : b < a := by omega
  let k := rank a b d
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let t : ℤ := 2^d
  let A := heads x y t 0
  let B := heads x y t 1
  let L := heads x y t 2
  let M := heads x y t 3
  let Bn := newHeads x y t 1
  let Ln := newHeads x y t 2
  let Mn := newHeads x y t 3
  let m : ℤ := 2^(a-d-3)
  let u : ℤ := 2^(a-b-1)
  let v : ℤ := 2^(b-d-2)
  have hx : x=8*t*v*u := by
    dsimp [x,t,v,u]
    calc
      (2:ℤ)^a=2^(d+(b-d-2)+(a-b-1)+3) := by congr 1; omega
      _ = _ := by simp only [pow_add]; norm_num; ring
  have hy : y=4*t*v := by
    dsimp [y,t,v]
    calc
      (2:ℤ)^b=2^(d+(b-d-2)+2) := by congr 1; omega
      _ = _ := by simp only [pow_add]; norm_num; ring
  have hm : m=v*u := by
    dsimp [m,v,u]; rw [←pow_add]; congr 1; omega
  have ht : 4 ≤ t := by
    simpa [t] using pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2) hd
  have hxhalf : x=2*(2:ℤ)^(a-1) := by
    dsimp [x]; conv_lhs => rw [show a=a-1+1 by omega,pow_succ]
    ring
  have hthalf : t=2*(2:ℤ)^(d-1) := by
    dsimp [t]; conv_lhs => rw [show d=d-1+1 by omega,pow_succ]
    ring
  have hyhalf : y=2*(2:ℤ)^(b-1) := by
    dsimp [y]; conv_lhs => rw [show b=b-1+1 by omega,pow_succ]
    ring
  have hN : N a b d=x*y*t*t-1 := by
    have h := (source_numeric a b d).1
    dsimp [x,y,t]; convert h using 1 <;> ring
  have hcap : 2*(N a b d/2)=N a b d-1 := by
    have hodd : N a b d=2*((2:ℤ)^(a-1)*y*t*t)-1 := by rw [hN,hxhalf]; ring
    omega
  have hD : 0 ≤ N a b d := by
    have h := (chain_values a b d d (by omega) (by omega) hd hd).1 0
    change 0 ≤ sourceMod a b d d
    omega
  have gates := large_checks u v t (by dsimp [u]; exact one_le_pow₀ (by norm_num : (1:ℤ) ≤ 2)) (by dsimp [v]; exact one_le_pow₀ (by norm_num : (1:ℤ) ≤ 2)) ht
  dsimp only at gates
  let P := largeP a b d
  let Q := largeQ a b d
  let R := largeR a b d
  let G := largeG a b d
  let n0 := k-1
  let n1 := d-1
  let n2 := 2*d-1
  let n3 := 2*d+b-1
  let bs : List (List ℕ × ℕ) := [(P.toList,n0),(Q.toList,n1),(R.toList,n2),(G.toList,n3)]
  let bsn : List (List ℕ × ℕ) := [(P.toList++[k],n0),(Q.toList,n1),(R.toList,n2),(G.toList,n3)]
  let pre := P.toList
  let post := n0::Q.toList++n1::R.toList++n2::G.toList++[n3]
  have tab := source a b d hd hdb hba
  have hear : g a b d k=A := tab.2.2.2.2
  have mf := large_mass a b d hd hb ha (f a b d) (A) (B) (L) (M)
    (fun i hi => by
      have h := (tab.2.2.1 0 i (by dsimp [length]; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t] using h)
    (fun i hi => by
      have h := (tab.2.2.1 1 i (by dsimp [length]; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t] using h)
    (fun i hi => by
      have h := (tab.2.2.1 2 i (by dsimp [length]; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t] using h)
    (fun i hi => by
      have h := (tab.2.2.1 3 i (by dsimp [length]; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t] using h)
  have mg := large_mass a b d hd hb ha (g a b d) (2*A) (Bn) (Ln) (Mn)
    (fun i hi => by
      have h := (tab.2.2.1 0 i (by dsimp [length]; omega)).2
      simpa [start,newHeads,A,B,L,M,Bn,Ln,Mn,x,y,t] using h)
    (fun i hi => by
      have h := (tab.2.2.1 1 i (by dsimp [length]; omega)).2
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t] using h)
    (fun i hi => by
      have h := (tab.2.2.1 2 i (by dsimp [length]; omega)).2
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t] using h)
    (fun i hi => by
      have h := (tab.2.2.1 3 i (by dsimp [length]; omega)).2
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t] using h)
  simp only [←toList_sum] at mf mg
  have f0 : 2*(P.toList.map (f a b d)).sum=(x-14*m)*M := by
    rw [hxhalf]; dsimp [P,m,u]; nlinarith only [mf.1]
  have f1 : 2*(Q.toList.map (f a b d)).sum=(t-2)*A+4*m*M := by
    rw [hthalf]; dsimp [Q,m,u]; nlinarith only [mf.2.1]
  have f2 : 2*(R.toList.map (f a b d)).sum=(t-2)*B+(10*m-2*u)*M := by
    rw [hthalf]; dsimp [R,m,u]; nlinarith only [mf.2.2.1]
  have f3 : 2*(G.toList.map (f a b d)).sum=(y-2)*L+(2*u-2)*M := by
    rw [hyhalf]; dsimp [G,m,u]; nlinarith only [mf.2.2.2]
  have g0 : 2*(P.toList.map (g a b d)).sum=(x-14*m)*Mn := by
    rw [hxhalf]; dsimp [P,m,u]; nlinarith only [mg.1]
  have g1 : 2*(Q.toList.map (g a b d)).sum=(t-2)*(2*A)+4*m*Mn := by
    rw [hthalf]; dsimp [Q,m,u]; nlinarith only [mg.2.1]
  have g2 : 2*(R.toList.map (g a b d)).sum=(t-2)*Bn+(10*m-2*u)*Mn := by
    rw [hthalf]; dsimp [R,m,u]; nlinarith only [mg.2.2.1]
  have g3 : 2*(G.toList.map (g a b d)).sum=(y-2)*Ln+(2*u-2)*Mn := by
    rw [hyhalf]; dsimp [G,m,u]; nlinarith only [mg.2.2.2]
  have nt0 := tab.2.2.2.1 3
  have e0 : start b d 3+length a b d 3-1=n0 := by
    dsimp [start,length,n0,k,rank]; omega
  rw [e0] at nt0
  change 2*f a b d n0=A-N a b d ∧ 2*g a b d n0=A-(2*N a b d+1) at nt0
  have nt1 := tab.2.2.2.1 0
  have e1 : start b d 0+length a b d 0-1=n1 := by
    dsimp [start,length,n1,k,rank]; omega
  rw [e1] at nt1
  change 2*f a b d n1=B-N a b d ∧ 2*g a b d n1=Bn-(2*N a b d+1) at nt1
  have nt2 := tab.2.2.2.1 1
  have e2 : start b d 1+length a b d 1-1=n2 := by
    dsimp [start,length,n2,k,rank]; omega
  rw [e2] at nt2
  change 2*f a b d n2=L-N a b d ∧ 2*g a b d n2=Ln-(2*N a b d+1) at nt2
  have nt3 := tab.2.2.2.1 2
  have e3 : start b d 2+length a b d 2-1=n3 := by
    dsimp [start,length,n3,k,rank] <;> omega
  rw [e3] at nt3
  change 2*f a b d n3=M-N a b d ∧ 2*g a b d n3=Mn-(2*N a b d+1) at nt3
  have posP : ∀ i ∈ P.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [P,largeP,largeQ,largeR,largeG,bankLarge,shift,image_Ico,image_range,rank,negatives,size] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have posQ : ∀ i ∈ Q.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [Q,largeP,largeQ,largeR,largeG,bankLarge,shift,image_Ico,image_range,rank,negatives,size] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have posR : ∀ i ∈ R.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [R,largeP,largeQ,largeR,largeG,bankLarge,shift,image_Ico,image_range,rank,negatives,size] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have posG : ∀ i ∈ G.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [G,largeP,largeQ,largeR,largeG,bankLarge,shift,image_Ico,image_range,rank,negatives,size] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have neg0 : f a b d n0 ≤ 0 ∧ g a b d n0 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n0,k,rank]; omega
    · simp [n0,k,rank,negatives,size] <;> omega
  have neg1 : f a b d n1 ≤ 0 ∧ g a b d n1 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n1,k,rank]; omega
    · simp [n1,k,rank,negatives,size] <;> omega
  have neg2 : f a b d n2 ≤ 0 ∧ g a b d n2 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n2,k,rank]; omega
    · simp [n2,k,rank,negatives,size]; omega
  have neg3 : f a b d n3 ≤ 0 ∧ g a b d n3 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n3,k,rank]; omega
    · simp [n3,k,rank,negatives,size]; omega
  have posear : ∀ i ∈ P.toList++[k], 0 ≤ g a b d i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact (posP i hi).2
    · rw [List.mem_singleton.mp hi,hear]; exact (tab.1 0).le
  have hperm : (blocksWord bs).Perm (List.range k) := by
    have h := large_partition a b d hd hb ha
    simpa [bs,blocksWord,P,Q,R,G,n0,n1,n2,n3,k,rank] using h
  have hcut : pre.length=d := by
    have hdis : Disjoint ({a-d-3}:Finset ℕ) (Finset.Ico (a-d) (a-1)) := by
      simp [Finset.disjoint_left]; omega
    simp only [pre,P,largeP,bankLarge,Matrix.cons_val_zero,shift,Finset.length_toList]
    rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)]
    rw [Finset.card_union_of_disjoint hdis,Finset.card_singleton,Nat.card_Ico]
    omega
  apply physical_plan a b d hd hdb hba bs bsn (d) pre post hcut
  · simp [bs,pre,post,blocksWord,List.append_assoc]
  · simp [bsn,pre,post,blocksWord,k,List.append_assoc,List.cons_append]
  · exact hperm
  · omega
  · exact hD
  · intro Z hZ i hi
    simp only [bs,List.mem_cons,List.mem_nil_iff,or_false] at hZ
    rcases hZ with rfl|rfl|rfl|rfl
    · exact (posP i hi).1
    · exact (posQ i hi).1
    · exact (posR i hi).1
    · exact (posG i hi).1
  · intro Z hZ i hi
    simp only [bsn,List.mem_cons,List.mem_nil_iff,or_false] at hZ
    rcases hZ with rfl|rfl|rfl|rfl
    · exact posear i hi
    · exact (posQ i hi).2
    · exact (posR i hi).2
    · exact (posG i hi).2
  · intro Z hZ
    simp only [bs,List.mem_cons,List.mem_nil_iff,or_false] at hZ
    rcases hZ with rfl|rfl|rfl|rfl
    · exact neg0.1
    · exact neg1.1
    · exact neg2.1
    · exact neg3.1
  · intro Z hZ
    simp only [bsn,List.mem_cons,List.mem_nil_iff,or_false] at hZ
    rcases hZ with rfl|rfl|rfl|rfl
    · exact neg0.2
    · exact neg1.2
    · exact neg2.2
    · exact neg3.2
  · rw [hcap]
    simpa only [bs,List.map_cons,List.map_nil,f0,f1,f2,f3,nt0.1,nt1.1,nt2.1,nt3.1,A,B,L,M,Bn,Ln,Mn,hN,hx,hy,hm] using gates.1
  · simpa only [bsn,List.map_cons,List.map_nil,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,hear,mul_add,g0,g1,g2,g3,nt0.2,nt1.2,nt2.2,nt3.2,A,B,L,M,Bn,Ln,Mn,hN,hx,hy,hm] using gates.2

end D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo
