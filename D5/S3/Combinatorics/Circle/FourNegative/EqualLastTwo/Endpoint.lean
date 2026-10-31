/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualLastTwo/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/EqualLastTwo/Endpoint
   mirror-E: none(waiver:physical-dependent-source-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complete physical joint insertion for every equal-last-two source. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo.Construction
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

open private large_partition adjacent_partition corner_two_partition corner_three_partition
  positive_label negative_label physical_plan large_plan
  from D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo.Construction

-- The physical partition and both source rows are checked together.
set_option maxHeartbeats 2400000 in
private theorem adjacent_plan (a d : ℕ) (hd : 2 ≤ d) (ha : d+4 ≤ a) :
    ∃ sigma : List (Fin (rank (a) (d+1) d)), d ≤ rank (a) (d+1) d ∧
      OriginalOrder (rank (a) (d+1) d) (amplitude (a) (d+1) d) sigma ∧
      OriginalOrder (rank (a) (d+1) d+1) (2*amplitude (a) (d+1) d)
        (earWord (rank (a) (d+1) d) sigma (d)) := by
  classical
  let b := d+1
  have hdb : d < b := by dsimp [b]; omega
  have hba : b < a := by dsimp [b]; omega
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
  let m : ℤ := 2^(a-d-4)
  have hx : x=16*t*m := by
    dsimp [x,t,m]
    calc
      (2:ℤ)^a=2^(d+(a-d-4)+4) := by congr 1; omega
      _ = _ := by simp only [pow_add]; norm_num; ring
  have hy : y=2*t := by dsimp [y,b,t]; rw [pow_succ]; ring
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
  have gates := adjacent_checks m t (by dsimp [m]; exact one_le_pow₀ (by norm_num : (1:ℤ) ≤ 2)) ht
  dsimp only at gates
  let P := adjacentP a d
  let Q := adjacentQ a d
  let R := adjacentR a d
  let G := adjacentG a d
  let n0 := k-1
  let n1 := d-1
  let n2 := 2*d-1
  let n3 := 3*d
  let bs : List (List ℕ × ℕ) := [(P.toList,n0),(Q.toList,n1),(R.toList,n2),(G.toList,n3)]
  let bsn : List (List ℕ × ℕ) := [(P.toList++[k],n0),(Q.toList,n1),(R.toList,n2),(G.toList,n3)]
  let pre := P.toList
  let post := n0::Q.toList++n1::R.toList++n2::G.toList++[n3]
  have tab := source a b d hd hdb hba
  have hear : g a b d k=A := tab.2.2.2.2
  have mf := adjacent_mass a d hd ha (f a b d) (A) (B) (L) (M)
    (fun i hi => by
      have h := (tab.2.2.1 0 i (by dsimp [length]; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 1 i (by dsimp [length]; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 2 i (by dsimp [length]; dsimp [b] at *; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 3 i (by dsimp [length]; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,show 2*d+(d+1)=3*d+1 by omega] using h)
  have mg := adjacent_mass a d hd ha (g a b d) (2*A) (Bn) (Ln) (Mn)
    (fun i hi => by
      have h := (tab.2.2.1 0 i (by dsimp [length]; omega)).2
      simpa [start,newHeads,A,B,L,M,Bn,Ln,Mn,x,y,t,b,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 1 i (by dsimp [length]; omega)).2
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 2 i (by dsimp [length]; dsimp [b] at *; omega)).2
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 3 i (by dsimp [length]; omega)).2
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,show 2*d+(d+1)=3*d+1 by omega] using h)
  simp only [←toList_sum] at mf mg
  have f0 : 2*(P.toList.map (f a b d)).sum=(x-30*m)*M := by
    rw [hxhalf]; dsimp [P,m]; nlinarith only [mf.1]
  have f1 : 2*(Q.toList.map (f a b d)).sum=(t-2)*A+4*m*M := by
    rw [hthalf]; dsimp [Q,m]; nlinarith only [mf.2.1]
  have f2 : 2*(R.toList.map (f a b d)).sum=(t-2)*B+16*m*M := by
    rw [hthalf]; dsimp [R,m]; nlinarith only [mf.2.2.1]
  have f3 : 2*(G.toList.map (f a b d)).sum=(2*t-2)*L+(10*m-2)*M := by
    rw [←hy]; rw [hyhalf]; dsimp [G,m,b] at *; nlinarith only [mf.2.2.2]
  have g0 : 2*(P.toList.map (g a b d)).sum=(x-30*m)*Mn := by
    rw [hxhalf]; dsimp [P,m]; nlinarith only [mg.1]
  have g1 : 2*(Q.toList.map (g a b d)).sum=(t-2)*(2*A)+4*m*Mn := by
    rw [hthalf]; dsimp [Q,m]; nlinarith only [mg.2.1]
  have g2 : 2*(R.toList.map (g a b d)).sum=(t-2)*Bn+16*m*Mn := by
    rw [hthalf]; dsimp [R,m]; nlinarith only [mg.2.2.1]
  have g3 : 2*(G.toList.map (g a b d)).sum=(2*t-2)*Ln+(10*m-2)*Mn := by
    rw [←hy]; rw [hyhalf]; dsimp [G,m,b] at *; nlinarith only [mg.2.2.2]
  have nt0 := tab.2.2.2.1 3
  have e0 : start b d 3+length a b d 3-1=n0 := by
    dsimp [start,length,n0,k,rank,b]; omega
  rw [e0] at nt0
  change 2*f a b d n0=A-N a b d ∧ 2*g a b d n0=A-(2*N a b d+1) at nt0
  have nt1 := tab.2.2.2.1 0
  have e1 : start b d 0+length a b d 0-1=n1 := by
    dsimp [start,length,n1,k,rank,b]; omega
  rw [e1] at nt1
  change 2*f a b d n1=B-N a b d ∧ 2*g a b d n1=Bn-(2*N a b d+1) at nt1
  have nt2 := tab.2.2.2.1 1
  have e2 : start b d 1+length a b d 1-1=n2 := by
    dsimp [start,length,n2,k,rank,b]; omega
  rw [e2] at nt2
  change 2*f a b d n2=L-N a b d ∧ 2*g a b d n2=Ln-(2*N a b d+1) at nt2
  have nt3 := tab.2.2.2.1 2
  have e3 : start b d 2+length a b d 2-1=n3 := by
    dsimp [start,length,n3,k,rank,b]; omega
  rw [e3] at nt3
  change 2*f a b d n3=M-N a b d ∧ 2*g a b d n3=Mn-(2*N a b d+1) at nt3
  have posP : ∀ i ∈ P.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [P,adjacentP,adjacentQ,adjacentR,adjacentG,bankAdjacent,shift,image_Ico,image_range,rank,negatives,size,b] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have posQ : ∀ i ∈ Q.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [Q,adjacentP,adjacentQ,adjacentR,adjacentG,bankAdjacent,shift,image_Ico,image_range,rank,negatives,size,b] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have posR : ∀ i ∈ R.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [R,adjacentP,adjacentQ,adjacentR,adjacentG,bankAdjacent,shift,image_Ico,image_range,rank,negatives,size,b] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have posG : ∀ i ∈ G.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [G,adjacentP,adjacentQ,adjacentR,adjacentG,bankAdjacent,shift,image_Ico,image_range,rank,negatives,size,b] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have neg0 : f a b d n0 ≤ 0 ∧ g a b d n0 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n0,k,rank,b]; omega
    · simp [n0,k,rank,negatives,size,b] <;> omega
  have neg1 : f a b d n1 ≤ 0 ∧ g a b d n1 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n1,k,rank,b]; omega
    · simp [n1,k,rank,negatives,size,b] <;> omega
  have neg2 : f a b d n2 ≤ 0 ∧ g a b d n2 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n2,k,rank,b]; omega
    · simp [n2,k,rank,negatives,size,b]; omega
  have neg3 : f a b d n3 ≤ 0 ∧ g a b d n3 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n3,k,rank,b]; omega
    · simp [n3,k,rank,negatives,size,b]; omega
  have posear : ∀ i ∈ P.toList++[k], 0 ≤ g a b d i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact (posP i hi).2
    · rw [List.mem_singleton.mp hi,hear]; exact (tab.1 0).le
  have hperm : (blocksWord bs).Perm (List.range k) := by
    have h := adjacent_partition a d hd ha
    simpa [bs,blocksWord,P,Q,R,G,n0,n1,n2,n3,k,rank,b] using h
  have hcut : pre.length=d := by
    have hdis : Disjoint ({a-d-4}:Finset ℕ) (Finset.Ico (a-d) (a-1)) := by
      simp [Finset.disjoint_left]; omega
    simp only [pre,P,adjacentP,bankAdjacent,Matrix.cons_val_zero,shift,Finset.length_toList]
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
    simpa only [bs,List.map_cons,List.map_nil,f0,f1,f2,f3,nt0.1,nt1.1,nt2.1,nt3.1,A,B,L,M,Bn,Ln,Mn,hN,hx,hy] using gates.1
  · simpa only [bsn,List.map_cons,List.map_nil,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,hear,mul_add,g0,g1,g2,g3,nt0.2,nt1.2,nt2.2,nt3.2,A,B,L,M,Bn,Ln,Mn,hN,hx,hy] using gates.2

-- The physical partition and both source rows are checked together.
set_option maxHeartbeats 2400000 in
private theorem corner_two_plan (d : ℕ) (hd : 2 ≤ d) :
    ∃ sigma : List (Fin (rank (d+2) (d+1) d)), 3*d+1 ≤ rank (d+2) (d+1) d ∧
      OriginalOrder (rank (d+2) (d+1) d) (amplitude (d+2) (d+1) d) sigma ∧
      OriginalOrder (rank (d+2) (d+1) d+1) (2*amplitude (d+2) (d+1) d)
        (earWord (rank (d+2) (d+1) d) sigma (3*d+1)) := by
  classical
  let a := d+2
  let b := d+1
  have hdb : d < b := by dsimp [b]; omega
  have hba : b < a := by dsimp [a,b]; omega
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
  have hx : x=4*t := by dsimp [x,a,t]; rw [pow_add]; norm_num; ring
  have hy : y=2*t := by dsimp [y,b,t]; rw [pow_succ]; ring
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
  have gates := corner_two_checks t ht
  dsimp only at gates
  let P := corner2P d
  let Q := corner2Q d
  let R := corner2R d
  let G := corner2G d
  let n0 := d-1
  let n1 := 2*d-1
  let n2 := k-1
  let n3 := 3*d
  let bs : List (List ℕ × ℕ) := [(P.toList,n0),(Q.toList,n1),(R.toList,n2),(G.toList,n3)]
  let bsn : List (List ℕ × ℕ) := [(P.toList,n0),(Q.toList,n1),(R.toList++[k],n2),(G.toList,n3)]
  let pre := P.toList++n0::Q.toList++n1::R.toList
  let post := n2::G.toList++[n3]
  have tab := source a b d hd hdb hba
  have hear : g a b d k=A := tab.2.2.2.2
  have mf := corner_two_mass d hd (f a b d) (A) (B) (L) (M)
    (fun i hi => by
      have h := (tab.2.2.1 0 i (by dsimp [length]; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 1 i (by dsimp [length]; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 2 i (by dsimp [length]; dsimp [b] at *; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 3 i (by dsimp [length]; dsimp [a] at *; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
  have mg := corner_two_mass d hd (g a b d) (2*A) (Bn) (Ln) (Mn)
    (fun i hi => by
      have h := (tab.2.2.1 0 i (by dsimp [length]; omega)).2
      simpa [start,newHeads,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 1 i (by dsimp [length]; omega)).2
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 2 i (by dsimp [length]; dsimp [b] at *; omega)).2
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 3 i (by dsimp [length]; dsimp [a] at *; omega)).2
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
  simp only [←toList_sum] at mf mg
  have f0 : 2*(P.toList.map (f a b d)).sum=(t-2)*A+2*M := by
    have hmass := mf.1
    change (P.toList.map (f a b d)).sum = _ at hmass
    rw [hmass]
    rw [hthalf]
    ring
  have f1 : 2*(Q.toList.map (f a b d)).sum=(t-2)*B+4*M := by
    have hmass := mf.2.1
    change (Q.toList.map (f a b d)).sum = _ at hmass
    rw [hmass]
    rw [hthalf]
    ring
  have f2 : 2*(R.toList.map (f a b d)).sum=(4*t-8)*M := by
    have hmass := mf.2.2.1
    change (R.toList.map (f a b d)).sum = _ at hmass
    rw [hmass]
    dsimp only [t]
    simp only [pow_add,pow_one]
    ring
  have f3 : 2*(G.toList.map (f a b d)).sum=(2*t-2)*L := by
    have hmass := mf.2.2.2
    change (G.toList.map (f a b d)).sum = _ at hmass
    rw [hmass]
    dsimp only [t]
    ring
  have g0 : 2*(P.toList.map (g a b d)).sum=(t-2)*(2*A)+2*Mn := by
    have hmass := mg.1
    change (P.toList.map (g a b d)).sum = _ at hmass
    rw [hmass]
    rw [hthalf]
    ring
  have g1 : 2*(Q.toList.map (g a b d)).sum=(t-2)*Bn+4*Mn := by
    have hmass := mg.2.1
    change (Q.toList.map (g a b d)).sum = _ at hmass
    rw [hmass]
    rw [hthalf]
    ring
  have g2 : 2*(R.toList.map (g a b d)).sum=(4*t-8)*Mn := by
    have hmass := mg.2.2.1
    change (R.toList.map (g a b d)).sum = _ at hmass
    rw [hmass]
    dsimp only [t]
    simp only [pow_add,pow_one]
    ring
  have g3 : 2*(G.toList.map (g a b d)).sum=(2*t-2)*Ln := by
    have hmass := mg.2.2.2
    change (G.toList.map (g a b d)).sum = _ at hmass
    rw [hmass]
    dsimp only [t]
    ring
  have nt0 := tab.2.2.2.1 0
  have e0 : start b d 0+length a b d 0-1=n0 := by
    dsimp [start,length,n0,k,rank,b,a]; omega
  rw [e0] at nt0
  change 2*f a b d n0=B-N a b d ∧ 2*g a b d n0=Bn-(2*N a b d+1) at nt0
  have nt1 := tab.2.2.2.1 1
  have e1 : start b d 1+length a b d 1-1=n1 := by
    dsimp [start,length,n1,k,rank,b,a]; omega
  rw [e1] at nt1
  change 2*f a b d n1=L-N a b d ∧ 2*g a b d n1=Ln-(2*N a b d+1) at nt1
  have nt2 := tab.2.2.2.1 3
  have e2 : start b d 3+length a b d 3-1=n2 := by
    dsimp [start,length,n2,k,rank,b,a]; omega
  rw [e2] at nt2
  change 2*f a b d n2=A-N a b d ∧ 2*g a b d n2=A-(2*N a b d+1) at nt2
  have nt3 := tab.2.2.2.1 2
  have e3 : start b d 2+length a b d 2-1=n3 := by
    dsimp [start,length,n3,k,rank,b,a]; omega
  rw [e3] at nt3
  change 2*f a b d n3=M-N a b d ∧ 2*g a b d n3=Mn-(2*N a b d+1) at nt3
  have posP : ∀ i ∈ P.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [P,corner2P,corner2Q,corner2R,corner2G,shift,image_Ico,image_range,rank,negatives,size,b,a] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have posQ : ∀ i ∈ Q.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [Q,corner2P,corner2Q,corner2R,corner2G,shift,image_Ico,image_range,rank,negatives,size,b,a] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have posR : ∀ i ∈ R.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [R,corner2P,corner2Q,corner2R,corner2G,shift,image_Ico,image_range,rank,negatives,size,b,a] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have posG : ∀ i ∈ G.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [G,corner2P,corner2Q,corner2R,corner2G,shift,image_Ico,image_range,rank,negatives,size,b,a] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have neg0 : f a b d n0 ≤ 0 ∧ g a b d n0 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n0,k,rank,b,a]; omega
    · simp [n0,k,rank,negatives,size,b,a] <;> omega
  have neg1 : f a b d n1 ≤ 0 ∧ g a b d n1 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n1,k,rank,b,a]; omega
    · simp [n1,k,rank,negatives,size,b,a]; omega
  have neg2 : f a b d n2 ≤ 0 ∧ g a b d n2 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n2,k,rank,b,a]; omega
    · simp [n2,k,rank,negatives,size,b,a] <;> omega
  have neg3 : f a b d n3 ≤ 0 ∧ g a b d n3 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n3,k,rank,b,a]; omega
    · simp [n3,k,rank,negatives,size,b,a]; omega
  have posear : ∀ i ∈ R.toList++[k], 0 ≤ g a b d i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact (posR i hi).2
    · rw [List.mem_singleton.mp hi,hear]; exact (tab.1 0).le
  have hperm : (blocksWord bs).Perm (List.range k) := by
    have h := corner_two_partition d hd
    have hkeq : k=4*d+3 := by dsimp [k,rank,a,b]; omega
    simpa only [bs,blocksWord,P,Q,R,G,n0,n1,n2,n3,hkeq,List.append_assoc,
      List.cons_append,List.nil_append,List.append_nil] using h
  have hcut : pre.length=3*d+1 := by
    have hdis : Disjoint (Finset.range (d-1)) ({3*d+1}:Finset ℕ) := by
      simp [Finset.disjoint_left]; omega
    have hdisQ : Disjoint (shift d (Finset.range (d-1))) ({3*d+2}:Finset ℕ) := by
      simp [Finset.disjoint_left,shift,image_range]; omega
    simp only [pre,P,Q,R,n0,n1,corner2P,corner2Q,corner2R,List.length_append,List.length_cons,Finset.length_toList]
    rw [Finset.card_union_of_disjoint hdis,Finset.card_union_of_disjoint hdisQ]
    dsimp only [shift]
    rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)]
    simp only [Finset.card_range,Finset.card_singleton,Nat.card_Ico]
    omega
  apply physical_plan a b d hd hdb hba bs bsn (3*d+1) pre post hcut
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
    · exact (posP i hi).2
    · exact (posQ i hi).2
    · exact posear i hi
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
    simpa only [bs,List.map_cons,List.map_nil,f0,f1,f2,f3,nt0.1,nt1.1,nt2.1,nt3.1,A,B,L,M,Bn,Ln,Mn,hN,hx,hy] using gates.1
  · simpa only [bsn,List.map_cons,List.map_nil,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,hear,mul_add,g0,g1,g2,g3,nt0.2,nt1.2,nt2.2,nt3.2,A,B,L,M,Bn,Ln,Mn,hN,hx,hy] using gates.2

-- The physical partition and both source rows are checked together.
set_option maxHeartbeats 2400000 in
private theorem corner_three_plan (d : ℕ) (hd : 2 ≤ d) :
    ∃ sigma : List (Fin (rank (d+3) (d+1) d)), d ≤ rank (d+3) (d+1) d ∧
      OriginalOrder (rank (d+3) (d+1) d) (amplitude (d+3) (d+1) d) sigma ∧
      OriginalOrder (rank (d+3) (d+1) d+1) (2*amplitude (d+3) (d+1) d)
        (earWord (rank (d+3) (d+1) d) sigma (d)) := by
  classical
  let a := d+3
  let b := d+1
  have hdb : d < b := by dsimp [b]; omega
  have hba : b < a := by dsimp [a,b]; omega
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
  have hx : x=8*t := by dsimp [x,a,t]; rw [pow_add]; norm_num; ring
  have hy : y=2*t := by dsimp [y,b,t]; rw [pow_succ]; ring
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
  have gates := corner_three_checks t ht
  dsimp only at gates
  let P := corner3P d
  let Q := corner3Q d
  let R := corner3R d
  let G := corner3G d
  let n0 := k-1
  let n1 := 2*d-1
  let n2 := d-1
  let n3 := 3*d
  let bs : List (List ℕ × ℕ) := [(P.toList,n0),(Q.toList,n1),(R.toList,n2),(G.toList,n3)]
  let bsn : List (List ℕ × ℕ) := [(P.toList++[k],n0),(Q.toList,n1),(R.toList,n2),(G.toList,n3)]
  let pre := P.toList
  let post := n0::Q.toList++n1::R.toList++n2::G.toList++[n3]
  have tab := source a b d hd hdb hba
  have hear : g a b d k=A := tab.2.2.2.2
  have mf := corner_three_mass d hd (f a b d) (A) (B) (L) (M)
    (fun i hi => by
      have h := (tab.2.2.1 0 i (by dsimp [length]; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 1 i (by dsimp [length]; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 2 i (by dsimp [length]; dsimp [b] at *; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 3 i (by dsimp [length]; dsimp [a] at *; omega)).1
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
  have mg := corner_three_mass d hd (g a b d) (2*A) (Bn) (Ln) (Mn)
    (fun i hi => by
      have h := (tab.2.2.1 0 i (by dsimp [length]; omega)).2
      simpa [start,newHeads,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 1 i (by dsimp [length]; omega)).2
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 2 i (by dsimp [length]; dsimp [b] at *; omega)).2
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
    (fun i hi => by
      have h := (tab.2.2.1 3 i (by dsimp [length]; dsimp [a] at *; omega)).2
      simpa [start,A,B,L,M,Bn,Ln,Mn,x,y,t,b,a,show 2*d+(d+1)=3*d+1 by omega] using h)
  simp only [←toList_sum] at mf mg
  have f0 : 2*(P.toList.map (f a b d)).sum=(8*t-14)*M := by
    have hmass := mf.1
    change (P.toList.map (f a b d)).sum = _ at hmass
    rw [hmass]
    dsimp only [t]
    simp only [pow_add,pow_one]
    ring
  have f1 : 2*(Q.toList.map (f a b d)).sum=(t-2)*B+8*M := by
    have hmass := mf.2.1
    change (Q.toList.map (f a b d)).sum = _ at hmass
    rw [hmass]
    rw [hthalf]
    ring
  have f2 : 2*(R.toList.map (f a b d)).sum=(t-2)*A+4*M := by
    have hmass := mf.2.2.1
    change (R.toList.map (f a b d)).sum = _ at hmass
    rw [hmass]
    rw [hthalf]
    ring
  have f3 : 2*(G.toList.map (f a b d)).sum=(2*t-2)*L := by
    have hmass := mf.2.2.2
    change (G.toList.map (f a b d)).sum = _ at hmass
    rw [hmass]
    dsimp only [t]
    ring
  have g0 : 2*(P.toList.map (g a b d)).sum=(8*t-14)*Mn := by
    have hmass := mg.1
    change (P.toList.map (g a b d)).sum = _ at hmass
    rw [hmass]
    dsimp only [t]
    simp only [pow_add,pow_one]
    ring
  have g1 : 2*(Q.toList.map (g a b d)).sum=(t-2)*Bn+8*Mn := by
    have hmass := mg.2.1
    change (Q.toList.map (g a b d)).sum = _ at hmass
    rw [hmass]
    rw [hthalf]
    ring
  have g2 : 2*(R.toList.map (g a b d)).sum=(t-2)*(2*A)+4*Mn := by
    have hmass := mg.2.2.1
    change (R.toList.map (g a b d)).sum = _ at hmass
    rw [hmass]
    rw [hthalf]
    ring
  have g3 : 2*(G.toList.map (g a b d)).sum=(2*t-2)*Ln := by
    have hmass := mg.2.2.2
    change (G.toList.map (g a b d)).sum = _ at hmass
    rw [hmass]
    dsimp only [t]
    ring
  have nt0 := tab.2.2.2.1 3
  have e0 : start b d 3+length a b d 3-1=n0 := by
    dsimp [start,length,n0,k,rank,b,a]; omega
  rw [e0] at nt0
  change 2*f a b d n0=A-N a b d ∧ 2*g a b d n0=A-(2*N a b d+1) at nt0
  have nt1 := tab.2.2.2.1 1
  have e1 : start b d 1+length a b d 1-1=n1 := by
    dsimp [start,length,n1,k,rank,b,a]; omega
  rw [e1] at nt1
  change 2*f a b d n1=L-N a b d ∧ 2*g a b d n1=Ln-(2*N a b d+1) at nt1
  have nt2 := tab.2.2.2.1 0
  have e2 : start b d 0+length a b d 0-1=n2 := by
    dsimp [start,length,n2,k,rank,b,a]; omega
  rw [e2] at nt2
  change 2*f a b d n2=B-N a b d ∧ 2*g a b d n2=Bn-(2*N a b d+1) at nt2
  have nt3 := tab.2.2.2.1 2
  have e3 : start b d 2+length a b d 2-1=n3 := by
    dsimp [start,length,n3,k,rank,b,a]; omega
  rw [e3] at nt3
  change 2*f a b d n3=M-N a b d ∧ 2*g a b d n3=Mn-(2*N a b d+1) at nt3
  have posP : ∀ i ∈ P.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [P,corner3P,corner3Q,corner3R,corner3G,shift,image_Ico,image_range,rank,negatives,size,b,a] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have posQ : ∀ i ∈ Q.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [Q,corner3P,corner3Q,corner3R,corner3G,shift,image_Ico,image_range,rank,negatives,size,b,a] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have posR : ∀ i ∈ R.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [R,corner3P,corner3Q,corner3R,corner3G,shift,image_Ico,image_range,rank,negatives,size,b,a] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have posG : ∀ i ∈ G.toList, 0 ≤ f a b d i ∧ 0 ≤ g a b d i := by
    intro i hi
    have hi := Finset.mem_toList.mp hi
    have good : i < rank a b d ∧ i ∉ negatives a b d d := by
      simp [G,corner3P,corner3Q,corner3R,corner3G,shift,image_Ico,image_range,rank,negatives,size,b,a] at hi ⊢
      omega
    exact positive_label a b d hd hdb hba i good.1 good.2
  have neg0 : f a b d n0 ≤ 0 ∧ g a b d n0 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n0,k,rank,b,a]; omega
    · simp [n0,k,rank,negatives,size,b,a] <;> omega
  have neg1 : f a b d n1 ≤ 0 ∧ g a b d n1 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n1,k,rank,b,a]; omega
    · simp [n1,k,rank,negatives,size,b,a]; omega
  have neg2 : f a b d n2 ≤ 0 ∧ g a b d n2 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n2,k,rank,b,a]; omega
    · simp [n2,k,rank,negatives,size,b,a] <;> omega
  have neg3 : f a b d n3 ≤ 0 ∧ g a b d n3 ≤ 0 := by
    apply negative_label a b d hd hdb hba
    · dsimp [n3,k,rank,b,a]; omega
    · simp [n3,k,rank,negatives,size,b,a]; omega
  have posear : ∀ i ∈ P.toList++[k], 0 ≤ g a b d i := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · exact (posP i hi).2
    · rw [List.mem_singleton.mp hi,hear]; exact (tab.1 0).le
  have hperm : (blocksWord bs).Perm (List.range k) := by
    have h := corner_three_partition d hd
    have hkeq : k=4*d+4 := by dsimp [k,rank,a,b]; omega
    simpa only [bs,blocksWord,P,Q,R,G,n0,n1,n2,n3,hkeq,List.append_assoc,
      List.cons_append,List.nil_append,List.append_nil] using h
  have hcut : pre.length=d := by
    have hdis : Disjoint ({3*d+1}:Finset ℕ) (Finset.Ico (3*d+4) (4*d+3)) := by
      simp [Finset.disjoint_left] <;> omega
    simp only [pre,P,corner3P,Matrix.cons_val_zero,shift,Finset.length_toList]
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
    simpa only [bs,List.map_cons,List.map_nil,f0,f1,f2,f3,nt0.1,nt1.1,nt2.1,nt3.1,A,B,L,M,Bn,Ln,Mn,hN,hx,hy] using gates.1
  · simpa only [bsn,List.map_cons,List.map_nil,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,hear,mul_add,g0,g1,g2,g3,nt0.2,nt1.2,nt2.2,nt3.2,A,B,L,M,Bn,Ln,Mn,hN,hx,hy] using gates.2

/-- One physical old permutation and its literal fresh-ear insertion for every
natural equal-last-two source. The adjacent offsets two and three remain unbounded. -/
theorem actualSource_equal_last_two_joint_lift (a b d : ℕ)
    (hd : 2 ≤ d) (hdb : d < b) (hba : b < a) :
    ∃ sigma : List (Fin (a+b+d+d)), ∃ cut : ℕ, cut ≤ a+b+d+d ∧
      OriginalOrder (a+b+d+d) (1+2^a+2^(a+b)+2^(a+b+d)) sigma ∧
      OriginalOrder (a+b+d+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+d)))
        (earWord (a+b+d+d) sigma cut) := by
  by_cases hb : d+2 ≤ b
  · obtain ⟨sigma,hcut,hold,hnew⟩ := large_plan a b d hd hb hba
    exact ⟨sigma,d,hcut,hold,hnew⟩
  · have hbd : b=d+1 := by omega
    subst b
    by_cases ha : d+4 ≤ a
    · obtain ⟨sigma,hcut,hold,hnew⟩ := adjacent_plan a d hd ha
      exact ⟨sigma,d,hcut,hold,hnew⟩
    · have ha23 : a=d+2 ∨ a=d+3 := by omega
      rcases ha23 with rfl|rfl
      · obtain ⟨sigma,hcut,hold,hnew⟩ := corner_two_plan d hd
        exact ⟨sigma,3*d+1,hcut,hold,hnew⟩
      · obtain ⟨sigma,hcut,hold,hnew⟩ := corner_three_plan d hd
        exact ⟨sigma,d,hcut,hold,hnew⟩

#print axioms actualSource_equal_last_two_joint_lift

end D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo
