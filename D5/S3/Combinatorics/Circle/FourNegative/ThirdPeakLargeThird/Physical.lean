/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLargeThird/Physical
   generality: I
   mirror-B: none(waiver:private-consumed-physical-helper)
   mirror-E: none(waiver:private-consumed-physical-helper)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Actual scalar consumption of the three bank orders through canonical packet strips. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Banks

/-! ThirdPeakLargeThird: Physical. The unrestricted Circle objective remains open. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird
open SourceWidth
open private size base newBase sourceMod oldValue newValue chainLength chainStart
  nextBase nextNewBase chain_values source_signs negatives charge
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private native_masses from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private full terminals from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open private banks order packets word earSlot cut inventory banks_good bank_masses literal_ear cut_bound
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Banks
open private window from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird.Arithmetic
open private blocksWord insertAt from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private packetChecks withEar strip_iff_packetChecks from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private withEar_positive withEar_negatives from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Equivalence

private def rowBase (a b c d : ℕ) (side : Bool) : Fin 4→ℤ :=
  if side then newBase a b c d else base a b c d
private def rowHeads (a b c d : ℕ) (strict side : Bool) : Fin 4→ℤ :=
  let F:=rowBase a b c d side
  ![if strict then F 3 else F 2,if strict then F 2 else F 3,base a b c d 0,F 1]
private def rowDoubles (a b c d v p : ℕ) (strict early side : Bool) : Fin 4→ℤ :=
  let F:=rowBase a b c d side
  let AA:=base a b c d 0
  let ee:=if side then AA else 0
  ![if strict then F 1+F 3-2*F 0 else F 1+F 2-2*F 0,
    (if strict then F 1+F 2-F 3+AA-2*F 0 else F 1-F 2+2*F 3-2*F 0)+
      2*(p:ℤ)*F 1+(if early then 2*ee else 0),
    (2*(v:ℤ)+1)*F 1-F 2,0]

set_option maxHeartbeats 2400000 in
private theorem physical_source (a b c d v p : ℕ) (strict early : Bool)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hv : v<2^(c-1)) (hp : p<2^(c-1))
    (hsub : ∀ e<c-1,p.testBit e=true → v.testBit e=true)
    (windows : ∀ (side : Bool) (r : Fin 4),
      window (rowDoubles a b c d v p strict early side r) (rowHeads a b c d strict side r)) :
    (word a b c d v p strict).Perm (List.range (size a b c d)) ∧
    InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (word a b c d v p strict) ∧
    cut a b c d v p strict early<size a b c d ∧
    InStrip (newValue a b c d) (sourceMod a b c d) 0
      (insertAt (size a b c d) (word a b c d v p strict) (cut a b c d v p strict early)) := by
  let bs:=packets a b c d v p strict
  let P:=banks a b c d v p strict
  let T:=order a b c d strict
  have perm:=inventory a b c d v p strict ha hb hc hd hsub
  have tab:=chain_values a b c d ha hb hc hd
  have checks (side : Bool) :
      if side then packetChecks (newValue a b c d) (sourceMod a b c d) 0
        (withEar (size a b c d) (earSlot early) bs)
      else packetChecks (oldValue a b c d) (sourceMod a b c d/2) 0 bs := by
    let F:=rowBase a b c d side
    let f:=if side then newValue a b c d else oldValue a b c d
    let N:=sourceMod a b c d
    let AA:=base a b c d 0
    let ee:=if side then AA else 0
    let C:=if side then N else N/2
    let M:=fun r : Fin 4 => ((P r).map f).sum
    have hf (r : Fin 4) (e : ℕ) (he : e<chainLength a b c d r-1) :
        f (chainStart b c d r+e)=2^e*F r := by
      cases side
      · exact (tab.2.1 r e (by omega)).trans (if_pos (by omega))
      · exact (tab.2.2.1 r e (by omega)).trans (if_pos (by omega))
    have masses:=bank_masses a b c d v p strict hv hp hsub f F hf
    have m0:=congrFun masses 0
    have m1:=congrFun masses 1
    have m2:=congrFun masses 2
    have m3:=congrFun masses 3
    change M 0=_ at m0
    change M 1=_ at m1
    change M 2=_ at m2
    change M 3=_ at m3
    have start : F 0=AA+ee := by cases side <;> dsimp [F,rowBase,AA,ee,newBase,charge] <;> ring
    have native (r : Fin 4) :
        (full a b c d r:ℤ)*F r+f (terminals a b c d r)=
          (![F 1,F 2,F 3,AA] : Fin 4→ℤ) r-F r ∧
        2*f (terminals a b c d r)=
          (![F 1,F 2,F 3,AA] : Fin 4→ℤ) r-(if side then 2*N+1 else N) := by
      have nn:=native_masses a b c d ha hb hc hd r
      have hi : chainStart b c d r+(chainLength a b c d r-1)=terminals a b c d r := by
        fin_cases r <;> dsimp [chainStart,chainLength,terminals] <;> omega
      dsimp only at nn
      rw [hi] at nn
      cases side <;> fin_cases r
      all_goals first
        | simpa [full,F,f,rowBase,nextBase,nextNewBase,AA,N] using And.intro nn.1 nn.2.2.1
        | simpa [full,F,f,rowBase,nextBase,nextNewBase,AA,N] using And.intro nn.2.1 nn.2.2.2
    have n0:=native 0
    have n1:=native 1
    have n2:=native 2
    have n3:=native 3
    let e0:=M 0+f (T 0)
    let e1:=e0+M 1+(if early then ee else 0)+f (T 1)
    let e2:=e1+M 2+(if early then 0 else ee)+f (T 2)
    let e3:=e2+M 3+f (T 3)
    let endpoints : Fin 4→ℤ:=![e0,e1,e2,e3]
    have doubled (r : Fin 4) : 2*endpoints r=rowDoubles a b c d v p strict early side r := by
      cases strict <;> cases early <;> fin_cases r
      all_goals dsimp [endpoints,e0,e1,e2,e3,rowDoubles,T,order]
      all_goals simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
        Matrix.cons_val_zero',Matrix.cons_val_succ',Function.comp_apply] at m0 m1 m2 m3 n0 n1 n2 n3
      all_goals change rowBase a b c d side 0=AA+ee at start
      all_goals simp only [Bool.false_eq_true,ite_false,ite_true] at m0 m1 m2 m3
      all_goals dsimp only [F,ee,AA] at m0 m1 m2 m3 n0 n1 n2 n3 start ⊢
      all_goals nlinarith only [m0,m1,m2,m3,n0.1,n0.2,n1.1,n1.2,n2.1,n2.2,n3.1,n3.2,start]
    have terminal_double (r : Fin 4) :
        2*f (T r)=rowHeads a b c d strict side r-(if side then 2*N+1 else N) := by
      cases strict <;> fin_cases r
      all_goals first
        | simpa [T,order,rowHeads,F] using n0.2
        | simpa [T,order,rowHeads,F] using n1.2
        | simpa [T,order,rowHeads,F] using n2.2
        | simpa [T,order,rowHeads,F] using n3.2
    have win (r : Fin 4) : 0≤endpoints r ∧ endpoints r-f (T r)≤C := by
      have hw:=windows side r
      have hdbl:=doubled r
      have ht:=terminal_double r
      dsimp [window] at hw
      cases side <;> dsimp [C] <;> simp only [Bool.false_eq_true,ite_false,ite_true] at ht
      all_goals omega
    have w0:=win 0
    have w1:=win 1
    have w2:=win 2
    have w3:=win 3
    dsimp [endpoints,e0,e1,e2,e3] at w0 w1 w2 w3
    cases side <;> cases early
    all_goals simp only [Bool.false_eq_true,ite_false,ite_true] at w0 w1 w2 w3 ⊢
    all_goals dsimp [bs,packets,withEar,earSlot,packetChecks]
    all_goals try simp only [zero_add]
    all_goals change 0≤M 0+f (T 0) ∧ M 0≤C ∧ _
    all_goals refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,True.intro⟩
    all_goals dsimp [M,P,f,C,ee,AA] at w0 w1 w2 w3 ⊢
    all_goals try simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,tab.2.2.2]
    all_goals nlinarith only [w0.1,w0.2,w1.1,w1.2,w2.1,w2.2,w3.1,w3.2]
  have positive (side : Bool) : ∀ pkt∈bs,∀ i∈pkt.1,
      0≤(if side then newValue a b c d else oldValue a b c d) i := by
    intro pkt hpk i hi
    simp only [bs,packets,List.mem_cons,List.mem_nil_iff,or_false] at hpk
    rcases hpk with rfl|rfl|rfl|rfl
    all_goals
      have good : i<size a b c d ∧ i∉negatives a b c d := by
        first
        | exact banks_good a b c d v p strict ha hb hc hd 0 i hi
        | exact banks_good a b c d v p strict ha hb hc hd 1 i hi
        | exact banks_good a b c d v p strict ha hb hc hd 2 i hi
        | exact banks_good a b c d v p strict ha hb hc hd 3 i hi
      have hs:=source_signs a b c d ha hb hc hd i good.1
      rw [if_neg good.2] at hs
      cases side
      · exact hs.1.le
      · exact hs.2.le
  have negative (side : Bool) : ∀ pkt∈bs,
      (if side then newValue a b c d else oldValue a b c d) pkt.2≤0 := by
    intro pkt hpk
    have ht : pkt.2∈negatives a b c d := by
      have hm : pkt.2∈bs.map Prod.snd := List.mem_map.mpr ⟨pkt,hpk,rfl⟩
      cases strict <;> simpa [bs,packets,order,terminals,negatives,size,or_comm,or_left_comm,or_assoc] using hm
    have hbnd : pkt.2<size a b c d := by
      simp only [negatives,List.mem_cons,List.mem_nil_iff,or_false,size] at ht ⊢
      omega
    have hs:=source_signs a b c d ha hb hc hd pkt.2 hbnd
    rw [if_pos ht] at hs
    cases side
    · exact hs.1.le
    · exact hs.2.le
  have hN : 0≤sourceMod a b c d := by have hh:=tab.1 0;omega
  have oldstrip : InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (word a b c d v p strict) := by
    exact (strip_iff_packetChecks _ _ _ bs ⟨by omega,by omega⟩ (positive false) (negative false)).mpr (checks false)
  have fresh : 0≤newValue a b c d (size a b c d) := by rw [tab.2.2.2];have hh:=tab.1 0;omega
  have newstrip : InStrip (newValue a b c d) (sourceMod a b c d) 0
      (blocksWord (withEar (size a b c d) (earSlot early) bs)) := by
    apply (strip_iff_packetChecks _ _ _ _ ⟨by omega,hN⟩
      (withEar_positive _ _ _ bs fresh (positive true)) ?_).mpr (checks true)
    intro pkt hpk
    have ht : pkt.2∈bs.map Prod.snd := by
      rw [←withEar_negatives (size a b c d) (earSlot early) bs]
      exact List.mem_map.mpr ⟨pkt,hpk,rfl⟩
    obtain ⟨other,ho,he⟩:=List.mem_map.mp ht
    simpa [he] using negative true other ho
  exact ⟨perm,oldstrip,cut_bound a b c d v p strict early perm,
    by simpa only [bs,literal_ear] using newstrip⟩

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird
