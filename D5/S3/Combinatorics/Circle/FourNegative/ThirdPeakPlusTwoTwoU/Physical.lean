/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPlusTwoTwoU/Physical
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Simultaneous scalar strip bounds on the original physical inventory. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU.Selection
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU.Banks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU
open SourceWidth
open private A B L K SU SV SW oldFirst oldSecond newFirst newSecond D window firstTwo
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU.Arithmetic
open private original_select from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU.Selection
open private full banks terminals pre post word marked banks_inventory banks_good banks_masses
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU.Banks
open private size base newBase charge sourceMod oldValue newValue negatives chainLength chainStart
  nextBase nextNewBase chain_values source_signs
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private packetChecks withEar strip_iff_packetChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private native_masses from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

private def rowBase (a b c d : ℕ) (side : Bool) : Fin 4→ℤ :=
  if side then newBase a b c d else base a b c d
private def rowHeads (a b c d : ℕ) (side : Bool) : Fin 4→ℤ :=
  let F:=rowBase a b c d side
  ![F 3,F 2,base a b c d 0,F 1]
private def rowSeams (a b c d : ℕ) (side : Bool) (u v : ℕ) : Fin 4→ℤ :=
  let F:=rowBase a b c d side
  let AA:=base a b c d 0
  ![F 1+F 3-2*(1+(u:ℤ))*F 0,
    F 1+F 2-F 3-2*(1+(u:ℤ))*F 0+AA,
    (2*(v:ℤ)+1)*F 1-F 2-2*(u:ℤ)*F 0,0]

private theorem selected_windows (a b d : ℕ) (hb : 2≤b) (hba : b<a)
    (hdom : a+3≤d ∨ b=2 ∧ d=a+2) :
    ∃ u v : ℕ, u<2^(d-1) ∧ v<2^((d+2)-1) ∧
      ∀ (side : Bool) (r : Fin 4),
        window (rowSeams a b (d+2) d side u v r) (rowHeads a b (d+2) d side r) := by
  obtain ⟨u,v,hu,hv,hf,ho,hn⟩ := original_select a b d hb hba hdom
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let t : ℤ := 2^d
  have hp : (2:ℤ)^(d+2)=4*(2:ℤ)^d := by rw [pow_add]; norm_num; ring
  have hbase : base a b (d+2) d=![A x y t,B x y t,L x y t,K x y t] := by
    funext r
    fin_cases r <;> dsimp [base,A,B,L,K,x,y,t] <;> (try simp only [hp]) <;> ring
  have hnew : newBase a b (d+2) d=![2*A x y t,SU x y t,SV x y t,SW x y t] := by
    funext r
    fin_cases r <;> dsimp [newBase,base,charge,SU,SV,SW,A,B,L,K,x,y,t] <;>
      (try simp only [hp]) <;> ring
  have oldRows : rowSeams a b (d+2) d false u v=
      ![oldFirst x y t u,oldSecond x y t u,D x y t u v,0] := by
    funext r
    fin_cases r <;> simp [rowSeams,rowBase,hbase,oldFirst,oldSecond,D] <;> ring
  have newRows : rowSeams a b (d+2) d true u v=
      ![newFirst x y t u,newSecond x y t u,2*D x y t u v+4*t-2*v,0] := by
    funext r
    fin_cases r <;> simp [rowSeams,rowBase,hbase,hnew,newFirst,newSecond,D,SU,SV,SW] <;> ring
  have oldHeads : rowHeads a b (d+2) d false=![K x y t,L x y t,A x y t,B x y t] := by
    simp [rowHeads,rowBase,hbase]
  have newHeads : rowHeads a b (d+2) d true=![SW x y t,SV x y t,A x y t,SU x y t] := by
    simp [rowHeads,rowBase,hbase,hnew]
  have hB : 0<B x y t := by dsimp [B,x,y,t]; positivity
  have hSU : 0<SU x y t := by dsimp [SU]; omega
  refine ⟨u,v,hu,hv,?_⟩
  intro side r
  cases side <;> fin_cases r
  · simpa only [oldRows,oldHeads,Matrix.cons_val_zero,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ'] using hf.1
  · simpa only [oldRows,oldHeads,Matrix.cons_val_one,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ'] using hf.2.2.1
  · simpa only [oldRows,oldHeads,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ'] using ho
  · simpa only [oldRows,oldHeads,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ',window] using
      (show 0≤(0:ℤ) ∧ 0≤B x y t-1 by omega)
  · simpa only [newRows,newHeads,Matrix.cons_val_zero,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ'] using hf.2.1
  · simpa only [newRows,newHeads,Matrix.cons_val_one,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ'] using hf.2.2.2
  · simpa only [newRows,newHeads,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ'] using hn
  · simpa only [newRows,newHeads,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ',window] using
      (show 0≤(0:ℤ) ∧ 0≤SU x y t-1 by omega)

/- The eight doubled heights below are derived from the actual bank sums and
native terminal values. The scalar packet engine controls every internal prefix. -/
set_option maxHeartbeats 2400000 in
private theorem bank_strips (a b c d u v : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hu : u<2^(d-1)) (hv : v<2^(c-1))
    (hw : ∀ (side : Bool) (r : Fin 4),
      window (rowSeams a b c d side u v r) (rowHeads a b c d side r)) :
    InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (word a b c d u v) ∧
    InStrip (newValue a b c d) (sourceMod a b c d) 0 (marked a b c d u v) := by
  let P:=banks a b c d u v
  let T:=terminals a b c d
  let bs : List (List ℕ×ℕ):=[(P 0,T 0),(P 1,T 1),(P 2,T 2),(P 3,T 3)]
  have tab:=chain_values a b c d ha hb hc hd
  have hN : 0≤sourceMod a b c d := by have hh:=(tab.1 0); omega
  have fresh : newValue a b c d (size a b c d)=base a b c d 0 := tab.2.2.2
  have pos (side : Bool) (r : Fin 4) (i : ℕ) (hi : i∈P r) :
      0≤(if side then newValue a b c d else oldValue a b c d) i := by
    obtain ⟨hib,hin⟩ := banks_good a b c d ha hb hc hd u v r i hi
    have hh:=source_signs a b c d ha hb hc hd i hib
    rw [if_neg hin] at hh
    cases side
    · exact hh.1.le
    · exact hh.2.le
  have neg (side : Bool) (r : Fin 4) :
      (if side then newValue a b c d else oldValue a b c d) (T r)≤0 := by
    have hib : T r<size a b c d := by fin_cases r <;> dsimp [T,terminals,size] <;> omega
    have hin : T r∈negatives a b c d := by
      fin_cases r <;> simp [T,terminals,negatives,size] <;> omega
    have hh:=source_signs a b c d ha hb hc hd (T r) hib
    rw [if_pos hin] at hh
    cases side
    · exact hh.1.le
    · exact hh.2.le
  have row (side : Bool) :
      InStrip (if side then newValue a b c d else oldValue a b c d)
        (if side then sourceMod a b c d else sourceMod a b c d/2) 0
        (if side then marked a b c d u v else word a b c d u v) := by
    let F:=rowBase a b c d side
    let f:=if side then newValue a b c d else oldValue a b c d
    let N:=sourceMod a b c d
    let AA:=base a b c d 0
    let E:=if side then AA else 0
    let C:=if side then N else N/2
    let bs':=if side then withEar (size a b c d) 2 bs else bs
    have hstart : F 0=AA+E := by
      cases side <;> dsimp [F,rowBase,E,AA,newBase,charge] <;> ring
    have hf (r : Fin 4) (i : ℕ) (hi : i<chainLength a b c d r-1) :
        f (chainStart b c d r+i)=2^i*F r := by
      cases side
      · exact (tab.2.1 r i (by omega)).trans (if_pos (by omega))
      · exact (tab.2.2.1 r i (by omega)).trans (if_pos (by omega))
    have masses:=banks_masses a b c d u v hu hv f F hf
    have mass0:=congrFun masses 0
    have mass1:=congrFun masses 1
    have mass2:=congrFun masses 2
    have mass3:=congrFun masses 3
    have native (r : Fin 4) :
        (full a b c d r:ℤ)*F r+f ((![T 3,T 1,T 0,T 2]:Fin 4→ℕ) r)=
          (![F 1,F 2,F 3,AA]:Fin 4→ℤ) r-F r ∧
        2*f ((![T 3,T 1,T 0,T 2]:Fin 4→ℕ) r)=
          (![F 1,F 2,F 3,AA]:Fin 4→ℤ) r-(if side then 2*N+1 else N) := by
      have nn:=native_masses a b c d ha hb hc hd r
      have hi : chainStart b c d r+(chainLength a b c d r-1)=
          (![T 3,T 1,T 0,T 2]:Fin 4→ℕ) r := by
        fin_cases r <;> dsimp [chainStart,chainLength,T,terminals] <;> omega
      dsimp only at nn
      rw [hi] at nn
      cases side <;> fin_cases r
      all_goals first
        | simpa [full,F,f,rowBase,nextBase,nextNewBase,AA,N] using
            And.intro nn.1 nn.2.2.1
        | simpa [full,F,f,rowBase,nextBase,nextNewBase,AA,N] using
            And.intro nn.2.1 nn.2.2.2
    have nn0:=(native 0).1
    have nn1:=(native 1).1
    have nn2:=(native 2).1
    have nn3:=(native 3).1
    have nt0:=(native 0).2
    have nt1:=(native 1).2
    have nt2:=(native 2).2
    have nt3:=(native 3).2
    have win (r : Fin 4) : 0≤rowSeams a b c d side u v r ∧
        rowSeams a b c d side u v r-2*f (T r)≤2*C := by
      have hh:=hw side r
      have ht : 2*f (T r)=rowHeads a b c d side r-(if side then 2*N+1 else N) := by
        fin_cases r
        · simpa [rowHeads,F] using nt2
        · simpa [rowHeads,F] using nt1
        · simpa [rowHeads,F] using nt3
        · simpa [rowHeads,F] using nt0
      unfold window at hh
      cases side <;> dsimp [C] <;> simp only [Bool.false_eq_true,ite_false,ite_true] at ht
      all_goals omega
    have win0:=win 0
    have win1:=win 1
    have win2:=win 2
    have win3:=win 3
    have hpos : ∀ b∈bs', ∀ i∈b.1, 0≤f i := by
      cases side
      · intro b hb' i hi
        simp only [bs',bs,ite_false,Bool.false_eq_true,List.mem_cons,List.mem_nil_iff,or_false] at hb'
        rcases hb' with rfl|rfl|rfl|rfl
        all_goals first
          | exact pos false 0 i hi | exact pos false 1 i hi
          | exact pos false 2 i hi | exact pos false 3 i hi
      · intro b hb' i hi
        simp only [bs',bs,ite_true,withEar,List.mem_cons,List.mem_nil_iff,or_false] at hb'
        rcases hb' with rfl|rfl|rfl|rfl
        · exact pos true 0 i hi
        · exact pos true 1 i hi
        · rcases List.mem_append.mp hi with hi|hi
          · exact pos true 2 i hi
          · have heq : i=size a b c d := by simpa using hi
            subst i
            change 0≤newValue a b c d (size a b c d)
            rw [fresh]
            have hh := (tab.1 0).1
            omega
        · exact pos true 3 i hi
    have hneg : ∀ b∈bs', f b.2≤0 := by
      cases side
      · intro b hb'
        simp only [bs',bs,ite_false,Bool.false_eq_true,List.mem_cons,List.mem_nil_iff,or_false] at hb'
        rcases hb' with rfl|rfl|rfl|rfl
        · exact neg false 0
        · exact neg false 1
        · exact neg false 2
        · exact neg false 3
      · intro b hb'
        simp only [bs',bs,ite_true,withEar,List.mem_cons,List.mem_nil_iff,or_false] at hb'
        rcases hb' with rfl|rfl|rfl|rfl
        · exact neg true 0
        · exact neg true 1
        · exact neg true 2
        · exact neg true 3
    have heword : blocksWord bs'=
        if side then marked a b c d u v else word a b c d u v := by
      cases side <;> simp [bs',bs,withEar,blocksWord,marked,word,pre,post,P,T,List.append_assoc]
    rw [←heword]
    apply (strip_iff_packetChecks f C 0 bs' ⟨by omega,by dsimp [C,N]; split_ifs <;> omega⟩ hpos hneg).mpr
    cases side <;>
      simp only [bs',bs,ite_true,ite_false,Bool.false_eq_true,withEar,packetChecks,
        List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,
        zero_add,f,fresh]
    all_goals simp only [rowSeams,rowHeads] at win0 win1 win2 win3
    all_goals
      dsimp only [F,AA,E,C,f,rowBase] at mass0 mass1 mass2 mass3 nn0 nn1 nn2 nn3 nt0 nt1 nt2 nt3 hstart win0 win1 win2 win3 ⊢
    all_goals simp only [ite_true,ite_false,Bool.false_eq_true,P,T,terminals,fresh,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ',
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] at mass0 mass1 mass2 mass3 nn0 nn1 nn2 nn3 nt0 nt1 nt2 nt3 hstart win0 win1 win2 win3 ⊢
    all_goals refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,True.intro⟩
    all_goals nlinarith only [mass0,mass1,mass2,mass3,nn0,nn1,nn2,nn3,
      nt0,nt1,nt2,nt3,hstart,win0.1,win0.2,win1.1,win1.2,win2.1,win2.2,win3.1,win3.2]
  exact ⟨row false,row true⟩

private theorem physical_word (a b d : ℕ) (hb : 2≤b) (hba : b<a)
    (hdom : a+3≤d ∨ b=2 ∧ d=a+2) :
    ∃ u v : ℕ,
      (word a b (d+2) d u v).Perm (List.range (size a b (d+2) d)) ∧
      InStrip (oldValue a b (d+2) d) (sourceMod a b (d+2) d/2) 0 (word a b (d+2) d u v) ∧
      InStrip (newValue a b (d+2) d) (sourceMod a b (d+2) d) 0 (marked a b (d+2) d u v) := by
  have hd : 2≤d := by rcases hdom with h|⟨_,h⟩ <;> omega
  obtain ⟨u,v,hu,hv,hw⟩ := selected_windows a b d hb hba hdom
  have hs := bank_strips a b (d+2) d u v (by omega) hb (by omega) hd hu hv hw
  exact ⟨u,v,banks_inventory a b (d+2) d (by omega) hb (by omega) hd u v,hs⟩

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU
