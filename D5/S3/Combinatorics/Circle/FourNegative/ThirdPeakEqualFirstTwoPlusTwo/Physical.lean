/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualFirstTwoPlusTwo/Physical
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical inventory and both scalar strip orders from the unbounded integer allocation. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Banks
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Selection

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
open SourceWidth
open private A B L K SU SV SW H1 H2 J1 J2 D T window firstTwo windows
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Parameters
open private full stock complement terminals banks word banks_inventory banks_good banks_masses
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Banks
open private sourceMod base newBase charge nextBase nextNewBase oldValue newValue chain_values new_base_bounds source_signs source_totals from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size chainLength chainStart negatives)
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (blocksWord)
open private packetChecks withEar strip_iff_packetChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private withEar_positive withEar_negatives
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Equivalence

private def rowBase (a b c d : ℕ) (side : Bool) : Fin 4→ℤ :=
  if side then newBase a b c d else base a b c d
private def rowHeads (a b c d : ℕ) (side : Bool) : Fin 4→ℤ :=
  let F:=rowBase a b c d side
  ![F 2,F 3,base a b c d 0,F 1]
private def rowSeams (a b c d u v : ℕ) (side : Bool) : Fin 4→ℤ :=
  let F:=rowBase a b c d side
  ![F 1+F 2-2*(1+(u:ℤ))*F 0,
    F 1-F 2+2*F 3-2*(1+(u:ℤ))*F 0,
    (2*(v:ℤ)+1)*F 1-F 2-2*(u:ℤ)*F 0,0]
private def packets (a b c d u v : ℕ) : List (List ℕ×ℕ) :=
  let P:=banks a b c d u v
  let Z:=terminals a b c d
  [(P 0,Z 0),(P 1,Z 1),(P 2,Z 2),(P 3,Z 3)]

-- The packet masses are sums of actual centered source values at set-bit labels.
set_option maxHeartbeats 1600000 in
private theorem row_checks (a b c d u v : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hu : u<2^(d-1)) (hv : v<2^(c-1))
    (hw : ∀ side r, window (rowSeams a b c d u v side r) (rowHeads a b c d side r))
    (side : Bool) :
    packetChecks (if side then newValue a b c d else oldValue a b c d)
      (if side then sourceMod a b c d else sourceMod a b c d/2) 0
      (if side then withEar (size a b c d) 2 (packets a b c d u v)
       else packets a b c d u v) := by
  let P:=banks a b c d u v
  let Z:=terminals a b c d
  let F:=rowBase a b c d side
  let f:=if side then newValue a b c d else oldValue a b c d
  let N:=sourceMod a b c d
  let AA:=base a b c d 0
  let ear:=if side then AA else 0
  let C:=if side then N else N/2
  have tab:=chain_values a b c d ha hb hc hd
  have hf (r : Fin 4) (e : ℕ) (he : e<chainLength a b c d r-1) :
      f (chainStart b c d r+e)=2^e*F r := by
    cases side
    · exact (tab.2.1 r e (by omega)).trans (if_pos (by omega))
    · exact (tab.2.2.1 r e (by omega)).trans (if_pos (by omega))
  have mass:=banks_masses a b c d u v hu hv f F hf
  have mass0:=congrFun mass 0
  have mass1:=congrFun mass 1
  have mass2:=congrFun mass 2
  have mass3:=congrFun mass 3
  have hstart : F 0=AA+ear := by
    cases side <;> dsimp [F,rowBase,AA,ear,newBase,charge] <;> ring
  let raw : Fin 4→ℕ := ![d-1,d+c-1,d+c+b-1,a+b+c+d-1]
  have native (r : Fin 4) :
      (full a b c d r:ℤ)*F r+f (raw r)=
        (![F 1,F 2,F 3,AA] : Fin 4→ℤ) r-F r ∧
      2*f (raw r)=(![F 1,F 2,F 3,AA] : Fin 4→ℤ) r-
        (if side then 2*N+1 else N) := by
    have nn:=native_masses a b c d ha hb hc hd r
    have hi : chainStart b c d r+(chainLength a b c d r-1)=raw r := by
      fin_cases r <;> dsimp [raw,chainStart,chainLength] <;> omega
    dsimp only at nn
    rw [hi] at nn
    cases side <;> fin_cases r
    all_goals first
      | simpa [full,F,f,rowBase,nextBase,nextNewBase,raw,AA,N]
          using And.intro nn.1 nn.2.2.1
      | simpa [full,F,f,rowBase,nextBase,nextNewBase,raw,AA,N]
          using And.intro nn.2.1 nn.2.2.2
  have nn0:=native 0
  have nn1:=native 1
  have nn2:=native 2
  have nn3:=native 3
  have win (r : Fin 4) :
      0≤rowSeams a b c d u v side r ∧
      rowSeams a b c d u v side r-2*f (Z r)≤2*C := by
    have hh:=hw side r
    have hn : 2*f (Z r)=rowHeads a b c d side r-(if side then 2*N+1 else N) := by
      fin_cases r
      all_goals first
        | simpa [Z,terminals,rowHeads,F,raw] using (native 0).2
        | simpa [Z,terminals,rowHeads,F,raw] using (native 1).2
        | simpa [Z,terminals,rowHeads,F,raw] using (native 2).2
        | simpa [Z,terminals,rowHeads,F,raw] using (native 3).2
    unfold window at hh
    cases side <;> dsimp [C] <;>
      simp only [Bool.false_eq_true,ite_false,ite_true] at hn
    all_goals omega
  have win0:=win 0
  have win1:=win 1
  have win2:=win 2
  have win3:=win 3
  have fresh : newValue a b c d (size a b c d)=AA := (source_totals a b c d ha hb hc hd).2.2
  cases side <;>
    simp only [packets,withEar,packetChecks,ite_true,ite_false,Bool.false_eq_true,
      List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,fresh,zero_add]
  all_goals simp only [rowSeams,ite_true,ite_false,Bool.false_eq_true] at win0 win1 win2 win3
  all_goals dsimp only at mass0 mass1 mass2 mass3
  all_goals dsimp only [Z,terminals,raw] at nn0 nn1 nn2 nn3 win0 win1 win2 win3
  all_goals dsimp only [f,F,P,AA,ear,C,rowBase] at mass0 mass1 mass2 mass3 nn0 nn1 nn2 nn3 hstart win0 win1 win2 win3 ⊢
  all_goals simp only [ite_true,ite_false,Bool.false_eq_true,terminals,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ'] at mass0 mass1 mass2 mass3 nn0 nn1 nn2 nn3 hstart win0 win1 win2 win3 ⊢
  all_goals refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,True.intro⟩
  all_goals nlinarith only [mass0,mass1,mass2,mass3,nn0.1,nn0.2,nn1.1,nn1.2,
    nn2.1,nn2.2,nn3.1,nn3.2,hstart,win0.1,win0.2,win1.1,win1.2,win2.1,win2.2,win3.1,win3.2]

-- Both strips use positive physical banks and their actual negative terminals.
set_option maxHeartbeats 1600000 in
private theorem physical_strips (a b c d u v : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hu : u<2^(d-1)) (hv : v<2^(c-1))
    (hw : ∀ side r, window (rowSeams a b c d u v side r) (rowHeads a b c d side r)) :
    ∃ pre tail : List ℕ,
      (pre++(a+b+c+d-1)::tail).Perm (List.range (a+b+c+d)) ∧
      InStrip (oldValue a b c d) (sourceMod a b c d/2) 0
        (pre++(a+b+c+d-1)::tail) ∧
      InStrip (newValue a b c d) (sourceMod a b c d) 0
        (pre++(a+b+c+d)::(a+b+c+d-1)::tail) := by
  let P:=banks a b c d u v
  let Z:=terminals a b c d
  let bs:=packets a b c d u v
  have hN : 0≤sourceMod a b c d := by
    have h := (chain_values a b c d ha hb hc hd).1 0
    omega
  have positive (side : Bool) : ∀ pkt∈bs, ∀ i∈pkt.1,
      0≤(if side then newValue a b c d else oldValue a b c d) i := by
    intro pkt hmem i hi
    have good (r : Fin 4) (hi : i∈P r) :
        0≤oldValue a b c d i ∧ 0≤newValue a b c d i := by
      obtain ⟨hib,hin⟩:=banks_good a b c d ha hb hc hd u v r i hi
      have hh:=source_signs a b c d ha hb hc hd i hib
      rw [if_neg hin] at hh
      exact ⟨hh.1.le,hh.2.le⟩
    simp only [bs,packets,List.mem_cons,List.mem_nil_iff,or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals cases side
    all_goals first
      | exact (good 0 hi).1 | exact (good 0 hi).2
      | exact (good 1 hi).1 | exact (good 1 hi).2
      | exact (good 2 hi).1 | exact (good 2 hi).2
      | exact (good 3 hi).1 | exact (good 3 hi).2
  have negative (side : Bool) : ∀ pkt∈bs,
      (if side then newValue a b c d else oldValue a b c d) pkt.2≤0 := by
    have good (r : Fin 4) : oldValue a b c d (Z r)≤0 ∧ newValue a b c d (Z r)≤0 := by
      have hz : Z r<size a b c d ∧ Z r∈negatives a b c d := by
        fin_cases r <;> simp [Z,terminals,size,negatives] <;> omega
      have hh:=source_signs a b c d ha hb hc hd (Z r) hz.1
      rw [if_pos hz.2] at hh
      exact ⟨hh.1.le,hh.2.le⟩
    intro pkt hmem
    simp only [bs,packets,List.mem_cons,List.mem_nil_iff,or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl
    all_goals cases side
    all_goals first
      | exact (good 0).1 | exact (good 0).2
      | exact (good 1).1 | exact (good 1).2
      | exact (good 2).1 | exact (good 2).2
      | exact (good 3).1 | exact (good 3).2
  have earpos : 0≤newValue a b c d (size a b c d) := by
    rw [(source_totals a b c d ha hb hc hd).2.2]
    have hh:=(chain_values a b c d ha hb hc hd).1 0
    omega
  have markedpos:=withEar_positive (newValue a b c d) (size a b c d) 2 bs earpos (positive true)
  have markedneg : ∀ pkt∈withEar (size a b c d) 2 bs, newValue a b c d pkt.2≤0 := by
    intro pkt hmem
    have hn : pkt.2∈bs.map Prod.snd := by
      rw [←withEar_negatives (size a b c d) 2 bs]
      exact List.mem_map.mpr ⟨pkt,hmem,rfl⟩
    obtain ⟨pkt',hpkt',he⟩:=List.mem_map.mp hn
    simpa [he] using negative true pkt' hpkt'
  have ho:=(strip_iff_packetChecks (oldValue a b c d) (sourceMod a b c d/2) 0 bs
    ⟨by omega,by omega⟩ (positive false) (negative false)).mpr
      (row_checks a b c d u v ha hb hc hd hu hv hw false)
  have hn:=(strip_iff_packetChecks (newValue a b c d) (sourceMod a b c d) 0
    (withEar (size a b c d) 2 bs) ⟨by omega,hN⟩ markedpos markedneg).mpr
      (row_checks a b c d u v ha hb hc hd hu hv hw true)
  let pre:=P 0++[Z 0]++P 1++[Z 1]++P 2
  let tail:=P 3++[Z 3]
  refine ⟨pre,tail,?_,?_,?_⟩
  · simpa [pre,tail,P,Z,word,terminals,List.append_assoc] using banks_inventory a b c d ha hb hc hd u v
  · simpa [pre,tail,bs,packets,blocksWord,P,Z,terminals,List.append_assoc] using ho
  · simpa [pre,tail,bs,packets,blocksWord,withEar,P,Z,terminals,size,List.append_assoc] using hn

private theorem physical_order (a d u v : ℕ) (ha : 2≤a) (had : a+2≤d)
    (hu : u<2^(d-1)) (hv : v<2^(d+1))
    (hw : windows ((2:ℤ)^a) ((2:ℤ)^d) u v) :
    ∃ pre tail : List ℕ,
      (pre++(2*a+2*d+2-1)::tail).Perm (List.range (2*a+2*d+2)) ∧
      InStrip (oldValue a a (d+2) d) (sourceMod a a (d+2) d/2) 0
        (pre++(2*a+2*d+2-1)::tail) ∧
      InStrip (newValue a a (d+2) d) (sourceMod a a (d+2) d) 0
        (pre++(2*a+2*d+2)::(2*a+2*d+2-1)::tail) := by
  let x : ℤ := 2^a
  let t : ℤ := 2^d
  have hc : (2:ℤ)^(d+2)=4*t := by dsimp [t]; rw [pow_add]; norm_num; ring
  have hbase : base a a (d+2) d=![A x t,B x t,L x t,K x t] := by
    funext r
    fin_cases r <;> dsimp [base] <;> (try simp only [hc]) <;> dsimp [A,B,L,K,x,t] <;> ring
  have hnew : newBase a a (d+2) d=![2*A x t,SU x t,SV x t,SW x t] := by
    funext r
    fin_cases r <;> dsimp [newBase,charge] <;> rw [hbase]
    all_goals dsimp [SU,SV,SW,x] <;> (try simp only [hc]) <;> ring
  have so : rowSeams a a (d+2) d u v false=![H1 x t u,H2 x t u,D x t u v,0] := by
    funext r
    fin_cases r <;> simp [rowSeams,rowBase,hbase,H1,H2,D]
  have sn : rowSeams a a (d+2) d u v true=![J1 x t u,J2 x t u,T x t u v,0] := by
    funext r
    fin_cases r <;> simp [rowSeams,rowBase,hbase,hnew,J1,J2,T,D,SU,SV] <;> ring
  have ho : rowHeads a a (d+2) d false=![L x t,K x t,A x t,B x t] := by
    simp [rowHeads,rowBase,hbase]
  have hn : rowHeads a a (d+2) d true=![SV x t,SW x t,A x t,SU x t] := by
    simp [rowHeads,rowBase,hbase,hnew]
  have hB : 1≤B x t := by
    have hh:=(chain_values a a (d+2) d ha ha (by omega) (by omega)).1 1
    simpa only [hbase,Matrix.cons_val_one,Matrix.cons_val_zero] using hh.1
  have hSU : 1≤SU x t := by
    have hh:=new_base_bounds a a (d+2) d ha ha (by omega) (by omega) 1
    simpa only [hnew,Matrix.cons_val_one,Matrix.cons_val_zero] using hh.1
  have hwin : ∀ side r, window (rowSeams a a (d+2) d u v side r) (rowHeads a a (d+2) d side r) := by
    intro side r
    cases side
    · rw [so,ho]
      fin_cases r
      · exact hw.1.1
      · exact hw.1.2.1
      · exact hw.2.1
      · change window 0 (B x t)
        exact ⟨by omega,by omega⟩
    · rw [sn,hn]
      fin_cases r
      · exact hw.1.2.2.1
      · exact hw.1.2.2.2
      · exact hw.2.2
      · change window 0 (SU x t)
        exact ⟨by omega,by omega⟩
  have he : a+a+(d+2)+d=2*a+2*d+2 := by omega
  have hv' : v<2^((d+2)-1) := by simpa only [show d+2-1=d+1 by omega] using hv
  simpa only [he] using physical_strips a a (d+2) d u v ha ha (by omega) (by omega) hu hv' hwin

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
