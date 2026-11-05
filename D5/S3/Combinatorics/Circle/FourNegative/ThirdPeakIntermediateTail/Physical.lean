/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakIntermediateTail/Physical
   generality: I
   mirror-B: none(waiver:private-consumed-physical-source)
   mirror-E: none(waiver:private-consumed-physical-source)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Both actual centered-source windows for all three physical constructions. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Banks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
import D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule

/-! Fresh is the first positive occurrence in bank1
only in mode III, and the first positive occurrence in bank2 otherwise. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail
open SourceWidth PeriodicShortening RunFirstEarTransport
open private branch route route_valid banks terminals word before after freshCut literal_cut
  banks_inventory banks_good
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Masks
open private xval rval sval qval power_coordinates half_power banks_masses original_windows
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Banks
open private A B L K SU SV SW rowBase rowHeads rowSeams reserve bankMasses window
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail.Arithmetic
open private size sourceMod base newBase charge oldValue newValue chainLength chainStart
  nextBase nextNewBase chain_values new_base_bounds source_signs source_totals
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private Gates four_strip
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule

private def earBank (mode : Fin 4) : Fin 4 := if mode=3 then 1 else 2
private def rowBanks (mode : Fin 4) (a b c d : ℕ) (side : Bool) (i : Fin 4) : List ℕ :=
  if side then (if i=earBank mode then size a b c d::banks mode a b c d i
    else banks mode a b c d i) else banks mode a b c d i
private def rowWord (mode : Fin 4) (a b c d : ℕ) (side : Bool) : List ℕ :=
  let P:=rowBanks mode a b c d side
  let T:=terminals a b c d
  P 0++[T 0]++P 1++[T 1]++P 2++[T 2]++P 3++[T 3]

private theorem row_word (mode : Fin 4) (a b c d : ℕ) (ha : 2≤a)
    (had : a≤d) (hdb : d<b) (hbc : b<c) (hm : branch a b d mode) :
    rowWord mode a b c d false=word mode a b c d ∧
    rowWord mode a b c d true=insertAt (size a b c d) (word mode a b c d) (freshCut a b d) := by
  constructor
  · rfl
  · rw [(literal_cut mode a b c d ha had hdb hbc hm).2.2.2]
    fin_cases mode <;> simp [rowWord,rowBanks,earBank,before,after,List.append_assoc]

private theorem insert_perm (k j : ℕ) (l : List ℕ) :
    (insertAt k l j).Perm (l++[k]) := by
  unfold insertAt
  have h:=(List.perm_append_singleton k (l.drop j)).symm.append_left (l.take j)
  simpa only [←List.append_assoc,List.take_append_drop] using h

private theorem base_coordinates (a b c d : ℕ) (had : a≤d) (hdb : d<b) (hbc : b<c) :
    ∀ (side : Bool) (i : Fin 4),
      ((if side then newBase a b c d else base a b c d) i:ℚ)=
        rowBase (xval a) (rval a d) (sval b d) (qval b c) side i := by
  have hp:=power_coordinates a b c d had hdb hbc
  intro side i
  cases side <;> fin_cases i
  all_goals norm_num [rowBase,base,newBase,charge,A,B,L,K,SU,SV,SW]
  all_goals push_cast
  all_goals simp only [hp.1,hp.2.1,hp.2.2]
  all_goals change _ = _
  all_goals dsimp only [xval]
  all_goals ring

/-- A rational form of the four-block criterion; every integer comparison is
transported back explicitly. The last seam is supplied by a separate zero law. -/
private theorem gates_of_windows (C M : ℤ) (m d : Fin 4→ℤ) (H E : Fin 4→ℚ)
    (hC : 0≤C) (hM : (M:ℚ)=2*(C:ℚ)+1)
    (hd : ∀ i, 2*(d i:ℚ)=H i-(M:ℚ))
    (e0 : (m 0:ℚ)+(d 0:ℚ)=E 0)
    (e1 : (m 0:ℚ)+(d 0:ℚ)+(m 1:ℚ)+(d 1:ℚ)=E 1)
    (e2 : (m 0:ℚ)+(d 0:ℚ)+(m 1:ℚ)+(d 1:ℚ)+(m 2:ℚ)+(d 2:ℚ)=E 2)
    (e3 : E 3=0)
    (hz : m 0+d 0+m 1+d 1+m 2+d 2+m 3+d 3=0)
    (hw : ∀ i, window (E i) (H i)) :
    Gates C (m 0) (d 0) (m 1) (d 1) (m 2) (d 2) (m 3) (d 3) := by
  have w0:=hw 0
  have w1:=hw 1
  have w2:=hw 2
  have w3:=hw 3
  dsimp only [window] at w0 w1 w2 w3
  have d0:=hd 0
  have d1:=hd 1
  have d2:=hd 2
  have d3:=hd 3
  have z : (m 0:ℚ)+(d 0:ℚ)+(m 1:ℚ)+(d 1:ℚ)+(m 2:ℚ)+(d 2:ℚ)+
      (m 3:ℚ)+(d 3:ℚ)=0 := by exact_mod_cast hz
  unfold Gates
  refine ⟨hC,?_,?_,?_,hz,?_,?_,?_,?_⟩
  · exact_mod_cast (show (0:ℚ)≤(m 0:ℚ)+(d 0:ℚ) by linarith only [e0,w0.1])
  · exact_mod_cast (show (0:ℚ)≤(m 0:ℚ)+(d 0:ℚ)+(m 1:ℚ)+(d 1:ℚ) by linarith only [e1,w1.1])
  · exact_mod_cast (show (0:ℚ)≤(m 0:ℚ)+(d 0:ℚ)+(m 1:ℚ)+(d 1:ℚ)+(m 2:ℚ)+(d 2:ℚ) by
      linarith only [e2,w2.1])
  · exact_mod_cast (show (m 0:ℚ)≤(C:ℚ) by linarith only [e0,d0,w0.2,hM])
  · exact_mod_cast (show (m 0:ℚ)+(d 0:ℚ)+(m 1:ℚ)≤(C:ℚ) by linarith only [e1,d1,w1.2,hM])
  · exact_mod_cast (show (m 0:ℚ)+(d 0:ℚ)+(m 1:ℚ)+(d 1:ℚ)+(m 2:ℚ)≤(C:ℚ) by
      linarith only [e2,d2,w2.2,hM])
  · exact_mod_cast (show (m 0:ℚ)+(d 0:ℚ)+(m 1:ℚ)+(d 1:ℚ)+(m 2:ℚ)+(d 2:ℚ)+(m 3:ℚ)≤(C:ℚ) by
      linarith only [z,d3,e3,w3.2,hM])

set_option maxHeartbeats 3200000 in
private theorem physical_source (a b c d : ℕ) (ha : 2≤a)
    (had : a≤d) (hdb : d<b) (hbc : b<c) :
    let mode:=route a b d
    (word mode a b c d).Perm (List.range (size a b c d)) ∧
    (before mode a b c d).length=freshCut a b d ∧
    freshCut a b d<size a b c d ∧
    InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (word mode a b c d) ∧
    InStrip (newValue a b c d) (sourceMod a b c d) 0
      (insertAt (size a b c d) (word mode a b c d) (freshCut a b d)) := by
  dsimp only
  let mode:=route a b d
  have hm : branch a b d mode := route_valid a b d had hdb
  let x:=xval a
  let r:=rval a d
  let s:=sval b d
  let q:=qval b c
  let N:=sourceMod a b c d
  let AA:=base a b c d 0
  let T:=terminals a b c d
  have hp:=banks_inventory mode a b c d ha had hdb hbc hm
  have cut:=literal_cut mode a b c d ha had hdb hbc hm
  have tab:=chain_values a b c d ha (by omega) (by omega) (by omega)
  have tabNew:=new_base_bounds a b c d ha (by omega) (by omega) (by omega)
  have totals:=source_totals a b c d ha (by omega) (by omega) (by omega)
  have bc:=base_coordinates a b c d had hdb hbc
  have oldbc (i : Fin 4) : (base a b c d i:ℚ)=rowBase x r s q false i := bc false i
  have newbc (i : Fin 4) : (newBase a b c d i:ℚ)=rowBase x r s q true i := bc true i
  have pc:=power_coordinates a b c d had hdb hbc
  have hw:=original_windows mode a b c d ha had hdb hbc hm
  have shape:=row_word mode a b c d ha had hdb hbc hm
  have hA : (AA:ℚ)=A x r s q := by simpa [AA,rowBase] using bc false 0
  change (base a b c d 0:ℚ)=A x r s q at hA
  have hN : 0≤N := by have hh:=tab.1 0; dsimp only [N]; omega
  have oddN : N=2*((2:ℤ)^a*2^b*2^c*2^(d-1))-1 := by
    have he : (2:ℤ)^d=2*2^(d-1) := by
      conv_lhs => rw [show d=(d-1)+1 by omega,pow_succ]
      ring
    dsimp [N,sourceMod]
    rw [he]
    ring
  have row (side : Bool) :
      InStrip (if side then newValue a b c d else oldValue a b c d)
        (if side then N else N/2) 0 (rowWord mode a b c d side) := by
    let f:=if side then newValue a b c d else oldValue a b c d
    let F:=if side then newBase a b c d else base a b c d
    let M:=if side then 2*N+1 else N
    let C:=if side then N else N/2
    let P:=rowBanks mode a b c d side
    let m:=fun i : Fin 4 => ((P i).map f).sum
    let dd:=fun i : Fin 4 => f (T i)
    have fpos (i : Fin 4) (e : ℕ) (he : e∈banks mode a b c d i) : 0≤f e := by
      have good:=banks_good mode a b c d ha had hdb hbc hm i e he
      have hv:=source_signs a b c d ha (by omega) (by omega) (by omega) e good.1
      rw [if_neg good.2] at hv
      cases side
      · exact hv.1.le
      · exact hv.2.le
    have positive (i : Fin 4) : ∀ e∈P i, 0≤f e := by
      intro e he
      cases side
      · exact fpos i e he
      · dsimp [P,rowBanks] at he
        split_ifs at he with hi
        · rcases List.mem_cons.mp he with he|he
          · rw [he]
            change 0≤newValue a b c d (size a b c d)
            rw [totals.2.2]
            have hh:=(tab.1 0).1
            omega
          · exact fpos i e he
        · exact fpos i e he
    have series (j : Fin 4) (e : ℕ) (he : e<chainLength a b c d j-1) :
        f (chainStart b c d j+e)=2^e*F j := by
      cases side
      · exact (tab.2.1 j e (by omega)).trans (if_pos (by omega))
      · exact (tab.2.2.1 j e (by omega)).trans (if_pos (by omega))
    have bm:=banks_masses mode a b c d ha had hdb hbc hm f F series
    have mass (i : Fin 4) : (m i:ℚ)=bankMasses mode x r s q (rowBase x r s q side) i+
        (if side then (if i=earBank mode then A x r s q else 0) else 0) := by
      have hh:=bm i
      have ff : (fun j => (F j:ℚ))=rowBase x r s q side := funext (bc side)
      rw [ff] at hh
      cases side
      · simpa [m,P,rowBanks] using hh
      · simp only [f,ite_true] at hh
        by_cases hi : i=earBank mode
        · simp only [m,P,rowBanks,f,ite_true,if_pos hi,List.map_cons,List.sum_cons,
            totals.2.2,Int.cast_add,hA]
          rw [hh]
          ring
        · simpa [m,P,rowBanks,f,hi] using hh
    -- Native chain mass and doubled actual terminal, in V,W,X,U order.
    have terminal (i : Fin 4) :
        2*(dd i:ℚ)=rowHeads x r s q side i-(M:ℚ) ∧
        (dd i:ℚ)=rowHeads x r s q side i-
          ((![q*s*r*x,s*r*x,x,r*x] : Fin 4→ℚ) i)/2*
          rowBase x r s q side ((![1,2,3,0] : Fin 4→Fin 4) i) := by
      let j:Fin 4:=(![1,2,3,0] : Fin 4→Fin 4) i
      have nn:=native_masses a b c d ha (by omega) (by omega) (by omega) j
      dsimp only at nn
      have ni : chainStart b c d j+(chainLength a b c d j-1)=T i := by
        fin_cases i <;> dsimp [j,T,terminals,chainStart,chainLength] <;> omega
      rw [ni] at nn
      have n1 : (((2^(chainLength a b c d j-1)-1:ℕ):ℤ)*F j+dd i)=
          (if side then nextNewBase a b c d j else nextBase a b c d j)-F j := by
        cases side
        · exact nn.1
        · exact nn.2.1
      have n2 : 2*dd i=(if side then nextNewBase a b c d j else nextBase a b c d j)-M := by
        cases side
        · exact nn.2.2.1
        · exact nn.2.2.2
      have nr1:=congrArg (fun z : ℤ => (z:ℚ)) n1
      have nr2:=congrArg (fun z : ℤ => (z:ℚ)) n2
      have hc : 1≤2^(chainLength a b c d j-1) := by have hh:=Nat.two_pow_pos (chainLength a b c d j-1); omega
      simp only [Nat.cast_sub hc,Nat.cast_one,Int.cast_add,Int.cast_sub,Int.cast_mul,
        Int.cast_ofNat,Int.cast_natCast,Nat.cast_pow,Nat.cast_ofNat] at nr1 nr2
      fin_cases i <;> cases side
      all_goals norm_num [j,chainLength,nextBase,nextNewBase,F,oldbc,newbc] at nr1 nr2
      all_goals try simp (disch := omega) only [half_power,pc.1,pc.2.1,pc.2.2] at nr1
      all_goals try simp only [show (2:ℚ)^a=x from rfl] at nr1
      all_goals norm_num [rowHeads,rowBase] at nr1 nr2 ⊢
      all_goals dsimp only [M,F] at nr1 nr2 ⊢
      all_goals constructor <;> linarith only [nr1,nr2]
    have seams :
        (m 0:ℚ)+(dd 0:ℚ)=rowSeams mode x r s q side 0 ∧
        (m 0:ℚ)+(dd 0:ℚ)+(m 1:ℚ)+(dd 1:ℚ)=rowSeams mode x r s q side 1 ∧
        (m 0:ℚ)+(dd 0:ℚ)+(m 1:ℚ)+(dd 1:ℚ)+(m 2:ℚ)+(dd 2:ℚ)=rowSeams mode x r s q side 2 := by
      simp only [mass 0,mass 1,mass 2,(terminal 0).2,(terminal 1).2,(terminal 2).2]
      generalize hmode : mode=selected at hm ⊢
      clear hmode
      fin_cases selected <;> cases side
      all_goals norm_num [rowSeams,rowHeads,rowBase,reserve,bankMasses,earBank]
      all_goals dsimp [x,r,s,q,xval,rval,sval,qval]
      all_goals simp [branch,Matrix.cons_val_zero',Matrix.cons_val_succ',Fin.mk.injEq] at hm
      all_goals first
        | (have er : d-a=0 := by omega
           have es : b-d=1 := by omega
           simp only [er,es,pow_zero,pow_one]
           constructor <;> first | ring | constructor <;> ring)
        | (have er : d-a=0 := by omega
           simp only [er,pow_zero]
           constructor <;> first | ring | constructor <;> ring)
        | (have es : b-d=1 := by omega
           simp only [es,pow_one]
           constructor <;> first | ring | constructor <;> ring)
        | (constructor <;> first | ring | constructor <;> ring)
      all_goals trivial
    -- Independent zero total from the native source, not from these windows.
    have zero : (rowWord mode a b c d side |>.map f).sum=0 := by
      cases side
      · change ((rowWord mode a b c d false).map (oldValue a b c d)).sum=0
        rw [shape.1]
        exact ((hp.map (oldValue a b c d)).sum_eq).trans totals.1
      · change ((rowWord mode a b c d true).map (newValue a b c d)).sum=0
        rw [shape.2]
        have pp:=(insert_perm (size a b c d) (freshCut a b d) (word mode a b c d)).trans
          (hp.append_right [size a b c d])
        rw [(pp.map (newValue a b c d)).sum_eq]
        simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,
          totals.2.1,totals.2.2,neg_add_cancel]
    have z : m 0+dd 0+m 1+dd 1+m 2+dd 2+m 3+dd 3=0 := by
      simpa only [rowWord,List.map_append,List.sum_append,List.map_singleton,
        List.sum_singleton,add_assoc] using zero
    have hC : 0≤C := by cases side <;> dsimp only [C] <;> omega
    have hM : (M:ℚ)=2*(C:ℚ)+1 := by
      have hi : M=2*C+1 := by
        cases side
        · change N=2*(N/2)+1
          omega
        · change 2*N+1=2*N+1
          rfl
      exact_mod_cast hi
    have gates : Gates C (m 0) (dd 0) (m 1) (dd 1) (m 2) (dd 2) (m 3) (dd 3) :=
      gates_of_windows C M m dd (rowHeads x r s q side) (rowSeams mode x r s q side)
        hC hM (fun i => (terminal i).1) seams.1 seams.2.1 seams.2.2
        (by simp [rowSeams]) z (hw side)
    exact four_strip f C (P 0) (P 1) (P 2) (P 3) (T 0) (T 1) (T 2) (T 3)
      (positive 0) (positive 1) (positive 2) (positive 3) gates
  exact ⟨hp,cut.1,cut.2.1,by simpa [shape.1,N,mode] using row false,
    by simpa [shape.2,N,mode] using row true⟩

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakIntermediateTail
