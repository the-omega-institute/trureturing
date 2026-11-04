/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/SourceCertificate
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/SourceCertificate
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original a2 near-b construction: SourceCertificate and its physical source consumer. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Banks

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private full stock complement banks word terminals banks_inventory banks_good banks_masses
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Banks
open SourceWidth
open private size base newBase charge sourceMod oldValue newValue negatives chainLength chainStart
  nextBase nextNewBase chain_values packet_masses source_signs
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private oldMass newMass from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private DataCertificate DataCertificate.mk orderedPackets finiteChecks finiteEarChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate
open private blocksWord insertAt insertAt_add from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private native_masses from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

open private packetChecks strip_iff_packetChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets

private def literalCut (a b c d v m M : ℕ) (before : Bool) : ℕ :=
  if before then 0 else (banks a b c d v m M 0).length+1

private def rowBase (a b c d : ℕ) (side : Bool) : Fin 4→ℤ :=
  if side then newBase a b c d else base a b c d
private def rowHeads (a b c d : ℕ) (side : Bool) : Fin 4→ℤ :=
  let F:=rowBase a b c d side
  ![base a b c d 0,F 1,F 3,F 2]
private def rowSeams (a b c d v m M : ℕ) (before side : Bool) : Fin 4→ℤ :=
  let F:=rowBase a b c d side
  let E:=if side then base a b c d 0 else 0
  ![2*((v:ℤ)*F 0-F 3+(m:ℤ)*F 2-(if before then 0 else E)),
    2*(F 1-F 3+(M:ℤ)*F 2),2*(F 1-F 2),0]

set_option maxHeartbeats 3000000 in
private theorem source_certificate (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (v m M : ℕ) (before : Bool) (hv0 : 1≤v) (hv : v≤2^(d-1))
    (hM : M<2^(b-1)) (hsub : Submask m M)
    (hwindows : ∀ (side : Bool) (r : Fin 4),
      0≤rowSeams a b c d v m M before side r ∧
      rowSeams a b c d v m M before side r≤rowHeads a b c d side r-1) :
    Nonempty (Certificate a b c d) ∧
      InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (word a b c d v m M) ∧
      InStrip (newValue a b c d) (sourceMod a b c d) 0
        (insertAt (size a b c d) (word a b c d v m M) (literalCut a b c d v m M before)) := by
  classical
  let P:=banks a b c d v m M
  let N:=terminals a b c d
  let BB:=fun r : Fin 4 => (P r).toFinset
  let ps : List (Finset ℕ×ℕ):=[(BB 0,N 0),(BB 1,N 1),(BB 2,N 2),(BB 3,N 3)]
  let ear : Fin 4:=if before then 0 else 1
  have hp:=banks_inventory a b c d ha hb hc hd v m M hsub
  have hn (r : Fin 4) : (P r).Nodup := by
    have hh:=hp.nodup_iff.mpr List.nodup_range
    simp only [word,List.nodup_append] at hh
    fin_cases r <;> tauto
  have hperm (r : Fin 4) : (BB r).toList.Perm (P r) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (hn r)).mpr
    intro i
    simp [BB]
  have good (r : Fin 4) (i : ℕ) (hi : i∈BB r) : i<size a b c d ∧ i∉negatives a b c d :=
    banks_good a b c d ha hb hc hd v m M r i (List.mem_toFinset.mp hi)
  have hm (side : Bool) (r : Fin 4) :
      (if side then newMass a b c d (BB r) else oldMass a b c d (BB r))=
      ((P r).map (if side then newValue a b c d else oldValue a b c d)).sum := by
    have hh:=packet_masses a b c d ha hb hc hd (BB r) (good r)
    have hs (f : ℕ→ℤ) : (∑ i∈BB r,f i)=((P r).map f).sum := List.sum_toFinset f (hn r)
    cases side
    · exact hh.1.symm.trans (hs _)
    · exact hh.2.symm.trans (hs _)
  have tab:=chain_values a b c d ha hb hc hd
  have oldmass (r : Fin 4) : oldMass a b c d (BB r)=((P r).map (oldValue a b c d)).sum := by
    simpa only [Bool.false_eq_true,ite_false] using hm false r
  have newmass (r : Fin 4) : newMass a b c d (BB r)=((P r).map (newValue a b c d)).sum := by
    simpa only [ite_true] using hm true r
  have indices (r : Fin 4) : chainStart b c d r+(chainLength a b c d r-1)=
      (![N 1,N 3,N 2,N 0] : Fin 4→ℕ) r := by
    fin_cases r <;> dsimp [chainStart,chainLength,N,terminals] <;> omega
  have row (side : Bool) :
      finiteEarChecks (if side then newMass a b c d else oldMass a b c d)
        (if side then newValue a b c d else oldValue a b c d)
        (if side then sourceMod a b c d else sourceMod a b c d/2)
        (if side then base a b c d 0 else 0) 0 ear.val ps := by
    let F:=rowBase a b c d side
    let f:=if side then newValue a b c d else oldValue a b c d
    let NN:=sourceMod a b c d
    let AA:=base a b c d 0
    let E:=if side then AA else 0
    let CC:=if side then NN else NN/2
    let mass:=fun r : Fin 4 => if side then newMass a b c d (BB r) else oldMass a b c d (BB r)
    have hf (r : Fin 4) (i : ℕ) (hi : i<chainLength a b c d r-1) :
        f (chainStart b c d r+i)=2^i*F r := by
      cases side
      · exact (tab.2.1 r i (by omega)).trans (if_pos (by omega))
      · exact (tab.2.2.1 r i (by omega)).trans (if_pos (by omega))
    have masses:=banks_masses a b c d v m M hv0 hv hM hsub f F hf
    have mm (r : Fin 4) : mass r=((P r).map f).sum := hm side r
    have mass0:=congrFun masses 0
    have mass1:=congrFun masses 1
    have mass2:=congrFun masses 2
    have mass3:=congrFun masses 3
    rw [←mm 0] at mass0
    rw [←mm 1] at mass1
    rw [←mm 2] at mass2
    rw [←mm 3] at mass3
    have hstart : F 0=AA+E := by
      cases side <;> dsimp [F,rowBase,E,AA,newBase,charge] <;> ring
    have native (r : Fin 4) :
        (full a b c d r:ℤ)*F r+
          f ((![N 1,N 3,N 2,N 0] : Fin 4→ℕ) r)=
          (![F 1,F 2,F 3,AA] : Fin 4→ℤ) r-F r ∧
        2*f ((![N 1,N 3,N 2,N 0] : Fin 4→ℕ) r)=
          (![F 1,F 2,F 3,AA] : Fin 4→ℤ) r-(if side then 2*NN+1 else NN) := by
      rw [←indices r]
      have nn:=native_masses a b c d ha hb hc hd r
      cases side <;> fin_cases r
      all_goals first
        | simpa [full,F,f,rowBase,nextBase,nextNewBase,AA,NN] using And.intro nn.1 nn.2.2.1
        | simpa [full,F,f,rowBase,nextBase,nextNewBase,AA,NN] using And.intro nn.2.1 nn.2.2.2
    have nn0:=(native 0).1
    have nn1:=(native 1).1
    have nn2:=(native 2).1
    have nn3:=(native 3).1
    have win (r : Fin 4) :
        0≤rowSeams a b c d v m M before side r ∧
        rowSeams a b c d v m M before side r-2*f (N r)≤2*CC := by
      have hh:=hwindows side r
      have ht : 2*f (N r)=rowHeads a b c d side r-(if side then 2*NN+1 else NN) := by
        fin_cases r
        all_goals first
          | simpa [rowHeads,F] using (native 3).2
          | simpa [rowHeads,F] using (native 0).2
          | simpa [rowHeads,F] using (native 2).2
          | simpa [rowHeads,F] using (native 1).2
      cases side <;> dsimp [CC] <;> simp only [Bool.false_eq_true,ite_false,ite_true] at ht
      all_goals omega
    have win0:=win 0
    have win1:=win 1
    have win2:=win 2
    have win3:=win 3
    change finiteEarChecks _ f CC E 0 ear.val ps
    cases before <;>
      simp only [ear,ps,finiteEarChecks,finiteChecks,zero_add,ite_true,ite_false,
        Bool.false_eq_true,Fin.val_one,Fin.val_ofNat]
    all_goals simp only [rowSeams,rowHeads,ite_true,ite_false,Bool.false_eq_true] at win0 win1 win2 win3
    all_goals dsimp only [F,AA,E,mass] at mass0 mass1 mass2 mass3 nn0 nn1 nn2 nn3 hstart win0 win1 win2 win3 ⊢
    all_goals simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ'] at mass0 mass1 mass2 mass3 nn0 nn1 nn2 nn3 win0 win1 win2 win3 ⊢
    all_goals simp only [ite_apply]
    all_goals refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,True.intro⟩
    all_goals nlinarith only [mass0,mass1,mass2,mass3,nn0,nn1,nn2,nn3,
      hstart,win0.1,win0.2,win1.1,win1.2,win2.1,win2.2,win3.1,win3.2]
  have cert : Nonempty (Certificate a b c d) := by
    refine ⟨DataCertificate.mk ps ?_ ear ?_ ?_ ?_ (row true)⟩
    · change ([a+b+c+d-1,d-1,d+c+b-1,d+c-1]).Perm
        ([d-1,d+c-1,d+c+b-1,a+b+c+d-1])
      change ([a+b+c+d-1]++[d-1]++[d+c+b-1]++[d+c-1]).Perm
        ([d-1]++[d+c-1]++[d+c+b-1]++[a+b+c+d-1])
      apply Multiset.coe_eq_coe.mp
      simp only [←Multiset.coe_add,Multiset.coe_singleton]
      ac_rfl
    · intro pkt hpkt i hi
      simp only [ps,List.mem_cons,List.mem_nil_iff,or_false] at hpkt
      rcases hpkt with rfl|rfl|rfl|rfl
      all_goals exact good _ i hi
    · have he : (blocksWord (orderedPackets ps)).Perm (word a b c d v m M) := by
        have hh:=(((((((hperm 0).append_right [N 0]).append (hperm 1)).append_right [N 1]).append
          (hperm 2)).append_right [N 2]).append (hperm 3)).append_right [N 3]
        simpa [ps,orderedPackets,blocksWord,word] using hh
      exact Multiset.coe_eq_coe.mpr (he.trans hp)
    · have hh:=row false
      cases before <;> simpa [ear,ps,finiteChecks,finiteEarChecks] using hh
  let bs : List (List ℕ×ℕ):=[(P 0,N 0),(P 1,N 1),(P 2,N 2),(P 3,N 3)]
  let marked : List (List ℕ×ℕ):=
    if before then [(size a b c d::P 0,N 0),(P 1,N 1),(P 2,N 2),(P 3,N 3)]
    else [(P 0,N 0),(size a b c d::P 1,N 1),(P 2,N 2),(P 3,N 3)]
  have oldchecks : packetChecks (oldValue a b c d) (sourceMod a b c d/2) 0 bs := by
    have hr:=row false
    cases before <;>
      simp only [ear,ps,finiteEarChecks,finiteChecks,ite_true,ite_false,Bool.false_eq_true,
        zero_add,add_zero,Fin.val_one,Fin.val_ofNat] at hr
    all_goals simp only [oldmass] at hr
    all_goals simpa only [bs,packetChecks,zero_add,add_zero] using hr
  have newchecks : packetChecks (newValue a b c d) (sourceMod a b c d) 0 marked := by
    have hr:=row true
    have hear:=tab.2.2.2
    cases before <;>
      simp only [ear,ps,finiteEarChecks,finiteChecks,ite_true,ite_false,Bool.false_eq_true,
        zero_add,Fin.val_one,Fin.val_ofNat] at hr
    all_goals simp only [newmass] at hr
    all_goals simpa [marked,packetChecks,hear,
      add_assoc,add_comm,add_left_comm] using hr
  have hmod : 0≤sourceMod a b c d := by have hh:=(tab.1 0); omega
  have pos (side : Bool) (r : Fin 4) (i : ℕ) (hi : i∈P r) :
      0≤(if side then newValue a b c d else oldValue a b c d) i := by
    have hg:=banks_good a b c d ha hb hc hd v m M r i hi
    have hs:=source_signs a b c d ha hb hc hd i hg.1
    rw [if_neg hg.2] at hs
    cases side <;> simp only [ite_true,ite_false,Bool.false_eq_true] <;> omega
  have neg (side : Bool) (r : Fin 4) :
      (if side then newValue a b c d else oldValue a b c d) (N r)≤0 := by
    have hnmem : N r∈negatives a b c d := by fin_cases r <;> simp [N,terminals,negatives,size]
    have hnlt : N r<size a b c d := by fin_cases r <;> dsimp [N,terminals,size] <;> omega
    have hs:=source_signs a b c d ha hb hc hd (N r) hnlt
    rw [if_pos hnmem] at hs
    cases side <;> simp only [ite_true,ite_false,Bool.false_eq_true] <;> omega
  have oldpos : ∀ pkt∈bs, ∀ i∈pkt.1, 0≤oldValue a b c d i := by
    intro pkt hpkt i hi
    simp only [bs,List.mem_cons,List.mem_nil_iff,or_false] at hpkt
    rcases hpkt with rfl|rfl|rfl|rfl
    all_goals first | exact pos false 0 i hi | exact pos false 1 i hi | exact pos false 2 i hi | exact pos false 3 i hi
  have oldneg : ∀ pkt∈bs, oldValue a b c d pkt.2≤0 := by
    intro pkt hpkt
    simp only [bs,List.mem_cons,List.mem_nil_iff,or_false] at hpkt
    rcases hpkt with rfl|rfl|rfl|rfl
    all_goals first | exact neg false 0 | exact neg false 1 | exact neg false 2 | exact neg false 3
  have newpos : ∀ pkt∈marked, ∀ i∈pkt.1, 0≤newValue a b c d i := by
    intro pkt hpkt i hi
    cases before <;> simp only [marked,ite_true,ite_false,Bool.false_eq_true,
      List.mem_cons,List.mem_nil_iff,or_false] at hpkt
    all_goals rcases hpkt with rfl|rfl|rfl|rfl
    all_goals first
      | exact pos true 0 i hi
      | exact pos true 1 i hi
      | exact pos true 2 i hi
      | exact pos true 3 i hi
      | rcases List.mem_cons.mp hi with rfl|hi
        · rw [tab.2.2.2]; have hh:=(tab.1 0).1; omega
        · first | exact pos true 0 i hi | exact pos true 1 i hi | exact pos true 2 i hi | exact pos true 3 i hi
  have newneg : ∀ pkt∈marked, newValue a b c d pkt.2≤0 := by
    intro pkt hpkt
    cases before <;> simp only [marked,ite_true,ite_false,Bool.false_eq_true,
      List.mem_cons,List.mem_nil_iff,or_false] at hpkt
    all_goals rcases hpkt with rfl|rfl|rfl|rfl
    all_goals first | exact neg true 0 | exact neg true 1 | exact neg true 2 | exact neg true 3
  have hold:=(strip_iff_packetChecks (oldValue a b c d) (sourceMod a b c d/2) 0 bs
    ⟨by omega,by omega⟩ oldpos oldneg).mpr oldchecks
  have hnew:=(strip_iff_packetChecks (newValue a b c d) (sourceMod a b c d) 0 marked
    ⟨by omega,hmod⟩ newpos newneg).mpr newchecks
  have hword : blocksWord bs=word a b c d v m M := by simp [bs,blocksWord,word,P,N,List.append_assoc]
  have hmarked : blocksWord marked=insertAt (size a b c d) (word a b c d v m M)
      (literalCut a b c d v m M before) := by
    cases before
    · let pre:=P 0++[N 0]
      let post:=P 1++[N 1]++P 2++[N 2]++P 3++[N 3]
      have he : word a b c d v m M=pre++post := by simp [word,pre,post,P,N,List.append_assoc]
      have hlen : literalCut a b c d v m M false=pre.length := by simp [literalCut,pre,P]
      rw [he,hlen,show pre.length=pre.length+0 by omega,insertAt_add]
      simp [marked,blocksWord,insertAt,pre,post,List.append_assoc]
    · simp [marked,blocksWord,insertAt,literalCut,word,P,N,List.append_assoc]
  exact ⟨cert,by simpa only [hword] using hold,by simpa only [hmarked] using hnew⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
