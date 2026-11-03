/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPaidV/SourceCertificate
   generality: I
   mirror-B: none(waiver:private-consumed-actual-certificate)
   mirror-E: none(waiver:private-consumed-actual-certificate)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Native masses, literal conditional preterminal ear, and physical certificates. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Arithmetic

/-! Physical paid-V construction. Both the reusable DataCertificate and the exact
increasing-decoder bank word are supplied, so no internal Finset enumeration
choice is used to identify the reviewed physical order. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV
open D5.S3.Combinatorics.Circle.SourceWidth
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private full stock complement banks word terminals banks_inventory banks_good banks_masses v_stock_masks
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open private window from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Arithmetic
open private size base newBase charge sourceMod oldValue newValue negatives chainLength chainStart
  nextBase nextNewBase chain_values packet_masses source_signs
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private oldMass newMass from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private DataCertificate DataCertificate.mk orderedPackets finiteChecks finiteEarChecks
  finiteChecks_equiv finiteEarChecks_equiv
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate
open private blocksWord insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private packetChecks withEar strip_iff_packetChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private finitePackets finite_packet_checks finite_ear_checks withEar_positive withEar_negatives
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Equivalence
open private native_masses from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

private def rowBase (a b c d : ℕ) (side : Bool) : Fin 4→ℤ :=
  if side then newBase a b c d else base a b c d
private def rowHeads (a b c d : ℕ) (side : Bool) : Fin 4→ℤ :=
  let F:=rowBase a b c d side
  ![F 1,F 2,F 3,base a b c d 0]
private def rowSeams (a b c d h : ℕ) (early side : Bool) : Fin 4→ℤ :=
  let F:=rowBase a b c d side
  let m : ℤ:=2^(c-d)
  let w : ℤ:=2^(b-a-1)
  let ear:=if side then base a b c d 0 else 0
  ![m*F 1-F 0,F 2-F 0-m*h*F 1+(if early then ear else 0),
    F 3-F 0-w*F 2+(if early then ear else 0),0]
private def earSlot (early : Bool) : Fin 4 := if early then 1 else 3
private def bankPackets (a b c d h : ℕ) : List (List ℕ×ℕ) :=
  let P:=banks a b c d h
  let T:=terminals a b c d
  [(P 0,T 0),(P 1,T 1),(P 2,T 2),(P 3,T 3)]
private def beforeEar (a b c d h : ℕ) (early : Bool) : List ℕ :=
  let P:=banks a b c d h
  let T:=terminals a b c d
  if early then P 0++[T 0]++P 1
  else P 0++[T 0]++P 1++[T 1]++P 2++[T 2]++P 3
private def afterEar (a b c d h : ℕ) (early : Bool) : List ℕ :=
  let P:=banks a b c d h
  let T:=terminals a b c d
  if early then [T 1]++P 2++[T 2]++P 3++[T 3] else [T 3]
private def freshCut (a b c d h : ℕ) (early : Bool) : ℕ :=
  (beforeEar a b c d h early).length

private theorem literal_ear (a b c d h : ℕ) (early : Bool) :
    blocksWord (withEar (size a b c d) (earSlot early).val (bankPackets a b c d h))=
      insertAt (size a b c d) (word a b c d h) (freshCut a b c d h early) := by
  have hw : word a b c d h=beforeEar a b c d h early++afterEar a b c d h early := by
    cases early <;> simp [word,beforeEar,afterEar,List.append_assoc]
  have he : blocksWord (withEar (size a b c d) (earSlot early).val (bankPackets a b c d h))=
      beforeEar a b c d h early++size a b c d::afterEar a b c d h early := by
    cases early <;> simp [bankPackets,earSlot,withEar,blocksWord,beforeEar,afterEar,List.append_assoc]
  rw [he,hw]
  simp [freshCut,insertAt]

set_option maxHeartbeats 2400000 in
private theorem source_certificate (a b c d h : ℕ)
    (ha : 2≤a) (hab : a<b) (hbd : b≤d) (hdc : d<c)
    (hh : h<2^(d-1)) (early : Bool)
    (hwindows : ∀ (side : Bool) (r : Fin 4),
      window (rowSeams a b c d h early side r) (rowHeads a b c d side r)) :
    Nonempty (Certificate a b c d) ∧
    (word a b c d h).Perm (List.range (size a b c d)) ∧
    InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (word a b c d h) ∧
    freshCut a b c d h early<size a b c d ∧
    InStrip (newValue a b c d) (sourceMod a b c d) 0
      (insertAt (size a b c d) (word a b c d h) (freshCut a b c d h early)) := by
  classical
  let P:=banks a b c d h
  let T:=terminals a b c d
  let BB:=fun r : Fin 4 => (P r).toFinset
  let ps : List (Finset ℕ×ℕ):=[(BB 0,T 0),(BB 1,T 1),(BB 2,T 2),(BB 3,T 3)]
  have hp:=banks_inventory a b c d h ha (by omega) (by omega) (by omega) (by omega)
  have hn (r : Fin 4) : (P r).Nodup := by
    have hall:=hp.nodup_iff.mpr List.nodup_range
    simp only [word,List.nodup_append] at hall
    fin_cases r <;> tauto
  have hperm (r : Fin 4) : (BB r).toList.Perm (P r) := List.toFinset_toList (hn r)
  have good (r : Fin 4) (i : ℕ) (hi : i∈BB r) : i<size a b c d ∧ i∉negatives a b c d :=
    banks_good a b c d h ha (by omega) (by omega) (by omega) (by omega) r i
      (List.mem_toFinset.mp hi)
  have hm (side : Bool) (r : Fin 4) :
      (if side then newMass a b c d (BB r) else oldMass a b c d (BB r))=
      ((P r).map (if side then newValue a b c d else oldValue a b c d)).sum := by
    have hm':=packet_masses a b c d ha (by omega) (by omega) (by omega) (BB r) (good r)
    have hs (f : ℕ→ℤ) : (∑ i∈BB r,f i)=((P r).map f).sum := List.sum_toFinset f (hn r)
    cases side
    · exact hm'.1.symm.trans (hs _)
    · exact hm'.2.symm.trans (hs _)
  have tab:=chain_values a b c d ha (by omega) (by omega) (by omega)
  have row (side : Bool) :
      finiteEarChecks (if side then newMass a b c d else oldMass a b c d)
        (if side then newValue a b c d else oldValue a b c d)
        (if side then sourceMod a b c d else sourceMod a b c d/2)
        (if side then base a b c d 0 else 0) 0 (earSlot early).val ps := by
    let F:=rowBase a b c d side
    let f:=if side then newValue a b c d else oldValue a b c d
    let N:=sourceMod a b c d
    let AA:=base a b c d 0
    let ee:=if side then AA else 0
    let C:=if side then N else N/2
    let M:=fun r : Fin 4 => if side then newMass a b c d (BB r) else oldMass a b c d (BB r)
    have hf (r : Fin 4) (i : ℕ) (hi : i<chainLength a b c d r-1) :
        f (chainStart b c d r+i)=2^i*F r := by
      cases side
      · exact (tab.2.1 r i (by omega)).trans (if_pos (by omega))
      · exact (tab.2.2.1 r i (by omega)).trans (if_pos (by omega))
    have masses:=banks_masses a b c d h ha hab (by omega) (by omega) hh f F hf
    have mm (r : Fin 4) : M r=((P r).map f).sum := hm side r
    have mass0:=congrFun masses 0
    have mass1:=congrFun masses 1
    have mass2:=congrFun masses 2
    have mass3:=congrFun masses 3
    rw [←mm 0] at mass0
    rw [←mm 1] at mass1
    rw [←mm 2] at mass2
    rw [←mm 3] at mass3
    have hstart : F 0=AA+ee := by cases side <;> dsimp [F,rowBase,ee,AA,newBase,charge] <;> ring
    have native (r : Fin 4) :
        (full a b c d r:ℤ)*F r+f (T r)=
          (![F 1,F 2,F 3,AA] : Fin 4→ℤ) r-F r ∧
        2*f (T r)=(![F 1,F 2,F 3,AA] : Fin 4→ℤ) r-(if side then 2*N+1 else N) := by
      have nn:=native_masses a b c d ha (by omega) (by omega) (by omega) r
      have hi : chainStart b c d r+(chainLength a b c d r-1)=T r := by
        fin_cases r <;> dsimp [T,chainStart,chainLength,terminals] <;> omega
      dsimp only at nn
      rw [hi] at nn
      cases side <;> fin_cases r
      all_goals first
        | simpa [full,F,f,rowBase,nextBase,nextNewBase,T,terminals,AA,N]
            using And.intro nn.1 nn.2.2.1
        | simpa [full,F,f,rowBase,nextBase,nextNewBase,T,terminals,AA,N]
            using And.intro nn.2.1 nn.2.2.2
    have nn0:=(native 0).1
    have nn1:=(native 1).1
    have nn2:=(native 2).1
    have nn3:=(native 3).1
    have vstock : (full a b c d 1:ℤ)=
        (2:ℤ)^(c-d)-1+(2:ℤ)^(c-d)*(full a b c d 0:ℤ) := by
      have hs:=congrArg (fun n : ℕ => (n:ℤ)) (v_stock_masks c d (by omega) (by omega))
      simpa [full,chainLength,Nat.cast_sub (show 1≤2^(c-1) by have := Nat.two_pow_pos (c-1);omega),
        Nat.cast_sub (show 1≤2^(c-d) by have := Nat.two_pow_pos (c-d);omega),
        Nat.cast_sub (show 1≤2^(d-1) by have := Nat.two_pow_pos (d-1);omega)] using hs
    rw [vstock] at nn1
    have win (r : Fin 4) : 0≤rowSeams a b c d h early side r ∧
        rowSeams a b c d h early side r-f (T r)≤C := by
      have hw:=hwindows side r
      have ht : 2*f (T r)=rowHeads a b c d side r-(if side then 2*N+1 else N) := by
        simpa [rowHeads,F] using (native r).2
      unfold window at hw
      cases side <;> dsimp [C] <;> simp only [Bool.false_eq_true,ite_false,ite_true] at ht
      all_goals omega
    have win0:=win 0
    have win1:=win 1
    have win2:=win 2
    have win3:=win 3
    change finiteEarChecks _ f C ee 0 (earSlot early).val ps
    cases early <;>
      simp only [earSlot,ps,finiteEarChecks,finiteChecks,zero_add,ite_true,ite_false,
        Bool.false_eq_true,Fin.val_one,Fin.val_ofNat]
    all_goals simp only [rowSeams,ite_true,ite_false,Bool.false_eq_true] at win0 win1 win2 win3
    all_goals dsimp only [F,AA,ee,M] at mass0 mass1 mass2 mass3 nn0 nn1 nn2 nn3 hstart win0 win1 win2 win3 ⊢
    all_goals simp only [ite_apply]
    all_goals simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Function.comp_apply,
      Matrix.cons_val_zero',Matrix.cons_val_succ'] at mass0 mass1 mass2 mass3 nn0 nn1 nn2 nn3 win0 win1 win2 win3
    all_goals refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,True.intro⟩
    all_goals nlinarith only [mass0,mass1,mass2,mass3,nn0,nn1,nn2,nn3,
      hstart,win0.1,win0.2,win1.1,win1.2,win2.1,win2.2,win3.1,win3.2]
  have oldrow : finiteChecks (oldMass a b c d) (oldValue a b c d) (sourceMod a b c d/2) 0 ps := by
    have hr:=row false
    cases early <;> simpa [earSlot,ps,finiteEarChecks,finiteChecks] using hr
  have cert : Nonempty (Certificate a b c d) := by
    refine ⟨DataCertificate.mk ps ?_ (earSlot early) ?_ ?_ oldrow (row true)⟩
    · exact List.Perm.refl _
    · intro pkt hpkt i hi
      simp only [ps,List.mem_cons,List.mem_nil_iff,or_false] at hpkt
      rcases hpkt with rfl|rfl|rfl|rfl
      all_goals exact good _ i hi
    · have he : (blocksWord (orderedPackets ps)).Perm (word a b c d h) := by
        have hp':=(((((((hperm 0).append_right [T 0]).append (hperm 1)).append_right [T 1]).append
          (hperm 2)).append_right [T 2]).append (hperm 3)).append_right [T 3]
        simpa [ps,orderedPackets,blocksWord,word] using hp'
      exact Multiset.coe_eq_coe.mpr (he.trans hp)
  -- Keep the original increasing list banks when obtaining the literal ear.
  let bs:=bankPackets a b c d h
  have bsnd : ∀ pkt∈bs, pkt.1.Nodup := by
    intro pkt hb
    simp only [bs,bankPackets,List.mem_cons,List.mem_nil_iff,or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl
    · exact hn 0
    · exact hn 1
    · exact hn 2
    · exact hn 3
  have hps : finitePackets bs=ps := rfl
  have hword : blocksWord bs=word a b c d h := by simp [bs,bankPackets,blocksWord,word,List.append_assoc]
  have positive (side : Bool) : ∀ pkt∈bs, ∀ i∈pkt.1,
      0≤(if side then newValue a b c d else oldValue a b c d) i := by
    intro pkt hb i hi
    simp only [bs,bankPackets,List.mem_cons,List.mem_nil_iff,or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl
    all_goals
      have hg : i<size a b c d ∧ i∉negatives a b c d := by
        first
        | exact banks_good a b c d h ha (by omega) (by omega) (by omega) (by omega) 0 i hi
        | exact banks_good a b c d h ha (by omega) (by omega) (by omega) (by omega) 1 i hi
        | exact banks_good a b c d h ha (by omega) (by omega) (by omega) (by omega) 2 i hi
        | exact banks_good a b c d h ha (by omega) (by omega) (by omega) (by omega) 3 i hi
      have hs:=source_signs a b c d ha (by omega) (by omega) (by omega) i hg.1
      rw [if_neg hg.2] at hs
      cases side
      · exact hs.1.le
      · exact hs.2.le
  have negative (side : Bool) : ∀ pkt∈bs,
      (if side then newValue a b c d else oldValue a b c d) pkt.2≤0 := by
    intro pkt hb
    have ht : pkt.2∈negatives a b c d := by
      have hm : pkt.2∈bs.map Prod.snd := List.mem_map.mpr ⟨pkt,hb,rfl⟩
      simpa [bs,bankPackets,terminals,negatives,size] using hm
    have htr : pkt.2<size a b c d := by
      have hmem:=ht
      simp only [negatives,List.mem_cons,List.mem_nil_iff,or_false,size] at hmem ⊢
      omega
    have hs:=source_signs a b c d ha (by omega) (by omega) (by omega) pkt.2 htr
    rw [if_pos ht] at hs
    cases side
    · exact hs.1.le
    · exact hs.2.le
  have massEq (side : Bool) : ∀ pkt∈ps,
      (if side then newMass a b c d else oldMass a b c d) pkt.1=
        ∑ i∈pkt.1,(if side then newValue a b c d else oldValue a b c d) i := by
    have eqMass (r : Fin 4) :
        (if side then newMass a b c d (BB r) else oldMass a b c d (BB r))=
          ∑ i∈BB r,(if side then newValue a b c d else oldValue a b c d) i := by
      have hs:=packet_masses a b c d ha (by omega) (by omega) (by omega) (BB r) (good r)
      cases side
      · exact hs.1.symm
      · exact hs.2.symm
    intro pkt hb
    simp only [ps,List.mem_cons,List.mem_nil_iff,or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl
    · simpa only [ite_apply] using eqMass 0
    · simpa only [ite_apply] using eqMass 1
    · simpa only [ite_apply] using eqMass 2
    · simpa only [ite_apply] using eqMass 3
  have hN : 0≤sourceMod a b c d := by have hh':=(tab.1 0);omega
  have oldchecks : packetChecks (oldValue a b c d) (sourceMod a b c d/2) 0 bs := by
    apply (finite_packet_checks _ _ _ bs bsnd).mp
    rw [hps]
    exact (finiteChecks_equiv _ _ _ _ ps (massEq false)).mp oldrow
  have newchecks : packetChecks (newValue a b c d) (sourceMod a b c d) 0
      (withEar (size a b c d) (earSlot early).val bs) := by
    apply (finite_ear_checks _ _ _ _ _ bs bsnd).mp
    rw [hps]
    exact (finiteEarChecks_equiv _ _ _ _ _ _ _ tab.2.2.2 ps (massEq true)).mp (row true)
  have hold : InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 (word a b c d h) := by
    rw [←hword]
    exact (strip_iff_packetChecks _ _ _ bs ⟨by omega,by omega⟩ (positive false) (negative false)).mpr oldchecks
  have hnew : InStrip (newValue a b c d) (sourceMod a b c d) 0
      (blocksWord (withEar (size a b c d) (earSlot early).val bs)) := by
    apply (strip_iff_packetChecks _ _ _ _ ⟨by omega,hN⟩
      (withEar_positive _ _ _ bs (by change 0≤newValue a b c d (size a b c d); have he:=tab.1 0;rw [tab.2.2.2];omega) (positive true)) ?_).mpr newchecks
    intro pkt hb
    have ht : pkt.2∈bs.map Prod.snd := by
      rw [←withEar_negatives (size a b c d) (earSlot early).val bs]
      exact List.mem_map.mpr ⟨pkt,hb,rfl⟩
    obtain ⟨pkt',hb',he⟩:=List.mem_map.mp ht
    simpa [he] using negative true pkt' hb'
  have hcut : freshCut a b c d h early<size a b c d := by
    have hl:=hp.length_eq
    have hsplit : word a b c d h=beforeEar a b c d h early++afterEar a b c d h early := by
      cases early <;> simp [word,beforeEar,afterEar,List.append_assoc]
    rw [hsplit] at hl
    have hpost : 0<(afterEar a b c d h early).length := by cases early <;> simp [afterEar]
    simp only [List.length_append,List.length_range] at hl
    dsimp [freshCut,size]
    omega
  exact ⟨cert,hp,hold,hcut,by simpa only [bs,literal_ear] using hnew⟩

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV
