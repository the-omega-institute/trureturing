/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualSecond/SourceCertificate
   generality: I
   mirror-B: none(waiver:private-consumed-actual-certificate)
   mirror-E: none(waiver:private-consumed-actual-certificate)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Native paired bank masses turn the two concrete schedules into physical certificates. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Banks
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Arithmetic

/-! Only the original labels and the single fresh occurrence are used. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private full stock complement banks word terminals banks_inventory banks_good banks_masses
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Banks
open private window from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond.Arithmetic
open private base newBase charge sourceMod oldValue newValue nextBase nextNewBase chain_values packet_masses from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source (size negatives chainLength chainStart)
open private oldMass newMass from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private DataCertificate DataCertificate.mk orderedPackets finiteChecks finiteEarChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure (blocksWord)
open private native_masses from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

private def rowBase (a b c : ℕ) (side : Bool) : Fin 4→ℤ :=
  if side then newBase a b c b else base a b c b
private def rowHeads (a b c : ℕ) (paid side : Bool) : Fin 4→ℤ :=
  let F:=rowBase a b c side
  let AA:=base a b c b 0
  if paid then ![F 1,F 2,F 3,AA] else ![F 2,F 3,AA,F 1]
private def rowSeams (a b c : ℕ) (paid side : Bool) (v w q : ℕ) : Fin 4→ℤ :=
  let F:=rowBase a b c side
  let AA:=base a b c b 0
  let E:=if side then AA else 0
  if paid then ![((v:ℤ)+1)*F 1-F 0,F 2-F 0,
    ((q:ℤ)+1)*F 3-F 0-(w:ℤ)*F 2,0]
  else ![F 2-((v:ℤ)+1)*F 1,F 3-(w:ℤ)*F 2-((v:ℤ)+1)*F 1+E,
    AA-((v:ℤ)+1)*F 1+E,0]

set_option maxHeartbeats 2400000 in
private theorem source_certificate (a b c : ℕ) (ha : 2≤a) (hab : a≤b) (hbc : b<c)
    (paid : Bool) (v w q : ℕ) (hv : v<2^(c-1)) (hw : w<2^(b-1)) (hq : q<2^(a-1))
    (hwindows : ∀ (side : Bool) (r : Fin 4),
      window (rowSeams a b c paid side v w q r) (rowHeads a b c paid side r)) :
    Nonempty (Certificate a b c b) := by
  classical
  let P:=banks a b c paid v w q
  let T:=terminals a b c paid
  let BB:=fun r : Fin 4 => (P r).toFinset
  let ps : List (Finset ℕ×ℕ):=[(BB 0,T 0),(BB 1,T 1),(BB 2,T 2),(BB 3,T 3)]
  let ear : Fin 4:=if paid then 3 else 1
  have hp:=banks_inventory a b c ha (by omega) (by omega) paid v w q
  have hn (r : Fin 4) : (P r).Nodup := by
    have hh:=hp.nodup_iff.mpr List.nodup_range
    simp only [word,List.nodup_append] at hh
    fin_cases r <;> tauto
  have hperm (r : Fin 4) : (BB r).toList.Perm (P r) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (hn r)).mpr
    intro i
    simp [BB]
  have good (r : Fin 4) (i : ℕ) (hi : i∈BB r) : i<size a b c b ∧ i∉negatives a b c b :=
    banks_good a b c ha (by omega) (by omega) paid v w q r i (List.mem_toFinset.mp hi)
  have hm (side : Bool) (r : Fin 4) :
      (if side then newMass a b c b (BB r) else oldMass a b c b (BB r))=
      ((P r).map (if side then newValue a b c b else oldValue a b c b)).sum := by
    have hh:=packet_masses a b c b ha (by omega) (by omega) (by omega) (BB r) (good r)
    have hs (f : ℕ→ℤ) : (∑ i∈BB r,f i)=((P r).map f).sum := List.sum_toFinset f (hn r)
    cases side
    · exact hh.1.symm.trans (hs _)
    · exact hh.2.symm.trans (hs _)
  have tab:=chain_values a b c b ha (by omega) (by omega) (by omega)
  have row (side : Bool) :
      finiteEarChecks (if side then newMass a b c b else oldMass a b c b)
        (if side then newValue a b c b else oldValue a b c b)
        (if side then sourceMod a b c b else sourceMod a b c b/2)
        (if side then base a b c b 0 else 0) 0 ear.val ps := by
    let F:=rowBase a b c side
    let f:=if side then newValue a b c b else oldValue a b c b
    let N:=sourceMod a b c b
    let AA:=base a b c b 0
    let E:=if side then AA else 0
    let C:=if side then N else N/2
    let M:=fun r : Fin 4 => if side then newMass a b c b (BB r) else oldMass a b c b (BB r)
    have hf (r : Fin 4) (i : ℕ) (hi : i<chainLength a b c b r-1) :
        f (chainStart b c b r+i)=2^i*F r := by
      cases side
      · exact (tab.2.1 r i (by omega)).trans (if_pos (by omega))
      · exact (tab.2.2.1 r i (by omega)).trans (if_pos (by omega))
    have masses:=banks_masses a b c paid v w q hv hw hq f F hf
    have mm (r : Fin 4) : M r=((P r).map f).sum := hm side r
    have mass0:=congrFun masses 0
    have mass1:=congrFun masses 1
    have mass2:=congrFun masses 2
    have mass3:=congrFun masses 3
    rw [←mm 0] at mass0
    rw [←mm 1] at mass1
    rw [←mm 2] at mass2
    rw [←mm 3] at mass3
    have hstart : F 0=AA+E := by cases side <;> dsimp [F,rowBase,E,AA,newBase,charge] <;> ring
    have native (r : Fin 4) :
        (full a b c r:ℤ)*F r+f (terminals a b c true r)=
          (![F 1,F 2,F 3,AA] : Fin 4→ℤ) r-F r ∧
        2*f (terminals a b c true r)=
          (![F 1,F 2,F 3,AA] : Fin 4→ℤ) r-(if side then 2*N+1 else N) := by
      have nn:=native_masses a b c b ha (by omega) (by omega) (by omega) r
      have hi : chainStart b c b r+(chainLength a b c b r-1)=terminals a b c true r := by
        fin_cases r <;> dsimp [chainStart,chainLength,terminals] <;> omega
      dsimp only at nn
      rw [hi] at nn
      cases side <;> fin_cases r
      all_goals first
        | simpa [full,F,f,rowBase,nextBase,nextNewBase,terminals,AA,N]
            using And.intro nn.1 nn.2.2.1
        | simpa [full,F,f,rowBase,nextBase,nextNewBase,terminals,AA,N]
            using And.intro nn.2.1 nn.2.2.2
    have nn0:=(native 0).1
    have nn1:=(native 1).1
    have nn2:=(native 2).1
    have nn3:=(native 3).1
    have win (r : Fin 4) :
        0≤rowSeams a b c paid side v w q r ∧
        rowSeams a b c paid side v w q r-f (T r)≤C := by
      have hh:=hwindows side r
      have ht : 2*f (T r)=rowHeads a b c paid side r-(if side then 2*N+1 else N) := by
        cases paid <;> fin_cases r
        all_goals first | simpa [T,terminals,rowHeads,F] using (native 0).2
                        | simpa [T,terminals,rowHeads,F] using (native 1).2
                        | simpa [T,terminals,rowHeads,F] using (native 2).2
                        | simpa [T,terminals,rowHeads,F] using (native 3).2
      unfold window at hh
      cases side <;> dsimp [C] <;> simp only [Bool.false_eq_true,ite_false,ite_true] at ht
      all_goals omega
    have win0:=win 0
    have win1:=win 1
    have win2:=win 2
    have win3:=win 3
    change finiteEarChecks _ f C E 0 ear.val ps
    cases paid <;>
      simp only [ear,ps,finiteEarChecks,finiteChecks,zero_add,ite_true,ite_false,
        Bool.false_eq_true,Fin.val_one,Fin.val_ofNat]
    all_goals simp only [rowSeams,rowHeads,ite_true,ite_false,Bool.false_eq_true] at win0 win1 win2 win3
    all_goals simp only [ite_true,ite_false,Bool.false_eq_true] at mass0 mass1 mass2 mass3
    all_goals dsimp [T,terminals] at *
    all_goals dsimp only [F,AA,E,M] at mass0 mass1 mass2 mass3 nn0 nn1 nn2 nn3 hstart win0 win1 win2 win3 ⊢
    all_goals simp only [ite_apply]
    all_goals refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,True.intro⟩
    all_goals nlinarith only [mass0,mass1,mass2,mass3,nn0,nn1,nn2,nn3,
      hstart,win0.1,win0.2,win1.1,win1.2,win2.1,win2.2,win3.1,win3.2]
  refine ⟨DataCertificate.mk ps ?_ ear ?_ ?_ ?_ (row true)⟩
  · cases paid
    · change ([b+c-1,b+c+b-1,a+b+c+b-1]++[b-1]).Perm
        ([b-1]++[b+c-1,b+c+b-1,a+b+c+b-1])
      exact List.perm_append_comm
    · exact List.Perm.refl _
  · intro pkt hpkt i hi
    simp only [ps,List.mem_cons,List.mem_nil_iff,or_false] at hpkt
    rcases hpkt with rfl|rfl|rfl|rfl
    all_goals exact good _ i hi
  · have he : (blocksWord (orderedPackets ps)).Perm (word a b c paid v w q) := by
      have hh:=(((((((hperm 0).append_right [T 0]).append (hperm 1)).append_right [T 1]).append
        (hperm 2)).append_right [T 2]).append (hperm 3)).append_right [T 3]
      simpa [ps,orderedPackets,blocksWord,word] using hh
    exact Multiset.coe_eq_coe.mpr (he.trans hp)
  · have hh:=row false
    cases paid <;> simpa [ear,ps,finiteChecks,finiteEarChecks] using hh

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond
