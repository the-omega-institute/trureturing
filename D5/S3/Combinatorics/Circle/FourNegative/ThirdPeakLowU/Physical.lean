/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLowU/Physical
   generality: I
   mirror-B: none(waiver:consumed-low-u-support)
   mirror-E: none(waiver:physical-low-u-construction)
   anchors: []
   utility: none
   digest: Exact native low-U masses and finite physical endpoint checks. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Banks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

/-! Exact native low-U masses and finite physical endpoint checks. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU
open SourceWidth
open PacketNormalForm
open private lowUBanks lowUTerminals lowUWord lowU_inventory lowU_good lowU_list_masses
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Banks
open private size base newBase charge sourceMod oldValue newValue negatives chainLength chainStart
  nextBase nextNewBase chain_values source_signs packet_masses
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private oldMass newMass from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private DataCertificate DataCertificate.mk orderedPackets finiteChecks finiteEarChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private native_masses from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

private def rowBase (a b c d : ℕ) (side : Bool) : Fin 4 → ℤ :=
  if side then newBase a b c d else base a b c d
private def rowHeads (a b c d : ℕ) (side : Bool) : Fin 4 → ℤ :=
  let F := rowBase a b c d side
  ![F 2,F 3,base a b c d 0,F 1]
private def rowSeams (a b c d u v w : ℕ) (side : Bool) : Fin 4 → ℤ :=
  let F := rowBase a b c d side
  let A := base a b c d 0
  let E := if side then A else 0
  ![2*(F 2-v*F 1),2*(F 3-w*F 2+u*F 0-v*F 1+E),
    2*(u*F 0+A-v*F 1+E),0]
private def lowUPackets (a b c d u v w : ℕ) : List (Finset ℕ × ℕ) :=
  let P := lowUBanks a b c d u v w
  let T := lowUTerminals a b c d
  [((P 0).toFinset,T 0),((P 1).toFinset,T 1),((P 2).toFinset,T 2),((P 3).toFinset,T 3)]

private theorem bank_nodup (a b c d u v w : ℕ) (r : Fin 4) :
    (lowUBanks a b c d u v w r).Nodup := by
  fin_cases r <;> dsimp [lowUBanks]
  all_goals first
    | exact MaxPlusTwo.Chambers.chamberLabels_nodup _ _ _
    | apply List.nodup_append.mpr
      refine ⟨MaxPlusTwo.Chambers.chamberLabels_nodup _ _ _,
        MaxPlusTwo.Chambers.chamberLabels_nodup _ _ _,?_⟩
      intro i hi j hj hij
      obtain ⟨e,he,_,hie⟩ := (MaxPlusTwo.Chambers.chamberLabels_mem _ _ _ _).mp hi
      obtain ⟨f,hf,_,hif⟩ := (MaxPlusTwo.Chambers.chamberLabels_mem _ _ _ _).mp hj
      omega

set_option maxHeartbeats 2400000 in
private theorem bank_checks (a b c d u v w : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hu : u<2^(d-1)) (hv : v-1<2^(c-1)) (hw : w<2^(b-1)) (hvpos : 1≤v)
    (wins : ∀ (side : Bool) (r : Fin 4),
      0≤rowSeams a b c d u v w side r ∧
      rowSeams a b c d u v w side r≤rowHeads a b c d side r-1) :
    finiteChecks (oldMass a b c d) (oldValue a b c d) (sourceMod a b c d/2) 0
      (lowUPackets a b c d u v w) ∧
    finiteEarChecks (newMass a b c d) (newValue a b c d) (sourceMod a b c d)
      (base a b c d 0) 0 1 (lowUPackets a b c d u v w) := by
  let P := lowUBanks a b c d u v w
  let T := lowUTerminals a b c d
  have tab := chain_values a b c d ha hb hc hd
  have hN : 0≤sourceMod a b c d := by have hh := tab.1 0; omega
  have vm : ((v-1 : ℕ) : ℤ)=(v : ℤ)-1 := by omega
  have row (side : Bool) :
      if side then finiteEarChecks (newMass a b c d) (newValue a b c d)
        (sourceMod a b c d) (base a b c d 0) 0 1 (lowUPackets a b c d u v w)
      else finiteChecks (oldMass a b c d) (oldValue a b c d) (sourceMod a b c d/2)
        0 (lowUPackets a b c d u v w) := by
    let F := rowBase a b c d side
    let f := if side then newValue a b c d else oldValue a b c d
    let mass := if side then newMass a b c d else oldMass a b c d
    let N := sourceMod a b c d
    let AA := base a b c d 0
    let E := if side then AA else 0
    let C := if side then N else N/2
    have hstart : F 0=AA+E := by
      cases side <;> dsimp [F,rowBase,E,AA,newBase,charge] <;> ring
    have hf (r : Fin 4) (i : ℕ) (hi : i<chainLength a b c d r-1) :
        f (chainStart b c d r+i)=2^i*F r := by
      cases side
      · exact (tab.2.1 r i (by omega)).trans (if_pos (by omega))
      · exact (tab.2.2.1 r i (by omega)).trans (if_pos (by omega))
    have masses := lowU_list_masses a b c d u v w hu hv hw f F hf
    have hm (r : Fin 4) : mass ((P r).toFinset)=((P r).map f).sum := by
      have hg : ∀ i∈(P r).toFinset, i<size a b c d ∧ i∉negatives a b c d := by
        intro i hi
        exact lowU_good a b c d u v w ha hb hc hd hu hv hw r i (by simpa [P] using hi)
      have hs := List.sum_toFinset f (bank_nodup a b c d u v w r)
      cases side
      · have hh := (packet_masses a b c d ha hb hc hd (P r).toFinset hg).1
        exact hh.symm.trans hs
      · have hh := (packet_masses a b c d ha hb hc hd (P r).toFinset hg).2
        exact hh.symm.trans hs
    have mass0 := (hm 0).trans (congrFun masses 0)
    have mass1 := (hm 1).trans (congrFun masses 1)
    have mass2 := (hm 2).trans (congrFun masses 2)
    have mass3 := (hm 3).trans (congrFun masses 3)
    have native (r : Fin 4) :
        ((2^(chainLength a b c d r-1)-1 : ℕ) : ℤ)*F r+
          f ((![T 3,T 0,T 1,T 2] : Fin 4→ℕ) r)=
          (![F 1,F 2,F 3,AA] : Fin 4→ℤ) r-F r ∧
        2*f ((![T 3,T 0,T 1,T 2] : Fin 4→ℕ) r)=
          (![F 1,F 2,F 3,AA] : Fin 4→ℤ) r-(if side then 2*N+1 else N) := by
      have nn := native_masses a b c d ha hb hc hd r
      have hi : chainStart b c d r+(chainLength a b c d r-1)=
          (![T 3,T 0,T 1,T 2] : Fin 4→ℕ) r := by
        fin_cases r <;> dsimp [chainStart,chainLength,T,lowUTerminals] <;> omega
      dsimp only at nn
      rw [hi] at nn
      cases side <;> fin_cases r
      all_goals first
        | simpa [F,f,rowBase,nextBase,nextNewBase,AA,N] using And.intro nn.1 nn.2.2.1
        | simpa [F,f,rowBase,nextBase,nextNewBase,AA,N] using And.intro nn.2.1 nn.2.2.2
    have nn0 := (native 0).1
    have nn1 := (native 1).1
    have nn2 := (native 2).1
    have nn3 := (native 3).1
    have nt0 := (native 0).2
    have nt1 := (native 1).2
    have nt2 := (native 2).2
    have nt3 := (native 3).2
    have win (r : Fin 4) : 0≤rowSeams a b c d u v w side r ∧
        rowSeams a b c d u v w side r-2*f (T r)≤2*C := by
      have hh := wins side r
      have ht : 2*f (T r)=rowHeads a b c d side r-(if side then 2*N+1 else N) := by
        fin_cases r
        · simpa [rowHeads,F] using nt1
        · simpa [rowHeads,F] using nt2
        · simpa [rowHeads,F] using nt3
        · simpa [rowHeads,F] using nt0
      cases side <;> dsimp [C] <;> simp only [Bool.false_eq_true,ite_false,ite_true] at ht
      all_goals omega
    have win0 := win 0
    have win1 := win 1
    have win2 := win 2
    have win3 := win 3
    cases side <;> simp only [ite_true,ite_false,Bool.false_eq_true,
      lowUPackets,finiteChecks,finiteEarChecks,zero_add]
    all_goals simp only [rowSeams,rowHeads] at win0 win1 win2 win3
    all_goals dsimp only [F,AA,E,C,f,mass,rowBase] at mass0 mass1 mass2 mass3 nn0 nn1 nn2 nn3 nt0 nt1 nt2 nt3 hstart win0 win1 win2 win3 ⊢
    all_goals simp only [ite_true,ite_false,Bool.false_eq_true,P,T,lowUTerminals,vm,
      chainLength,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ'] at *
    all_goals refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,True.intro⟩
    all_goals nlinarith only [mass0,mass1,mass2,mass3,nn0,nn1,nn2,nn3,
      nt0,nt1,nt2,nt3,hstart,win0.1,win0.2,win1.1,win1.2,win2.1,win2.2,win3.1,win3.2]
  exact ⟨row false,row true⟩

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU
