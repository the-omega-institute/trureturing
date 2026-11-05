/- GID: D5/S3/Combinatorics/Circle/FourNegative/LastTwoMaximum/SourceCertificate
   generality: I
   mirror-B: none(waiver:private-consumed-literal-source)
   mirror-E: none(waiver:private-consumed-literal-source)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Actual-source packet checks with one literal preterminal ear. -/
import D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Banks
import D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.BorrowArithmetic
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum
namespace StrictDictionary
open SourceWidth PeriodicShortening RunFirstEarTransport
open private x y z A B D L K H SU SV SW vNat quotientT wBit hybridOld hybridNew
  vEndpoint vNewEndpoint borrowT borrowU wEndpoint wNewEndpoint hybrid_decomposition
  from D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Source
open private firstBank hybridLabels borrowBanks singletonBanks banksWord terminals
  mixedMass masks_masses singleton_masses borrow_inventory singleton_inventory banks_good
  from D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Banks
open private singleton_scalar_windows window
  from D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.Arithmetic
open private borrow_selector_windows
  from D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum.BorrowArithmetic
open private full from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open private sourceMod charge nextBase nextNewBase chain_values source_signs from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size base newBase oldValue newValue chainLength chainStart negatives)
open private native_masses
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (blocksWord insertAt)
open private packetChecks withEar strip_iff_packetChecks withEar_split
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private withEar_positive withEar_negatives
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Equivalence
open private actual_nat_joint_iff
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint

private def rowBase (a b s : ℕ) (side : Bool) : Fin 4 → ℤ :=
  if side then newBase a b s s else base a b s s
private def rowValue (a b s : ℕ) (side : Bool) : ℕ → ℤ :=
  if side then newValue a b s s else oldValue a b s s
private def packetList (a b s : ℕ) (P : Fin 4 → List ℕ) : List (List ℕ × ℕ) :=
  [(P 0,terminals a b s 0),(P 1,terminals a b s 1),
    (P 2,terminals a b s 2),(P 3,terminals a b s 3)]
private def seams (a b s t : ℕ) (tail : Bool → ℤ) (slot : Fin 4)
    (side : Bool) : Fin 4 → ℤ :=
  let F := rowBase a b s side
  let ear := if side then base a b s s 0 else 0
  ![(vNat b : ℤ)*(F 1-F 0),
    F 2-F 0-mixedMass b F t+(if slot.val≤1 then ear else 0),
    F 3-F 0-tail side+(if slot.val≤2 then ear else 0),0]
private def heads (a b s : ℕ) (side : Bool) : Fin 4 → ℤ :=
  let F := rowBase a b s side
  ![F 1,F 2,F 3,base a b s s 0]

/- The inputs below are the exact scalar sums of the four actual banks.
   Both consumers construct P, prove its complete physical permutation, and
   derive these identities by the decoder mass lemmas in Banks. -/
set_option maxHeartbeats 2000000 in
private theorem physical_joint_from_windows (a b s t : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hbs : b≤s)
    (P : Fin 4 → List ℕ) (tail : Bool → ℤ) (slot : Fin 4) (hslot : 1≤slot.val)
    (hp : (banksWord a b s P).Perm (List.range (a+b+s+s)))
    (hgood : ∀ r : Fin 4, ∀ i∈P r, i<size a b s s ∧ i∉negatives a b s s)
    (hmass : ∀ side : Bool,
      let F := rowBase a b s side
      let f := rowValue a b s side
      let C := fun r : Fin 4 => (full a b s s r : ℤ)
      let E := C 0*F 0+((vNat b : ℤ)-1)*(F 1-F 0)
      (fun r : Fin 4 => ((P r).map f).sum)=
        ![E,C 0*F 0+C 1*F 1-E-mixedMass b F t,
          C 2*F 2+mixedMass b F t-tail side,C 3*F 3+tail side])
    (hwindows : ∀ side : Bool, ∀ r : Fin 4,
      window (seams a b s t tail slot side r) (heads a b s side r)) :
    ∃ sigma : List (Fin (a+b+s+s)), ∃ j : ℕ, j≤a+b+s+s ∧
      OriginalOrder (a+b+s+s) (1+2^a+2^(a+b)+2^(a+b+s)) sigma ∧
      OriginalOrder (a+b+s+s+1) (2*(1+2^a+2^(a+b)+2^(a+b+s)))
        (earWord (a+b+s+s) sigma j) := by
  let bs := packetList a b s P
  let N := sourceMod a b s s
  let AA := base a b s s 0
  have tab := chain_values a b s s ha hb (by omega) (by omega)
  have hN : 0≤N := by have hh := tab.1 0;dsimp [N];omega
  have hword : blocksWord bs=banksWord a b s P := by
    simp [bs,packetList,blocksWord,banksWord,List.append_assoc]
  have positive (side : Bool) : ∀ pkt∈bs, ∀ i∈pkt.1, 0≤rowValue a b s side i := by
    intro pkt hpkt i hi
    simp only [bs,packetList,List.mem_cons,List.mem_nil_iff,or_false] at hpkt
    rcases hpkt with rfl | rfl | rfl | rfl
    all_goals
      have hg : i<size a b s s ∧ i∉negatives a b s s := by
        first | exact hgood 0 i hi | exact hgood 1 i hi
              | exact hgood 2 i hi | exact hgood 3 i hi
      have hs := source_signs a b s s ha hb (by omega) (by omega) i hg.1
      rw [if_neg hg.2] at hs
      cases side
      · exact hs.1.le
      · exact hs.2.le
  have negative (side : Bool) : ∀ pkt∈bs, rowValue a b s side pkt.2≤0 := by
    intro pkt hpkt
    have hn : pkt.2∈negatives a b s s := by
      simp only [bs,packetList,List.mem_cons,List.mem_nil_iff,or_false] at hpkt
      rcases hpkt with rfl | rfl | rfl | rfl
      all_goals simp [terminals,negatives,size,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
    have hlt : pkt.2<size a b s s := by
      have hn' := hn
      simp only [negatives,size,List.mem_cons,List.mem_nil_iff,or_false] at hn' ⊢
      omega
    have hs := source_signs a b s s ha hb (by omega) (by omega) pkt.2 hlt
    rw [if_pos hn] at hs
    cases side
    · exact hs.1.le
    · exact hs.2.le
  have checks (side : Bool) :
      packetChecks (rowValue a b s side) (if side then N else N/2) 0
        (if side then withEar (size a b s s) slot.val bs else bs) := by
    let F := rowBase a b s side
    let f := rowValue a b s side
    let C := if side then N else N/2
    have hm := hmass side
    have mass0 := congrFun hm 0
    have mass1 := congrFun hm 1
    have mass2 := congrFun hm 2
    have mass3 := congrFun hm 3
    have native (r : Fin 4) :
        (full a b s s r : ℤ)*F r+f (terminals a b s r)=heads a b s side r-F r ∧
        2*f (terminals a b s r)=heads a b s side r-(if side then 2*N+1 else N) := by
      have nn := native_masses a b s s ha hb (by omega) (by omega) r
      have hi : chainStart b s s r+(chainLength a b s s r-1)=terminals a b s r := by
        fin_cases r <;> dsimp [chainStart,chainLength,terminals] <;> omega
      dsimp only at nn
      rw [hi] at nn
      cases side <;> fin_cases r
      all_goals first
        | simpa [F,f,full,rowBase,rowValue,heads,nextBase,nextNewBase,N,AA] using
            And.intro nn.1 nn.2.2.1
        | simpa [F,f,full,rowBase,rowValue,heads,nextBase,nextNewBase,N,AA] using
            And.intro nn.2.1 nn.2.2.2
    have nn0 := (native 0).1
    have nn1 := (native 1).1
    have nn2 := (native 2).1
    have nn3 := (native 3).1
    have hstart : F 0=AA+(if side then AA else 0) := by
      cases side <;> dsimp [F,rowBase,AA,newBase,charge] <;> ring
    have win (r : Fin 4) : 0≤seams a b s t tail slot side r ∧
        seams a b s t tail slot side r-f (terminals a b s r)≤C := by
      have hw := hwindows side r
      have ht := (native r).2
      unfold window at hw
      cases side <;> dsimp [C] <;> simp only [Bool.false_eq_true,ite_false,ite_true] at ht
      all_goals omega
    have win0 := win 0
    have win1 := win 1
    have win2 := win 2
    have win3 := win 3
    change packetChecks f C 0 (if side then withEar (size a b s s) slot.val bs else bs)
    have fresh : newValue a b s s (size a b s s)=AA := tab.2.2.2
    cases side <;> fin_cases slot
    all_goals norm_num at hslot
    all_goals simp only [Bool.false_eq_true,ite_false,ite_true,bs,packetList,withEar,packetChecks,List.map_append,List.sum_append,
      List.map_singleton,List.sum_singleton,zero_add,fresh]
    all_goals simp [seams,heads,F,f,C,rowValue,AA,fresh] at mass0 mass1 mass2 mass3 win0 win1 win2 win3 nn0 nn1 nn2 nn3 hstart ⊢
    all_goals repeat' apply And.intro
    all_goals first | trivial | linarith only [mass0,mass1,mass2,mass3,nn0,nn1,nn2,nn3,hstart,win0,win1,win2,win3]
  have oldchecks : packetChecks (oldValue a b s s) (N/2) 0 bs := checks false
  have hold : InStrip (oldValue a b s s) (N/2) 0 (banksWord a b s P) := by
    rw [←hword]
    exact (strip_iff_packetChecks _ _ _ bs ⟨by omega,by omega⟩
      (positive false) (negative false)).mpr oldchecks
  have newchecks : packetChecks (newValue a b s s) N 0
      (withEar (size a b s s) slot.val bs) := checks true
  have hnew : InStrip (newValue a b s s) N 0
      (blocksWord (withEar (size a b s s) slot.val bs)) := by
    apply (strip_iff_packetChecks _ _ _ _ ⟨by omega,hN⟩
      (withEar_positive _ _ _ bs (by change 0≤newValue a b s s (size a b s s); rw [tab.2.2.2];have hh := tab.1 0;omega)
        (positive true)) ?_).mpr newchecks
    intro pkt hb'
    have hmem : pkt.2∈bs.map Prod.snd := by
      rw [←withEar_negatives (size a b s s) slot.val bs]
      exact List.mem_map.mpr ⟨pkt,hb',rfl⟩
    obtain ⟨pkt',hpk',he⟩ := List.mem_map.mp hmem
    simpa [he] using negative true pkt' hpk'
  obtain ⟨pre,post,hsplit,hmarked⟩ :=
    withEar_split (size a b s s) slot.val bs (by simp [bs,packetList])
  have hsplit' : banksWord a b s P=pre++post := by rw [←hword];exact hsplit
  have hlen := hp.length_eq
  rw [hsplit'] at hlen
  have hj : pre.length≤size a b s s := by
    simp only [List.length_append,List.length_range] at hlen
    dsimp [size]
    omega
  apply (actual_nat_joint_iff a b s s ha hb (by omega) (by omega)).mpr
  refine ⟨banksWord a b s P,hp,hold,pre.length,hj,?_⟩
  have hear : insertAt (size a b s s) (banksWord a b s P) pre.length=
      pre++size a b s s::post := by rw [hsplit'];simp [insertAt]
  rw [hear]
  rw [hmarked] at hnew
  exact hnew


private theorem singleton_actual_source (a b s : ℕ) (ha : 2≤a) (hab : a<b)
    (hbs : b≤s) (hnotbalanced : ¬ (b=s ∧ s=a+1)) :
    ∃ sigma : List (Fin (a+b+s+s)), ∃ j : ℕ, j≤a+b+s+s ∧
      OriginalOrder (a+b+s+s) (1+2^a+2^(a+b)+2^(a+b+s)) sigma ∧
      OriginalOrder (a+b+s+s+1) (2*(1+2^a+2^(a+b)+2^(a+b+s)))
        (earWord (a+b+s+s) sigma j) := by
  let t := quotientT a b s
  let w := wBit a b
  let P := singletonBanks a b s t w
  let tail := fun side : Bool => (w : ℤ)*rowBase a b s side 2
  let slot : Fin 4 := if vNewEndpoint a b s t<0 then 1 else 3
  obtain ⟨ht,hw,hE,hEp,hR,hRp,hG,hGp,hGpa⟩ :=
    singleton_scalar_windows a b s ha hab hbs hnotbalanced
  change window (if vNewEndpoint a b s t<0 then
    vNewEndpoint a b s t+A a b s else vNewEndpoint a b s t) (SV a b s) at hRp
  have hb : 2≤b := by omega
  have tab := chain_values a b s s ha hb (by omega) (by omega)
  have rowOld : rowBase a b s false=![A a b s,B a b s,L a b s,K a b s] := by
    funext r
    fin_cases r <;> dsimp [rowBase,base,A,B,L,K,x,y,z] <;> ring
  have rowNew : rowBase a b s true=![2*A a b s,SU a b s,SV a b s,SW a b s] := by
    funext r
    fin_cases r <;> dsimp [rowBase,newBase,charge,base,A,B,L,K,H,SU,SV,SW,x,y,z] <;> ring
  have hAA : base a b s s 0=A a b s := by dsimp [base,A,x,y,z];ring
  have mixOld : mixedMass b ![A a b s,B a b s,L a b s,K a b s] t=hybridOld a b s t := by
    exact (hybrid_decomposition a b s t).symm
  have mixNew : mixedMass b ![2*A a b s,SU a b s,SV a b s,SW a b s] t=hybridNew a b s t := by
    change (t%vNat b : ℕ)*(2*A a b s)+(t-t%vNat b : ℕ)*(2*B a b s-1)=
      2*hybridOld a b s t-(t-t%vNat b : ℕ)
    rw [hybrid_decomposition]
    ring
  apply physical_joint_from_windows a b s t ha hb hbs P tail slot
    (by dsimp [slot];split <;> decide)
    (singleton_inventory a b s t w ha hb hbs)
    (fun r i hi => banks_good a b s t w ha hb hbs P (Or.inr rfl) r i hi)
  · intro side
    have hf (r : Fin 4) (e : ℕ) (he : e<chainLength a b s s r-1) :
        rowValue a b s side (chainStart b s s r+e)=2^e*rowBase a b s side r := by
      cases side
      · exact (tab.2.1 r e (by omega)).trans (if_pos (by omega))
      · exact (tab.2.2.1 r e (by omega)).trans (if_pos (by omega))
    exact singleton_masses a b s t w ha hb hbs ht hw _ _ hf
  · have hA : 1≤A a b s := by rw [←hAA];exact (tab.1 0).1
    have oldSeams : seams a b s t tail slot false=
        ![(vNat b : ℤ)*D a b s,vEndpoint a b s t,K a b s-A a b s-(w : ℤ)*L a b s,0] := by
      funext r
      fin_cases r <;> dsimp [seams]
      all_goals simp only [mixOld,rowOld,Bool.false_eq_true,ite_false,ite_self,hAA]
      all_goals dsimp [tail]
      all_goals try simp only [rowOld]
      all_goals dsimp [D,vEndpoint]
      all_goals ring
    have newSeams : seams a b s t tail slot true=
        ![(vNat b : ℤ)*(2*D a b s-1),
          vNewEndpoint a b s t+(if slot.val≤1 then A a b s else 0),
          2*(K a b s-A a b s-(w : ℤ)*L a b s)-H b s+(w : ℤ)*(z s+1)+
            (if slot.val≤2 then A a b s else 0),0] := by
      funext r
      fin_cases r <;> dsimp [seams]
      all_goals simp only [mixNew,rowNew,ite_true,hAA]
      all_goals dsimp [tail]
      all_goals try simp only [rowNew]
      all_goals dsimp [hybridNew,D,vNewEndpoint,vEndpoint,SU,SV,SW]
      all_goals ring
    intro side r
    cases side
    · rw [oldSeams]
      dsimp [heads]
      rw [rowOld,hAA]
      fin_cases r <;> norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, Function.comp_apply, id_eq,
        Fin.val_ofNat, Fin.val_mk]
      · exact hE
      · exact hR
      · exact hG
      · change window 0 (A a b s)
        exact ⟨by omega,by omega⟩
    · rw [newSeams]
      dsimp [heads]
      rw [rowNew,hAA]
      by_cases he : vNewEndpoint a b s t<0
      · have hs : slot=(1 : Fin 4) := by simp [slot,he]
        rw [hs]
        fin_cases r <;> norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, Function.comp_apply, id_eq,
        Fin.val_ofNat, Fin.val_mk]
        · exact hEp
        · simpa [he,t,w] using hRp
        · exact hGpa
        · change window 0 (A a b s)
          exact ⟨by omega,by omega⟩
      · have hs : slot=(3 : Fin 4) := by simp [slot,he]
        rw [hs]
        fin_cases r <;> norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, Function.comp_apply, id_eq,
        Fin.val_ofNat, Fin.val_mk]
        · exact hEp
        · simpa [he,t,w] using hRp
        · simpa [t,w] using hGp
        · change window 0 (A a b s)
          exact ⟨by omega,by omega⟩

private theorem borrow_actual_source (a b s : ℕ) (hb : 2≤b) (hba : b<a)
    (has : a<s) :
    ∃ sigma : List (Fin (a+b+s+s)), ∃ j : ℕ, j≤a+b+s+s ∧
      OriginalOrder (a+b+s+s) (1+2^a+2^(a+b)+2^(a+b+s)) sigma ∧
      OriginalOrder (a+b+s+s+1) (2*(1+2^a+2^(a+b)+2^(a+b+s)))
        (earWord (a+b+s+s) sigma j) := by
  let t := borrowT a b s
  let u := borrowU a b s
  let P := borrowBanks a b s t u
  let tail := fun side : Bool => mixedMass b (rowBase a b s side) u
  let slot : Fin 4 := if s=a+1 then 3 else
    if vNewEndpoint a b s t<0 then 1 else
      if wNewEndpoint a b s u<0 then 2 else 3
  obtain ⟨ht,hu,hsub,hE,hEp,hR,hRp,hG,hGp⟩ :=
    borrow_selector_windows a b s hb hba has
  have ha : 2≤a := by omega
  have hbs : b≤s := by omega
  have tab := chain_values a b s s ha hb (by omega) (by omega)
  have rowOld : rowBase a b s false=![A a b s,B a b s,L a b s,K a b s] := by
    funext r
    fin_cases r <;> dsimp [rowBase,base,A,B,L,K,x,y,z] <;> ring
  have rowNew : rowBase a b s true=![2*A a b s,SU a b s,SV a b s,SW a b s] := by
    funext r
    fin_cases r <;> dsimp [rowBase,newBase,charge,base,A,B,L,K,H,SU,SV,SW,x,y,z] <;> ring
  have hAA : base a b s s 0=A a b s := by dsimp [base,A,x,y,z];ring
  have mixOld (q : ℕ) : mixedMass b ![A a b s,B a b s,L a b s,K a b s] q=hybridOld a b s q := by
    exact (hybrid_decomposition a b s q).symm
  have mixNew (q : ℕ) : mixedMass b ![2*A a b s,SU a b s,SV a b s,SW a b s] q=hybridNew a b s q := by
    change (q%vNat b : ℕ)*(2*A a b s)+(q-q%vNat b : ℕ)*(2*B a b s-1)=
      2*hybridOld a b s q-(q-q%vNat b : ℕ)
    rw [hybrid_decomposition]
    ring
  have earV : (if slot.val≤1 then A a b s else 0)=
      (if s=a+1 then 0 else if vNewEndpoint a b s t<0 then A a b s else 0) := by
    by_cases ha' : s=a+1
    · simp [slot,ha']
    · by_cases hv' : vNewEndpoint a b s t<0
      · simp [slot,ha',hv']
      · by_cases hw' : wNewEndpoint a b s u<0 <;> simp [slot,ha',hv',hw']
  have earW : (if slot.val≤2 then A a b s else 0)=
      (if s=a+1 then 0 else
        if vNewEndpoint a b s t<0 ∨ wNewEndpoint a b s u<0 then A a b s else 0) := by
    by_cases ha' : s=a+1
    · simp [slot,ha']
    · by_cases hv' : vNewEndpoint a b s t<0
      · simp [slot,ha',hv']
      · by_cases hw' : wNewEndpoint a b s u<0 <;> simp [slot,ha',hv',hw']
  apply physical_joint_from_windows a b s t ha hb hbs P tail slot
    (by dsimp [slot];split_ifs <;> decide)
    (borrow_inventory a b s t u ha hb hbs hsub)
    (fun r i hi => banks_good a b s t u ha hb hbs P (Or.inl rfl) r i hi)
  · intro side
    have hf (r : Fin 4) (e : ℕ) (he : e<chainLength a b s s r-1) :
        rowValue a b s side (chainStart b s s r+e)=2^e*rowBase a b s side r := by
      cases side
      · exact (tab.2.1 r e (by omega)).trans (if_pos (by omega))
      · exact (tab.2.2.1 r e (by omega)).trans (if_pos (by omega))
    exact masks_masses a b s t u ha hb hbs ht hu hsub _ _ hf
  · have hA : 1≤A a b s := by rw [←hAA];exact (tab.1 0).1
    have oldSeams : seams a b s t tail slot false=
        ![(vNat b : ℤ)*D a b s,vEndpoint a b s t,wEndpoint a b s u,0] := by
      funext r
      fin_cases r <;> dsimp [seams]
      all_goals simp only [mixOld,rowOld,Bool.false_eq_true,ite_false,ite_self,hAA]
      all_goals dsimp [tail]
      all_goals try simp only [rowOld,mixOld]
      all_goals dsimp [D,vEndpoint,wEndpoint]
      all_goals ring
    have newSeams : seams a b s t tail slot true=
        ![(vNat b : ℤ)*(2*D a b s-1),
          vNewEndpoint a b s t+(if slot.val≤1 then A a b s else 0),
          wNewEndpoint a b s u+(if slot.val≤2 then A a b s else 0),0] := by
      funext r
      fin_cases r <;> dsimp [seams]
      all_goals simp only [mixNew,rowNew,ite_true,hAA]
      all_goals dsimp [tail]
      all_goals try simp only [rowNew,mixNew]
      all_goals dsimp [hybridNew,D,vNewEndpoint,vEndpoint,wNewEndpoint,wEndpoint,SU,SV,SW]
      all_goals ring
    intro side r
    cases side
    · rw [oldSeams]
      dsimp [heads]
      rw [rowOld,hAA]
      fin_cases r <;> norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, Function.comp_apply, id_eq,
        Fin.val_ofNat, Fin.val_mk]
      · exact hE
      · exact hR
      · exact hG
      · change window 0 (A a b s)
        exact ⟨by omega,by omega⟩
    · rw [newSeams]
      dsimp [heads]
      rw [rowNew,hAA]
      fin_cases r <;> norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_succ,
        Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, Function.comp_apply, id_eq,
        Fin.val_ofNat, Fin.val_mk]
      · exact hEp
      · simpa only [earV,t] using hRp
      · simpa only [earW,t,u] using hGp
      · change window 0 (A a b s)
        exact ⟨by omega,by omega⟩

end StrictDictionary
end D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum
