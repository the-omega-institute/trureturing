/- GID: D5/S3/Combinatorics/Circle/FourNegative/OppositeFirstThirdMaximum/Physical
   generality: I
   mirror-B: none(waiver:private-consumed-endpoint-implementation)
   mirror-E: none(waiver:private-consumed-endpoint-implementation)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Both complete centered physical strips from quotient margins and nonnegative shared charges. -/
import D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum.Source
import D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000
namespace D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum
open SourceWidth PeriodicShortening RunFirstEarTransport
open private C A B L K SU SV SW gates from
  D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum.Arithmetic
open private vMask rawBanks banks terminals word newBanks enlarged inventory banks_good raw_masses
  label_charge literal_ear freshCut cut_bound from
  D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum.Source
open private full from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open private sourceMod base newBase charge oldValue newValue nextBase nextNewBase chain_values source_totals new_base_bounds source_signs from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size chainLength chainStart negatives)
open private native_masses from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private four_strip from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private actual_nat_joint_iff from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private insertAt from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure

private def heads (p q : Fin 4→ℤ) : Fin 3→ℤ :=
  ![p 0,p 0+q 0+p 1,p 0+q 0+p 1+q 1+p 2]
private def seams (p q : Fin 4→ℤ) : Fin 3→ℤ :=
  ![p 0+q 0,p 0+q 0+p 1+q 1,p 0+q 0+p 1+q 1+p 2+q 2]
private def withFresh (p : Fin 4→ℤ) (E : ℤ) (early : Bool) : Fin 4→ℤ :=
  if early then ![p 0,p 1+E,p 2,p 3] else ![p 0,p 1,p 2,p 3+E]
private def mixed (p q pn qn : Fin 4→ℤ) (E N : ℤ) (early : Bool) : Fin 6→ℤ :=
  if early then
    ![N-2*heads p q 0,2*seams pn qn 0,2*seams p q 1,
      2*(N-heads (withFresh pn E early) qn 1),2*seams p q 2,
      2*(N-heads (withFresh pn E early) qn 2)]
  else
    ![N-2*heads p q 0,2*seams pn qn 0,N-2*heads p q 1,
      2*seams pn qn 1,N-2*heads p q 2,2*seams pn qn 2]

/-- Complete both rows by accounting for every nonnegative shared charge.
The bank containing the fresh label may be empty apart from that label. -/
private theorem complete_checks (p q pn qn : Fin 4→ℤ) (E N : ℤ) (early : Bool)
    (cp : ∀ r, 0≤2*p r-pn r) (cq : ∀ r, 0≤2*q r-qn r)
    (oldzero : p 0+q 0+p 1+q 1+p 2+q 2+p 3+q 3=0)
    (newzero : pn 0+qn 0+pn 1+qn 1+pn 2+qn 2+pn 3+qn 3= -E)
    (hm : ∀ i, 0≤mixed p q pn qn E N early i) :
    ∀ i : Fin 3, heads p q i≤N/2 ∧ 0≤seams p q i ∧
      heads (withFresh pn E early) qn i≤N ∧
      0≤seams (withFresh pn E early) qn i := by
  have cp0:=cp 0; have cp1:=cp 1; have cp2:=cp 2; have cp3:=cp 3
  have cq0:=cq 0; have cq1:=cq 1; have cq2:=cq 2; have cq3:=cq 3
  have h0:=hm 0; have h1:=hm 1; have h2:=hm 2
  have h3:=hm 3; have h4:=hm 4; have h5:=hm 5
  cases early <;> intro i <;> fin_cases i
  all_goals dsimp [mixed,heads,seams,withFresh] at h0 h1 h2 h3 h4 h5 ⊢
  all_goals omega

private theorem charge_sum (f g : ℕ→ℤ) (xs : List ℕ)
    (hc : ∀ i∈xs, 0≤2*f i-g i) : 0≤2*(xs.map f).sum-(xs.map g).sum := by
  revert hc
  induction xs with
  | nil => intro hc; simp
  | cons i xs ih =>
    intro hc
    have hi:=hc i (by simp)
    have hs:=ih (fun j hj => hc j (by simp [hj]))
    simp only [List.map_cons,List.sum_cons]
    omega

private theorem twice_full (a b d : ℕ) (r : Fin 4) (hl : 1≤chainLength a b a d r) :
    2*(full a b a d r:ℤ)=(2:ℤ)^(chainLength a b a d r)-2 := by
  have hp : (2:ℤ)^(chainLength a b a d r)=2*(2:ℤ)^(chainLength a b a d r-1) := by
    calc
      (2:ℤ)^(chainLength a b a d r)=(2:ℤ)^((chainLength a b a d r-1)+1) := by
        congr 1; omega
      _ = 2*(2:ℤ)^(chainLength a b a d r-1) := by rw [pow_succ]; ring
  have hc : (full a b a d r:ℤ)=(2:ℤ)^(chainLength a b a d r-1)-1 := by
    dsimp [full]
    rw [Nat.cast_sub (by have := Nat.two_pow_pos (chainLength a b a d r-1); omega)]
    norm_cast
  rw [hc,hp]; ring

private theorem physical_joint (a b d m : ℕ) (early : Bool)
    (hb : 2≤b) (hd : 2≤d) (hba : b<a) (hda : d<a)
    (hm : m<2^(a-1))
    (hw : ∀ i : Fin 6, 0≤gates (2^a) (2^b) (2^d) (2^(a-b)) m early i) :
    ∃ sigma : List (Fin (a+b+a+d)), ∃ j : ℕ, j≤a+b+a+d ∧
      OriginalOrder (a+b+a+d) (1+2^a+2^(a+b)+2^(a+b+a)) sigma ∧
      OriginalOrder (a+b+a+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+a)))
        (earWord (a+b+a+d) sigma j) := by
  have ha : 2≤a := by omega
  let k:=size a b a d
  let N:=sourceMod a b a d
  let E:=base a b a d 0
  let f:=oldValue a b a d
  let g:=newValue a b a d
  let P:=banks a b d m early
  let T:=terminals a b d early
  let Pn:=newBanks a b d m early
  let p:=fun r : Fin 4 => ((P r).map f).sum
  let pn:=fun r : Fin 4 => ((P r).map g).sum
  let q:=fun r : Fin 4 => f (T r)
  let qn:=fun r : Fin 4 => g (T r)
  let l:=word a b d m early
  have hp : l.Perm (List.range k) := inventory a b d m early ha hb hd
  have tab:=chain_values a b a d ha hb ha hd
  have total:=source_totals a b a d ha hb ha hd
  have hE : 0≤E := by have h:=(tab.1 0).1; omega
  have hN : 0≤N := by have h:=tab.1 0; omega
  have hfzero : (l.map f).sum=0 := (hp.map f).sum_eq.trans total.1
  have hrawzero : (l.map g).sum= -E := (hp.map g).sum_eq.trans total.2.1
  have hear : g k=E := total.2.2
  have positive (r : Fin 4) (i : ℕ) (hi : i∈P r) : 0≤f i ∧ 0≤g i := by
    have hh:=banks_good a b d m early ha hb hd r i hi
    have hs:=source_signs a b a d ha hb ha hd i hh.1
    rw [if_neg hh.2] at hs
    exact ⟨hs.1.le,hs.2.le⟩
  have cp (r : Fin 4) : 0≤2*p r-pn r := by
    apply charge_sum f g (P r)
    intro i hi
    exact label_charge a b d ha hb hd i (banks_good a b d m early ha hb hd r i hi).1
  have htbound (r : Fin 4) : T r<k := by
    cases early <;> fin_cases r <;> dsimp [T,terminals,k,size] <;> omega
  have cq (r : Fin 4) : 0≤2*q r-qn r := label_charge a b d ha hb hd (T r) (htbound r)
  have ototal : p 0+q 0+p 1+q 1+p 2+q 2+p 3+q 3=0 := by
    simpa [l,word,p,q,P,T,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
      List.map_nil,List.sum_nil,add_assoc] using hfzero
  have ntotal : pn 0+qn 0+pn 1+qn 1+pn 2+qn 2+pn 3+qn 3= -E := by
    simpa [l,word,pn,qn,P,T,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
      List.map_nil,List.sum_nil,add_assoc] using hrawzero
  let x : ℤ:=2^a
  let y : ℤ:=2^b
  let t : ℤ:=2^d
  let eta : ℤ:=2^(a-b)
  have bv : base a b a d=![A x y,B x y t,L x t,K x y t] := by
    funext r; fin_cases r <;> dsimp [base,A,B,L,K,C,x,y,t] <;> ring
  have nv : newBase a b a d=![2*A x y,SU x y t,SV x t,SW x y t] := by
    funext r; fin_cases r <;> dsimp [newBase,charge,base,A,B,L,K,C,SU,SV,SW,x,y,t] <;> ring
  have hmasses (side : Bool) :
      (fun r => ((rawBanks a b d m r).map (if side then g else f)).sum)=
      let F:=if side then newBase a b a d else base a b a d
      ![(full a b a d 0:ℤ)*F 0+(m:ℤ)*F 3,
        ((full a b a d 3:ℤ)-m)*F 3,
        (full a b a d 2:ℤ)*F 2+(vMask a b:ℤ)*F 1,
        ((full a b a d 1:ℤ)-vMask a b)*F 1] := by
    apply raw_masses a b d m ha hb hba hm
    intro r e he
    cases side
    · exact (tab.2.1 r e (by omega)).trans (if_pos (by omega))
    · exact (tab.2.2.1 r e (by omega)).trans (if_pos (by omega))
  have cu:=twice_full a b d 0 (by simp [chainLength]; omega)
  have cv:=twice_full a b d 1 (by simp [chainLength]; omega)
  have cw:=twice_full a b d 2 (by simp [chainLength]; omega)
  have cx:=twice_full a b d 3 (by simp [chainLength]; omega)
  have cn : 2*(vMask a b:ℤ)=eta := by
    have he : 2*(2:ℤ)^(a-b-1)=(2:ℤ)^(a-b) := by
      calc
        2*(2:ℤ)^(a-b-1)=(2:ℤ)^((a-b-1)+1) := by rw [pow_succ]; ring
        _ = (2:ℤ)^(a-b) := by congr 1; omega
    simpa only [vMask,eta,Nat.cast_pow,Nat.cast_ofNat] using he
  simp only [chainLength,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three] at cu cv cw cx
  change 2*(full a b a d 0:ℤ)=t-2 at cu
  change 2*(full a b a d 1:ℤ)=x-2 at cv
  change 2*(full a b a d 2:ℤ)=y-2 at cw
  change 2*(full a b a d 3:ℤ)=x-2 at cx
  let op : Fin 4→ℤ:=![(t-2)*A x y+2*m*K x y t,(x-2-2*m)*K x y t,
    (y-2)*L x t+eta*B x y t,(x-2-eta)*B x y t]
  let np : Fin 4→ℤ:=![2*(t-2)*A x y+2*m*SW x y t,(x-2-2*m)*SW x y t,
    (y-2)*SV x t+eta*SU x y t,(x-2-eta)*SU x y t]
  have odm (r : Fin 4) : 2*((rawBanks a b d m r).map f).sum=op r := by
    have hh:=congrFun (hmasses false) r
    simp only [Bool.false_eq_true,ite_false,bv] at hh
    have hcu:=congrArg (fun z : ℤ => z*A x y) cu
    have hcx:=congrArg (fun z : ℤ => z*K x y t) cx
    have hcw:=congrArg (fun z : ℤ => z*L x t) cw
    have hcv:=congrArg (fun z : ℤ => z*B x y t) cv
    have hcn:=congrArg (fun z : ℤ => z*B x y t) cn
    fin_cases r <;> dsimp [op] at hh ⊢ <;> nlinarith only [hh,hcu,hcx,hcw,hcv,hcn]
  have ndm (r : Fin 4) : 2*((rawBanks a b d m r).map g).sum=np r := by
    have hh:=congrFun (hmasses true) r
    simp only [ite_true,nv] at hh
    have hcu:=congrArg (fun z : ℤ => z*(2*A x y)) cu
    have hcx:=congrArg (fun z : ℤ => z*SW x y t) cx
    have hcw:=congrArg (fun z : ℤ => z*SV x t) cw
    have hcv:=congrArg (fun z : ℤ => z*SU x y t) cv
    have hcn:=congrArg (fun z : ℤ => z*SU x y t) cn
    fin_cases r <;> dsimp [np] at hh ⊢ <;> nlinarith only [hh,hcu,hcx,hcw,hcv,hcn]
  have native (r : Fin 4) :
      2*f (![d-1,d+a-1,d+a+b-1,a+b+a+d-1] r)=
        (![B x y t,L x t,K x y t,A x y] : Fin 4→ℤ) r-N ∧
      2*g (![d-1,d+a-1,d+a+b-1,a+b+a+d-1] r)=
        (![SU x y t,SV x t,SW x y t,A x y] : Fin 4→ℤ) r-(2*N+1) := by
    have hn:=native_masses a b a d ha hb ha hd r
    dsimp only at hn
    have he : chainStart b a d r+(chainLength a b a d r-1)=
        (![d-1,d+a-1,d+a+b-1,a+b+a+d-1] : Fin 4→ℕ) r := by
      fin_cases r <;> dsimp [chainStart,chainLength] <;> omega
    rw [he] at hn
    fin_cases r
    all_goals first
      | simpa [f,g,N,nextBase,nextNewBase,bv,nv] using And.intro hn.2.2.1 hn.2.2.2
  have j0:=native 0; have j1:=native 1; have j2:=native 2; have j3:=native 3
  have o0:=odm 0; have o1:=odm 1; have o2:=odm 2; have o3:=odm 3
  have n0:=ndm 0; have n1:=ndm 1; have n2:=ndm 2; have n3:=ndm 3
  have hEeq : E=A x y := congrFun bv 0
  have hNeq : N=x*x*y*t-1 := by dsimp [N,sourceMod,x,y,t]; ring
  have hxe : x=eta*y := by dsimp [x,eta,y]; rw [←pow_add,Nat.sub_add_cancel (by omega : b≤a)]
  have actualMargins : ∀ i : Fin 6, 0≤mixed p q pn qn E N early i := by
    intro i
    have hwi:=hw i
    change 0≤gates x y t eta m early i at hwi
    have he : mixed p q pn qn E N early i=gates x y t eta m early i := by
      cases early <;> fin_cases i
      all_goals dsimp [p,q,pn,qn,P,T,banks,terminals,mixed,heads,seams,withFresh,gates]
      all_goals dsimp [op,np] at o0 o1 o2 o3 n0 n1 n2 n3 j0 j1 j2 j3
      all_goals simp only [hEeq,hNeq] at j0 j1 j2 j3 ⊢
      all_goals dsimp [A,B,L,K,C,SU,SV,SW] at o0 o1 o2 o3 n0 n1 n2 n3 j0 j1 j2 j3 ⊢
      · linear_combination -o2
      · linear_combination n2+j1.2
      · linear_combination -o2-j1.1-o3
      · linear_combination n2+j1.2+n3+j2.2
      · linear_combination -o2-j1.1-o3-j2.1-o0
      · linear_combination n2+j1.2+n3+j2.2+n0+j3.2
      · linear_combination -o0
      · linear_combination n0+j3.2
      · linear_combination o0+j3.1+o1+j0.1
      · linear_combination -n0-j3.2-n1
      · linear_combination o0+j3.1+o1+j0.1+o2+j1.1
      · linear_combination -n0-j3.2-n1-j0.2-n2
    rw [he]
    exact hwi
  have checks:=complete_checks p q pn qn E N early cp cq ototal ntotal actualMargins
  have cs0:=checks 0; have cs1:=checks 1; have cs2:=checks 2
  have oldlast : 0≤ -q 3 ∧ -q 3≤N/2 := by
    cases early
    · have hbnd:=tab.1 1
      change 0≤ -f (d-1) ∧ -f (d-1)≤N/2
      have hn:=j0.1
      dsimp at hn
      have hB : 1≤B x y t ∧ B x y t<N := by simpa [bv] using hbnd
      omega
    · have hbnd:=tab.1 3
      change 0≤ -f (d+a+b-1) ∧ -f (d+a+b-1)≤N/2
      have hn:=j2.1
      dsimp at hn
      have hK : 1≤K x y t ∧ K x y t<N := by simpa [bv] using hbnd
      omega
  have newlast : 0≤ -qn 3 ∧ -qn 3≤N := by
    cases early
    · have hbnd:=new_base_bounds a b a d ha hb ha hd 1
      change 0≤ -g (d-1) ∧ -g (d-1)≤N
      have hn:=j0.2
      dsimp at hn
      have hB : 1≤SU x y t ∧ SU x y t<2*N+1 := by simpa [nv] using hbnd
      omega
    · have hbnd:=new_base_bounds a b a d ha hb ha hd 3
      change 0≤ -g (d+a+b-1) ∧ -g (d+a+b-1)≤N
      have hn:=j2.2
      dsimp at hn
      have hK : 1≤SW x y t ∧ SW x y t<2*N+1 := by simpa [nv] using hbnd
      omega
  have oldstrip : InStrip f (N/2) 0 l := by
    apply four_strip f (P 0) (P 1) (P 2) (P 3) (T 0) (T 1) (T 2) (T 3) (N/2) 0
      (fun i hi => (positive 0 i hi).1) (fun i hi => (positive 1 i hi).1)
      (fun i hi => (positive 2 i hi).1) (fun i hi => (positive 3 i hi).1) le_rfl
    · simpa [heads,seams,p,q,zero_add] using And.intro cs0.1 cs0.2.1
    · simpa [heads,seams,p,q,zero_add] using And.intro cs1.1 cs1.2.1
    · simpa [heads,seams,p,q,zero_add] using And.intro cs2.1 cs2.2.1
    · exact oldlast
    · simpa [l,word,P,T,zero_add] using hfzero
  have newmass (r : Fin 4) : ((Pn r).map g).sum=withFresh pn E early r := by
    cases early <;> fin_cases r <;> simp [Pn,newBanks,withFresh,pn,P,hear,k,add_comm]
  have newpositive (r : Fin 4) (i : ℕ) (hi : i∈Pn r) : 0≤g i := by
    cases early <;> fin_cases r <;> dsimp [Pn,newBanks] at hi
    all_goals try simp only [List.mem_cons] at hi
    all_goals first
      | exact (positive _ i hi).2
      | (rcases hi with rfl|hi
         · rw [hear]; exact hE
         · exact (positive _ i hi).2)
  have newzero : ((enlarged a b d m early).map g).sum=0 := by
    have hs : ((enlarged a b d m early).map g).sum=E+(l.map g).sum := by
      cases early <;> simp [enlarged,newBanks,l,word,P,T,hear,k,List.map_append,
        List.sum_append,List.map_cons,List.sum_cons] <;> ring
    rw [hs,hrawzero]; omega
  have newstrip : InStrip g N 0 (enlarged a b d m early) := by
    apply four_strip g (Pn 0) (Pn 1) (Pn 2) (Pn 3) (T 0) (T 1) (T 2) (T 3) N 0
      (newpositive 0) (newpositive 1) (newpositive 2) (newpositive 3) le_rfl
    · simpa [heads,seams,qn,zero_add,←newmass] using And.intro cs0.2.2.1 cs0.2.2.2
    · simpa [heads,seams,qn,zero_add,←newmass] using And.intro cs1.2.2.1 cs1.2.2.2
    · simpa [heads,seams,qn,zero_add,←newmass] using And.intro cs2.2.2.1 cs2.2.2.2
    · exact newlast
    · simpa [enlarged,Pn,T,zero_add] using newzero
  apply (actual_nat_joint_iff a b a d ha hb ha hd).mpr
  refine ⟨l,hp,oldstrip,freshCut a b d m early,cut_bound a b d m early ha hb hd,?_⟩
  rw [literal_ear]
  exact newstrip

end D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum
