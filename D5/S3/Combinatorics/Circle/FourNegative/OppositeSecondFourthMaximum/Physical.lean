/- GID: D5/S3/Combinatorics/Circle/FourNegative/OppositeSecondFourthMaximum/Physical
   generality: I
   mirror-B: none(waiver:private-consumed-original-label-construction)
   mirror-E: none(waiver:private-consumed-original-label-construction)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Complementary original U/W masks and a fresh label immediately before the X terminal. -/
import D5.S3.Combinatorics.Circle.FourNegative.OppositeSecondFourthMaximum.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.OppositeSecondFourthMaximum
open SourceWidth PeriodicShortening RunFirstEarTransport
open private A B L K SU SV SW window oldSeams newSeams oldHeads newHeads Windows from
  D5.S3.Combinatorics.Circle.FourNegative.OppositeSecondFourthMaximum.Arithmetic
open private full stock complement stock_split canonical_inventory stock_good stock_mass complement_mass
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open private size base newBase charge sourceMod oldValue newValue negatives chainLength chainStart
  nextBase nextNewBase source_totals chain_values source_signs new_base_bounds from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private native_masses from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private four_strip from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (insertAt)
open private actual_nat_joint_iff from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint

private def rawBanks (a s c m n : ℕ) : Fin 4 → List ℕ :=
  ![complement a s c s 0 m,
    stock a s c s 0 m ++ stock a s c s 1 (full a s c s 1),
    complement a s c s 2 n,
    stock a s c s 2 n ++ stock a s c s 3 (full a s c s 3)]

private theorem raw_masses (a s c m n : ℕ)
    (hm : m<2^(s-1)) (hn : n<2^(s-1))
    (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a s c s r-1,
      f (chainStart s c s r+e)=2^e*F r) :
    (fun r => (((rawBanks a s c m n) r).map f).sum)=
      ![((full a s c s 0:ℤ)-m)*F 0,
        m*F 0+(full a s c s 1:ℤ)*F 1,
        ((full a s c s 2:ℤ)-n)*F 2,
        n*F 2+(full a s c s 3:ℤ)*F 3] := by
  have cap (r : Fin 4) : full a s c s r<2^(chainLength a s c s r-1) := by
    dsimp [full];have := Nat.two_pow_pos (chainLength a s c s r-1);omega
  have hm' : m<2^(chainLength a s c s 0-1) := by simpa [chainLength] using hm
  have hn' : n<2^(chainLength a s c s 2-1) := by simpa [chainLength] using hn
  have h0 := complement_mass a s c s 0 m hm' f F hf
  have h1 := stock_mass a s c s 0 m hm' f F hf
  have h2 := complement_mass a s c s 2 n hn' f F hf
  have h3 := stock_mass a s c s 2 n hn' f F hf
  have hv := stock_mass a s c s 1 _ (cap 1) f F hf
  have hx := stock_mass a s c s 3 _ (cap 3) f F hf
  funext r
  fin_cases r <;> dsimp [rawBanks]
  all_goals simp only [List.map_append,List.sum_append,h0,h1,h2,h3,hv,hx]

private theorem physical_joint (a s c m n : ℕ) (rev : Bool)
    (ha : 2≤a) (hs : 2≤s) (hc : 2≤c)
    (hm : m<2^(s-1)) (hn : n<2^(s-1))
    (hw : Windows (2^a) (2^s) (2^c) m n rev) :
    ∃ sigma : List (Fin (a+s+c+s)), ∃ j : ℕ, j≤a+s+c+s ∧
      OriginalOrder (a+s+c+s) (1+2^a+2^(a+s)+2^(a+s+c)) sigma ∧
      OriginalOrder (a+s+c+s+1) (2*(1+2^a+2^(a+s)+2^(a+s+c)))
        (earWord (a+s+c+s) sigma j) := by
  classical
  let k := a+s+c+s
  let N := sourceMod a s c s
  let AA := A (2^a) (2^s) (2^c)
  let BB := B (2^a) (2^s) (2^c)
  let LL := L (2^a) (2^s) (2^c)
  let KK := K (2^a) (2^s) (2^c)
  let UU := SU (2^a) (2^s) (2^c)
  let VV := SV (2^a) (2^s) (2^c)
  let WW := SW (2^a) (2^s) (2^c)
  let f := oldValue a s c s
  let g := newValue a s c s
  let R := rawBanks a s c m n
  let P : Fin 4→List ℕ := if rev then ![R 2,R 3,R 0,R 1] else R
  let T : Fin 4→ℕ := if rev then ![s+c+s-1,k-1,s-1,s+c-1]
    else ![s-1,s+c-1,s+c+s-1,k-1]
  let l := P 0 ++ T 0 :: P 1 ++ T 1 :: P 2 ++ T 2 :: P 3 ++ [T 3]
  let Pn : Fin 4→List ℕ := if rev then ![P 0,P 1++[k],P 2,P 3]
    else ![P 0,P 1,P 2,P 3++[k]]
  let ln := Pn 0 ++ T 0 :: Pn 1 ++ T 1 :: Pn 2 ++ T 2 :: Pn 3 ++ [T 3]
  let pre := if rev then P 0++[T 0]++P 1
    else P 0++[T 0]++P 1++[T 1]++P 2++[T 2]++P 3
  let post := if rev then T 1::P 2++T 2::P 3++[T 3] else [T 3]
  let cut := pre.length
  have hl : l=pre++post := by cases rev <;> simp [l,pre,post,List.append_assoc]
  have hp : l.Perm (List.range k) := by
    have hu := Multiset.coe_eq_coe.mpr (stock_split a s c s 0 m)
    have hw' := Multiset.coe_eq_coe.mpr (stock_split a s c s 2 n)
    simp only [←Multiset.coe_add] at hu hw'
    apply Multiset.coe_eq_coe.mp
    rw [show k=a+s+c+s by rfl,←canonical_inventory a s c s ha hs hc hs]
    simp only [←Multiset.coe_add,Multiset.coe_singleton]
    rw [←hu,←hw']
    cases rev <;> dsimp [l,P,T,R,rawBanks,k]
    all_goals simp only [←Multiset.coe_add,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_singleton]
    all_goals ac_rfl
  have basevec : base a s c s=![AA,BB,LL,KK] := by
    funext r
    fin_cases r <;> dsimp [base,AA,BB,LL,KK,A,B,L,K] <;> ring
  have newvec : newBase a s c s=![2*AA,UU,VV,WW] := by
    funext r
    fin_cases r <;> simp only [newBase,charge,basevec,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    all_goals dsimp [AA,BB,LL,KK,UU,VV,WW,A,B,L,K,SU,SV,SW]
    all_goals ring
  have cv := chain_values a s c s ha hs hc hs
  have oldpos (r : Fin 4) (e : ℕ) (he : e<chainLength a s c s r-1) :
      f (chainStart s c s r+e)=2^e*base a s c s r := by
    simpa only [if_pos (show e+1<chainLength a s c s r by omega)] using
      cv.2.1 r e (by omega)
  have newpos (r : Fin 4) (e : ℕ) (he : e<chainLength a s c s r-1) :
      g (chainStart s c s r+e)=2^e*newBase a s c s r := by
    simpa only [if_pos (show e+1<chainLength a s c s r by omega)] using
      cv.2.2.1 r e (by omega)
  have mo := raw_masses a s c m n hm hn f (base a s c s) oldpos
  have mn := raw_masses a s c m n hm hn g (newBase a s c s) newpos
  rw [basevec] at mo
  rw [newvec] at mn
  have mo0 := congrFun mo 0
  have mo1 := congrFun mo 1
  have mo2 := congrFun mo 2
  have mo3 := congrFun mo 3
  have mn0 := congrFun mn 0
  have mn1 := congrFun mn 1
  have mn2 := congrFun mn 2
  have mn3 := congrFun mn 3
  have nt0 := native_masses a s c s ha hs hc hs 0
  have nt1 := native_masses a s c s ha hs hc hs 1
  have nt2 := native_masses a s c s ha hs hc hs 2
  have nt3 := native_masses a s c s ha hs hc hs 3
  change ((R 0).map f).sum=((full a s c s 0:ℤ)-m)*AA at mo0
  change ((R 1).map f).sum=m*AA+(full a s c s 1:ℤ)*BB at mo1
  change ((R 2).map f).sum=((full a s c s 2:ℤ)-n)*LL at mo2
  change ((R 3).map f).sum=n*LL+(full a s c s 3:ℤ)*KK at mo3
  change ((R 0).map g).sum=((full a s c s 0:ℤ)-m)*(2*AA) at mn0
  change ((R 1).map g).sum=m*(2*AA)+(full a s c s 1:ℤ)*UU at mn1
  change ((R 2).map g).sum=((full a s c s 2:ℤ)-n)*VV at mn2
  change ((R 3).map g).sum=n*VV+(full a s c s 3:ℤ)*WW at mn3
  have eu : 0+(s-1)=s-1 := by omega
  have ev : s+(c-1)=s+c-1 := by omega
  have ew : s+c+(s-1)=s+c+s-1 := by omega
  have ex : s+c+s+(a-1)=k-1 := by dsimp [k];omega
  simp only [chainLength,chainStart,nextBase,nextNewBase,basevec,newvec,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,
    Matrix.vecTail,Function.comp_apply,eu,ev,ew,ex] at nt0 nt1 nt2 nt3
  change (full a s c s 0:ℤ)*AA+f (s-1)=BB-AA ∧
    (full a s c s 0:ℤ)*(2*AA)+g (s-1)=UU-2*AA ∧
    2*f (s-1)=BB-N ∧ 2*g (s-1)=UU-(2*N+1) at nt0
  change (full a s c s 1:ℤ)*BB+f (s+c-1)=LL-BB ∧
    (full a s c s 1:ℤ)*UU+g (s+c-1)=VV-UU ∧
    2*f (s+c-1)=LL-N ∧ 2*g (s+c-1)=VV-(2*N+1) at nt1
  change (full a s c s 2:ℤ)*LL+f (s+c+s-1)=KK-LL ∧
    (full a s c s 2:ℤ)*VV+g (s+c+s-1)=WW-VV ∧
    2*f (s+c+s-1)=KK-N ∧ 2*g (s+c+s-1)=WW-(2*N+1) at nt2
  change (full a s c s 3:ℤ)*KK+f (k-1)=AA-KK ∧
    (full a s c s 3:ℤ)*WW+g (k-1)=AA-WW ∧
    2*f (k-1)=AA-N ∧ 2*g (k-1)=AA-(2*N+1) at nt3
  dsimp only [AA,BB,LL,KK,UU,VV,WW] at mo0 mo1 mo2 mo3 mn0 mn1 mn2 mn3 nt0 nt1 nt2 nt3
  have totals := source_totals a s c s ha hs hc hs
  have hfzero : (l.map f).sum=0 := (hp.map f).sum_eq.trans totals.1
  have hear : g k=AA := by simpa [basevec,g,k,size] using totals.2.2
  have hgzero : AA+(l.map g).sum=0 := by
    have h := (hp.map g).sum_eq.trans totals.2.1
    change (l.map g).sum= -base a s c s 0 at h
    simpa only [basevec,Matrix.cons_val_zero] using (show base a s c s 0+(l.map g).sum=0 by omega)
  have lnzero : (ln.map g).sum=0 := by
    have he : (ln.map g).sum=AA+(l.map g).sum := by
      cases rev <;> simp [ln,l,Pn,List.map_append,List.sum_append,hear] <;> ring
    rw [he];exact hgzero
  have rpos (r : Fin 4) (i : ℕ) (hi : i∈R r) : 0≤f i ∧ 0≤g i := by
    have good : i<size a s c s ∧ i∉negatives a s c s := by
      fin_cases r <;> dsimp [R,rawBanks,complement] at hi
      all_goals try (simp only [List.mem_append] at hi;rcases hi with hi|hi)
      all_goals exact stock_good a s c s ha hs hc hs _ _ i hi
    have h := source_signs a s c s ha hs hc hs i good.1
    rw [if_neg good.2] at h
    exact ⟨h.1.le,h.2.le⟩
  have pos (r : Fin 4) (i : ℕ) (hi : i∈P r) : 0≤f i ∧ 0≤g i := by
    cases rev <;> fin_cases r <;> simp only [P,Bool.false_eq_true,if_false,if_true,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] at hi
    all_goals first | exact rpos 0 i hi | exact rpos 1 i hi | exact rpos 2 i hi | exact rpos 3 i hi
  have hAA : 1≤AA := by simpa only [basevec,Matrix.cons_val_zero] using (cv.1 0).1
  have npos (r : Fin 4) (i : ℕ) (hi : i∈Pn r) : 0≤g i := by
    cases rev <;> fin_cases r <;> simp [Pn] at hi
    all_goals first | exact (pos _ i hi).2 | rcases hi with hi|rfl
    all_goals first | exact (pos _ i hi).2 | (rw [hear];omega)
  have terminal_good (r : Fin 4) : T r<size a s c s ∧ T r∈negatives a s c s := by
    cases rev <;> fin_cases r <;> simp [T,negatives,size,k] <;> omega
  have tneg (r : Fin 4) : f (T r)<0 ∧ g (T r)<0 := by
    have h := source_signs a s c s ha hs hc hs (T r) (terminal_good r).1
    simpa only [if_pos (terminal_good r).2] using h
  have td (r : Fin 4) :
      2*f (T r)=oldHeads (2^a) (2^s) (2^c) rev r-N ∧
      2*g (T r)=newHeads (2^a) (2^s) (2^c) rev r-(2*N+1) := by
    cases rev <;> fin_cases r <;> dsimp [T,oldHeads,newHeads]
    all_goals first | exact ⟨nt0.2.2.1,nt0.2.2.2⟩ | exact ⟨nt1.2.2.1,nt1.2.2.2⟩
                    | exact ⟨nt2.2.2.1,nt2.2.2.2⟩ | exact ⟨nt3.2.2.1,nt3.2.2.2⟩
  have lastpos : 1≤oldHeads (2^a) (2^s) (2^c) rev 3 ∧
      1≤newHeads (2^a) (2^s) (2^c) rev 3 := by
    cases rev
    · simpa [oldHeads,newHeads,basevec] using And.intro (cv.1 0).1 (cv.1 0).1
    · have hn' := (new_base_bounds a s c s ha hs hc hs 2).1
      simpa [oldHeads,newHeads,basevec,newvec] using And.intro (cv.1 2).1 hn'
  have os0 : ((P 0).map f).sum+f (T 0)=oldSeams (2^a) (2^s) (2^c) m n rev 0 := by
    cases rev <;> dsimp [P,T,oldSeams]
    all_goals nlinarith only [mo0,mo2,nt0.1,nt2.1]
  have os1 : ((P 0).map f).sum+f (T 0)+((P 1).map f).sum+f (T 1)=
      oldSeams (2^a) (2^s) (2^c) m n rev 1 := by
    cases rev <;> dsimp [P,T,oldSeams]
    all_goals nlinarith only [mo0,mo1,mo2,mo3,nt0.1,nt1.1,nt2.1,nt3.1]
  have os2 : ((P 0).map f).sum+f (T 0)+((P 1).map f).sum+f (T 1)+
      ((P 2).map f).sum+f (T 2)=oldSeams (2^a) (2^s) (2^c) m n rev 2 := by
    cases rev <;> dsimp [P,T,oldSeams]
    all_goals nlinarith only [mo0,mo1,mo2,mo3,nt0.1,nt1.1,nt2.1,nt3.1]
  have ns0 : ((Pn 0).map g).sum+g (T 0)=newSeams (2^a) (2^s) (2^c) m n rev 0 := by
    cases rev <;> simp only [Pn,P,T,newSeams,if_true,if_false,Bool.false_eq_true,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
      List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,hear,AA]
    all_goals nlinarith only [mn0,mn2,nt0.2.1,nt2.2.1]
  have ns1 : ((Pn 0).map g).sum+g (T 0)+((Pn 1).map g).sum+g (T 1)=
      newSeams (2^a) (2^s) (2^c) m n rev 1 := by
    cases rev <;> simp only [Pn,P,T,newSeams,if_true,if_false,Bool.false_eq_true,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
      List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,hear,AA]
    all_goals nlinarith only [mn0,mn1,mn2,mn3,nt0.2.1,nt1.2.1,nt2.2.1,nt3.2.1]
  have ns2 : ((Pn 0).map g).sum+g (T 0)+((Pn 1).map g).sum+g (T 1)+
      ((Pn 2).map g).sum+g (T 2)=newSeams (2^a) (2^s) (2^c) m n rev 2 := by
    cases rev <;> simp only [Pn,P,T,newSeams,if_true,if_false,Bool.false_eq_true,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
      List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,hear,AA]
    all_goals nlinarith only [mn0,mn1,mn2,mn3,nt0.2.1,nt1.2.1,nt2.2.1,nt3.2.1]
  have w0 := hw 0
  have w1 := hw 1
  have w2 := hw 2
  change window (oldSeams (2^a) (2^s) (2^c) m n rev 0) (oldHeads (2^a) (2^s) (2^c) rev 0) ∧
    window (newSeams (2^a) (2^s) (2^c) m n rev 0) (newHeads (2^a) (2^s) (2^c) rev 0) at w0
  change window (oldSeams (2^a) (2^s) (2^c) m n rev 1) (oldHeads (2^a) (2^s) (2^c) rev 1) ∧
    window (newSeams (2^a) (2^s) (2^c) m n rev 1) (newHeads (2^a) (2^s) (2^c) rev 1) at w1
  change window (oldSeams (2^a) (2^s) (2^c) m n rev 2) (oldHeads (2^a) (2^s) (2^c) rev 2) ∧
    window (newSeams (2^a) (2^s) (2^c) m n rev 2) (newHeads (2^a) (2^s) (2^c) rev 2) at w2
  dsimp only [window] at w0 w1 w2
  have t0 := td 0
  have t1 := td 1
  have t2 := td 2
  have t3 := td 3
  have oldstrip : InStrip f (N/2) 0 l := by
    apply four_strip f (P 0) (P 1) (P 2) (P 3) (T 0) (T 1) (T 2) (T 3) (N/2) 0
      (fun i hi => (pos 0 i hi).1) (fun i hi => (pos 1 i hi).1)
      (fun i hi => (pos 2 i hi).1) (fun i hi => (pos 3 i hi).1) le_rfl
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · have h := tneg 3;constructor <;> omega
    · simpa only [l,zero_add] using hfzero
  have newstrip : InStrip g N 0 ln := by
    apply four_strip g (Pn 0) (Pn 1) (Pn 2) (Pn 3) (T 0) (T 1) (T 2) (T 3) N 0
      (npos 0) (npos 1) (npos 2) (npos 3) le_rfl
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · have h := tneg 3;constructor <;> omega
    · simpa only [ln,zero_add] using lnzero
  have hcut : cut≤k := by
    have hlen := hp.length_eq
    rw [hl,List.length_append,List.length_range] at hlen
    dsimp [cut];omega
  have hinsert : insertAt k l cut=ln := by
    rw [hl]
    change insertAt k (pre++post) (pre.length+0)=ln
    unfold insertAt
    rw [List.take_length_add_append,List.drop_length_add_append]
    cases rev <;> simp [pre,post,ln,Pn,List.append_assoc]
  apply (actual_nat_joint_iff a s c s ha hs hc hs).mpr
  refine ⟨l,hp,oldstrip,cut,hcut,?_⟩
  change InStrip g N 0 (insertAt k l cut)
  rw [hinsert]
  exact newstrip

end D5.S3.Combinatorics.Circle.FourNegative.OppositeSecondFourthMaximum
