/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/Physical
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Physical original orders from exact paired equal-tail seam windows and a literal fresh cut. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Masses
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule

/-! The two ear modes use the same unchanged old permutation and source. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
open SourceWidth PeriodicShortening RunFirstEarTransport
open private Submask from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Dilation
open private bank terminal word bank_inventory bank_good from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Source
open private bank_masses from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Masses
open private sourceMod charge nextBase nextNewBase chain_values source_signs source_totals new_base_bounds from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size base newBase chainLength chainStart oldValue newValue negatives)
open private native_masses from
  D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native
open private four_strip from
  D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (insertAt)
open private actual_nat_joint_iff from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint

private def oldSeams (a b c alpha M v J : ℕ) : Fin 3 → ℤ :=
  let F := base a b c c
  ![((alpha:ℤ)+1)*F 3-((M:ℤ)+1)*F 2,
    F 0+(v:ℤ)*F 1-((J:ℤ)+1)*F 2,
    ((v:ℤ)+1)*F 1-((J:ℤ)+1)*F 2]
private def newSeams (a b c alpha M v J : ℕ) (early : Bool) : Fin 3 → ℤ :=
  let F := newBase a b c c
  let A := base a b c c 0
  ![(if early then A else 0)+((alpha:ℤ)+1)*F 3-((M:ℤ)+1)*F 2,
    2*A+(v:ℤ)*F 1-((J:ℤ)+1)*F 2,
    ((v:ℤ)+1)*F 1-((J:ℤ)+1)*F 2]
private def seamWindows (a b c alpha M v J : ℕ) (early : Bool) : Prop :=
  ∀ i : Fin 3,
    0 ≤ 2*oldSeams a b c alpha M v J i ∧
    2*oldSeams a b c alpha M v J i ≤
      ![base a b c c 3,base a b c c 0,base a b c c 1] i-1 ∧
    0 ≤ 2*newSeams a b c alpha M v J early i ∧
    2*newSeams a b c alpha M v J early i ≤
      ![newBase a b c c 3,base a b c c 0,newBase a b c c 1] i-1

set_option maxHeartbeats 2500000 in
private theorem physical_joint (a b c alpha M v J : ℕ) (early : Bool)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (haCap : alpha < 2^(a-1)) (hmCap : M < 2^(b-1)) (hvCap : v < 2^(c-1))
    (hj : Submask J M) (hw : seamWindows a b c alpha M v J early) :
    ∃ sigma : List (Fin (a+b+c+c)), ∃ cut : ℕ, cut ≤ a+b+c+c ∧
      OriginalOrder (a+b+c+c) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+c+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+c) sigma cut) := by
  classical
  let k := a+b+c+c
  let N := sourceMod a b c c
  let A := base a b c c 0
  let B := base a b c c 1
  let L := base a b c c 2
  let K := base a b c c 3
  let SU := newBase a b c c 1
  let SV := newBase a b c c 2
  let SW := newBase a b c c 3
  let P := bank a b c alpha M v J
  let T := terminal a b c
  let l := word a b c alpha M v J
  let f := oldValue a b c c
  let g := newValue a b c c
  let C := fun n : ℕ => ((2^(n-1)-1:ℕ):ℤ)
  let e0 : ℤ := if early then A else 0
  let e1 : ℤ := if early then 0 else A
  let Pn : Fin 4 → List ℕ :=
    ![(if early then [k] else [])++P 0,
      (if early then [] else [k])++P 1,P 2,P 3]
  let ln := Pn 0 ++ T 0 :: Pn 1 ++ T 1 :: Pn 2 ++ T 2 :: Pn 3 ++ [T 3]
  let cut := if early then 0 else (P 0).length+1
  have headd : e0+e1=A := by cases early <;> simp [e0,e1]
  have hp : l.Perm (List.range k) := bank_inventory a b c alpha M v J ha hb hc hj
  have basevec : base a b c c = ![A,B,L,K] := by
    funext i
    fin_cases i <;> rfl
  have newvec : newBase a b c c = ![2*A,SU,SV,SW] := by
    funext i
    fin_cases i
    · dsimp [newBase,charge,A]; ring
    · rfl
    · rfl
    · rfl
  have mo := bank_masses a b c alpha M v J ha hb hc haCap hmCap hvCap hj false
  have mn := bank_masses a b c alpha M v J ha hb hc haCap hmCap hvCap hj true
  change ((P 0).map f).sum=(C b-M)*L+alpha*K ∧
    ((P 1).map f).sum=(C a-alpha)*K+(M-J)*L+v*B ∧
    ((P 2).map f).sum=C c*A ∧ ((P 3).map f).sum=(C c-v)*B+J*L at mo
  change ((P 0).map g).sum=(C b-M)*SV+alpha*SW ∧
    ((P 1).map g).sum=(C a-alpha)*SW+(M-J)*SV+v*SU ∧
    ((P 2).map g).sum=C c*(2*A) ∧ ((P 3).map g).sum=(C c-v)*SU+J*SV at mn
  have nt0 := native_masses a b c c ha hb hc hc 0
  have nt1 := native_masses a b c c ha hb hc hc 1
  have nt2 := native_masses a b c c ha hb hc hc 2
  have nt3 := native_masses a b c c ha hb hc hc 3
  have eu : 0+(c-1)=T 2 := by dsimp [T,terminal]; omega
  have ev : c+(c-1)=T 3 := by dsimp [T,terminal]; omega
  have ew : c+c+(b-1)=T 0 := by dsimp [T,terminal]; omega
  have ex : c+c+b+(a-1)=T 1 := by dsimp [T,terminal]; omega
  simp only [chainLength,chainStart,nextBase,nextNewBase,basevec,newvec,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,
    Matrix.vecTail,Function.comp_apply,eu,ev,ew,ex] at nt0 nt1 nt2 nt3
  change C c*A+f (T 2)=B-A ∧ C c*(2*A)+g (T 2)=SU-2*A ∧
    2*f (T 2)=B-N ∧ 2*g (T 2)=SU-(2*N+1) at nt0
  change C c*B+f (T 3)=L-B ∧ C c*SU+g (T 3)=SV-SU ∧
    2*f (T 3)=L-N ∧ 2*g (T 3)=SV-(2*N+1) at nt1
  change C b*L+f (T 0)=K-L ∧ C b*SV+g (T 0)=SW-SV ∧
    2*f (T 0)=K-N ∧ 2*g (T 0)=SW-(2*N+1) at nt2
  change C a*K+f (T 1)=A-K ∧ C a*SW+g (T 1)=A-SW ∧
    2*f (T 1)=A-N ∧ 2*g (T 1)=A-(2*N+1) at nt3
  have w0 := hw 0
  have w1 := hw 1
  have w2 := hw 2
  change 0 ≤ 2*(((alpha:ℤ)+1)*K-((M:ℤ)+1)*L) ∧
    2*(((alpha:ℤ)+1)*K-((M:ℤ)+1)*L) ≤ K-1 ∧
    0 ≤ 2*(e0+((alpha:ℤ)+1)*SW-((M:ℤ)+1)*SV) ∧
    2*(e0+((alpha:ℤ)+1)*SW-((M:ℤ)+1)*SV) ≤ SW-1 at w0
  change 0 ≤ 2*(A+(v:ℤ)*B-((J:ℤ)+1)*L) ∧
    2*(A+(v:ℤ)*B-((J:ℤ)+1)*L) ≤ A-1 ∧
    0 ≤ 2*(2*A+(v:ℤ)*SU-((J:ℤ)+1)*SV) ∧
    2*(2*A+(v:ℤ)*SU-((J:ℤ)+1)*SV) ≤ A-1 at w1
  change 0 ≤ 2*(((v:ℤ)+1)*B-((J:ℤ)+1)*L) ∧
    2*(((v:ℤ)+1)*B-((J:ℤ)+1)*L) ≤ B-1 ∧
    0 ≤ 2*(((v:ℤ)+1)*SU-((J:ℤ)+1)*SV) ∧
    2*(((v:ℤ)+1)*SU-((J:ℤ)+1)*SV) ≤ SU-1 at w2
  have os0 : ((P 0).map f).sum+f (T 0)=((alpha:ℤ)+1)*K-((M:ℤ)+1)*L := by
    nlinarith only [mo.1,nt2.1]
  have os1 : ((P 0).map f).sum+f (T 0)+((P 1).map f).sum+f (T 1)=
      A+(v:ℤ)*B-((J:ℤ)+1)*L := by
    nlinarith only [os0,mo.2.1,nt3.1]
  have os2 : ((P 0).map f).sum+f (T 0)+((P 1).map f).sum+f (T 1)+
      ((P 2).map f).sum+f (T 2)=((v:ℤ)+1)*B-((J:ℤ)+1)*L := by
    nlinarith only [os1,mo.2.2.1,nt0.1]
  have totals := source_totals a b c c ha hb hc hc
  have hfzero : (l.map f).sum=0 := (hp.map f).sum_eq.trans totals.1
  have hear : g k=A := totals.2.2
  have hgzero : A+(l.map g).sum=0 := by
    have h := (hp.map g).sum_eq.trans totals.2.1
    change (l.map g).sum=-A at h
    omega
  have pos (j : Fin 4) (i : ℕ) (hi : i∈P j) : 0 ≤ f i ∧ 0 ≤ g i := by
    have good := bank_good a b c alpha M v J ha hb hc j i hi
    have h := source_signs a b c c ha hb hc hc i good.1
    rw [if_neg good.2] at h
    exact ⟨h.1.le,h.2.le⟩
  have hbases := (chain_values a b c c ha hb hc hc).1
  have hA : 1 ≤ A := (hbases 0).1
  have hL : 1 ≤ L ∧ L<N := hbases 2
  have hSV : 1 ≤ SV ∧ SV<2*N+1 := new_base_bounds a b c c ha hb hc hc 2
  have oldstrip : InStrip f (N/2) 0 l := by
    change InStrip f (N/2) 0 (P 0 ++ T 0 :: P 1 ++ T 1 :: P 2 ++ T 2 :: P 3 ++ [T 3])
    apply four_strip f (P 0) (P 1) (P 2) (P 3) (T 0) (T 1) (T 2) (T 3) (N/2) 0
      (fun i hi => (pos 0 i hi).1) (fun i hi => (pos 1 i hi).1)
      (fun i hi => (pos 2 i hi).1) (fun i hi => (pos 3 i hi).1) le_rfl
    · constructor <;> nlinarith only [os0,nt2.2.2.1,w0.1,w0.2.1,
        Int.emod_nonneg N (by decide : (2:ℤ)≠0),Int.emod_lt_of_pos N (by decide : (0:ℤ)<2),
        Int.emod_add_mul_ediv N 2]
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · simpa only [l,word,P,T,zero_add] using hfzero
  have nsum0 : ((Pn 0).map g).sum=e0+((P 0).map g).sum := by
    cases early <;> simp [Pn,e0,hear]
  have nsum1 : ((Pn 1).map g).sum=e1+((P 1).map g).sum := by
    cases early <;> simp [Pn,e1,hear]
  have ns0 : ((Pn 0).map g).sum+g (T 0)=e0+((alpha:ℤ)+1)*SW-((M:ℤ)+1)*SV := by
    nlinarith only [nsum0,mn.1,nt2.2.1]
  have ns1 : ((Pn 0).map g).sum+g (T 0)+((Pn 1).map g).sum+g (T 1)=
      2*A+(v:ℤ)*SU-((J:ℤ)+1)*SV := by
    nlinarith only [ns0,nsum1,mn.2.1,nt3.2.1,headd]
  have ns2 : ((Pn 0).map g).sum+g (T 0)+((Pn 1).map g).sum+g (T 1)+
      ((P 2).map g).sum+g (T 2)=((v:ℤ)+1)*SU-((J:ℤ)+1)*SV := by
    nlinarith only [ns1,mn.2.2.1,nt0.2.1]
  have lnzero : (ln.map g).sum=0 := by
    have eqsum : (ln.map g).sum=A+(l.map g).sum := by
      dsimp [ln]
      simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons,
        List.map_nil,List.sum_nil,add_zero]
      rw [nsum0,nsum1]
      simp [Pn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
      simp only [l,word,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
        List.map_nil,List.sum_nil,add_zero]
      linarith only [headd]
    rw [eqsum]
    exact hgzero
  have npos (j : Fin 4) (i : ℕ) (hi : i∈Pn j) : 0 ≤ g i := by
    fin_cases j <;> cases early <;> simp [Pn] at hi
    all_goals first
      | exact (pos _ i hi).2
      | rcases hi with rfl|hi
    all_goals first | (rw [hear]; omega) | exact (pos _ i hi).2
  have newstrip : InStrip g N 0 ln := by
    apply four_strip g (Pn 0) (Pn 1) (P 2) (P 3) (T 0) (T 1) (T 2) (T 3) N 0
      (npos 0) (npos 1) (fun i hi => (pos 2 i hi).2)
      (fun i hi => (pos 3 i hi).2) le_rfl
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · simpa [ln,Pn,zero_add] using lnzero
  have hcut : cut ≤ k := by
    have hlen : l.length = k := by
      have h := hp.length_eq
      simpa only [List.length_range] using h
    have hpre : (P 0).length + 1 ≤ l.length := by
      dsimp [P,l,word]
      simp only [List.length_append,List.length_cons,List.length_singleton]
      omega
    have hP0 : (P 0).length + 1 ≤ k := by omega
    dsimp [cut]
    split_ifs
    · omega
    · exact hP0
  have hinsert : insertAt k l cut=ln := by
    cases early
    · let pre := P 0++[T 0]
      let post := P 1++T 1::P 2++T 2::P 3++[T 3]
      have hl : l=pre++post := by simp [l,word,pre,post,P,T,List.append_assoc]
      have hcl : cut=pre.length := by simp [cut,pre]
      rw [hl,hcl]
      change insertAt k (pre ++ post) (pre.length + 0) = _
      unfold insertAt
      rw [List.take_length_add_append, List.drop_length_add_append]
      simp [pre,post,ln,Pn,List.append_assoc]
    · simp [cut,insertAt,ln,Pn,l,word,P,T]
  apply (actual_nat_joint_iff a b c c ha hb hc hc).mpr
  refine ⟨l,hp,oldstrip,cut,hcut,?_⟩
  have hfinal : InStrip g N 0 (insertAt k l cut) := by
    rw [hinsert]
    exact newstrip
  simpa [size,k] using hfinal

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
