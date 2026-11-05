/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLowU/Constructors
   generality: I
   mirror-B: none(waiver:consumed-low-u-support)
   mirror-E: none(waiver:physical-low-u-construction)
   anchors: []
   utility: none
   digest: Original-domain low-U certificates with the actual pre-W ear slot. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Physical
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Selection
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Fallback

/-! Original-domain low-U certificates with the actual pre-W ear slot. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU
open PacketNormalForm
open private lowUBanks lowUTerminals lowUWord lowU_inventory lowU_good
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Banks
open private lowUPackets bank_nodup bank_checks rowBase rowSeams rowHeads
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Physical
open private base newBase charge sourceMod oldValue newValue from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size negatives)
open private oldMass newMass from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
open private DataCertificate DataCertificate.mk orderedPackets finiteChecks finiteEarChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (blocksWord)
open private A B L K C SU SV SW window from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Arithmetic
open private strict_select from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Selection
open private fallback_select from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Fallback

private theorem physical_certificate (a b c d u v w : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hu : u<2^(d-1)) (hv : v-1<2^(c-1)) (hw : w<2^(b-1)) (hvpos : 1≤v)
    (wins : ∀ (side : Bool) (r : Fin 4),
      0≤rowSeams a b c d u v w side r ∧
      rowSeams a b c d u v w side r≤rowHeads a b c d side r-1) :
    Nonempty (Certificate a b c d) := by
  classical
  let P := lowUBanks a b c d u v w
  let T := lowUTerminals a b c d
  let ps := lowUPackets a b c d u v w
  have checks := bank_checks a b c d u v w ha hb hc hd hu hv hw hvpos wins
  have perm (r : Fin 4) : (P r).toFinset.toList.Perm (P r) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (bank_nodup a b c d u v w r)).mpr
    intro i
    simp [P]
  have hp := lowU_inventory a b c d u v w ha hb hc hd hu hv hw
  have hneg : (ps.map Prod.snd).Perm (negatives a b c d) := by
    apply Multiset.coe_eq_coe.mp
    simp only [ps,lowUPackets,List.map_cons,List.map_nil,Prod.snd]
    dsimp [T,lowUTerminals,negatives,size]
    simp only [←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_nil]
    have ex : d+c+b+a-1=a+b+c+d-1 := by omega
    rw [ex]
    ac_rfl
  have hpos : ∀ q∈ps, ∀ i∈q.1, i<size a b c d ∧ i∉negatives a b c d := by
    intro q hq i hi
    change q∈[((P 0).toFinset,T 0),((P 1).toFinset,T 1),((P 2).toFinset,T 2),((P 3).toFinset,T 3)] at hq
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    all_goals exact lowU_good a b c d u v w ha hb hc hd hu hv hw _ i (by simpa [P] using hi)
  have hpart : (blocksWord (orderedPackets ps) : Multiset ℕ)=(List.range (size a b c d) : Multiset ℕ) := by
    have h0 := Multiset.coe_eq_coe.mpr (perm 0)
    have h1 := Multiset.coe_eq_coe.mpr (perm 1)
    have h2 := Multiset.coe_eq_coe.mpr (perm 2)
    have h3 := Multiset.coe_eq_coe.mpr (perm 3)
    have hr := Multiset.coe_eq_coe.mpr hp
    change (blocksWord [((P 0).toFinset.toList,T 0),((P 1).toFinset.toList,T 1),
      ((P 2).toFinset.toList,T 2),((P 3).toFinset.toList,T 3)] : Multiset ℕ)=_
    simp only [blocksWord,←Multiset.coe_add,←Multiset.cons_coe,←Multiset.singleton_add,Multiset.coe_nil,add_zero,h0,h1,h2,h3]
    simpa only [lowUWord,←Multiset.coe_add,Multiset.coe_singleton,P,T,size,add_assoc] using hr
  exact ⟨DataCertificate.mk ps hneg ⟨1,by decide⟩ hpos hpart checks.1 checks.2⟩

private theorem pow_half (n : ℕ) (hn : 1≤n) : (2 : ℤ)^n=2*(2 : ℤ)^(n-1) := by
  conv_lhs => rw [show n=(n-1)+1 by omega,pow_succ]
  ring

private theorem construction_I_target (a b c d : ℕ)
    (ha : 2≤a) (hab : a<b) (hbd : b<d) (hc : d+3≤c) :
    Nonempty (Certificate a b c d) := by
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let s : ℤ := 2^(d-b)
  let z : ℤ := 2^c
  have hx : 4≤x := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) ha
    norm_num at h
    exact h
  have hy : 2*x≤y := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show a+1≤b by omega)
    simpa [x,y,pow_succ,mul_comm] using h
  have hs : 2≤s := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 1≤d-b by omega)
    norm_num at h
    exact h
  have ht : (2 : ℤ)^d=s*y := by dsimp [s,y]; rw [←pow_add]; congr 1; omega
  have hz : 8*s*y≤z := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hc
    rw [pow_add] at h
    norm_num at h
    simpa [z,ht,mul_assoc,mul_comm,mul_left_comm] using h
  have gap : y=2*x ∨ y=4*x ∨ 8*x≤y := by
    by_cases h1 : b=a+1
    · left; simp [x,y,h1,pow_succ,mul_comm]
    by_cases h2 : b=a+2
    · right; left; simp [x,y,h2,pow_add]; ring
    · right; right
      have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show a+3≤b by omega)
      simpa [x,y,pow_add,mul_comm] using h
  obtain ⟨u,v,w,ueq,vpos,vbound,wbound,ho0,ho1,ho2,hn0,hn1,hn2⟩ :=
    strict_select x y s z hx hy hs hz gap
  have hu : u<2^(d-1) := by
    have hy2 : 2≤y := by omega
    have hmul := mul_le_mul_of_nonneg_left hy2 (show 0≤s by omega)
    have hhalf := pow_half d (by omega)
    have : (u : ℤ)<(2 : ℤ)^(d-1) := by nlinarith only [hmul,ueq,ht,hhalf]
    exact_mod_cast this
  have hv : v-1<2^(c-1) := by
    have hhalf := pow_half c (by omega)
    have : (v : ℤ)<(2 : ℤ)^(c-1) := by dsimp [z] at vbound; omega
    exact_mod_cast (show ((v-1 : ℕ) : ℤ)<(2 : ℤ)^(c-1) by omega)
  have hw : w<2^(b-1) := by
    have hhalf := pow_half b (by omega)
    have : (w : ℤ)<(2 : ℤ)^(b-1) := by dsimp [y] at wbound; omega
    exact_mod_cast this
  have identify (side : Bool) : rowBase a b c d side=
      if side then ![2*A x y z,SU x y s,SV x y s z,SW y s z]
      else ![A x y z,B x y s,L x y s z,K y s z] := by
    funext r
    cases side <;> fin_cases r <;> dsimp [rowBase,newBase,base,charge,A,B,L,K,SU,SV,SW,C]
    all_goals try simp only [ht]
    all_goals try dsimp [x,y,z]
    all_goals ring
  have hb0 : base a b c d 0=A x y z := by
    have h := congrFun (identify false) 0
    exact h
  apply physical_certificate a b c d u v w ha (by omega) (by omega) (by omega) hu hv hw vpos
  intro side r
  cases side <;> fin_cases r
  all_goals simp only [rowSeams,rowHeads,identify,hb0,ite_true,ite_false,Bool.false_eq_true]
  all_goals simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals first
    | exact ⟨by nlinarith only [ho0.1],by nlinarith only [ho0.2]⟩
    | exact ⟨by nlinarith only [ho1.1],by nlinarith only [ho1.2]⟩
    | exact ⟨by nlinarith only [ho2.1],by nlinarith only [ho2.2]⟩
    | exact ⟨by nlinarith only [hn0.1],by nlinarith only [hn0.2]⟩
    | exact ⟨by nlinarith only [hn1.1],by nlinarith only [hn1.2]⟩
    | exact ⟨by nlinarith only [hn2.1],by nlinarith only [hn2.2]⟩
    | constructor <;> first | omega | (dsimp [B,SU,x,y,s]; ring_nf; positivity)

private theorem construction_II_target (d : ℕ) (hd : 4≤d) :
    Nonempty (Certificate 2 3 (d+2) d) := by
  let s : ℤ := 2^(d-3)
  have hs : 2≤s := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 1≤d-3 by omega)
    norm_num at h
    exact h
  have gap : s=2 ∨ 4≤s := by
    by_cases h : d=4
    · left; simp [s,h]
    · right
      have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 2≤d-3 by omega)
      norm_num at h
      exact h
  have ht : (2 : ℤ)^d=8*s := by
    dsimp [s]
    conv_lhs => rw [show d=(d-3)+3 by omega,pow_add]
    norm_num
    ring
  have hz : (2 : ℤ)^(d+2)=32*s := by rw [pow_add,ht]; norm_num; ring
  obtain ⟨u,v,w,ubound,vpos,vbound,rfl,ho0,ho1,ho2,hn0,hn1,hn2⟩ := fallback_select s hs gap
  have hu : u<2^(d-1) := by
    have hhalf := pow_half d (by omega)
    have : (u : ℤ)<(2 : ℤ)^(d-1) := by omega
    exact_mod_cast this
  have hv : v-1<2^((d+2)-1) := by
    have hhalf := pow_half (d+2) (by omega)
    have : (v : ℤ)<(2 : ℤ)^((d+2)-1) := by omega
    exact_mod_cast (show ((v-1 : ℕ) : ℤ)<(2 : ℤ)^((d+2)-1) by omega)
  have hw : 1<2^(3-1) := by norm_num
  have identify (side : Bool) : rowBase 2 3 (d+2) d side=
      if side then ![2*A 4 8 (32*s),SU 4 8 s,SV 4 8 s (32*s),SW 8 s (32*s)]
      else ![A 4 8 (32*s),B 4 8 s,L 4 8 s (32*s),K 8 s (32*s)] := by
    funext r
    cases side <;> fin_cases r <;> dsimp [rowBase,newBase,base,charge,A,B,L,K,SU,SV,SW,C]
    all_goals try simp only [ht,hz]
    all_goals norm_num
    all_goals ring
  have hb0 : base 2 3 (d+2) d 0=A 4 8 (32*s) := congrFun (identify false) 0
  apply physical_certificate 2 3 (d+2) d u v 1 (by norm_num) (by norm_num)
    (by omega) (by omega) hu hv hw vpos
  intro side r
  cases side <;> fin_cases r
  all_goals simp only [rowSeams,rowHeads,identify,hb0,ite_true,ite_false,Bool.false_eq_true]
  all_goals simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals first
    | exact ⟨by nlinarith only [ho0.1],by nlinarith only [ho0.2]⟩
    | exact ⟨by nlinarith only [ho1.1],by nlinarith only [ho1.2]⟩
    | exact ⟨by nlinarith only [ho2.1],by nlinarith only [ho2.2]⟩
    | exact ⟨by nlinarith only [hn0.1],by nlinarith only [hn0.2]⟩
    | exact ⟨by nlinarith only [hn1.1],by nlinarith only [hn1.2]⟩
    | exact ⟨by nlinarith only [hn2.1],by nlinarith only [hn2.2]⟩
    | constructor <;> first | omega | (dsimp [B,SU]; ring_nf; positivity)

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU
