/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakCSecond/Endpoint
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/FirstPeakCSecond/Endpoint
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange, mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: One actual physical order and literal fresh-label cut for all a greater than c greater than max b d. -/
/- SOURCE_ONLY_UNCOMPILED. Full FirstPeakCSecond consumed implementation.
Repository API pin: 1add3bcde3f5768e7c5b7c84867d9758df1e6e6b.
Caller construction and ordinary proof; no Pro or kernel validation.
Full unrestricted physical J / Circle C3.1 remain OPEN. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Banks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddle
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond
open SourceWidth PeriodicShortening RunFirstEarTransport
open private size seed sourceMod base newBase charge chainLength chainStart nextBase nextNewBase
  oldValue newValue negatives chain_values source_signs source_totals new_base_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private label lift_order marked_word
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
open private four_perm four_strip
  from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule
open private UniformBounds from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Polynomials
open private corner grainExponent grain reserve half_power gap_power uniform_bounds reserve_capacity tight_ceiling later_gates
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Arithmetic
open private positives support banks positive_mem support_bound reserve_bits banks_inventory bank_masses first_length
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.Banks

private def reserveNat (a b c d : ℕ) : ℕ :=
  2^(if d=2 ∧ b=3 ∧ c=4 then a-5 else a-d-2) *
    (if d=2 ∧ b=3 ∧ c=4 then 11 else 2*2^d-3)

private theorem reserve_cast (a b c d : ℕ) (hd : 2≤d) :
    (reserveNat a b c d : ℤ)=reserve a b c d := by
  have ht : 4≤(2:ℕ)^d := by
    have := Nat.pow_le_pow_right (by decide : 0<2) hd
    norm_num at this; exact this
  by_cases hh : d=2 ∧ b=3 ∧ c=4
  · simp [reserveNat,reserve,grain,grainExponent,corner,hh]
  · simp [reserveNat,reserve,grain,grainExponent,corner,hh,Nat.cast_sub (by omega : 3≤2*2^d)]

open private all_nat_joint from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddle
open private actual_nat_joint_iff from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint

set_option maxHeartbeats 2400000 in
/-- For every a>c>max(b,d), b,d>=2, one physical permutation and one literal
fresh-label cut satisfy both complete actual OriginalOrder predicates.
The b<=d branch includes b=d; the strict d<b branch constructs its own exact
banks, seam gates, source totals and same-word lift below. -/
theorem actualSource_first_peak_c_second_joint_lift (a b c d : ℕ)
    (hb : 2≤b) (hd : 2≤d) (hbc : b<c) (hdc : d<c) (hca : c<a) :
    ∃ sigma : List (Fin (a+b+c+d)), ∃ j : ℕ, j≤a+b+c+d ∧
      OriginalOrder (a+b+c+d) (1+2^a+2^(a+b)+2^(a+b+c)) sigma ∧
      OriginalOrder (a+b+c+d+1) (2*(1+2^a+2^(a+b)+2^(a+b+c)))
        (earWord (a+b+c+d) sigma j) := by
  classical
  by_cases hbd : b≤d
  · exact (actual_nat_joint_iff a b c d (by omega) hb (by omega) hd).mpr
      (all_nat_joint a b c d hb hbd hdc hca)
  · have hdb : d<b := by omega
    let k := a+b+c+d
    let seedN := 1+2^a+2^(a+b)+2^(a+b+c)
    let x : ℤ := 2^a
    let y : ℤ := 2^b
    let z : ℤ := 2^c
    let t : ℤ := 2^d
    let H : ℤ := 2^(a-c-1)
    let g := grain a b c d
    let s := reserve a b c d
    let sn := reserveNat a b c d
    let D := y*z+y+1
    let A := x*D+1
    let B := x*t*(y+1)+t+1
    let L := x*z*t+z*t+z+1
    let M := t*y*z+D
    let Mn := 2*M-D
    let Bn := 2*B-1
    let Ln := 2*L-z-1
    let N := sourceMod a b c d
    let f := oldValue a b c d
    let fnew := newValue a b c d
    let r := (B-1)/Mn+1
    let w := if z=2*y then (1:ℤ) else (L-r*M)/B
    have ht : 4≤t := by
      have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hd
      norm_num at hh; exact hh
    have hy : 1≤y := by dsimp [y]; exact one_le_pow₀ (by norm_num)
    have hz : 4≤z := by
      have hh := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 2≤c by omega)
      norm_num at hh; exact hh
    have hx : 1≤x := by dsimp [x]; exact one_le_pow₀ (by norm_num)
    have hH : 1≤H := by dsimp [H]; exact one_le_pow₀ (by norm_num)
    have ht0 : 0<t := by omega
    have hy0 : 0<y := by omega
    have hz0 : 0<z := by omega
    have hx0 : 0<x := by omega
    have hD : z+1≤D := by
      dsimp [D]
      nlinarith only [hy,hz,mul_nonneg (show 0≤y-1 by omega) (show 0≤z by omega)]
    have hM : 0<M := by dsimp [M,D]; positivity
    have hMn : 0<Mn := by dsimp [Mn,M,D]; ring_nf; positivity
    have hB : 1≤B := by dsimp [B]; nlinarith only [mul_nonneg (show 0≤x*t by positivity) (show 0≤y+1 by omega),ht]
    have bounds := uniform_bounds a b c d hd hdb hbc hca
    change UniformBounds x y z t H g s at bounds
    rcases bounds with ⟨boldLower,boldUpper,bnewLower,bnewUpper,
      btightOld,btightCeil,bgrainCapacity,bthird⟩
    change 0≤t*A-2*s*M at boldLower
    change 0≤A-1-(t*A-2*s*M) at boldUpper
    change 0≤2*(t-1)*A-2*s*Mn at bnewLower
    change 0≤A-1-(2*(t-1)*A-2*s*Mn) at bnewUpper
    change (z=2*y ∧ 0≤L-B-H*M ∧ 0≤2*B-L-1) ∨
      (4*y≤z ∧ 0≤L-2*B-H*D ∧ 0≤z*B-2*L-1) at bthird
    have caps := reserve_capacity a b c d hd hdb hbc hca
    change 1≤g ∧ 1≤s ∧ 2*s≤x ∧ g∣s at caps
    have hsn : (sn:ℤ)=s := reserve_cast a b c d hd
    have hHphysical : x=(2*z)*H := by
      simpa [x,z,H] using gap_power a c 1 (by omega)
    have hHexact : x/(2*z)=H := Int.ediv_eq_of_eq_mul_right (by omega) hHphysical
    have hcapPhysical : B≤(x/(2*z))*Mn := by
      rw [hHexact]
      have hh := btightCeil
      change 0≤H*Mn-B at hh
      omega
    have hbank : H*M≤B-1 := by
      have hh := btightOld
      change 0≤B-H*M-1 at hh
      omega
    have hrs := tight_ceiling B M D H hB hM hMn hH (by simpa only [hHexact] using hcapPhysical) hbank
    change 1≤r ∧ r≤H ∧ B≤r*Mn ∧ r*Mn<B+Mn ∧ r*M≤B-1 at hrs
    have hrg : r≤g := by have hh := bgrainCapacity; omega
    have hgs : g≤s := by
      obtain ⟨v,hv⟩ := caps.2.2.2
      have hvpos : 1≤v := by
        by_contra hn
        have hh := mul_nonpos_of_nonneg_of_nonpos (show 0≤g by omega) (show v≤0 by omega)
        nlinarith only [hv,caps.2.1,hh]
      nlinarith only [hv,mul_nonneg (show 0≤g by omega) (show 0≤v-1 by omega)]
    have hthird : if decide (z=2*y) then (0≤L-B-H*M ∧ 0≤2*B-L-1) else
        (0≤L-2*B-H*D ∧ 0≤z*B-2*L-1) := by
      rcases bthird with hh|hh
      · simpa [hh.1] using hh.2
      · have hn : z≠2*y := by nlinarith only [hh.1,hy]
        simpa [hn] using hh.2
    have hzhalf : z=2*(2:ℤ)^(c-1) := half_power c (by omega)
    have hzEven : z%2=0 := by omega
    have gates := later_gates B L M D z H r hB hM hD hz hH hrs
      (decide (z=2*y)) hthird hzEven
    have gates : 0≤w ∧ w<z/2 ∧
      (0≤2*(B-r*M) ∧ 2*(B-r*M)≤B-1) ∧
      (0≤2*(Bn-r*Mn) ∧ 2*(Bn-r*Mn)≤Bn-1) ∧
      (0≤2*(L-r*M-w*B) ∧ 2*(L-r*M-w*B)≤L-1) ∧
      (0≤2*(Ln-r*Mn-w*Bn) ∧ 2*(Ln-r*Mn-w*Bn)≤Ln-1) := by
      by_cases hadj : z=2*y <;> simpa [w,hadj,Mn,Bn,Ln] using gates
    -- Every integer capacity is established before converting any selected mask.
    have hr0 : 0≤r := by omega
    have hw0 : 0≤w := gates.1
    have hs0 : 0≤s := by omega
    have hxhalf : x=2*(2:ℤ)^(a-1) := half_power a (by omega)
    have hthalf : t=2*(2:ℤ)^(d-1) := half_power d (by omega)
    have hmask : 0≤s-r ∧ s-r<(2:ℤ)^(a-1) ∧
        0≤r-1 ∧ r-1<(2:ℤ)^(a-1) ∧ s-1<(2:ℤ)^(a-1) := by
      have hh := caps.2.2.1
      omega
    have hwcap : w<(2:ℤ)^(c-1) := by omega
    let rn := r.toNat
    let wn := w.toNat
    let p := sn-rn
    let q := rn-1
    let m := sn-1
    have hrn : (rn:ℤ)=r := Int.toNat_of_nonneg hr0
    have hwn : (wn:ℤ)=w := Int.toNat_of_nonneg hw0
    have hrsn : rn≤sn := by exact_mod_cast (show (rn:ℤ)≤(sn:ℤ) by rw [hrn,hsn]; omega)
    have hrn1 : 1≤rn := by exact_mod_cast (show (1:ℤ)≤(rn:ℤ) by rw [hrn]; omega)
    have hsn1 : 1≤sn := by exact_mod_cast (show (1:ℤ)≤(sn:ℤ) by rw [hsn]; omega)
    have hpcast : (p:ℤ)=s-r := by dsimp [p]; rw [Nat.cast_sub hrsn,hsn,hrn]
    have hqcast : (q:ℤ)=r-1 := by dsimp [q]; rw [Nat.cast_sub hrn1,hrn]; norm_num
    have hmcast : (m:ℤ)=s-1 := by dsimp [m]; rw [Nat.cast_sub hsn1,hsn]; norm_num
    have hp : p<2^(a-1) := by exact_mod_cast (show (p:ℤ)<(2:ℤ)^(a-1) by rw [hpcast]; exact hmask.2.1)
    have hq : q<2^(a-1) := by exact_mod_cast (show (q:ℤ)<(2:ℤ)^(a-1) by rw [hqcast]; exact hmask.2.2.2.1)
    have hm : m<2^(a-1) := by exact_mod_cast (show (m:ℤ)<(2:ℤ)^(a-1) by rw [hmcast]; exact hmask.2.2.2.2)
    have hw : wn<2^(c-1) := by exact_mod_cast (show (wn:ℤ)<(2:ℤ)^(c-1) by rw [hwn]; exact hwcap)
    have hdiv : 2^(grainExponent a b c d)∣sn := by
      change 2^(grainExponent a b c d)∣reserveNat a b c d
      dsimp [reserveNat,grainExponent,corner]
      exact dvd_mul_right _ _
    have hrgrain : rn≤2^(grainExponent a b c d) := by
      exact_mod_cast (show (rn:ℤ)≤(2:ℤ)^(grainExponent a b c d) by rw [hrn]; exact hrg)
    have bits := reserve_bits (grainExponent a b c d) sn rn hsn1 hdiv ⟨hrn1,hrgrain⟩
    change Disjoint p.bitIndices.toFinset q.bitIndices.toFinset ∧
      p.bitIndices.toFinset∪q.bitIndices.toFinset=m.bitIndices.toFinset at bits
    let P := banks a b c d p q wn 0
    let Q := banks a b c d p q wn 1
    let R := banks a b c d p q wn 2
    let nx := k-1
    let nu := d-1
    let nv := d+c-1
    let nw := d+c+b-1
    let G := Finset.range k \ (P∪Q∪R∪{nx,nu,nv,nw})
    let pre := P.toList++[nx]
    let post := Q.toList++nu::R.toList++nv::G.toList++[nw]
    let word := pre++post
    let j := a+d-1-m.bitIndices.toFinset.card
    have inventory := banks_inventory a b c d p q wn (by omega) (by omega) (by omega) hd hp hq hw bits.1
    have hpword := four_perm k nx nu nv nw P Q R (inventory.1 0) (inventory.1 1) (inventory.1 2)
      (inventory.2.1 0 1 (by decide)) (inventory.2.1 0 2 (by decide)) (inventory.2.1 1 2 (by decide))
      (by simp [nx,nu,nv,nw,k]; omega)
      (by intro i hi; simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
          rcases hi with rfl|rfl|rfl|rfl <;> dsimp [nx,nu,nv,nw,k] <;> omega)
    have hpword : word.Perm (List.range k) := by
      simpa only [word,pre,post,G,List.append_assoc,List.cons_append,List.nil_append,List.singleton_append] using hpword
    have Gphysical : G=positives a b c d 2 ∪ support (d+c+b) q ∪ support d wn := inventory.2.2
    have plen : pre.length=j := by
      have hh := first_length a b c d p q m (by omega) hd hm bits.2
      simpa [pre,P,j,banks] using hh
    have hj : j≤k := by
      have hh := hpword.length_eq
      simp only [word,List.length_append,List.length_range] at hh
      omega
    have hbase : base a b c d=![A,B,L,M] := by
      funext rr; fin_cases rr <;> dsimp [base,A,B,L,M,D,x,y,z,t] <;> ring
    have hnewbase : newBase a b c d=![2*A,Bn,Ln,Mn] := by
      funext rr; fin_cases rr <;> dsimp [newBase,charge,Mn,Bn,Ln]
      all_goals rw [hbase] <;> dsimp <;> ring
    have hseed : (seedN:ℤ)=A := by
      dsimp [seedN,A,D,x,y,z]
      push_cast
      simp only [pow_add]
      ring
    have hN : N=x*y*z*t-1 := rfl
    have hmod : modulus k=N := by dsimp [k,N,sourceMod,modulus]; ring
    have hmod' : modulus (k+1)=2*N+1 := by dsimp [k,N,sourceMod,modulus]; ring
    have tab := chain_values a b c d (by omega) (by omega) (by omega) hd
    have positive_values (rr : Fin 4) (i : ℕ) (hi : i+1<chainLength a b c d rr) :
        f (chainStart b c d rr+i)=(2:ℤ)^i*base a b c d rr ∧
        fnew (chainStart b c d rr+i)=(2:ℤ)^i*newBase a b c d rr := by
      exact ⟨by simpa only [if_pos hi] using tab.2.1 rr i (by omega),
        by simpa only [if_pos hi] using tab.2.2.1 rr i (by omega)⟩
    have allpos (i : ℕ) (hi : i<k) (hn : i≠nx ∧ i≠nu ∧ i≠nv ∧ i≠nw) :
        0≤f i ∧ 0≤fnew i := by
      have hs := source_signs a b c d (by omega) (by omega) (by omega) hd i hi
      have hnot : i∉negatives a b c d := by simp [negatives,size,nx,nu,nv,nw,k] at *; tauto
      rw [if_neg hnot] at hs
      exact ⟨hs.1.le,hs.2.le⟩
    have pos (rr : Fin 3) (i : ℕ) (hi : i∈(banks a b c d p q wn rr).toList) :
        0≤f i ∧ 0≤fnew i := by
      have hh := inventory.1 rr i (Finset.mem_toList.mp hi)
      exact allpos i hh.1 hh.2
    have posG (i : ℕ) (hi : i∈G.toList) : 0≤f i ∧ 0≤fnew i := by
      have hh := Finset.mem_toList.mp hi
      rw [Gphysical] at hh
      simp only [Finset.mem_union] at hh
      rcases hh with (hh|hh)|hh
      · have hb := (positive_mem a b c d 2 i).mp hh
        simp at hb
        apply allpos i <;> dsimp [k,nx,nu,nv,nw] <;> omega
      · have hb := support_bound (a-1) (d+c+b) q i hq hh
        apply allpos i <;> dsimp [k,nx,nu,nv,nw] <;> omega
      · have hb := support_bound (c-1) d wn i hw hh
        apply allpos i <;> dsimp [k,nx,nu,nv,nw] <;> omega
    have mf := bank_masses a b c d p q wn (by omega) (by omega) (by omega) hd hp hq hw bits.1 f A B M
      (fun i hi => by simpa [chainStart,hbase] using (positive_values 0 i (by dsimp [chainLength]; omega)).1)
      (fun i hi => by simpa [chainStart,hbase] using (positive_values 1 i (by dsimp [chainLength]; omega)).1)
      (fun i hi => by simpa [chainStart,hbase] using (positive_values 3 i (by dsimp [chainLength]; omega)).1)
    have mg := bank_masses a b c d p q wn (by omega) (by omega) (by omega) hd hp hq hw bits.1 fnew (2*A) Bn Mn
      (fun i hi => by simpa [chainStart,hnewbase] using (positive_values 0 i (by dsimp [chainLength]; omega)).2)
      (fun i hi => by simpa [chainStart,hnewbase] using (positive_values 1 i (by dsimp [chainLength]; omega)).2)
      (fun i hi => by simpa [chainStart,hnewbase] using (positive_values 3 i (by dsimp [chainLength]; omega)).2)
    have sumlist (S : Finset ℕ) (F : ℕ→ℤ) : (S.toList.map F).sum=∑ i∈S,F i := by
      change ((S.toList:Multiset ℕ).map F).sum=_
      simp
    simp only [←sumlist] at mf mg
    have m0 : 2*(P.toList.map f).sum=(x-2*s)*M+(t-2)*A := by
      dsimp [P]
      have hh := mf.1
      rw [hpcast,hqcast] at hh
      rw [hxhalf,hthalf]
      nlinarith only [hh]
    have m1 : (Q.toList.map f).sum=(s-r)*M := by
      change ((banks a b c d p q wn 1).toList.map f).sum=_
      rw [mf.2.1,hpcast]
    have m2 : 2*(R.toList.map f).sum=(z-2-2*w)*B := by
      dsimp [R]
      have hh := mf.2.2
      rw [hwn] at hh
      rw [hzhalf]
      nlinarith only [hh]
    have n0 : 2*(P.toList.map fnew).sum=(x-2*s)*Mn+(t-2)*(2*A) := by
      dsimp [P]
      have hh := mg.1
      rw [hpcast,hqcast] at hh
      rw [hxhalf,hthalf]
      nlinarith only [hh]
    have n1 : (Q.toList.map fnew).sum=(s-r)*Mn := by
      change ((banks a b c d p q wn 1).toList.map fnew).sum=_
      rw [mg.2.1,hpcast]
    have n2 : 2*(R.toList.map fnew).sum=(z-2-2*w)*Bn := by
      dsimp [R]
      have hh := mg.2.2
      rw [hwn] at hh
      rw [hzhalf]
      nlinarith only [hh]
    have totals := source_totals a b c d (by omega) (by omega) (by omega) hd
    have hfzero : (word.map f).sum=0 := (hpword.map f).sum_eq.trans totals.1
    have hear : fnew k=A := by simpa [k,size,hbase] using tab.2.2.2
    have hgzero : A+(word.map fnew).sum=0 := by
      have he := (hpword.map fnew).sum_eq.trans totals.2.1
      rw [hbase] at he
      dsimp at he
      omega
    have terminal (rr : Fin 4) :
        f (chainStart b c d rr+(chainLength a b c d rr-1))=-(N-nextBase a b c d rr)/2 ∧
        fnew (chainStart b c d rr+(chainLength a b c d rr-1))=
          -((2*N+1)-nextNewBase a b c d rr)/2 := by
      have hl : 2≤chainLength a b c d rr := by fin_cases rr <;> dsimp [chainLength] <;> omega
      exact ⟨by simpa only [if_neg (by omega : ¬chainLength a b c d rr-1+1<chainLength a b c d rr)] using
          tab.2.1 rr (chainLength a b c d rr-1) (by omega),
        by simpa only [if_neg (by omega : ¬chainLength a b c d rr-1+1<chainLength a b c d rr)] using
          tab.2.2.1 rr (chainLength a b c d rr-1) (by omega)⟩
    have nt0 := terminal 3
    have nt1 := terminal 0
    have nt2 := terminal 1
    have nt3 := terminal 2
    simp only [chainStart,chainLength,nextBase,nextNewBase,hbase,hnewbase,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,
      Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,zero_add] at nt0 nt1 nt2 nt3
    have en0 : d+c+b+(a-1)=nx := by dsimp [nx,k]; omega
    have en1 : d+(c-1)=nv := by dsimp [nv]; omega
    have en2 : d+c+(b-1)=nw := by dsimp [nw]; omega
    rw [en0] at nt0
    rw [en1] at nt2
    rw [en2] at nt3
    have nf0 : 2*f nx=A-N := by
      have he : A-N=2*((2:ℤ)^(a-1)*(D-y*z*t)+1) := by dsimp [A]; rw [hN,hxhalf]; ring
      rw [nt0.1]; omega
    have ng0 : 2*fnew nx=A-(2*N+1) := by
      have he : A-(2*N+1)=2*((2:ℤ)^(a-1)*(D-2*y*z*t)+1) := by dsimp [A]; rw [hN,hxhalf]; ring
      rw [nt0.2]; omega
    have nf1 : 2*f nu=B-N := by
      have he : B-N=2*((2:ℤ)^(d-1)*(1+x+x*y-x*y*z)+1) := by dsimp [B]; rw [hN,hthalf]; ring
      rw [nt1.1]; change 2*(-(N-B)/2)=B-N; omega
    have ng1 : 2*fnew nu=Bn-(2*N+1) := by rw [nt1.2]; dsimp [Bn]; omega
    have nf2 : 2*f nv=L-N := by
      have he : L-N=2*((2:ℤ)^(c-1)*(t*(1+x)-x*y*t+1)+1) := by dsimp [L]; rw [hN,hzhalf]; ring
      rw [nt2.1]; omega
    have ng2 : 2*fnew nv=Ln-(2*N+1) := by
      have he : Ln-(2*N+1)=2*(L-N-1-(2:ℤ)^(c-1)) := by dsimp [Ln]; rw [hzhalf]; ring
      rw [nt2.2]; omega
    have relx : x*M=N+A := by dsimp [M,A,D]; rw [hN]; ring
    have relt : t*A=N+B := by dsimp [A,B,D]; rw [hN]; ring
    have relz : z*B=N+L := by dsimp [B,L]; rw [hN]; ring
    have relxn : x*Mn=2*N+1+A := by dsimp [Mn,M,D,A]; rw [hN]; ring
    have reltn : t*(2*A)=2*N+1+Bn := by dsimp [Bn]; nlinarith only [relt]
    have relzn : z*Bn=2*N+1+Ln := by dsimp [Bn,Ln]; nlinarith only [relz]
    have hNodd : N%2=1 := by
      have he : N=2*(x*y*z*(2:ℤ)^(d-1)-1)+1 := by rw [hN,hthalf]; ring
      omega
    have hN0 : 0≤N := by have hh := tab.1 0; change 1≤base a b c d 0 ∧ base a b c d 0<N at hh; omega
    have lastold : 0≤-f nw ∧ -f nw≤N/2 := by
      have hh := tab.1 3
      rw [hbase] at hh
      dsimp at hh
      rw [nt3.1]
      omega
    have lastnew : 0≤-fnew nw ∧ -fnew nw≤N := by
      have hh := new_base_bounds a b c d (by omega) (by omega) (by omega) hd 3
      rw [hnewbase] at hh
      dsimp at hh
      rw [nt3.2]
      omega
    have oldfirst : 0≤t*A-2*s*M ∧ t*A-2*s*M≤A-1 := by
      exact ⟨boldLower,sub_nonneg.mp boldUpper⟩
    have newfirst : 0≤2*(t-1)*A-2*s*Mn ∧ 2*(t-1)*A-2*s*Mn≤A-1 := by
      exact ⟨bnewLower,sub_nonneg.mp bnewUpper⟩
    -- These equations identify the seams of this very word, in both rows.
    have S0 : 2*((P.toList.map f).sum+f nx)=t*A-2*s*M := by nlinarith only [m0,nf0,relx]
    have S1 : (P.toList.map f).sum+f nx+(Q.toList.map f).sum+f nu=B-r*M := by
      nlinarith only [m0,m1,nf0,nf1,relx,relt]
    have S2 : (P.toList.map f).sum+f nx+(Q.toList.map f).sum+f nu+(R.toList.map f).sum+f nv=L-r*M-w*B := by
      nlinarith only [m0,m1,m2,nf0,nf1,nf2,relx,relt,relz]
    have K0 : 2*((P.toList.map fnew).sum+fnew nx)=2*(t-1)*A-2*s*Mn := by
      nlinarith only [n0,ng0,relxn]
    have K1 : (P.toList.map fnew).sum+fnew nx+A+(Q.toList.map fnew).sum+fnew nu=Bn-r*Mn := by
      nlinarith only [n0,n1,ng0,ng1,relxn,reltn]
    have K2 : (P.toList.map fnew).sum+fnew nx+A+(Q.toList.map fnew).sum+fnew nu+
        (R.toList.map fnew).sum+fnew nv=Ln-r*Mn-w*Bn := by
      nlinarith only [n0,n1,n2,ng0,ng1,ng2,relxn,reltn,relzn]
    have oldstrip : InStrip f (N/2) 0 word := by
      suffices hh : InStrip f (N/2) 0
          (P.toList++nx::Q.toList++nu::R.toList++nv::G.toList++[nw]) by
        simpa only [word,pre,post,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using hh
      apply four_strip f P.toList Q.toList R.toList G.toList nx nu nv nw (N/2) 0
        (fun i hi => (pos 0 i hi).1) (fun i hi => (pos 1 i hi).1)
        (fun i hi => (pos 2 i hi).1) (fun i hi => (posG i hi).1) (by omega)
      · constructor <;> nlinarith only [S0,nf0,oldfirst.1,oldfirst.2,hNodd,Int.emod_add_mul_ediv N 2]
      · constructor <;> nlinarith only [S1,nf1,gates.2.2.1.1,gates.2.2.1.2,hNodd,Int.emod_add_mul_ediv N 2]
      · constructor <;> nlinarith only [S2,nf2,gates.2.2.2.2.1.1,gates.2.2.2.2.1.2,hNodd,Int.emod_add_mul_ediv N 2]
      · exact lastold
      · simpa only [word,pre,post,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append,zero_add] using hfzero
    have newstrip : InStrip fnew N 0 (pre++k::post) := by
      let Qear := k::Q.toList
      have hQear : (Qear.map fnew).sum=A+(Q.toList.map fnew).sum := by simp [Qear,hear]
      have hnewtotal : ((pre++k::post).map fnew).sum=0 := by
        simpa [word,List.map_append,List.sum_append,hear,add_assoc,add_comm,add_left_comm] using hgzero
      have posQear : ∀ i∈Qear,0≤fnew i := by
        intro i hi
        rcases List.mem_cons.mp hi with rfl|hi
        · rw [hear]; have hh := tab.1 0; rw [hbase] at hh; dsimp at hh; omega
        · exact (pos 1 i hi).2
      have hh := four_strip fnew P.toList Qear R.toList G.toList nx nu nv nw N 0
        (fun i hi => (pos 0 i hi).2) posQear
        (fun i hi => (pos 2 i hi).2) (fun i hi => (posG i hi).2) (by omega)
        (by constructor <;> nlinarith only [K0,ng0,newfirst.1,newfirst.2])
        (by rw [hQear]; constructor <;> nlinarith only [K1,ng1,gates.2.2.2.1.1,gates.2.2.2.1.2])
        (by rw [hQear]; constructor <;> nlinarith only [K2,ng2,gates.2.2.2.2.2.1,gates.2.2.2.2.2.2])
        lastnew (by simpa [pre,post,Qear,List.append_assoc] using hnewtotal)
      simpa only [pre,post,Qear,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using hh
    have hpnew : (pre++k::post).Perm (List.range (k+1)) := by
      have hh : (pre++k::post).Perm (word++[k]) := by
        simpa [word,List.append_assoc] using (List.perm_append_singleton k post).symm.append_left pre
      exact hh.trans (by simpa [List.range_succ] using hpword.append_right [k])
    have fform : f=fun i => centered N ((2:ℤ)^i*A) := by
      funext i
      change centered N ((2:ℤ)^i*base a b c d 0)=_
      rw [hbase]; rfl
    have gform : fnew=fun i => centered (2*N+1) ((2:ℤ)^i*(2*A)) := by
      funext i
      change centered (2*N+1) ((2:ℤ)^i*(2*base a b c d 0))=_
      rw [hbase]; rfl
    change ∃ sigma : List (Fin k), ∃ j : ℕ, j≤k ∧ OriginalOrder k seedN sigma ∧
      OriginalOrder (k+1) (2*seedN) (earWord k sigma j)
    refine ⟨word.map (label k (by dsimp [k]; omega)),j,hj,?_,?_⟩
    · apply lift_order k seedN (by dsimp [k]; omega) word hpword
      · simpa only [fform,hmod,hseed] using oldstrip
      · exact ThreeNegativeEqualOuterSourceBridge.source_zero k seedN (by dsimp [k]; omega)
    · have marked := marked_word k j (by dsimp [k]; omega) pre post plen hpword
      rw [marked]
      apply lift_order (k+1) (2*seedN) (by omega) (pre++k::post) hpnew
      · have hseed' : ((2*seedN:ℕ):ℤ)=2*A := by push_cast; rw [hseed]
        simpa only [gform,hmod',hseed',show (2*N+1)/2=N by omega] using newstrip
      · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*seedN) (by dsimp [k]; omega)

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond
