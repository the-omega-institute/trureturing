/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakCSecond/CMiddle
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange, mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Both CMiddle physical strip transports, literal cuts and exhaustive ten-chart dispatch. -/
/- SOURCE_ONLY_UNCOMPILED. Full FirstPeakCSecond consumed implementation.
Repository API pin: 1add3bcde3f5768e7c5b7c84867d9758df1e6e6b.
Caller construction and ordinary proof; no Pro or kernel validation.
Full unrestricted physical J / Circle C3.1 remain OPEN. -/
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddlePolynomials
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddleVPolynomials
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddleXPolynomials
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddleCore
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.List.FinRange
import Batteries.Tactic.OpenPrivate
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddle
open SourceWidth PeriodicShortening RunFirstEarTransport
open MaxPlusTwo.Chambers
open scoped BigOperators
open private size seed sourceMod base newBase charge chainLength chainStart
  nextBase nextNewBase oldValue newValue negatives actual_values chain_values
  new_base_bounds source_signs source_totals
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private blocksWord insertAt
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private packetChecks strip_iff_packetChecks
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Packets
open private strip_append_iff
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Transport

open private margins_strict_adjacent margins_strict_separated
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddlePolynomials
open private margins_h2_e2 margins_h2_t8 margins_h2_t4_e16
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddleVPolynomials
open private margins_h4_e2_t8 margins_h32_e2_t4 margins_h4_e4_t8 margins_h4_e8_t4 margins_h8_e4_t4
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddleXPolynomials
open private ceil XGates x_floor_gates x_one_gates dynamic_first bit_below
  predecessor_submask dynamic_submask mask full full_split xPackets
  vPackets freshAfter x_inventory v_inventory mask_mass complement_mass
  split_mass power_split actualRow row_source power_pred terminal_double
  source_odd four_checks terminal_nonpositive packet_positive fresh_positive fresh_word
  fresh_total full_double native_balance
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddleCore

private theorem x_transport (a b c d : ℕ) (s r w : ℤ)
    (hb : 2≤b) (hbd : b≤d) (hdc : d<c) (hca : c<a)
    (hs : 1≤s) (hr : 1≤r) (hrs : r≤s) (hw : 0≤w)
    (hscap : 2*s≤(2:ℤ)^a) (hwcap : 2*w<(2:ℤ)^c)
    (hsub : ∀ i, (r.toNat-1).testBit i=true → (s.toNat-1).testBit i=true)
    (hgate : XGates (actualRow a b c d) s r w) :
    let bs:=xPackets a b c d (s.toNat-1) (r.toNat-1) w.toNat
    let l:=blocksWord bs
    let j:=(blocksWord (bs.take 1)).length
    l.Perm (List.range (size a b c d)) ∧ j≤size a b c d ∧
      InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 l ∧
      InStrip (newValue a b c d) (sourceMod a b c d) 0 (insertAt (size a b c d) l j) := by
  have ha : 2≤a := by omega
  have hc : 2≤c := by omega
  have hd : 2≤d := by omega
  let v:=actualRow a b c d
  change XGates v s r w at hgate
  let m:=s.toNat-1
  let q:=r.toNat-1
  let wn:=w.toNat
  let bs:=xPackets a b c d m q wn
  let l:=blocksWord bs
  let j:=(blocksWord (bs.take 1)).length
  have hm : (m:ℤ)=s-1 := by dsimp [m]; omega
  have hq : (q:ℤ)=r-1 := by dsimp [q]; omega
  have hwn : (wn:ℤ)=w := by dsimp [wn]; omega
  have hrow:=row_source a b c d hca.le hdc.le
  change v.x=2^a ∧ v.y=2^b ∧ v.z=2^c ∧ v.t=2^d ∧
    v.A=base a b c d 0 ∧ v.B=base a b c d 1 ∧
    v.L=base a b c d 2 ∧ v.M=base a b c d 3 ∧
    v.Bn=newBase a b c d 1 ∧ v.Ln=newBase a b c d 2 ∧
    v.Mn=newBase a b c d 3 ∧ newBase a b c d 0=2*v.A at hrow
  rcases hrow with ⟨hx,hy,hz,ht,hA,hB,hL,hM,hBn,hLn,hMn,hAn⟩
  have hpow:=power_pred a (by omega)
  have hpowc:=power_pred c (by omega)
  have hmc : m<2^(a-1) := by exact_mod_cast (show (m:ℤ)<2^(a-1) by nlinarith)
  have hqc : q<2^(a-1) := by exact_mod_cast (show (q:ℤ)<2^(a-1) by nlinarith)
  have hwc : wn<2^(c-1) := by exact_mod_cast (show (wn:ℤ)<2^(c-1) by nlinarith)
  have cap (r : Fin 4) : full a b c d r<2^(chainLength a b c d r-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a b c d r-1); omega
  have u:=mask_mass a b c d (full a b c d 0) 0 ha hb hc hd (cap 0)
  have x:=complement_mass a b c d m 3 ha hb hc hd hmc
  have p:=split_mass a b c d m q 3 ha hb hc hd hmc hqc hsub
  have vv:=complement_mass a b c d wn 1 ha hb hc hd hwc
  have uf:=full_double a b c d 0 ha hb hc hd
  have xf:=full_double a b c d 3 ha hb hc hd
  have vf:=full_double a b c d 1 ha hb hc hd
  have t0:=terminal_double a b c d 3 ha hb hc hd
  have t1:=terminal_double a b c d 0 ha hb hc hd
  have t2:=terminal_double a b c d 1 ha hb hc hd
  have t3:=terminal_double a b c d 2 ha hb hc hd
  have nb0:=native_balance a b c d 0 ha hb hc hd
  have nb1:=native_balance a b c d 1 ha hb hc hd
  have nb3:=native_balance a b c d 3 ha hb hc hd
  have ua:=congrArg (fun z : ℤ => z*v.A) uf
  simp [chainLength,←ht] at ua
  simp only [nextBase,nextNewBase,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] at nb0 nb1 nb3
  simp only [←hA,←hB,←hL,←hM,←hBn,←hLn,←hMn,hAn,hm,hq,hwn]
    at u x p vv nb0 nb1 nb3
  simp only [nextBase,nextNewBase,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    ←hA,←hB,←hL,←hM,←hBn,←hLn,←hMn,hAn] at t0 t1 t2 t3
  have odd:=source_odd a b c d (by omega)
  have hp:=x_inventory a b c d m q wn ha hb hc hd hmc hqc hsub
  have hlen : l.length=size a b c d := by simpa [l,bs] using hp.length_eq
  have hj : j≤size a b c d := by
    have := List.length_take_le 1 bs
    have hsplit : l=blocksWord (bs.take 1)++blocksWord (bs.drop 1) := by
      simp [l,bs,xPackets,blocksWord]
    have := congrArg List.length hsplit
    simp only [List.length_append] at this
    omega
  have hzero : (l.map (oldValue a b c d)).sum=0 :=
    (hp.map _).sum_eq.trans (source_totals a b c d ha hb hc hd).1
  have hzeron : ((blocksWord (freshAfter (size a b c d) 1 bs)).map (newValue a b c d)).sum=0 := by
    rw [fresh_word _ _ _ (by simp [bs,xPackets])]
    exact fresh_total a b c d l j ha hb hc hd hp
  have hmN : 2*(sourceMod a b c d/2)+1=sourceMod a b c d := by omega
  have fpos:=packet_positive a b c d ha hb hc hd m q wn 0
  have gpos:=fresh_positive a b c d 1 bs ha hb hc hd (by
    intro P hP i hi; exact (fpos.1 P hP i hi).2)
  have ng (P : List ℕ×ℕ) (hP : P∈bs) :
      oldValue a b c d P.2≤0 ∧ newValue a b c d P.2≤0 := by
    simp only [bs,xPackets,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hP
    rcases hP with rfl|rfl|rfl|rfl
    all_goals exact terminal_nonpositive a b c d _ ha hb hc hd
  have ng' (P : List ℕ×ℕ) (hP : P∈freshAfter (size a b c d) 1 bs) :
      newValue a b c d P.2≤0 := by
    simp only [bs,xPackets,freshAfter,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hP
    rcases hP with rfl|rfl|rfl|rfl
    all_goals exact (terminal_nonpositive a b c d _ ha hb hc hd).2
  have oldChecks : packetChecks (oldValue a b c d) (sourceMod a b c d/2) 0 bs := by
    apply four_checks _ _ _ _ _ _ _ _ _ _
      (v.t*v.A-2*s*v.M) (2*(v.B-r*v.M)) (2*(v.L-r*v.M-w*v.B))
      v.A v.B v.L v.M
    · simp only [bs,xPackets,List.map_append,List.sum_append]
      rw [x.1,u.1]
      simp [chainLength] at uf xf
      nlinarith only [nb3.1,ua]
    · simp only [bs,xPackets,List.map_append,List.sum_append]
      rw [x.1,u.1,p.1]
      simp [chainLength] at uf xf
      nlinarith only [nb3.1,nb0.1]
    · simp only [bs,xPackets,List.map_append,List.sum_append]
      rw [x.1,u.1,p.1,vv.1]
      simp [chainLength] at uf xf vf
      nlinarith only [nb3.1,nb0.1,nb1.1]
    · exact hzero
    · omega
    · omega
    · omega
    · omega
    · exact hgate.1
    · exact hgate.2.2.1
    · exact hgate.2.2.2.2.1
    · have := (chain_values a b c d ha hb hc hd).1 3; omega
  have newChecks : packetChecks (newValue a b c d) (sourceMod a b c d) 0
      (freshAfter (size a b c d) 1 bs) := by
    apply four_checks _ _ _ _ _ _ _ _ _ _
      (2*((v.t-1)*v.A-s*v.Mn)) (2*(v.Bn-r*v.Mn)) (2*(v.Ln-r*v.Mn-w*v.Bn))
      v.A v.Bn v.Ln v.Mn
    · simp only [bs,xPackets,freshAfter,List.map_append,List.sum_append]
      rw [x.2,u.2]
      simp [chainLength] at uf xf
      nlinarith only [nb3.2,ua]
    · simp only [bs,xPackets,freshAfter,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
      rw [x.2,u.2,p.2,(chain_values a b c d ha hb hc hd).2.2.2,←hA]
      simp [chainLength] at uf xf
      nlinarith only [nb3.2,nb0.2]
    · simp only [bs,xPackets,freshAfter,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
      rw [x.2,u.2,p.2,vv.2,(chain_values a b c d ha hb hc hd).2.2.2,←hA]
      simp [chainLength] at uf xf vf
      nlinarith only [nb3.2,nb0.2,nb1.2]
    · exact hzeron
    · omega
    · omega
    · omega
    · omega
    · exact hgate.2.1
    · exact hgate.2.2.2.1
    · exact hgate.2.2.2.2.2
    · have := new_base_bounds a b c d ha hb hc hd 3; omega
  refine ⟨hp,hj,?_,?_⟩
  · exact (strip_iff_packetChecks _ _ _ bs ⟨by omega,by
      have := (chain_values a b c d ha hb hc hd).1 0; omega⟩
      (fun P hP i hi => (fpos.1 P hP i hi).1) (fun P hP => (ng P hP).1)).mpr oldChecks
  · rw [←fresh_word _ _ _ (by simp [bs,xPackets])]
    exact (strip_iff_packetChecks _ _ _ _ ⟨by omega,by
      have := (chain_values a b c d ha hb hc hd).1 0; omega⟩ gpos ng').mpr newChecks

private theorem rank_two (t e h : ℤ) :
    let v:=model t t e h
    let C:=(v.x-v.z)*(t+1)
    v.A-v.L=C ∧ v.B-v.M=t*C ∧
      v.M=(t+1)*(t*v.z+1) ∧ v.B=(t+1)*(t*v.x+1) := by
  dsimp [model]
  refine ⟨?_,?_,?_,?_⟩ <;> ring

private def VGates (v : Row) (r R : ℤ) : Prop :=
  let C:=(v.x-v.z)*(v.t+1)
  0≤2*(v.L-r*v.B) ∧ 0≤v.L-1-2*(v.L-r*v.B) ∧
  0≤2*(v.Ln-r*v.Bn) ∧ 0≤v.Ln-1-2*(v.Ln-r*v.Bn) ∧
  0≤2*(v.M-C) ∧ 0≤v.B-1-2*(v.M-C) ∧
  0≤2*(v.Mn-2*C-v.z-1) ∧ 0≤v.Bn-1-2*(v.Mn-2*C-v.z-1) ∧
  0≤2*(v.L-R*v.M) ∧ 0≤v.A-1-2*(v.L-R*v.M) ∧
  0≤2*(v.Ln-R*v.Mn) ∧ 0≤v.A-1-2*(v.Ln-R*v.Mn) ∧
  0≤(0:ℤ) ∧ 0≤v.M-1 ∧ 0≤(0:ℤ) ∧ 0≤v.Mn-1

private theorem v_transport (a c d : ℕ) (r R : ℤ)
    (hd : 2≤d) (hdc : d<c) (hac : a=c+1)
    (hr : 1≤r) (hR : 1≤R) (hodd : R%2=1)
    (hrcap : 2*(r-1)<(2:ℤ)^c) (hRcap : 2*R<(2:ℤ)^a)
    (hgate : VGates (actualRow a d c d) r R) :
    let bs:=vPackets a d c d (r.toNat-1) R.toNat
    let l:=blocksWord bs
    let j:=(blocksWord (bs.take 2)).length
    l.Perm (List.range (size a d c d)) ∧ j≤size a d c d ∧
      InStrip (oldValue a d c d) (sourceMod a d c d/2) 0 l ∧
      InStrip (newValue a d c d) (sourceMod a d c d) 0 (insertAt (size a d c d) l j) := by
  have ha : 2≤a := by omega
  have hc : 2≤c := by omega
  let v:=actualRow a d c d
  let C:=(v.x-v.z)*(v.t+1)
  let q:=r.toNat-1
  let Rn:=R.toNat
  let bs:=vPackets a d c d q Rn
  let l:=blocksWord bs
  let j:=(blocksWord (bs.take 2)).length
  have hq : (q:ℤ)=r-1 := by dsimp [q]; omega
  have hRn : (Rn:ℤ)=R := by dsimp [Rn]; omega
  have hoddn : Rn%2=1 := by omega
  have hrow:=row_source a d c d (by omega) hdc.le
  change v.x=2^a ∧ v.y=2^d ∧ v.z=2^c ∧ v.t=2^d ∧
    v.A=base a d c d 0 ∧ v.B=base a d c d 1 ∧
    v.L=base a d c d 2 ∧ v.M=base a d c d 3 ∧
    v.Bn=newBase a d c d 1 ∧ v.Ln=newBase a d c d 2 ∧
    v.Mn=newBase a d c d 3 ∧ newBase a d c d 0=2*v.A at hrow
  rcases hrow with ⟨hx,hy,hz,ht,hA,hB,hL,hM,hBn,hLn,hMn,hAn⟩
  have hxz : v.x=2*v.z := by rw [hx,hz,hac,pow_succ]; ring
  have hrank:=rank_two ((2:ℤ)^d) ((2:ℤ)^(c-d)) ((2:ℤ)^(a-c))
  change v.A-v.L=C ∧ v.B-v.M=v.t*C ∧
    v.M=(v.t+1)*(v.t*v.z+1) ∧ v.B=(v.t+1)*(v.t*v.x+1) at hrank
  have hpow:=power_pred a (by omega)
  have hpowc:=power_pred c (by omega)
  have hqc : q<2^(c-1) := by exact_mod_cast (show (q:ℤ)<2^(c-1) by nlinarith)
  have hRc : Rn<2^(a-1) := by exact_mod_cast (show (Rn:ℤ)<2^(a-1) by nlinarith)
  have h1c : 1<2^(a-1) := by
    have := Nat.pow_le_pow_right Nat.zero_lt_two (show 1≤a-1 by omega)
    norm_num at this; omega
  have cap (r : Fin 4) : full a d c d r<2^(chainLength a d c d r-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a d c d r-1); omega
  have u:=mask_mass a d c d (full a d c d 0) 0 ha hd hc hd (cap 0)
  have vq:=mask_mass a d c d q 1 ha hd hc hd hqc
  have x1:=mask_mass a d c d 1 3 ha hd hc hd h1c
  have vv:=complement_mass a d c d q 1 ha hd hc hd hqc
  have xx:=complement_mass a d c d Rn 3 ha hd hc hd hRc
  have uf:=full_double a d c d 0 ha hd hc hd
  have vf:=full_double a d c d 1 ha hd hc hd
  have xf:=full_double a d c d 3 ha hd hc hd
  have t0:=terminal_double a d c d 1 ha hd hc hd
  have t1:=terminal_double a d c d 0 ha hd hc hd
  have t2:=terminal_double a d c d 3 ha hd hc hd
  have t3:=terminal_double a d c d 2 ha hd hc hd
  have nb0:=native_balance a d c d 0 ha hd hc hd
  have nb1:=native_balance a d c d 1 ha hd hc hd
  have nb3:=native_balance a d c d 3 ha hd hc hd
  simp only [nextBase,nextNewBase,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three] at nb0 nb1 nb3
  simp only [←hA,←hB,←hL,←hM,←hBn,←hLn,←hMn,hAn,hq,hRn]
    at u vq x1 vv xx nb0 nb1 nb3
  simp only [nextBase,nextNewBase,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    ←hA,←hB,←hL,←hM,←hBn,←hLn,←hMn,hAn] at t0 t1 t2 t3
  have odd:=source_odd a d c d (by omega)
  have hp:=v_inventory a d c d q Rn ha hd hc hd hoddn hRc h1c
  have hj : j≤size a d c d := by
    have hsplit : l=blocksWord (bs.take 2)++blocksWord (bs.drop 2) := by
      simp [l,bs,vPackets,blocksWord]
    have hlen : l.length=size a d c d := by simpa [l,bs] using hp.length_eq
    have := congrArg List.length hsplit
    simp only [List.length_append] at this
    omega
  have hzero : (l.map (oldValue a d c d)).sum=0 :=
    (hp.map _).sum_eq.trans (source_totals a d c d ha hd hc hd).1
  have hzeron : ((blocksWord (freshAfter (size a d c d) 2 bs)).map (newValue a d c d)).sum=0 := by
    rw [fresh_word _ _ _ (by simp [bs,vPackets])]
    exact fresh_total a d c d l j ha hd hc hd hp
  have hmN : 2*(sourceMod a d c d/2)+1=sourceMod a d c d := by omega
  change VGates v r R at hgate
  rcases hgate with ⟨g0,g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12,g13,g14,g15⟩
  change 0≤2*(v.M-C) at g4
  change 0≤v.B-1-2*(v.M-C) at g5
  change 0≤2*(v.Mn-2*C-v.z-1) at g6
  change 0≤v.Bn-1-2*(v.Mn-2*C-v.z-1) at g7
  have oldChecks : packetChecks (oldValue a d c d) (sourceMod a d c d/2) 0 bs := by
    apply four_checks _ _ _ _ _ _ _ _ _ _
      (2*(v.L-r*v.B)) (2*(v.M-C)) (2*(v.L-R*v.M)) v.L v.B v.A v.M
    · rw [vv.1]
      simp [chainLength] at vf
      nlinarith only [nb1.1]
    · simp only [bs,vPackets,List.map_append,List.sum_append]
      rw [vv.1,u.1,vq.1,x1.1]
      simp [chainLength] at uf vf
      nlinarith only [nb1.1,nb0.1,hrank.1]
    · simp only [bs,vPackets,List.map_append,List.sum_append]
      rw [vv.1,u.1,vq.1,x1.1,xx.1]
      simp [chainLength] at uf vf xf
      nlinarith only [nb1.1,nb0.1,nb3.1,hrank.1]
    · exact hzero
    · omega
    · omega
    · omega
    · omega
    · exact ⟨g0,by omega⟩
    · exact ⟨g4,by omega⟩
    · exact ⟨g8,by omega⟩
    · omega
  have newChecks : packetChecks (newValue a d c d) (sourceMod a d c d) 0
      (freshAfter (size a d c d) 2 bs) := by
    apply four_checks _ _ _ _ _ _ _ _ _ _
      (2*(v.Ln-r*v.Bn)) (2*(v.Mn-2*C-v.z-1)) (2*(v.Ln-R*v.Mn))
      v.Ln v.Bn v.A v.Mn
    · rw [vv.2]
      simp [chainLength] at vf
      nlinarith only [nb1.2]
    · simp only [bs,vPackets,freshAfter,List.map_append,List.sum_append]
      rw [vv.2,u.2,vq.2,x1.2]
      simp [chainLength] at uf vf
      have hη : v.D=v.y*v.z+v.y+1 := rfl
      have hb' : v.Bn=2*v.B-1 := rfl
      have hl' : v.Ln=2*v.L-v.z-1 := rfl
      have hm' : v.Mn=2*v.M-v.D := rfl
      nlinarith only [nb1.2,nb0.2,hrank.1,hl']
    · simp only [bs,vPackets,freshAfter,List.map_append,List.sum_append,List.map_cons,List.sum_cons]
      rw [vv.2,u.2,vq.2,x1.2,xx.2,(chain_values a d c d ha hd hc hd).2.2.2,←hA]
      simp [chainLength] at uf vf xf
      have hη : v.D=v.y*v.z+v.y+1 := rfl
      have hb' : v.Bn=2*v.B-1 := rfl
      have hl' : v.Ln=2*v.L-v.z-1 := rfl
      have hm' : v.Mn=2*v.M-v.D := rfl
      nlinarith only [nb1.2,nb0.2,nb3.2,hrank.1]
    · exact hzeron
    · omega
    · omega
    · omega
    · omega
    · exact ⟨g2,by omega⟩
    · exact ⟨g6,by omega⟩
    · exact ⟨g10,by omega⟩
    · omega
  have fpos:=packet_positive a d c d ha hd hc hd 0 q 0 Rn
  have gpos:=fresh_positive a d c d 2 bs ha hd hc hd (by
    intro P hP i hi; exact (fpos.2 P hP i hi).2)
  have ng (P : List ℕ×ℕ) (hP : P∈bs) :
      oldValue a d c d P.2≤0 ∧ newValue a d c d P.2≤0 := by
    simp only [bs,vPackets,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hP
    rcases hP with rfl|rfl|rfl|rfl
    all_goals exact terminal_nonpositive a d c d _ ha hd hc hd
  have ng' (P : List ℕ×ℕ) (hP : P∈freshAfter (size a d c d) 2 bs) :
      newValue a d c d P.2≤0 := by
    simp only [bs,vPackets,freshAfter,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hP
    rcases hP with rfl|rfl|rfl|rfl
    all_goals exact (terminal_nonpositive a d c d _ ha hd hc hd).2
  refine ⟨hp,hj,?_,?_⟩
  · exact (strip_iff_packetChecks _ _ _ bs ⟨by omega,by
      have := (chain_values a d c d ha hd hc hd).1 0; omega⟩
      (fun P hP i hi => (fpos.2 P hP i hi).1) (fun P hP => (ng P hP).1)).mpr oldChecks
  · rw [←fresh_word _ _ _ (by simp [bs,vPackets])]
    exact (strip_iff_packetChecks _ _ _ _ ⟨by omega,by
      have := (chain_values a d c d ha hd hc hd).1 0; omega⟩ gpos ng').mpr newChecks

/- popcount counts distinct set bit positions, hence distinct physical occurrences.
The equality below is independent of the chosen adequate chain length. -/
private def popcount (m : ℕ) : ℕ := m.bitIndices.toFinset.card

private theorem mask_length (a b c d m : ℕ) (r : Fin 4)
    (hm : m<2^(chainLength a b c d r-1)) :
    (mask a b c d r m).length=popcount m := by
  let off:=chainStart b c d r
  have hset : (mask a b c d r m).toFinset=m.bitIndices.toFinset.image (off+·) := by
    ext i
    simp only [List.mem_toFinset,Finset.mem_image,Nat.mem_bitIndices]
    change i∈chamberLabels (chainLength a b c d r-1) off m ↔ _
    rw [chamberLabels_mem]
    constructor
    · rintro ⟨j,hj,hbit,he⟩
      exact ⟨j,hbit,he⟩
    · rintro ⟨j,hbit,he⟩
      exact ⟨j,bit_below m _ j hm hbit,hbit,he⟩
  calc
    _ = (mask a b c d r m).toFinset.card := by
      symm
      exact List.toFinset_card_of_nodup (chamberLabels_nodup _ _ _)
    _ = popcount m := by
      rw [hset,Finset.card_image_of_injective _ (fun x y h => Nat.add_left_cancel h)]
      rfl

private theorem x_literal_cut (a b c d m q w : ℕ)
    (ha : 2≤a) (hd : 2≤d) (hm : m<2^(a-1)) :
    (blocksWord ((xPackets a b c d m q w).take 1)).length=
      a+d-1-popcount m := by
  have hx:=full_split a b c d 3 m
  have hl:=hx.length_eq
  have hu:=chamberLabels_full (d-1) 0
  have hxf:=chamberLabels_full (a-1) (d+c+b)
  have hpop:=mask_length a b c d m 3 hm
  simp [mask,full,chainLength,chainStart] at hl hpop
  rw [hxf,List.length_range'] at hl
  simp only [xPackets,List.take_succ_cons,List.take_zero,blocksWord,
    List.length_append,List.length_cons,List.length_nil,add_zero]
  simp [mask,full,chainLength,chainStart]
  rw [hu,List.length_range']
  omega

private theorem v_literal_cut (a c d q R : ℕ) (hd : 2≤d) (hdc : d<c) (hac : a=c+1)
    (hq : q<2^(c-1)) :
    (blocksWord ((vPackets a d c d q R).take 2)).length=c+d+1 := by
  have hv:=full_split a d c d 1 q
  have hl:=hv.length_eq
  have hu:=chamberLabels_full (d-1) 0
  have hvf:=chamberLabels_full (c-1) d
  have hbit : chamberLabels (a-1) (d+c+d) 1=[d+c+d] := by
    dsimp [chamberLabels,labels]
    have hf : ((List.range (a-1)).filter (fun i => (1:ℕ).testBit i))=[0] := by
      apply List.Perm.eq_singleton
      apply (List.perm_ext_iff_of_nodup
        (List.Nodup.filter (fun i => (1:ℕ).testBit i) List.nodup_range)
        (by simp)).mpr
      intro i
      simp only [List.mem_filter,List.mem_range,List.mem_singleton]
      constructor
      · rintro ⟨hi,hbit⟩
        have := bit_below 1 1 i (by norm_num) hbit
        omega
      · intro hi
        subst i
        simp [show 0<a-1 by omega,Nat.testBit_eq_decide_div_mod_eq]
    rw [hf]
    simp
  simp [mask,full,chainLength,chainStart] at hl
  rw [hvf,List.length_range'] at hl
  simp only [vPackets,List.take_succ_cons,List.take_zero,blocksWord,
    List.length_append,List.length_cons,List.length_nil,add_zero]
  simp [mask,full,chainLength,chainStart]
  rw [hu,List.length_range',hbit]
  simp only [List.length_singleton]
  omega

private def NatJoint (a b c d : ℕ) : Prop :=
  ∃ l : List ℕ, l.Perm (List.range (size a b c d)) ∧
    InStrip (oldValue a b c d) (sourceMod a b c d/2) 0 l ∧
    ∃ j : ℕ, j≤size a b c d ∧
      InStrip (newValue a b c d) (sourceMod a b c d) 0 (insertAt (size a b c d) l j)

private theorem x_nat_joint (a b c d : ℕ) (s r w : ℤ)
    (hb : 2≤b) (hbd : b≤d) (hdc : d<c) (hca : c<a)
    (hs : 1≤s) (hr : 1≤r) (hrs : r≤s) (hw : 0≤w)
    (hscap : 2*s≤(2:ℤ)^a) (hwcap : 2*w<(2:ℤ)^c)
    (hsub : ∀ i, (r.toNat-1).testBit i=true → (s.toNat-1).testBit i=true)
    (hgate : XGates (actualRow a b c d) s r w) : NatJoint a b c d := by
  let bs:=xPackets a b c d (s.toNat-1) (r.toNat-1) w.toNat
  obtain ⟨hp,hj,ho,hn⟩ := x_transport a b c d s r w hb hbd hdc hca
    hs hr hrs hw hscap hwcap hsub hgate
  have hcut := x_literal_cut a b c d (s.toNat-1) (r.toNat-1) w.toNat
    (by omega) (by omega) (by
      have hp:=power_pred a (by omega)
      exact_mod_cast (show ((s.toNat-1:ℕ):ℤ)<2^(a-1) by omega))
  refine ⟨blocksWord bs,hp,ho,a+d-1-popcount (s.toNat-1),?_,?_⟩
  · simpa only [hcut] using hj
  · simpa only [hcut] using hn

private theorem v_nat_joint (a c d : ℕ) (r R : ℤ)
    (hd : 2≤d) (hdc : d<c) (hac : a=c+1)
    (hr : 1≤r) (hR : 1≤R) (hodd : R%2=1)
    (hrcap : 2*(r-1)<(2:ℤ)^c) (hRcap : 2*R<(2:ℤ)^a)
    (hgate : VGates (actualRow a d c d) r R) : NatJoint a d c d := by
  let bs:=vPackets a d c d (r.toNat-1) R.toNat
  obtain ⟨hp,hj,ho,hn⟩ := v_transport a c d r R hd hdc hac hr hR hodd hrcap hRcap hgate
  have hcut := v_literal_cut a c d (r.toNat-1) R.toNat hd hdc hac (by
    have hp:=power_pred c (by omega)
    exact_mod_cast (show ((r.toNat-1:ℕ):ℤ)<2^(c-1) by omega))
  refine ⟨blocksWord bs,hp,ho,c+d+1,?_,?_⟩
  · simpa only [hcut] using hj
  · simpa only [hcut] using hn

private theorem pow_lower (j m : ℕ) (h : m≤j) : (2:ℤ)^m≤2^j :=
  pow_le_pow_right₀ (by norm_num) h

private theorem x_multiple_joint (a b c d ell u : ℕ) (s r w : ℤ)
    (hb : 2≤b) (hbd : b≤d) (hdc : d<c) (hca : c<a)
    (hu : 1≤u) (hs : s=(2:ℤ)^ell*(u:ℤ))
    (hr : 1≤r) (hrg : r≤(2:ℤ)^ell) (hw : 0≤w)
    (hscap : 2*s≤(2:ℤ)^a) (hwcap : 2*w<(2:ℤ)^c)
    (hgate : XGates (actualRow a b c d) s r w) : NatJoint a b c d := by
  have hg : (1:ℤ)≤2^ell := by exact_mod_cast (Nat.one_le_two_pow (n:=ell))
  have hug : (2:ℤ)^ell≤s := by
    rw [hs]
    have := mul_le_mul_of_nonneg_left (show (1:ℤ)≤u by exact_mod_cast hu) (show (0:ℤ)≤2^ell by positivity)
    simpa using this
  have hse : s.toNat=2^ell*u := by
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg (by omega)]
    push_cast
    exact hs
  have hq : r.toNat-1<2^ell := by
    have hrc : (r.toNat:ℤ)=r := Int.toNat_of_nonneg (by omega)
    exact_mod_cast (show ((r.toNat-1:ℕ):ℤ)<2^ell by omega)
  apply x_nat_joint a b c d s r w hb hbd hdc hca (by omega) hr (by omega) hw hscap hwcap
    (by rw [hse]; exact predecessor_submask ell u (r.toNat-1) hu hq) hgate

private def FloorMargins (v : Row) (s g : ℤ) : Prop :=
  0≤v.t*v.A-2*s*v.M ∧ 0≤v.A-1-(v.t*v.A-2*s*v.M) ∧
  0≤2*((v.t-1)*v.A-s*v.Mn) ∧ 0≤v.A-1-2*((v.t-1)*v.A-s*v.Mn) ∧
  0≤v.B*v.t*v.y*v.z-v.M*v.Mn ∧ 0≤g*v.Mn-v.B ∧
  0≤v.L-2*v.B-g*v.D ∧ 0≤v.z*v.B-2*v.L-1

private theorem floor_multiple_chart (a b c d ell u : ℕ)
    (hb : 2≤b) (hbd : b≤d) (hdc : d<c) (hca : c<a) (hu : 1≤u)
    (hscap : 2*((2:ℤ)^ell*(u:ℤ))≤(2:ℤ)^a)
    (hmargins : FloorMargins (actualRow a b c d) ((2:ℤ)^ell*(u:ℤ)) ((2:ℤ)^ell)) :
    NatJoint a b c d := by
  let y : ℤ:=2^b
  let t : ℤ:=2^d
  let e : ℤ:=2^(c-d)
  let h : ℤ:=2^(a-c)
  let v:=actualRow a b c d
  let s : ℤ:=2^ell*(u:ℤ)
  let g : ℤ:=2^ell
  rcases hmargins with ⟨f0,f1,f2,f3,F,G,W,Z⟩
  have gates:=x_floor_gates y t e h s g
    (by simpa [y] using pow_lower b 2 hb)
    (by simpa [t] using pow_lower d 2 (by omega))
    (by simpa [e] using pow_lower (c-d) 1 (by omega))
    (by simpa [h] using pow_lower (a-c) 1 (by omega))
    ⟨⟨f0,sub_nonneg.mp f1⟩,⟨f2,sub_nonneg.mp f3⟩⟩ F G W Z
  change 1≤ceil v.B v.Mn ∧ ceil v.B v.Mn≤g ∧ ceil v.B v.Mn*v.M<v.B ∧
    0≤(v.L-ceil v.B v.Mn*v.M)/v.B ∧
    2*((v.L-ceil v.B v.Mn*v.M)/v.B)<v.z ∧
    XGates v s (ceil v.B v.Mn) ((v.L-ceil v.B v.Mn*v.M)/v.B) at gates
  apply x_multiple_joint a b c d ell u s (ceil v.B v.Mn)
    ((v.L-ceil v.B v.Mn*v.M)/v.B) hb hbd hdc hca hu rfl gates.1 gates.2.1
    gates.2.2.2.1 hscap
  · have hvz : v.z=(2:ℤ)^c := (row_source a b c d hca.le hdc.le).2.2.1
    simpa only [hvz] using gates.2.2.2.2.1
  · exact gates.2.2.2.2.2

private theorem one_multiple_chart (a c d : ℕ)
    (hd : 2≤d) (hdc : c=d+1) (hca : c+2≤a)
    (hmargins : let v:=actualRow a d c d
      let s:=(2:ℤ)^(a-c)*(2^d-1)
      0≤v.t*v.A-2*s*v.M ∧ 0≤v.A-1-(v.t*v.A-2*s*v.M) ∧
      0≤2*((v.t-1)*v.A-s*v.Mn) ∧ 0≤v.A-1-2*((v.t-1)*v.A-s*v.Mn) ∧
      0≤v.B*v.t*v.y*v.z-v.M*v.Mn ∧ 0≤(2:ℤ)^(a-c)*v.Mn-v.B ∧
      0≤(v.L-v.B-v.M)*v.Mn-v.B*v.M ∧ 0≤2*v.B-v.L-1) :
    NatJoint a d c d := by
  let t : ℤ:=2^d
  let h : ℤ:=2^(a-c)
  let s:=h*(t-1)
  let v:=actualRow a d c d
  have he : c-d=1 := by omega
  have hv : v=model t t 2 h := by dsimp [v,actualRow,t,h]; rw [he]; norm_num
  have gates:=x_one_gates t h s
    (by simpa [t] using pow_lower d 2 hd)
    (by simpa [h] using pow_lower (a-c) 2 (by omega))
    (by simpa only [←hv] using hmargins)
  change 1≤ceil (model t t 2 h).B (model t t 2 h).Mn ∧ _ at gates
  rw [←hv] at gates
  have hsCap : 2*s≤(2:ℤ)^a := by
    have hx:=power_split a c (by omega)
    have hz : (2:ℤ)^c=2*t := by rw [hdc,pow_succ]; dsimp [t]; ring
    rw [hx,hz]
    dsimp [s,h]
    nlinarith [show (0:ℤ)≤2^(a-c) by positivity]
  apply x_multiple_joint a d c d (a-c) (2^d-1) s (ceil v.B v.Mn) 1
    hd (by omega) (by omega) (by omega) (by have := Nat.pow_le_pow_right Nat.zero_lt_two hd; norm_num at this; omega)
    (by dsimp [s,h,t]; rw [Nat.cast_sub (Nat.one_le_two_pow)]; norm_num)
    gates.1 gates.2.1 (by norm_num) hsCap
  · have hz : v.z=(2:ℤ)^c := (row_source a d c d (by omega) (by omega)).2.2.1
    simpa only [hz,mul_one] using gates.2.2.2.1
  · exact gates.2.2.2.2

private theorem factor_four (j : ℕ) (hj : 2≤j) :
    (2:ℤ)^j=4*2^(j-2) := by
  rw [show j=2+(j-2) by omega,pow_add]
  norm_num

private theorem adj_capacity (a d ell : ℕ) (hd : 2≤d) (he : a=ell+d+1) :
    2*((2:ℤ)^ell*((2^d-1:ℕ):ℤ))≤(2:ℤ)^a := by
  have hp : 1≤(2:ℕ)^d := Nat.one_le_two_pow
  simp only [Nat.cast_sub hp,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  rw [he,pow_succ,pow_add]
  nlinarith [show (0:ℤ)≤2^ell by positivity]

private theorem sep_capacity (a d ell : ℕ) (hd : 2≤d) (he : a=ell+d+2) :
    2*((2:ℤ)^ell*((2*2^d-3:ℕ):ℤ))≤(2:ℤ)^a := by
  have hp : 3≤2*(2:ℕ)^d := by have := Nat.pow_le_pow_right Nat.zero_lt_two hd; norm_num at this; omega
  simp only [Nat.cast_sub hp,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [he,pow_add,pow_add]
  norm_num
  nlinarith [show (0:ℤ)≤2^ell by positivity]

/- Strict chart S1: e=2, g=h, s=h(t-1); b<d is used only here
in the coefficient substitution t=2y+T, and in no equality-face inference. -/
private theorem strict_adjacent (a b c d : ℕ)
    (hb : 2≤b) (hbd : b<d) (hcd : c=d+1) (hca : c<a) : NatJoint a b c d := by
  let y : ℤ:=2^b
  let t : ℤ:=2^d
  let h : ℤ:=2^(a-c)
  have hy : 4≤y := by simpa [y] using pow_lower b 2 hb
  have ht : 2*y≤t := by
    have hp:=pow_lower d (b+1) (by omega)
    simpa [pow_succ,y,t,mul_comm] using hp
  have hh : 2≤h := by simpa [h] using pow_lower (a-c) 1 (by omega)
  have cm:=margins_strict_adjacent (y-4) (t-2*y) (h-2) 0
    (by omega) (by omega) (by omega) (by norm_num)
  apply floor_multiple_chart a b c d (a-c) (2^d-1) hb hbd.le (by omega) hca
    (by have := Nat.pow_le_pow_right Nat.zero_lt_two (show 2≤d by omega); norm_num at this; omega)
    (adj_capacity a d (a-c) (by omega) (by omega))
  have hcd' : c-d=1 := by omega
  convert cm using 1 <;>
    dsimp [FloorMargins,actualRow,model,y,t,h] <;>
    simp only [hcd',pow_one,Nat.cast_sub (Nat.one_le_two_pow),Nat.cast_pow,
      Nat.cast_ofNat,Nat.cast_one] <;> ring_nf

/- Strict chart S2: e>=4, g=2^(c-d-2+a-c), s=g(2t-3). -/
private theorem strict_separated (a b c d : ℕ)
    (hb : 2≤b) (hbd : b<d) (hcd : d+2≤c) (hca : c<a) : NatJoint a b c d := by
  let y : ℤ:=2^b
  let t : ℤ:=2^d
  let h : ℤ:=2^(a-c)
  let f : ℤ:=2^(c-d-2)
  let ell:=c-d-2+(a-c)
  have hy : 4≤y := by simpa [y] using pow_lower b 2 hb
  have ht : 2*y≤t := by
    have hp:=pow_lower d (b+1) (by omega)
    simpa [pow_succ,y,t,mul_comm] using hp
  have hh : 2≤h := by simpa [h] using pow_lower (a-c) 1 (by omega)
  have hf : 1≤f := by dsimp [f]; exact_mod_cast (Nat.one_le_two_pow (n:=c-d-2))
  have cm:=margins_strict_separated (y-4) (t-2*y) (h-2) (f-1)
    (by omega) (by omega) (by omega) (by omega)
  have hu : 3≤2*(2:ℕ)^d := by have := Nat.pow_le_pow_right Nat.zero_lt_two (show 2≤d by omega); norm_num at this; omega
  apply floor_multiple_chart a b c d ell (2*2^d-3) hb hbd.le (by omega) hca
    (by omega) (sep_capacity a d ell (by omega) (by dsimp [ell]; omega))
  have he:=factor_four (c-d) (by omega)
  have hg : (2:ℤ)^ell=f*h := by dsimp [ell,f,h]; rw [pow_add]
  convert cm using 1 <;>
    dsimp [FloorMargins,actualRow] <;> simp only [he,hg] <;>
    dsimp [model] <;>
    simp only [Nat.cast_sub hu,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] <;>
    dsimp [y,t,h,f] <;> ring_nf

/- Equality X1 and X2 retain w=1; their third-bank certificates differ
from the floor charts, including the infinite t=4,h>=32 family. -/
private theorem equal_x1 (a c d : ℕ)
    (hd : 3≤d) (hcd : c=d+1) (hca : c+2≤a) : NatJoint a d c d := by
  let t : ℤ:=2^d
  let h : ℤ:=2^(a-c)
  have ht : 8≤t := by simpa [t] using pow_lower d 3 hd
  have hh : 4≤h := by simpa [h] using pow_lower (a-c) 2 (by omega)
  have cm:=margins_h4_e2_t8 0 (t-8) (h-4) 0
    (by norm_num) (by omega) (by omega) (by norm_num)
  apply one_multiple_chart a c d (by omega) hcd hca
  have he : c-d=1 := by omega
  convert cm using 1 <;> dsimp [actualRow,model,t,h] <;> simp only [he,pow_one] <;> ring_nf

private theorem equal_x2 (a : ℕ) (ha : 8≤a) : NatJoint a 2 3 2 := by
  let h : ℤ:=2^(a-3)
  have hh : 32≤h := by simpa [h] using pow_lower (a-3) 5 (by omega)
  have cm:=margins_h32_e2_t4 0 0 (h-32) 0
    (by norm_num) (by norm_num) (by omega) (by norm_num)
  apply one_multiple_chart a 3 2 (by norm_num) (by norm_num) (by omega)
  convert cm using 1 <;> dsimp [actualRow,model,h] <;> norm_num <;> ring_nf

/- Equality X3: e>=4,t>=8,h>=4; X4: e>=8,t=4,h>=4. -/
private theorem equal_x3 (a c d : ℕ)
    (hd : 3≤d) (hcd : d+2≤c) (hca : c+2≤a) : NatJoint a d c d := by
  let t : ℤ:=2^d
  let h : ℤ:=2^(a-c)
  let f : ℤ:=2^(c-d-2)
  let ell:=c-d-2+(a-c)
  have ht : 8≤t := by simpa [t] using pow_lower d 3 hd
  have hh : 4≤h := by simpa [h] using pow_lower (a-c) 2 (by omega)
  have hf : 1≤f := by dsimp [f]; exact one_le_pow₀ (by norm_num)
  have cm:=margins_h4_e4_t8 0 (t-8) (h-4) (f-1)
    (by norm_num) (by omega) (by omega) (by omega)
  have hu : 3≤2*(2:ℕ)^d := by have := Nat.pow_le_pow_right Nat.zero_lt_two (show 2≤d by omega); norm_num at this; omega
  apply floor_multiple_chart a d c d ell (2*2^d-3) (by omega) (by omega) (by omega) (by omega)
    (by omega) (sep_capacity a d ell (by omega) (by dsimp [ell]; omega))
  have he:=factor_four (c-d) (by omega)
  have hg : (2:ℤ)^ell=f*h := by dsimp [ell,f,h]; rw [pow_add]
  convert cm using 1 <;> dsimp [FloorMargins,actualRow] <;> simp only [he,hg] <;>
    dsimp [model] <;> simp only [Nat.cast_sub hu,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] <;>
    dsimp [t,h,f] <;> ring_nf

private theorem equal_x4 (a c : ℕ)
    (hc : 5≤c) (hca : c+2≤a) : NatJoint a 2 c 2 := by
  let h : ℤ:=2^(a-c)
  let f : ℤ:=2^(c-5)
  let ell:=c-4+(a-c)
  have hh : 4≤h := by simpa [h] using pow_lower (a-c) 2 (by omega)
  have hf : 1≤f := by dsimp [f]; exact one_le_pow₀ (by norm_num)
  have cm:=margins_h4_e8_t4 0 0 (h-4) (f-1)
    (by norm_num) (by norm_num) (by omega) (by omega)
  apply floor_multiple_chart a 2 c 2 ell 5 (by norm_num) (by norm_num) (by omega) (by omega)
    (by norm_num) (by simpa using sep_capacity a 2 ell (by norm_num) (by dsimp [ell]; omega))
  have he : (2:ℤ)^(c-2)=8*f := by
    have hex : c-2=3+(c-5) := by omega
    rw [hex,pow_add]; norm_num [f]
  have hg : (2:ℤ)^ell=2*f*h := by
    have hex : ell=1+(c-5)+(a-c) := by dsimp [ell]; omega
    rw [hex,pow_add,pow_add] <;> dsimp [f,h] <;> ring
  convert cm using 1 <;> dsimp [FloorMargins,actualRow] <;> simp only [he,hg] <;>
    dsimp [model] <;> norm_num <;> dsimp [h,f] <;> ring_nf

/- Equality X5: no divisibility assumption on s=5h+r. -/
private theorem equal_x5 (a : ℕ) (ha : 7≤a) : NatJoint a 2 4 2 := by
  let h : ℤ:=2^(a-4)
  let v:=model 4 4 4 h
  let r:=ceil v.B v.Mn
  let s:=5*h+r
  have hh : 8≤h := by simpa [h] using pow_lower (a-4) 3 (by omega)
  have cm:=margins_h8_e4_t4 0 0 (h-8) 0
    (by norm_num) (by norm_num) (by omega) (by norm_num)
  have bounds :
      0≤2*(2*v.A-5*h*v.M-v.B) ∧
      0≤(10*h*v.M-3*v.A-1)*v.Mn+2*v.B*v.M ∧
      0≤2*(3*v.A-5*h*v.Mn-v.B-v.Mn) ∧
      0≤10*h*v.Mn+2*v.B-5*v.A-1 ∧
      0≤v.B*v.t*v.y*v.z-v.M*v.Mn ∧ 0≤h*v.Mn-v.B ∧
      0≤v.L-2*v.B-h*v.D ∧ 0≤v.z*v.B-2*v.L-1 := by
    convert cm using 1 <;> dsimp [v,model] <;> ring_nf
  rcases bounds with ⟨b0,b1,b2,b3,F,G,W,Z⟩
  have first:=dynamic_first h hh ⟨b0,b1,b2,b3,F,G⟩
  have gates:=x_floor_gates 4 4 4 h s h (by norm_num) (by norm_num) (by norm_num)
    (by omega) first F G W Z
  change 1≤r ∧ r≤h ∧ r*v.M<v.B ∧ 0≤(v.L-r*v.M)/v.B ∧
    2*((v.L-r*v.M)/v.B)<v.z ∧ XGates v s r ((v.L-r*v.M)/v.B) at gates
  have hv : actualRow a 2 4 2=v := by dsimp [actualRow,v,h]; norm_num
  have hx : (2:ℤ)^a=16*h := by
    rw [power_split a 4 (by omega)] <;> norm_num [h] <;> ring
  have hq : r.toNat-1<2^(a-4) := by
    exact_mod_cast (show ((r.toNat-1:ℕ):ℤ)<2^(a-4) by dsimp [h] at gates; omega)
  have hsm : s.toNat-1=5*2^(a-4)+(r.toNat-1) := by
    have hs0 : 0≤s := by dsimp [s]; omega
    have hr0 : 0≤r := by omega
    apply Int.ofNat_inj.mp
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
    dsimp [s,h]
    omega
  apply x_nat_joint a 2 4 2 s r ((v.L-r*v.M)/v.B)
    (by norm_num) (by norm_num) (by omega) (by omega)
    (by dsimp [s]; omega) gates.1 (by dsimp [s]; omega) gates.2.2.2.1
    (by rw [hx]; dsimp [s]; nlinarith [gates.2.1])
    (by simpa [v,model] using gates.2.2.2.2.1)
    (by rw [hsm]; exact dynamic_submask (a-4) (r.toNat-1) hq)
  rw [hv]
  exact gates.2.2.2.2.2

/- Equality V1: h=2,e=2, all t>=4. -/
private theorem equal_v1 (a c d : ℕ)
    (hd : 2≤d) (hcd : c=d+1) (hac : a=c+1) : NatJoint a d c d := by
  let t : ℤ:=2^d
  have ht : 4≤t := by simpa [t] using pow_lower d 2 hd
  have cm:=margins_h2_e2 0 (t-4) 0 0
    (by norm_num) (by omega) (by norm_num) (by norm_num)
  have hz : (2:ℤ)^c=2*t := by rw [hcd,pow_succ]; dsimp [t]; ring
  have hx : (2:ℤ)^a=4*t := by rw [hac,pow_succ,hz]; ring
  apply v_nat_joint a c d 1 3 hd (by omega) hac (by norm_num) (by norm_num)
    (by norm_num) (by rw [hz]; omega) (by rw [hx]; omega)
  have hc1 : c-d=1 := by omega
  have ha1 : a-c=1 := by omega
  convert cm using 1 <;>
    dsimp [VGates,actualRow,model] <;> simp only [hc1,ha1,pow_one] <;>
    dsimp [t] <;> ring_nf <;> first | rfl | trivial

/- Equality V2: h=2,e>=4,t>=8. R=6f+1 is odd before toNat. -/
private theorem equal_v2 (a c d : ℕ)
    (hd : 3≤d) (hcd : d+2≤c) (hac : a=c+1) : NatJoint a d c d := by
  let t : ℤ:=2^d
  let f : ℤ:=2^(c-d-2)
  have ht : 8≤t := by simpa [t] using pow_lower d 3 hd
  have hf : 1≤f := by dsimp [f]; exact one_le_pow₀ (by norm_num)
  have cm:=margins_h2_t8 0 (t-8) 0 (f-1)
    (by norm_num) (by omega) (by norm_num) (by omega)
  have he:=factor_four (c-d) (by omega)
  have hz : (2:ℤ)^c=4*f*t := by rw [power_split c d (by omega),he] <;> dsimp [f,t] <;> ring
  have hx : (2:ℤ)^a=8*f*t := by rw [hac,pow_succ,hz]; ring
  apply v_nat_joint a c d (2*f) (6*f+1) (by omega) (by omega) hac
    (by omega) (by omega) (by omega) (by rw [hz]; nlinarith) (by rw [hx]; nlinarith)
  have ha1 : a-c=1 := by omega
  convert cm using 1 <;> dsimp [VGates,actualRow] <;> simp only [he] <;>
    dsimp [model] <;> simp only [ha1,pow_one] <;> dsimp [t,f] <;> ring_nf <;> first | rfl | trivial

/- Equality V3: h=2,t=4,e>=16. The e=4,8 corners are literal finite words. -/
private theorem equal_v3 (a c : ℕ) (hc : 6≤c) (hac : a=c+1) : NatJoint a 2 c 2 := by
  let f : ℤ:=2^(c-6)
  have hf : 1≤f := by dsimp [f]; exact one_le_pow₀ (by norm_num)
  have cm:=margins_h2_t4_e16 0 0 0 (f-1)
    (by norm_num) (by norm_num) (by norm_num) (by omega)
  have he : (2:ℤ)^(c-2)=16*f := by
    have h : c-2=4+(c-6) := by omega
    rw [h,pow_add]; norm_num [f]
  have hz : (2:ℤ)^c=64*f := by rw [power_split c 2 (by omega),he]; norm_num <;> ring
  have hx : (2:ℤ)^a=128*f := by rw [hac,pow_succ,hz]; ring
  apply v_nat_joint a c 2 (8*f) (24*f+1) (by norm_num) (by omega) hac
    (by omega) (by omega) (by omega) (by rw [hz]; nlinarith) (by rw [hx]; nlinarith)
  have ha1 : a-c=1 := by omega
  convert cm using 1 <;> dsimp [VGates,actualRow] <;> simp only [he] <;>
    dsimp [model] <;> simp only [ha1,pow_one] <;> norm_num <;> dsimp [f] <;> ring_nf <;> simp only [iff_self,implies_true]

/- Six isolated finite words. Only concrete list permutation and integer
reduction are used here. The recursive strip proposition covers every natural
take-prefix, including overlong prefixes, by the imported transport theorem. -/

private theorem finite_5232 : NatJoint 5 2 3 2 := by
  refine ⟨[10, 9, 4, 5, 8, 7, 1, 3, 11, 0, 2, 6], ?_, ?_, 7, by norm_num [size], ?_⟩
  · change ([10, 9, 4, 5, 8, 7, 1, 3, 11, 0, 2, 6] : List ℕ).Perm (List.range 12)
    decide
  · norm_num [InStrip,oldValue,sourceMod,base,size,centered]
  · norm_num [InStrip,newValue,sourceMod,base,size,centered,insertAt]

private theorem finite_6232 : NatJoint 6 2 3 2 := by
  refine ⟨[11, 10, 4, 3, 8, 7, 1, 5, 9, 12, 0, 2, 6], ?_, ?_, 7, by norm_num [size], ?_⟩
  · change ([11, 10, 4, 3, 8, 7, 1, 5, 9, 12, 0, 2, 6] : List ℕ).Perm (List.range 13)
    decide
  · norm_num [InStrip,oldValue,sourceMod,base,size,centered]
  · norm_num [InStrip,newValue,sourceMod,base,size,centered,insertAt]

private theorem finite_7232 : NatJoint 7 2 3 2 := by
  refine ⟨[12, 11, 7, 4, 3, 9, 8, 1, 0, 13, 5, 2, 10, 6], ?_, ?_, 8, by norm_num [size], ?_⟩
  · change ([12, 11, 7, 4, 3, 9, 8, 1, 0, 13, 5, 2, 10, 6] : List ℕ).Perm (List.range 14)
    decide
  · norm_num [InStrip,oldValue,sourceMod,base,size,centered]
  · norm_num [InStrip,newValue,sourceMod,base,size,centered,insertAt]

private theorem finite_6242 : NatJoint 6 2 4 2 := by
  refine ⟨[4, 11, 8, 5, 6, 10, 9, 1, 12, 2, 13, 0, 3, 7], ?_, ?_, 8, by norm_num [size], ?_⟩
  · change ([4, 11, 8, 5, 6, 10, 9, 1, 12, 2, 13, 0, 3, 7] : List ℕ).Perm (List.range 14)
    decide
  · norm_num [InStrip,oldValue,sourceMod,base,size,centered]
  · norm_num [InStrip,newValue,sourceMod,base,size,centered,insertAt]

private theorem finite_5242 : NatJoint 5 2 4 2 := by
  refine ⟨[11, 3, 5, 4, 2, 1, 0, 9, 12, 6, 10, 8, 7], ?_, ?_, 6, by norm_num [size], ?_⟩
  · change ([11, 3, 5, 4, 2, 1, 0, 9, 12, 6, 10, 8, 7] : List ℕ).Perm (List.range 13)
    decide
  · norm_num [InStrip,oldValue,sourceMod,base,size,centered]
  · norm_num [InStrip,newValue,sourceMod,base,size,centered,insertAt]

private theorem finite_6252 : NatJoint 6 2 5 2 := by
  refine ⟨[5, 4, 9, 6, 0, 11, 10, 1, 13, 3, 14, 7, 12, 2, 8], ?_, ?_, 8, by norm_num [size], ?_⟩
  · change ([5, 4, 9, 6, 0, 11, 10, 1, 13, 3, 14, 7, 12, 2, 8] : List ℕ).Perm (List.range 15)
    decide
  · norm_num [InStrip,oldValue,sourceMod,base,size,centered]
  · norm_num [InStrip,newValue,sourceMod,base,size,centered,insertAt]

/- Exhaustion is on the natural exponents, not on a bounded parameter search.
There are exactly two strict charts, eight equality charts and six fixed words. -/
private theorem all_nat_joint (a b c d : ℕ)
    (hb : 2≤b) (hbd : b≤d) (hdc : d<c) (hca : c<a) : NatJoint a b c d := by
  by_cases hstrict : b<d
  · by_cases hnear : c=d+1
    · exact strict_adjacent a b c d hb hstrict hnear hca
    · exact strict_separated a b c d hb hstrict (by omega) hca
  · have heq : b=d := by omega
    subst b
    by_cases htwo : a=c+1
    · by_cases he2 : c=d+1
      · exact equal_v1 a c d hb he2 htwo
      · by_cases ht8 : 3≤d
        · exact equal_v2 a c d ht8 (by omega) htwo
        · have hd2 : d=2 := by omega
          subst d
          by_cases he16 : 6≤c
          · exact equal_v3 a c he16 htwo
          · have corners : (a=5 ∧ c=4) ∨ (a=6 ∧ c=5) := by omega
            rcases corners with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
            · exact finite_5242
            · exact finite_6252
    · have hfour : c+2≤a := by omega
      by_cases he2 : c=d+1
      · by_cases ht8 : 3≤d
        · exact equal_x1 a c d ht8 he2 hfour
        · have hd2 : d=2 := by omega
          have hc3 : c=3 := by omega
          subst d
          subst c
          by_cases hh32 : 8≤a
          · exact equal_x2 a hh32
          · have corners : a=5 ∨ a=6 ∨ a=7 := by omega
            rcases corners with rfl|rfl|rfl
            · exact finite_5232
            · exact finite_6232
            · exact finite_7232
      · by_cases ht8 : 3≤d
        · exact equal_x3 a c d ht8 (by omega) hfour
        · have hd2 : d=2 := by omega
          subst d
          by_cases he8 : 5≤c
          · exact equal_x4 a c he8 hfour
          · have hc4 : c=4 := by omega
            subst c
            by_cases hh8 : 7≤a
            · exact equal_x5 a hh8
            · have ha6 : a=6 := by omega
              subst a
              exact finite_6242


end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakCSecond.CMiddle
