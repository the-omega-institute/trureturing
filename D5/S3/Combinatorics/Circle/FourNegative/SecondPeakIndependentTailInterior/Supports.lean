/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Supports
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-consumed-native-supports)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Exhaustive disjoint native bit supports, including literal complements. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Parameters
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.NativeMasks
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
open private Parameters Parameters.a Parameters.b Parameters.c Parameters.d
  Parameters.hc Parameters.hd Parameters.ha Parameters.hb r s v parameter_eqs from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Parameters
open private MaskPartition partition_labels labels_disjoint full_bits from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.NativeMasks
open MaxPlusTwo.Chambers
open scoped BigOperators

private def lengths (p : Parameters) : Fin 4 → ℕ := ![p.d-1,p.c-1,p.b-1,p.a-1]
private def offsets (p : Parameters) : Fin 4 → ℕ := ![0,p.d,p.d+p.c,p.d+p.c+p.b]
private def uSupport (p : Parameters) : Fin 4 → Finset ℕ :=
  let A := if p.c = 2 then Finset.range (p.d-3) else {p.d-p.c-1}
  let B := {p.d-3}
  ![A,Finset.range (p.d-1) \ (A ∪ B),B,∅]
private def vSupport (p : Parameters) : Fin 4 → Finset ℕ :=
  ![Finset.range (p.c-1),∅,∅,∅]
private def wFirst (p : Parameters) : Finset ℕ :=
  if r p = 0 then
    if p.c = 2 then Finset.range (s p+2)
    else if p.c = 3 then
      if s p = 0 then {1} else insert (s p+1) (insert (s p) (Finset.range (s p-1)))
    else if s p = 0 then ∅ else insert (s p) (Finset.range (s p-1))
  else if r p = 1 then
    if p.c = 2 then Finset.range (s p+2) else Finset.range (s p+1)
  else if r p = 2 then insert (s p+1) (Finset.range (s p))
  else Finset.range (s p)
private def wSupport (p : Parameters) : Fin 4 → Finset ℕ :=
  ![wFirst p,∅,Finset.range (s p+2) \ wFirst p,
    Finset.range (p.b-1) \ Finset.range (s p+2)]
private def xFirst (p : Parameters) : Finset ℕ :=
  if r p = 0 then
    if p.c = 2 then {p.d-3}
    else if p.c = 3 then {p.d-3,1}
    else {p.d-3,p.c-2,p.c-3}
  else if r p = 1 then
    if p.c = 2 then {p.d-2,1} else {p.d-2,p.c-1,p.c-2}
  else if r p = 2 then {p.d-1,p.c,p.c-1}
  else {r p+p.d-3,r p+p.c-2,r p+p.c-3,r p-2}
private def xSupport (p : Parameters) : Fin 4 → Finset ℕ :=
  let A := xFirst p
  let B := {p.a-3}
  let P := {0}
  ![A,B,Finset.range (p.a-1) \ ((A ∪ B) ∪ P),P]

private def roundingD (p : Parameters) : ℚ :=
  let z : ℚ := 2^p.c
  let w : ℚ := 2^p.d
  if r p = 0 then
    if p.c = 2 then w/8 else if p.c = 3 then w/8+2 else (w+3*z)/8
  else if r p = 1 then
    if p.c = 2 then w/4+2 else (w+3*z)/4
  else if r p = 2 then (w+3*z)/2
  else 2^(r p)*(w+3*z+2)/8
private def roundingEps (p : Parameters) : ℚ := if s p = 0 then 1/2 else 0
private def roundingW (p : Parameters) : ℚ :=
  let q : ℚ := 2^(s p)
  if r p = 0 then
    if p.c = 2 then 4*q-1
    else if p.c = 3 then 7*q/2-1-roundingEps p
    else 3*q/2-1-roundingEps p
  else if r p = 1 then
    if p.c = 2 then 4*q-1 else 2*q-1
  else if r p = 2 then 3*q-1
  else q-1

private theorem xFirst_bounds (p : Parameters) (e : ℕ) (he : e ∈ xFirst p) :
    0 < e ∧ e < p.a-3 := by
  have hc := p.hc; have hd := p.hd; have ha := p.ha
  have heA := (parameter_eqs p).1
  by_cases h0 : r p = 0 <;> by_cases h1 : r p = 1 <;>
    by_cases h2 : r p = 2 <;> by_cases hc2 : p.c = 2 <;> by_cases hc3 : p.c = 3 <;>
    simp_all [xFirst] <;> omega

private theorem wFirst_bounds (p : Parameters) (e : ℕ) (he : e ∈ wFirst p) :
    e < s p+2 := by
  by_cases h0 : r p = 0 <;> by_cases h1 : r p = 1 <;>
    by_cases h2 : r p = 2 <;> by_cases hc2 : p.c = 2 <;>
    by_cases hc3 : p.c = 3 <;> by_cases hs : s p = 0 <;>
    simp_all [wFirst] <;> omega
private def support (p : Parameters) (bank chain : Fin 4) : Finset ℕ :=
  (![uSupport p,vSupport p,wSupport p,xSupport p] : Fin 4 → Fin 4 → Finset ℕ) chain bank
private def nativeMask (p : Parameters) (bank chain : Fin 4) : ℕ :=
  ∑ e ∈ support p bank chain, 2^e

private theorem power_sub_q (n k : ℕ) (hk : k ≤ n) :
    (2 : ℚ)^(n-k) = 2^n / 2^k := by
  apply (eq_div_iff (by positivity : (2 : ℚ)^k ≠ 0)).2
  rw [← pow_add, Nat.sub_add_cancel hk]

private theorem sum_pair_q (i j : ℕ) (h : i ≠ j) :
    (∑ e ∈ ({i,j} : Finset ℕ), (2 : ℚ)^e) = 2^i+2^j := by simp [h]
private theorem sum_triple_q (i j k : ℕ)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (∑ e ∈ ({i,j,k} : Finset ℕ), (2 : ℚ)^e) = 2^i+2^j+2^k := by
  simp [hij,hik,hjk,add_assoc]
private theorem sum_quad_q (i j k l : ℕ)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (∑ e ∈ ({i,j,k,l} : Finset ℕ), (2 : ℚ)^e) = 2^i+2^j+2^k+2^l := by
  simp [hij,hik,hil,hjk,hjl,hkl,add_assoc]

private theorem native_X0 (p : Parameters) :
    (nativeMask p 0 3 : ℚ) = roundingD p := by
  simp only [nativeMask,Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat]
  change (∑ e ∈ xFirst p, (2 : ℚ)^e) = roundingD p
  have hc := p.hc; have hd := p.hd
  dsimp only [xFirst,roundingD]
  split_ifs with h0 hc2 hc3 h1 hc2 h2
  · simp only [Finset.sum_singleton]
    simpa using power_sub_q p.d 3 (by omega)
  · rw [sum_pair_q _ _ (by omega)]
    rw [power_sub_q p.d 3 (by omega)]
    norm_num
  · rw [sum_triple_q _ _ _ (by omega) (by omega) (by omega)]
    rw [power_sub_q p.d 3 (by omega),power_sub_q p.c 2 (by omega),
      power_sub_q p.c 3 (by omega)]
    norm_num; ring
  · rw [sum_pair_q _ _ (by omega)]
    rw [power_sub_q p.d 2 (by omega)]
    norm_num
  · rw [sum_triple_q _ _ _ (by omega) (by omega) (by omega)]
    rw [power_sub_q p.d 2 (by omega),power_sub_q p.c 1 (by omega),
      power_sub_q p.c 2 (by omega)]
    norm_num; ring
  · rw [sum_triple_q _ _ _ (by omega) (by omega) (by omega)]
    rw [power_sub_q p.d 1 (by omega),power_sub_q p.c 1 (by omega)]
    norm_num; ring
  · have hr : 3 ≤ r p := by omega
    rw [sum_quad_q _ _ _ _ (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)]
    rw [power_sub_q (r p+p.d) 3 (by omega),
      power_sub_q (r p+p.c) 2 (by omega),
      power_sub_q (r p+p.c) 3 (by omega),power_sub_q (r p) 2 (by omega)]
    simp only [pow_add]; norm_num; ring

private theorem sum_range_rat (n : ℕ) :
    (∑ e ∈ Finset.range n, (2 : ℚ)^e) = 2^n-1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring

private theorem native_W0 (p : Parameters) :
    (nativeMask p 0 2 : ℚ) = roundingW p := by
  simp only [nativeMask,Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat]
  change (∑ e ∈ wFirst p, (2 : ℚ)^e) = roundingW p
  dsimp only [wFirst,roundingW,roundingEps]
  split_ifs with h0 hc2 hc3 hs hs h1 hc2 h2
  · rw [sum_range_rat]; simp only [pow_add]; norm_num; ring
  · simp [hs]; norm_num
  · rw [Finset.sum_insert (by simp),Finset.sum_insert (by simp),sum_range_rat]
    rw [power_sub_q (s p) 1 (by omega)]
    simp only [pow_succ]; norm_num; ring
  · simp [hs]; norm_num
  · rw [Finset.sum_insert (by simp),sum_range_rat]
    rw [power_sub_q (s p) 1 (by omega)]
    norm_num; ring
  · rw [sum_range_rat]; simp only [pow_add]; norm_num; ring
  · rw [sum_range_rat,pow_succ]; ring
  · rw [Finset.sum_insert (by simp),sum_range_rat,pow_succ]; ring
  · rw [sum_range_rat]

private theorem support_partition (p : Parameters) :
    (∀ chain bank, support p bank chain ⊆ Finset.range (lengths p chain)) ∧
    (∀ chain j k, j ≠ k → Disjoint (support p j chain) (support p k chain)) ∧
    (∀ chain, ((support p 0 chain ∪ support p 1 chain) ∪ support p 2 chain) ∪
      support p 3 chain = Finset.range (lengths p chain)) := by
  have hc := p.hc; have hd := p.hd; have ha := p.ha; have hb := p.hb
  obtain ⟨heA,heB,heD⟩ := parameter_eqs p
  have X (e : ℕ) : e ∈ xFirst p → 0 < e ∧ e < p.a-3 := xFirst_bounds p e
  have W (e : ℕ) : e ∈ wFirst p → e < s p+2 := wFirst_bounds p e
  constructor
  · intro chain bank e he
    have hX := X e; have hW := W e
    by_cases h : p.c = 2
    all_goals fin_cases chain <;> fin_cases bank <;>
      simp [support,uSupport,vSupport,wSupport,xSupport,lengths,h] at he ⊢ <;> omega
  constructor
  · intro chain j k hjk
    apply Finset.disjoint_left.mpr
    intro e he hf
    have hX := X e; have hW := W e
    by_cases h : p.c = 2
    all_goals fin_cases chain <;> fin_cases j <;> fin_cases k <;>
      simp_all [support,uSupport,vSupport,wSupport,xSupport]
    all_goals omega
  · intro chain
    ext e
    have hX := X e; have hW := W e
    by_cases h : p.c = 2
    all_goals fin_cases chain <;>
      simp [support,uSupport,vSupport,wSupport,xSupport,lengths,h] <;> omega

private theorem native_bits (p : Parameters) (j chain : Fin 4) :
    (nativeMask p j chain).bitIndices.toFinset = support p j chain :=
  Finset.toFinset_bitIndices_sum_two_pow _

private theorem native_total (p : Parameters) (chain : Fin 4) :
    nativeMask p 0 chain + nativeMask p 1 chain +
      nativeMask p 2 chain + nativeMask p 3 chain = 2^(lengths p chain)-1 := by
  obtain ⟨_,hd,hfull⟩ := support_partition p
  have h01 := hd chain 0 1 (by decide)
  have h012 : Disjoint (support p 0 chain ∪ support p 1 chain) (support p 2 chain) := by
    exact Finset.disjoint_union_left.mpr ⟨hd chain 0 2 (by decide),hd chain 1 2 (by decide)⟩
  have h3 : Disjoint ((support p 0 chain ∪ support p 1 chain) ∪ support p 2 chain)
      (support p 3 chain) := by
    exact Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨hd chain 0 3 (by decide),hd chain 1 3 (by decide)⟩,
       hd chain 2 3 (by decide)⟩
  have hs := Finset.sum_union h3 (f := fun e : ℕ => 2^e)
  rw [hfull,Finset.sum_union h012,Finset.sum_union h01] at hs
  have hgeom := congrArg (fun S : Finset ℕ => ∑ e ∈ S, (2 : ℕ)^e)
    (full_bits (lengths p chain))
  simp only [Finset.sum_toFinset_bitIndices_two_pow] at hgeom
  rw [← hgeom] at hs
  exact hs.symm

private theorem native_cap (p : Parameters) (j chain : Fin 4) :
    nativeMask p j chain < 2^(lengths p chain) := by
  have ht := native_total p chain
  have hp := Nat.two_pow_pos (lengths p chain)
  fin_cases j <;> omega

private theorem bits_add (m n : ℕ)
    (hd : Disjoint m.bitIndices.toFinset n.bitIndices.toFinset) :
    (m+n).bitIndices.toFinset = m.bitIndices.toFinset ∪ n.bitIndices.toFinset := by
  apply Finset.geomSum_injective (by decide : 2 ≤ (2:ℕ))
  rw [Finset.sum_toFinset_bitIndices_two_pow,Finset.sum_union hd]
  simp only [Finset.sum_toFinset_bitIndices_two_pow]

private theorem labels_add (len off m n : ℕ)
    (hd : Disjoint m.bitIndices.toFinset n.bitIndices.toFinset) :
    (chamberLabels len off m ++ chamberLabels len off n).Perm
      (chamberLabels len off (m+n)) := by
  apply (List.perm_ext_iff_of_nodup
    ((chamberLabels_nodup _ _ _).append (chamberLabels_nodup _ _ _)
      (labels_disjoint len off m n hd)) (chamberLabels_nodup _ _ _)).mpr
  intro i
  have hb := bits_add m n hd
  have hbit (e : ℕ) : (m+n).testBit e = true ↔ m.testBit e = true ∨ n.testBit e = true := by
    have he := Finset.ext_iff.mp hb e
    simpa only [Finset.mem_union,List.mem_toFinset,Nat.mem_bitIndices] using he
  simp only [List.mem_append,chamberLabels_mem,hbit]
  constructor
  · rintro (⟨e,he,h,hi⟩|⟨e,he,h,hi⟩)
    · exact ⟨e,he,Or.inl h,hi⟩
    · exact ⟨e,he,Or.inr h,hi⟩
  · rintro ⟨e,he,h,hi⟩
    rcases h with h|h
    · exact Or.inl ⟨e,he,h,hi⟩
    · exact Or.inr ⟨e,he,h,hi⟩

private def chainLabels (p : Parameters) (j chain : Fin 4) : List ℕ :=
  chamberLabels (lengths p chain) (offsets p chain) (nativeMask p j chain)

private theorem native_inventory (p : Parameters) (chain : Fin 4) :
    (chainLabels p 0 chain ++ chainLabels p 1 chain ++
      chainLabels p 2 chain ++ chainLabels p 3 chain).Perm
      (List.range' (offsets p chain) (lengths p chain)) := by
  obtain ⟨_,hd,hfull⟩ := support_partition p
  have dis (j k : Fin 4) (hjk : j ≠ k) :
      Disjoint (nativeMask p j chain).bitIndices.toFinset
        (nativeMask p k chain).bitIndices.toFinset := by
    rw [native_bits,native_bits]; exact hd chain j k hjk
  have hb := bits_add _ _ (dis 1 2 (by decide))
  have ht := native_total p chain
  have hp := Nat.two_pow_pos (lengths p chain)
  have partition : MaskPartition (lengths p chain) (nativeMask p 0 chain)
      (nativeMask p 1 chain + nativeMask p 2 chain) (nativeMask p 3 chain) := by
    refine ⟨native_cap p 0 chain,by omega,native_cap p 3 chain,?_,dis 0 3 (by decide),?_,?_⟩
    · rw [hb]
      exact Finset.disjoint_union_right.mpr ⟨dis 0 1 (by decide),dis 0 2 (by decide)⟩
    · rw [hb]
      exact Finset.disjoint_union_left.mpr ⟨dis 1 3 (by decide),dis 2 3 (by decide)⟩
    · rw [hb,native_bits,native_bits,native_bits,native_bits]
      simpa only [Finset.union_assoc] using hfull chain
  have hs := (labels_add (lengths p chain) (offsets p chain)
      (nativeMask p 1 chain) (nativeMask p 2 chain) (dis 1 2 (by decide))).append_left
        (chainLabels p 0 chain)
  have hf := partition_labels _ (offsets p chain) _ _ _ partition
  exact (by simpa only [chainLabels,List.append_assoc] using
    hs.append_right (chainLabels p 3 chain)).trans hf

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
