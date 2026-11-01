/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Supports
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-consumed-native-supports)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Exhaustive disjoint native bit supports, including literal complements. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior.Parameters
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
private def wSupport (p : Parameters) : Fin 4 → Finset ℕ :=
  let A := Finset.range (s p)
  let B := {s p,s p+1}
  ![A,∅,B,Finset.range (p.b-1) \ (A ∪ B)]
private def xSupport (p : Parameters) : Fin 4 → Finset ℕ :=
  let A := {r p+p.d,r p+p.c+1,r p+p.c,r p+1}
  let B := {r p+p.c+p.d}
  let P := {0}
  ![A,B,Finset.range (p.a-1) \ ((A ∪ B) ∪ P),P]
private def support (p : Parameters) (bank chain : Fin 4) : Finset ℕ :=
  (![uSupport p,vSupport p,wSupport p,xSupport p] : Fin 4 → Fin 4 → Finset ℕ) chain bank
private def nativeMask (p : Parameters) (bank chain : Fin 4) : ℕ :=
  ∑ e ∈ support p bank chain, 2^e

private theorem support_partition (p : Parameters) :
    (∀ chain bank, support p bank chain ⊆ Finset.range (lengths p chain)) ∧
    (∀ chain j k, j ≠ k → Disjoint (support p j chain) (support p k chain)) ∧
    (∀ chain, ((support p 0 chain ∪ support p 1 chain) ∪ support p 2 chain) ∪
      support p 3 chain = Finset.range (lengths p chain)) := by
  have hc := p.hc; have hd := p.hd; have ha := p.ha; have hb := p.hb
  obtain ⟨heA,heB,heD⟩ := parameter_eqs p
  constructor
  · intro chain bank e he
    by_cases h : p.c = 2
    all_goals fin_cases chain <;> fin_cases bank <;>
      simp [support,uSupport,vSupport,wSupport,xSupport,lengths,h] at he ⊢ <;> omega
  constructor
  · intro chain j k hjk
    apply Finset.disjoint_left.mpr
    intro e he hf
    by_cases h : p.c = 2
    all_goals fin_cases chain <;> fin_cases j <;> fin_cases k <;>
      simp_all [support,uSupport,vSupport,wSupport,xSupport]
    all_goals omega
  · intro chain
    ext e
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
