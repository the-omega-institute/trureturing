/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/NativeMasks
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Native shifted high-mask and low-mask partition of physical W occurrences. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks

/-! Native shifted high-mask and low-mask partition of physical W occurrences. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private mask_complement from D5.S3.Combinatorics.Circle.ThreeBitSource
open scoped BigOperators

/-- All three masks are genuine native bit subsets, rather than capacities alone. -/
private structure MaskPartition (len h q low : ℕ) : Prop where
  hcap : h<2^len
  qcap : q<2^len
  lowcap : low<2^len
  hq : Disjoint h.bitIndices.toFinset q.bitIndices.toFinset
  hl : Disjoint h.bitIndices.toFinset low.bitIndices.toFinset
  ql : Disjoint q.bitIndices.toFinset low.bitIndices.toFinset
  full : (h.bitIndices.toFinset ∪ q.bitIndices.toFinset) ∪ low.bitIndices.toFinset=
    Finset.range len

/-- Uniqueness of binary geometric sums proves the exact native shift. -/
private theorem scaled_bits (s n : ℕ) :
    (2^s*n).bitIndices.toFinset=n.bitIndices.toFinset.image (s+·) := by
  apply Finset.geomSum_injective (by decide : 2 ≤ (2:ℕ))
  dsimp only
  rw [Finset.sum_toFinset_bitIndices_two_pow,
    Finset.sum_image (by intro i hi j hj hij; exact Nat.add_left_cancel hij)]
  simp_rw [pow_add]
  rw [←Finset.mul_sum,Finset.sum_toFinset_bitIndices_two_pow]

private theorem full_bits (c : ℕ) :
    (2^c-1).bitIndices.toFinset=Finset.range c := by
  ext i
  simp [List.mem_toFinset,Nat.mem_bitIndices,Nat.testBit_two_pow_sub_one]

private theorem native_partition (c s H : ℕ) (hH : H ≤ 2^c-1) :
    let lam := 2^s
    let m := (2^c-1)*lam
    let h := lam*H
    let low := lam-1
    (m ^^^ h)+h=m ∧ MaskPartition (c+s) h (m ^^^ h) low := by
  dsimp only
  let lam := 2^s
  let m := (2^c-1)*lam
  let h := lam*H
  let low := lam-1
  let q := m ^^^ h
  have zpos : 0<2^c := Nat.two_pow_pos c
  have lampos : 0<lam := Nat.two_pow_pos s
  have Hlt : H<2^c := by omega
  have Hbits : H.bitIndices.toFinset⊆Finset.range c := by
    intro i hi
    have hp := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)
    apply Finset.mem_range.mpr
    by_contra hnot
    have hpow := Nat.pow_le_pow_right (by decide : 0<2) (show c ≤ i by omega)
    omega
  have hbits : h.bitIndices.toFinset=H.bitIndices.toFinset.image (s+·) := by
    exact scaled_bits s H
  have mbits : m.bitIndices.toFinset=(Finset.range c).image (s+·) := by
    dsimp [m,lam]
    rw [Nat.mul_comm,scaled_bits,full_bits]
  have sub : h.bitIndices.toFinset⊆m.bitIndices.toFinset := by
    rw [hbits,mbits]
    intro i hi
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨e,Hbits he,rfl⟩
  have bit_sub (i : ℕ) : h.testBit i=true → m.testBit i=true := by
    intro hi
    have hb : i∈h.bitIndices.toFinset := by simpa using Nat.mem_bitIndices.mpr hi
    have hm := sub hb
    simpa using hm
  have xor_union : q.bitIndices.toFinset ∪ h.bitIndices.toFinset=m.bitIndices.toFinset := by
    ext i
    simp only [Finset.mem_union,List.mem_toFinset,Nat.mem_bitIndices]
    dsimp [q]
    rw [Nat.testBit_xor]
    have hs := bit_sub i
    cases hm : m.testBit i <;> cases hh : h.testBit i <;> simp_all
  have xor_dis : Disjoint q.bitIndices.toFinset h.bitIndices.toFinset := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hqi : q.testBit i=true := by simpa using hi
    have hhi : h.testBit i=true := by simpa using hj
    have hmi := bit_sub i hhi
    simpa [q,Nat.testBit_xor,hmi,hhi] using hqi
  have qsum : q+h=m := by
    have hs := Finset.sum_union xor_dis (f:=fun i : ℕ => 2^i)
    rw [xor_union] at hs
    simp only [Finset.sum_toFinset_bitIndices_two_pow] at hs
    exact hs.symm
  have mlow : m+low=2^(c+s)-1 := by
    dsimp [m,low,lam]
    rw [pow_add,Nat.sub_mul,Nat.one_mul]
    have hmul : 2^s ≤ 2^c*2^s := by
      simpa using Nat.mul_le_mul_right (2^s) (show 1 ≤ 2^c by omega)
    omega
  have ml := mask_complement (c+s) m low mlow
  have fullpos : 0<2^(c+s) := Nat.two_pow_pos _
  have mcap : m<2^(c+s) := by omega
  have lowcap : low<2^(c+s) := by omega
  have hcap : h<2^(c+s) := by omega
  have qcap : q<2^(c+s) := by omega
  have qsub : q.bitIndices.toFinset⊆m.bitIndices.toFinset := by
    intro i hi
    rw [←xor_union]
    exact Finset.mem_union_left _ hi
  refine ⟨qsum,⟨hcap,qcap,lowcap,xor_dis.symm,?_,?_,?_⟩⟩
  · exact ml.1.mono_left sub
  · exact ml.1.mono_left qsub
  · rw [show h.bitIndices.toFinset ∪ q.bitIndices.toFinset=m.bitIndices.toFinset by
      simpa only [Finset.union_comm] using xor_union,ml.2]

/-- Native support disjointness is transported to distinct physical occurrences. -/
private theorem labels_disjoint (len off u v : ℕ)
    (hd : Disjoint u.bitIndices.toFinset v.bitIndices.toFinset) :
    List.Disjoint (chamberLabels len off u) (chamberLabels len off v) := by
  apply List.disjoint_left.mpr
  intro i hi hj
  obtain ⟨e,he,hbe,hei⟩ := (chamberLabels_mem _ _ _ _).mp hi
  obtain ⟨j,hj,hbj,hji⟩ := (chamberLabels_mem _ _ _ _).mp hj
  have ej : e=j := by omega
  subst j
  exact Finset.disjoint_left.mp hd
    (by simpa using Nat.mem_bitIndices.mpr hbe)
    (by simpa using Nat.mem_bitIndices.mpr hbj)

private theorem partition_labels (len off h q low : ℕ)
    (hp : MaskPartition len h q low) :
    ((chamberLabels len off h ++ chamberLabels len off q) ++
      chamberLabels len off low).Perm (List.range' off len) := by
  have hd := labels_disjoint len off h q hp.hq
  have hdl : List.Disjoint
      (chamberLabels len off h ++ chamberLabels len off q) (chamberLabels len off low) := by
    apply List.disjoint_left.mpr
    intro i hi hj
    rcases List.mem_append.mp hi with hi|hi
    · exact List.disjoint_left.mp (labels_disjoint len off h low hp.hl) hi hj
    · exact List.disjoint_left.mp (labels_disjoint len off q low hp.ql) hi hj
  have nd := ((chamberLabels_nodup len off h).append (chamberLabels_nodup len off q) hd).append
    (chamberLabels_nodup len off low) hdl
  apply (List.perm_ext_iff_of_nodup nd (List.nodup_range' (s:=off) (n:=len))).mpr
  intro i
  simp only [List.mem_append,chamberLabels_mem,List.mem_range']
  constructor
  · rintro ((⟨e,he,_,hei⟩|⟨e,he,_,hei⟩)|⟨e,he,_,hei⟩)
    all_goals exact ⟨e,he,by omega⟩
  · rintro ⟨e,he,hei⟩
    have hb : e∈(h.bitIndices.toFinset ∪ q.bitIndices.toFinset) ∪ low.bitIndices.toFinset := by
      rw [hp.full]
      exact Finset.mem_range.mpr he
    simp only [Finset.mem_union,List.mem_toFinset,Nat.mem_bitIndices] at hb
    rcases hb with (hb|hb)|hb
    · exact Or.inl (Or.inl ⟨e,he,hb,by omega⟩)
    · exact Or.inl (Or.inr ⟨e,he,hb,by omega⟩)
    · exact Or.inr ⟨e,he,hb,by omega⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
