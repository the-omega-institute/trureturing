/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Masks
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Masks
   mirror-E: none(waiver:internal-mask-bridge)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Increasing physical bit decoder and exact weighted mask masses. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Constructor

/-! Physical occurrence identities are retained by the increasing decoder. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private chainMask chainMask_sum from D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventual
open private mask_labels mask_labels_mem from D5.S3.Combinatorics.Circle.ThreeBitSource

private theorem labels_perm_chainMask (len off mask : ℕ) (hm : mask<2^len) :
    (labels len off mask).Perm (chainMask len off mask) := by
  classical
  apply (List.perm_ext_iff_of_nodup (labels_nodup len off mask) ?_).mpr
  · intro i
    simp only [labels_mem, chainMask, dif_pos hm, Finset.mem_toList, mask_labels_mem]
  · simp only [chainMask, dif_pos hm]
    exact Finset.nodup_toList _

private theorem labels_sum (len off mask : ℕ) (hm : mask<2^len)
    (f : ℕ→ℤ) (A : ℤ) (hf : ∀ e<len, f (off+e)=2^e*A) :
    ((labels len off mask).map f).sum=(mask:ℤ)*A := by
  rw [((labels_perm_chainMask len off mask hm).map f).sum_eq]
  exact chainMask_sum len off mask hm f A hf

private theorem labels_positive (len off mask : ℕ) (f : ℕ→ℤ) (A : ℤ)
    (hA : 0≤A) (hf : ∀ e<len, f (off+e)=2^e*A) :
    ∀ i∈labels len off mask, 0≤f i := by
  intro i hi
  obtain ⟨e,he,_,rfl⟩ := (labels_mem len off mask i).mp hi
  rw [hf e he]
  positivity

/-- Nested bits split into physical subsets with no duplicate occurrence. -/
private theorem labels_split (len off outer inner : ℕ)
    (hsub : ∀ e<len, inner.testBit e=true → outer.testBit e=true) :
    (labels len off (outer ^^^ inner) ++ labels len off inner).Perm (labels len off outer) := by
  apply (List.perm_ext_iff_of_nodup ?_ (labels_nodup len off outer)).mpr
  · intro i
    simp only [List.mem_append,labels_mem]
    constructor
    · rintro (⟨e,he,hb,hi⟩|⟨e,he,hb,hi⟩)
      · refine ⟨e,he,?_,hi⟩
        have h:=hsub e he
        rw [Nat.testBit_xor] at hb
        cases ho : outer.testBit e <;> cases hn : inner.testBit e <;> simp_all
      · exact ⟨e,he,hsub e he hb,hi⟩
    · rintro ⟨e,he,hb,hi⟩
      cases hn : inner.testBit e
      · left
        exact ⟨e,he,by simp [Nat.testBit_xor,hb,hn],hi⟩
      · right
        exact ⟨e,he,hn,hi⟩
  · apply List.nodup_append.mpr
    refine ⟨labels_nodup _ _ _,labels_nodup _ _ _,?_⟩
    intro i hi j hj hij
    obtain ⟨e,he,hb,hi'⟩ := (labels_mem _ _ _ _).mp hi
    obtain ⟨e',he',hb',hj'⟩ := (labels_mem _ _ _ _).mp hj
    have heq : e=e' := by omega
    subst e'
    have hout:=hsub e he hb'
    simpa [Nat.testBit_xor,hout,hb'] using hb

private theorem labels_full (len off : ℕ) :
    labels len off (2^len-1)=List.range' off len := by
  have hf : (List.range len).filter (fun i => (2^len-1).testBit i)=List.range len := by
    apply List.filter_eq_self.mpr
    intro i hi
    simp [Nat.testBit_two_pow_sub_one,List.mem_range.mp hi]
  rw [labels,hf,List.range_eq_range']
  simpa only [Nat.add_zero] using (List.map_add_range' (a := off) 0 len 1)

private theorem labels_nested_four (len off u1 u2 u3 : ℕ)
    (h12 : ∀ e<len, u2.testBit e=true → u1.testBit e=true)
    (h23 : ∀ e<len, u3.testBit e=true → u2.testBit e=true) :
    (labels len off ((2^len-1) ^^^ u1) ++ labels len off (u1 ^^^ u2) ++
      labels len off (u2 ^^^ u3) ++ labels len off u3).Perm (List.range' off len) := by
  have h1 := labels_split len off (2^len-1) u1
    (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he])
  have h2 := labels_split len off u1 u2 h12
  have h3 := labels_split len off u2 u3 h23
  have hp := (h3.append_left (labels len off (u1 ^^^ u2))).trans h2
  have hp' := (hp.append_left (labels len off ((2^len-1) ^^^ u1))).trans h1
  simpa only [List.append_assoc,labels_full] using hp'

theorem chamberLabels_sum (len off mask : ℕ) (hm : mask<2^len)
    (f : ℕ→ℤ) (A : ℤ) (hf : ∀ e<len, f (off+e)=2^e*A) :
    ((chamberLabels len off mask).map f).sum=(mask:ℤ)*A := by
  exact labels_sum len off mask hm f A hf

theorem chamberLabels_positive (len off mask : ℕ) (f : ℕ→ℤ) (A : ℤ)
    (hA : 0≤A) (hf : ∀ e<len, f (off+e)=2^e*A) :
    ∀ i∈chamberLabels len off mask, 0≤f i := by
  exact labels_positive len off mask f A hA hf

theorem chamberLabels_nested_four (len off u1 u2 u3 : ℕ)
    (h12 : ∀ e<len, u2.testBit e=true → u1.testBit e=true)
    (h23 : ∀ e<len, u3.testBit e=true → u2.testBit e=true) :
    (chamberLabels len off ((2^len-1) ^^^ u1) ++
      chamberLabels len off (u1 ^^^ u2) ++ chamberLabels len off (u2 ^^^ u3) ++
      chamberLabels len off u3).Perm (List.range' off len) := by
  exact labels_nested_four len off u1 u2 u3 h12 h23

theorem chamberLabels_full (len off : ℕ) :
    chamberLabels len off (2^len-1)=List.range' off len := by
  exact labels_full len off

theorem chamberLabels_split (len off outer inner : ℕ)
    (hsub : ∀ e<len, inner.testBit e=true → outer.testBit e=true) :
    (chamberLabels len off (outer ^^^ inner) ++
      chamberLabels len off inner).Perm (chamberLabels len off outer) := by
  exact labels_split len off outer inner hsub

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
