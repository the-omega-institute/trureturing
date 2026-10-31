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
open private labels labels_mem labels_nodup from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Constructor
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

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
