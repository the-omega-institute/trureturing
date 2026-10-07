/- GID: D5/S3/Combinatorics/PrefixCovers/HeightNormalization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PrefixCovers/HeightNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: none
   digest: Finite labelled prefix covers admit a depth bound preserving their source. -/

import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators

namespace D5.S3.Combinatorics.PrefixCovers.HeightNormalization
variable {α ι κ W : Type*}

/-- Agreement on the first k symbols of two streams. -/
def Prefix (k : ℕ) (x w : ℕ → α) : Prop := ∀ t < k, x t = w t

def insertDigit (j : ℕ) (a : α) (x : ℕ → α) (t : ℕ) : α :=
  if t < j then x t else if t = j then a else x (t - 1)

def deleteDigit (j : ℕ) (w : ℕ → α) (t : ℕ) : α :=
  if t < j then w t else w (t + 1)

lemma prefix_insert_shallow (j k : ℕ) (a : α) (x w : ℕ → α) (h : k ≤ j) :
    Prefix k (insertDigit j a x) w ↔ Prefix k x w := by
  unfold Prefix
  constructor <;> intro hp t ht
  · simpa [insertDigit, show t < j by omega] using hp t ht
  · simpa [insertDigit, show t < j by omega] using hp t ht

lemma prefix_insert_deep (j k : ℕ) (a : α) (x w : ℕ → α) (h : j < k) :
    Prefix k (insertDigit j a x) w ↔
      w j = a ∧ Prefix (k - 1) x (deleteDigit j w) := by
  constructor
  · intro hp
    refine ⟨?_, ?_⟩
    · simpa [insertDigit] using (hp j h).symm
    · intro t ht
      by_cases hj : t < j
      · simpa [deleteDigit, insertDigit, hj] using hp t (by omega)
      · have hlt : ¬ t + 1 < j := by omega
        have hne : t + 1 ≠ j := by omega
        simpa [deleteDigit, insertDigit, hj, hlt, hne] using hp (t + 1) (by omega)
  · rintro ⟨ha,hp⟩ t ht
    by_cases hj : t < j
    · simpa [insertDigit, deleteDigit, hj] using hp t (by omega)
    · by_cases he : t = j
      · subst t; simp [insertDigit, ha]
      · have hpred : ¬t - 1 < j := by omega
        have htpos : 0 < t := by omega
        simpa [insertDigit, deleteDigit, hj, he, hpred,
          Nat.sub_add_cancel htpos] using hp (t - 1) (by omega)

def compressedHeight (j k : ℕ) : ℕ := if k ≤ j then k else k - 1

def compressedWord (j k : ℕ) (w : ℕ → α) : ℕ → α :=
  if k ≤ j then w else deleteDigit j w

def keep (j k : ℕ) (a : α) (w : ℕ → α) : Prop := k ≤ j ∨ w j = a

lemma compressedHeight_injective_on_gap (j k l : ℕ)
    (hk : k ≠ j + 1) (hl : l ≠ j + 1)
    (he : compressedHeight j k = compressedHeight j l) : k = l := by
  unfold compressedHeight at he
  split_ifs at he <;> omega

lemma compressedHeight_bounds (r j k : ℕ) (hr : r ≤ j) (hk : r < k)
    (hgap : k ≠ j + 1) :
    r < compressedHeight j k ∧ compressedHeight j k ≤ k := by
  unfold compressedHeight
  split_ifs <;> omega

lemma compressedWord_preserves (r j k : ℕ) (w : ℕ → α) (hr : r ≤ j) :
    Prefix r (compressedWord j k w) w := by
  intro t ht
  unfold compressedWord
  split_ifs
  · rfl
  · simp [deleteDigit, show t < j by omega]

lemma prefix_compressed (j k : ℕ) (a : α) (x w : ℕ → α) :
    Prefix k (insertDigit j a x) w ↔
      keep j k a w ∧ Prefix (compressedHeight j k) x (compressedWord j k w) := by
  by_cases h : k ≤ j
  · simpa [keep, compressedHeight, compressedWord, h] using
      prefix_insert_shallow j k a x w h
  · simpa [keep, compressedHeight, compressedWord, h] using
      prefix_insert_deep j k a x w (by omega)

/-- Every target point lies in an indexed prefix cylinder with its side condition. -/
def Covers (I : Finset ι) (height : ι → ℕ) (word : ι → ℕ → α)
    (side : ι → W → Prop) (E : (ℕ → α) → W → Prop) : Prop :=
  ∀ x z, E x z → ∃ i ∈ I, Prefix (height i) x (word i) ∧ side i z

noncomputable def kept (I : Finset ι) (height : ι → ℕ) (word : ι → ℕ → α)
    (j : ℕ) (a : α) : Finset ι := by
  classical
  exact I.filter fun i => keep j (height i) a (word i)

lemma contract_cover (I : Finset ι) (height : ι → ℕ) (word : ι → ℕ → α)
    (side : ι → W → Prop) (E : (ℕ → α) → W → Prop) (r j : ℕ) (a : α)
    (hr : r ≤ j)
    (hE : ∀ x y z, Prefix r x y → E x z → E y z)
    (hc : Covers I height word side E) :
    let J := kept I height word j a
    Covers J (fun i => compressedHeight j (height i))
      (fun i => compressedWord j (height i) (word i)) side E := by
  classical
  intro J x z hx
  have hp : Prefix r x (insertDigit j a x) := by
    intro t ht
    simp [insertDigit, show t < j by omega]
  obtain ⟨i,hi,hpi,hsi⟩ := hc (insertDigit j a x) z (hE x _ z hp hx)
  have hnew := (prefix_compressed j (height i) a x (word i)).mp hpi
  exact ⟨i, mem_filter.mpr ⟨hi,hnew.1⟩, hnew.2, hsi⟩

lemma exists_unused_height (I : Finset ι) (height : ι → ℕ) (r K : ℕ)
    (hK : r + I.card < K) :
    ∃ g ∈ Icc (r + 1) K, ∀ i ∈ I, height i ≠ g := by
  classical
  have hcard : (I.image height).card < (Icc (r + 1) K).card := by
    have h := card_image_le (s := I) (f := height)
    rw [Nat.card_Icc]
    omega
  obtain ⟨g,hg,hnot⟩ := exists_mem_notMem_of_card_lt_card hcard
  exact ⟨g,hg, fun i hi he => hnot (mem_image.mpr ⟨i,hi,he⟩)⟩

lemma contract_sum_lt (I : Finset ι) (height : ι → ℕ) (word : ι → ℕ → α)
    (j : ℕ) (a : α) (hdeep : ∃ i ∈ I, j < height i) :
    (∑ i ∈ kept I height word j a, compressedHeight j (height i)) < ∑ i ∈ I, height i := by
  classical
  unfold kept
  apply lt_of_le_of_lt (sum_le_sum_of_subset (filter_subset _ I))
  apply sum_lt_sum
  · intro i _; simp only [compressedHeight]; split_ifs <;> omega
  · obtain ⟨i,hi,h⟩ := hdeep
    refine ⟨i,hi,?_⟩
    simp only [compressedHeight, show ¬ height i ≤ j by omega, if_false]
    omega

lemma contract_labels (I : Finset ι) (height : ι → ℕ) (label : ι → κ)
    (j : ℕ) (hgap : ∀ i ∈ I, height i ≠ j + 1)
    (hinj : Set.InjOn (fun i => (height i, label i)) I) :
    Set.InjOn (fun i => (compressedHeight j (height i), label i)) I := by
  intro i hi l hl he
  have hheight := compressedHeight_injective_on_gap j (height i) (height l)
    (hgap i hi) (hgap l hl) (congrArg Prod.fst he)
  have hlabel : label i = label l := congrArg (fun v : ℕ × κ => v.2) he
  apply hinj hi hl
  exact Prod.ext hheight hlabel

/-- Remove unused prefix depths while preserving the target, side conditions,
old prefix symbols and distinct height-label pairs. -/
theorem normalize_cover (I : Finset ι) (height : ι → ℕ) (word : ι → ℕ → α)
    (label : ι → κ) (side : ι → W → Prop) (E : (ℕ → α) → W → Prop)
    (r : ℕ) (a : α)
    (hE : ∀ x y z, Prefix r x y → E x z → E y z)
    (hlow : ∀ i ∈ I, r < height i)
    (hinj : Set.InjOn (fun i => (height i, label i)) I)
    (hc : Covers I height word side E) :
    ∃ J ⊆ I, ∃ height' word',
      (∀ i ∈ J, r < height' i ∧ height' i ≤ r + J.card ∧ height' i ≤ height i ∧
        Prefix r (word' i) (word i)) ∧
      Set.InjOn (fun i => (height' i, label i)) J ∧ Covers J height' word' side E := by
  classical
  by_cases hdone : ∀ i ∈ I, height i ≤ r + I.card
  · exact ⟨I, Subset.refl _, height, word,
      fun i hi => ⟨hlow i hi, hdone i hi, le_refl _, fun _ _ => rfl⟩, hinj, hc⟩
  · push Not at hdone
    obtain ⟨imax, himax, hmax⟩ := hdone
    obtain ⟨g,hg,hgap⟩ := exists_unused_height I height r (height imax) hmax
    have hrg : r < g := (mem_Icc.mp hg).1
    have hgm : g < height imax := lt_of_le_of_ne (mem_Icc.mp hg).2 (hgap imax himax).symm
    let j := g - 1
    have hj : r ≤ j := by omega
    have hgap' : ∀ i ∈ I, height i ≠ j + 1 := by
      intro i hi
      simpa [j, Nat.sub_add_cancel (show 1 ≤ g by omega)] using hgap i hi
    let J := kept I height word j a
    let height' := fun i => compressedHeight j (height i)
    let word' := fun i => compressedWord j (height i) (word i)
    have hJI : J ⊆ I := filter_subset _ _
    have hlow' : ∀ i ∈ J, r < height' i := by
      intro i hi
      exact (compressedHeight_bounds r j (height i) hj (hlow i (hJI hi))
        (hgap' i (hJI hi))).1
    have hinj' : Set.InjOn (fun i => (height' i, label i)) J :=
      (contract_labels I height label j hgap' hinj).mono hJI
    have hc' : Covers J height' word' side E := contract_cover I height word side E r j a hj hE hc
    obtain ⟨K,hKJ,height'',word'',hb,hic,hcc⟩ :=
      normalize_cover J height' word' label side E r a hE hlow' hinj' hc'
    refine ⟨K,hKJ.trans hJI,height'',word'',?_,hic,hcc⟩
    intro i hi
    refine ⟨(hb i hi).1,(hb i hi).2.1,?_,?_⟩
    · exact (hb i hi).2.2.1.trans
        (compressedHeight_bounds r j (height i) hj (hlow i (hJI (hKJ hi)))
          (hgap' i (hJI (hKJ hi)))).2
    · intro t ht
      exact ((hb i hi).2.2.2 t ht).trans (compressedWord_preserves r j (height i) (word i) hj t ht)
termination_by ∑ i ∈ I, height i
decreasing_by
  exact contract_sum_lt I height word j a ⟨imax,himax,by omega⟩

end D5.S3.Combinatorics.PrefixCovers.HeightNormalization
