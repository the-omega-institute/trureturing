/- GID: D5/S3/Combinatorics/SubsetSpectrum/NonnegativeRecovery
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubsetSpectrum/NonnegativeRecovery
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors]
   utility: none
   digest: Nonnegative real coefficient recovery from the full occurrence spectrum. -/

import D5.S3.Combinatorics.SubsetSpectrum.TengokuSubsetSums
import D5.S3.Combinatorics.SubsetSpectrum.SignAction
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SubsetSpectrum

variable {α : Type*}

private lemma subset_sums_cons (a : ℝ) (s : Multiset ℝ) :
    subsetSums (a ::ₘ s) = subsetSums s + (subsetSums s).map (a + ·) := by
  simp [subsetSums, Multiset.powerset_cons, Multiset.map_add, Multiset.map_map,
    Function.comp_def]

private noncomputable def spectrumAlgebra (s : Multiset ℝ) : AddMonoidAlgebra ℕ ℝ :=
  AddMonoidAlgebra.ofCoeff s.toFinsupp

private lemma spectrum_algebra_injective : Function.Injective spectrumAlgebra := by
  intro s t h
  exact Multiset.toFinsupp.injective (AddMonoidAlgebra.ofCoeff_injective h)

private lemma spectrum_algebra_translate (a : ℝ) (s : Multiset ℝ) :
    spectrumAlgebra (s.map (a + ·)) = AddMonoidAlgebra.single a 1 * spectrumAlgebra s := by
  induction s using Multiset.induction_on with
  | empty => simp [spectrumAlgebra, Multiset.toFinsupp_zero]
  | cons x s ih =>
    have hadd (u v : Multiset ℝ) : spectrumAlgebra (u + v) = spectrumAlgebra u + spectrumAlgebra v := by
      simp [spectrumAlgebra, Multiset.toFinsupp_add, AddMonoidAlgebra.ofCoeff_add]
    have hcons (x : ℝ) (s : Multiset ℝ) :
        spectrumAlgebra (x ::ₘ s) = AddMonoidAlgebra.single x 1 + spectrumAlgebra s := by
      rw [← Multiset.singleton_add, hadd]
      simp [spectrumAlgebra]
    rw [Multiset.map_cons, hcons, hcons, mul_add, ← ih]
    simp

private lemma cancel_subset_sum_factor (a : ℝ) (s t : Multiset ℝ)
    (h : s + s.map (a + ·) = t + t.map (a + ·)) : s = t := by
  have hadd (u v : Multiset ℝ) : spectrumAlgebra (u + v) = spectrumAlgebra u + spectrumAlgebra v := by
    simp [spectrumAlgebra, Multiset.toFinsupp_add, AddMonoidAlgebra.ofCoeff_add]
  have hh := congrArg spectrumAlgebra h
  rw [hadd, hadd, spectrum_algebra_translate, spectrum_algebra_translate] at hh
  have hf : (1 + AddMonoidAlgebra.single a 1 : AddMonoidAlgebra ℕ ℝ) ≠ 0 := by
    intro hz
    have hc := congrArg (fun f : AddMonoidAlgebra ℕ ℝ => f.coeff 0) hz
    simp [AddMonoidAlgebra.one_def] at hc
  apply spectrum_algebra_injective
  apply mul_left_cancel₀ hf
  simpa only [add_mul, one_mul] using hh

private lemma one_empty_occurrence (s : Multiset ℝ) : s.powerset.count 0 = 1 := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.powerset_cons, Multiset.count_add, ih]
    have hz : (s.powerset.map (Multiset.cons a)).count 0 = 0 := by simp
    rw [hz, add_zero]

private lemma minimum_coefficient_occurrence (s : Multiset ℝ)
    (hs : ∀ x ∈ s, 0 ≤ x) (a : ℝ) (ha : a ∈ s) (hmin : ∀ x ∈ s, a ≤ x) :
    IsLeast {x : ℝ | x ∈ (subsetSums s).erase 0} a := by
  classical
  have hmap : (s.powerset.erase 0).map Multiset.sum = (subsetSums s).erase 0 := by
    simpa [subsetSums] using
      Multiset.map_erase_of_mem Multiset.sum s.powerset (Multiset.zero_mem_powerset s)
  have hnot : (0 : Multiset ℝ) ∉ s.powerset.erase 0 := by
    rw [← Multiset.count_eq_zero, Multiset.count_erase_self, one_empty_occurrence]
  rw [← hmap]
  constructor
  · refine Multiset.mem_map.mpr ⟨{a}, ?_, by simp⟩
    apply (Multiset.mem_erase_of_ne (by simp : ({a} : Multiset ℝ) ≠ 0)).mpr
    exact Multiset.mem_powerset.mpr (by simpa using ha)
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hx
    have hune : u ≠ 0 := fun h => hnot (h ▸ hu)
    have hus : u ≤ s := Multiset.mem_powerset.mp (Multiset.mem_of_mem_erase hu)
    obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hune
    exact (hmin y (Multiset.mem_of_le hus hy)).trans
      (Multiset.single_le_sum (fun z hz => hs z (Multiset.mem_of_le hus hz)) y hy)

/-- Nonnegative real coefficients, including zeros and repetitions, are
recovered from their full subset-sum multiset. -/
theorem nonnegative_subset_sum_recovery (s t : Multiset ℝ)
    (hs : ∀ x ∈ s, 0 ≤ x) (ht : ∀ x ∈ t, 0 ≤ x)
    (h : subsetSums s = subsetSums t) : s = t := by
  classical
  have go : ∀ n, ∀ s t : Multiset ℝ, s.card = n →
      (∀ x ∈ s, 0 ≤ x) → (∀ x ∈ t, 0 ≤ x) → subsetSums s = subsetSums t → s = t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s t hsc hs ht h
      have hc : s.card = t.card := Nat.pow_right_injective (by decide : 2 ≤ 2)
        (by simpa [subsetSums] using congrArg Multiset.card h)
      by_cases hs0 : s = 0
      · have ht0 : t = 0 := Multiset.card_eq_zero.mp (by simpa [hs0] using hc.symm)
        simp [hs0, ht0]
      · have ht0 : t ≠ 0 := by
          intro h0
          exact hs0 (Multiset.card_eq_zero.mp (by simpa [h0] using hc))
        obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hs0
        obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero ht0
        have hsn : s.toFinset.Nonempty := ⟨x, by simpa using hx⟩
        have htn : t.toFinset.Nonempty := ⟨y, by simpa using hy⟩
        let a := s.toFinset.min' hsn
        let d := t.toFinset.min' htn
        have ha : a ∈ s := by simpa [a] using Finset.min'_mem s.toFinset hsn
        have hd : d ∈ t := by simpa [d] using Finset.min'_mem t.toFinset htn
        have ham : ∀ x ∈ s, a ≤ x := fun x hx =>
          Finset.min'_le s.toFinset x (by simpa using hx)
        have hdm : ∀ x ∈ t, d ≤ x := fun x hx =>
          Finset.min'_le t.toFinset x (by simpa using hx)
        have hma := minimum_coefficient_occurrence s hs a ha ham
        have hmd := minimum_coefficient_occurrence t ht d hd hdm
        have had : a = d := le_antisymm
          (hma.2 (by rw [h]; exact hmd.1)) (hmd.2 (by rw [← h]; exact hma.1))
        have hat : a ∈ t := had.symm ▸ hd
        have hse := Multiset.cons_erase ha
        have hte := Multiset.cons_erase hat
        rw [← hse, ← hte, subset_sums_cons, subset_sums_cons] at h
        have hrem := cancel_subset_sum_factor a (subsetSums (s.erase a)) (subsetSums (t.erase a)) h
        have hlt : (s.erase a).card < n := by
          exact (Multiset.card_erase_lt_of_mem ha).trans_eq hsc
        have hrec := ih (s.erase a).card hlt (s.erase a) (t.erase a) rfl
          (fun x hx => hs x (Multiset.mem_of_mem_erase hx))
          (fun x hx => ht x (Multiset.mem_of_mem_erase hx)) hrem
        exact hse.symm.trans ((congrArg (Multiset.cons a) hrec).trans hte)
  exact go s.card s t rfl hs ht h

/-- Indexed subset sums agree with the attributed multiset construction. -/
theorem indexed_full_spectrum [Fintype α] (b : α → ℝ) :
    fullSubsetSums Finset.univ b = subsetSums (Finset.univ.val.map b) := by
  have hval : ((Finset.univ : Finset α).powerset.val.map Finset.val) =
      (Finset.univ : Finset α).val.powerset := by
    simp [Finset.powerset, Multiset.map_pmap, Multiset.pmap_eq_map]
  unfold fullSubsetSums subsetSums
  rw [← powerset_map_eq, Multiset.map_map, ← hval, Multiset.map_map]
  rfl

end D5.S3.Combinatorics.SubsetSpectrum
