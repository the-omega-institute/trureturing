/- GID: D5/S3/Combinatorics/SubsetSpectrum/SignAction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubsetSpectrum/SignAction
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Finset.SymmDiff]
   utility: none
   digest: Even zero-sum flips and coordinate permutations preserve even spectra. -/

import D5.S3.Combinatorics.SubsetSpectrum.EvenBridge
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SubsetSpectrum

open scoped BigOperators symmDiff

variable {α : Type*} [DecidableEq α]

/-- Change the signs on exactly the indicated index set. -/
def flipCoefficients (I : Finset α) (b : α → ℝ) (i : α) : ℝ :=
  if i ∈ I then -b i else b i

private lemma flip_subset_sum (I S : Finset α) (b : α → ℝ) :
    (∑ i ∈ S, flipCoefficients I b i) = (∑ i ∈ I ∆ S, b i) - ∑ i ∈ I, b i := by
  have hsplit : (∑ i ∈ S, flipCoefficients I b i) =
      -(∑ i ∈ S ∩ I, b i) + ∑ i ∈ S \ I, b i := by
    simp only [flipCoefficients, Finset.sum_ite, Finset.sum_neg_distrib,
      Finset.filter_mem_eq_inter, ← Finset.sdiff_eq_filter]
  have hdis : Disjoint (I \ S) (S \ I) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  rw [hsplit, Finset.symmDiff_def, Finset.sum_union hdis]
  have hI := Finset.sum_inter_add_sum_sdiff I S b
  rw [Finset.inter_comm I S] at hI
  rw [← hI]
  ring

private lemma symmDiff_parity (I S : Finset α) :
    Even (I ∆ S).card ↔ (Even I.card ↔ Even S.card) := by
  have hdis : Disjoint (I \ S) (S \ I) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hcard : (I ∆ S).card + 2 * (I ∩ S).card = I.card + S.card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdis]
    have hi := Finset.card_sdiff_add_card_inter I S
    have hs := Finset.card_sdiff_add_card_inter S I
    rw [Finset.inter_comm S I] at hs
    omega
  simp only [Nat.even_iff]
  omega

private lemma symmDiff_even_iff (I S : Finset α) (hI : Even I.card) :
    Even (I ∆ S).card ↔ Even S.card := by
  simpa [hI] using symmDiff_parity I S

/-- An even-cardinality zero-sum sign change preserves the even spectrum. -/
theorem even_zero_flip_preserves_spectrum [Fintype α] (I : Finset α) (b : α → ℝ)
    (heven : Even I.card) (hzero : (∑ i ∈ I, b i) = 0) :
    evenSubsetSums Finset.univ (flipCoefficients I b) = evenSubsetSums Finset.univ b := by
  classical
  let e : Finset α ↪ Finset α := ⟨fun S => I ∆ S, symmDiff_right_injective I⟩
  have hmap : (evenSubsets (Finset.univ : Finset α)).map e = evenSubsets Finset.univ := by
    ext S
    simp only [Finset.mem_map, evenSubsets, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and]
    constructor
    · rintro ⟨T, hT, rfl⟩
      exact (symmDiff_even_iff I T heven).mpr hT
    · intro hS
      refine ⟨I ∆ S, (symmDiff_even_iff I S heven).mpr hS, ?_⟩
      simp [e]
  unfold evenSubsetSums
  conv_rhs => rw [← hmap]
  rw [Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro S _
  dsimp [e]
  rw [flip_subset_sum, hzero, sub_zero]

omit [DecidableEq α] in
/-- Reindexing by a permutation preserves every occurrence of the even spectrum. -/
theorem even_spectrum_permutation [Fintype α] (σ : Equiv.Perm α) (b : α → ℝ) :
    evenSubsetSums Finset.univ (fun i => b (σ i)) = evenSubsetSums Finset.univ b := by
  classical
  let e : Finset α ↪ Finset α := ⟨fun S => S.map σ.toEmbedding,
    Finset.map_injective σ.toEmbedding⟩
  have hmap : (evenSubsets (Finset.univ : Finset α)).map e = evenSubsets Finset.univ := by
    ext S
    simp only [Finset.mem_map, evenSubsets, Finset.mem_filter, Finset.mem_powerset,
      Finset.subset_univ, true_and]
    constructor
    · rintro ⟨T, hT, rfl⟩
      simpa [e] using hT
    · intro hS
      refine ⟨S.map σ.symm.toEmbedding, by simpa using hS, ?_⟩
      simp [e, Finset.map_map]
  unfold evenSubsetSums
  conv_rhs => rw [← hmap]
  rw [Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro S _
  dsimp [e]
  exact (Finset.sum_map S σ.toEmbedding b).symm

/-- The sign-permutation condition implies even-spectrum equality in every
finite dimension, without restrictions on zeros or repeated coefficients. -/
theorem even_spectrum_of_sign_permutation {m : ℕ} (b c : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) (I : Finset (Fin m)) (heven : Even I.card)
    (hzero : (∑ i ∈ I, b i) = 0)
    (hc : ∀ i, c (σ i) = if i ∈ I then -b i else b i) :
    evenSubsetSums Finset.univ b = evenSubsetSums Finset.univ c := by
  have hfun : (fun i => c (σ i)) = flipCoefficients I b := funext hc
  rw [← even_spectrum_permutation σ c, hfun, even_zero_flip_preserves_spectrum I b heven hzero]

/-- An odd-cardinality zero-sum sign change carries the even spectrum to the odd one. -/
theorem odd_zero_flip_interchanges_spectra [Fintype α] (I : Finset α) (b : α → ℝ)
    (hodd : Odd I.card) (hzero : (∑ i ∈ I, b i) = 0) :
    evenSubsetSums Finset.univ (flipCoefficients I b) = oddSubsetSums Finset.univ b := by
  classical
  have hnot : ¬ Even I.card := Nat.not_even_iff_odd.mpr hodd
  have hpar (S : Finset α) : Even S.card ↔ Odd (I ∆ S).card := by
    simpa [hnot] using symmDiff_parity I (I ∆ S)
  let e : Finset α ↪ Finset α := ⟨fun S => I ∆ S, symmDiff_right_injective I⟩
  have hmap : (evenSubsets (Finset.univ : Finset α)).map e = oddSubsets Finset.univ := by
    ext S
    simp only [Finset.mem_map, evenSubsets, oddSubsets, Finset.mem_filter,
      Finset.mem_powerset, Finset.subset_univ, true_and]
    constructor
    · rintro ⟨T, hT, rfl⟩
      exact (hpar T).mp hT
    · intro hS
      refine ⟨I ∆ S, (hpar (I ∆ S)).mpr (by simpa using hS), ?_⟩
      simp [e]
  unfold evenSubsetSums oddSubsetSums
  conv_rhs => rw [← hmap]
  rw [Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro S _
  dsimp [e]
  rw [flip_subset_sum, hzero, sub_zero]

private lemma minimum_subset_unique [Fintype α] (b : α → ℝ) (hb : ∀ i, b i ≠ 0)
    (S : Finset α)
    (h : (∑ i ∈ S, b i) = ∑ i ∈ Finset.univ.filter (fun i => b i < 0), b i) :
    S = Finset.univ.filter (fun i => b i < 0) := by
  classical
  let N := Finset.univ.filter (fun i => b i < 0)
  let f : α → ℝ := fun i => if i ∈ N then b i else 0
  let g : α → ℝ := fun i => if i ∈ S then b i else 0
  have hle (i : α) (_hi : i ∈ (Finset.univ : Finset α)) : f i ≤ g i := by
    dsimp [f, g, N]
    by_cases hn : b i < 0 <;> by_cases hs : i ∈ S <;> simp [hn, hs]
    · exact le_of_lt hn
    · exact le_of_not_gt hn
  have hsum : (∑ i, f i) = ∑ i, g i := by
    simpa [f, g, N, ← Finset.sum_filter] using h.symm
  have hpoint := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
  ext i
  have hi := hpoint i (Finset.mem_univ i)
  change (i ∈ S ↔ i ∈ N)
  dsimp [f, g] at hi
  by_cases hn : i ∈ N
  · by_cases hs : i ∈ S
    · simp [hn, hs]
    · exact (hb i (by simpa [hn, hs] using hi)).elim
  · by_cases hs : i ∈ S
    · exact (hb i (by simpa [hn, hs] using hi.symm)).elim
    · simp [hn, hs]

omit [DecidableEq α] in
/-- With no zero coefficient, the even and odd spectra are different: the full
minimum has a unique index subset and therefore a unique parity. -/
theorem even_ne_odd_of_nonzero [Fintype α] (b : α → ℝ) (hb : ∀ i, b i ≠ 0) :
    evenSubsetSums Finset.univ b ≠ oddSubsetSums Finset.univ b := by
  classical
  intro h
  let N := Finset.univ.filter (fun i => b i < 0)
  have unique (S : Finset α) (hs : (∑ i ∈ S, b i) = ∑ i ∈ N, b i) : S = N :=
    minimum_subset_unique b hb S hs
  by_cases he : Even N.card
  · have hm : (∑ i ∈ N, b i) ∈ evenSubsetSums Finset.univ b :=
      Multiset.mem_map.mpr ⟨N, by simp [evenSubsets, he], rfl⟩
    rw [h] at hm
    obtain ⟨S, hS, hsum⟩ := Multiset.mem_map.mp hm
    have hsodd : Odd S.card := (Finset.mem_filter.mp hS).2
    have hSN := unique S hsum
    exact (Nat.not_even_iff_odd.mpr hsodd) (hSN.symm ▸ he)
  · have ho : Odd N.card := Nat.not_even_iff_odd.mp he
    have hm : (∑ i ∈ N, b i) ∈ oddSubsetSums Finset.univ b :=
      Multiset.mem_map.mpr ⟨N, by simp [oddSubsets, ho], rfl⟩
    rw [← h] at hm
    obtain ⟨S, hS, hsum⟩ := Multiset.mem_map.mp hm
    have hseven : Even S.card := (Finset.mem_filter.mp hS).2
    exact he ((unique S hsum) ▸ hseven)

/-- Any zero-sum flip which preserves the even spectrum either has even
cardinality or the coefficient family contains a zero. -/
theorem sign_set_even_or_zero [Fintype α] (I : Finset α) (b : α → ℝ)
    (hzero : (∑ i ∈ I, b i) = 0)
    (h : evenSubsetSums Finset.univ (flipCoefficients I b) = evenSubsetSums Finset.univ b) :
    Even I.card ∨ ∃ i, b i = 0 := by
  classical
  by_cases he : Even I.card
  · exact Or.inl he
  · right
    by_contra hn
    have hnonzero : ∀ i, b i ≠ 0 := fun i hi => hn ⟨i, hi⟩
    have hEO : evenSubsetSums Finset.univ b = oddSubsetSums Finset.univ b := by
      rw [← h, odd_zero_flip_interchanges_spectra I b (Nat.not_even_iff_odd.mp he) hzero]
    exact even_ne_odd_of_nonzero b hnonzero hEO

/-- A zero coordinate can repair the parity of any zero-sum flip preserving
the even spectrum, without changing the resulting coefficient family. -/
theorem repair_flip_parity [Fintype α] (I : Finset α) (b : α → ℝ)
    (hzero : (∑ i ∈ I, b i) = 0)
    (h : evenSubsetSums Finset.univ (flipCoefficients I b) = evenSubsetSums Finset.univ b) :
    ∃ J : Finset α, Even J.card ∧ (∑ i ∈ J, b i) = 0 ∧
      flipCoefficients J b = flipCoefficients I b := by
  classical
  by_cases he : Even I.card
  · exact ⟨I, he, hzero, rfl⟩
  · obtain ⟨z, hz⟩ := (sign_set_even_or_zero I b hzero h).resolve_left he
    by_cases hzi : z ∈ I
    · refine ⟨I.erase z, ?_, ?_, ?_⟩
      · have hc := Finset.card_erase_add_one hzi
        simp only [Nat.even_iff] at he ⊢
        omega
      · have hs := Finset.sum_erase_add I b hzi
        simpa [hz, hzero] using hs
      · funext i
        by_cases hi : i = z
        · subst i
          simp [flipCoefficients, hz]
        · simp [flipCoefficients, hi]
    · refine ⟨insert z I, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hzi]
        simpa only [Nat.even_add_one, Nat.not_even_iff_odd] using he
      · rw [Finset.sum_insert hzi, hz, hzero, add_zero]
      · funext i
        by_cases hi : i = z
        · subst i
          simp [flipCoefficients, hz]
        · simp [flipCoefficients, hi]

/-- The indices of strictly negative coefficients. -/
noncomputable def negativeIndices [Fintype α] (b : α → ℝ) : Finset α :=
  Finset.univ.filter (fun i => b i < 0)

/-- The minimum possible subset sum. -/
noncomputable def negativeMass [Fintype α] (b : α → ℝ) : ℝ := ∑ i ∈ negativeIndices b, b i

/-- The full signed spectrum is the nonnegative absolute-value spectrum
translated by the sum of the negative coefficients. -/
theorem full_spectrum_signed_normalization [Fintype α] (b : α → ℝ) :
    fullSubsetSums Finset.univ b =
      (fullSubsetSums Finset.univ (fun i => |b i|)).map (fun x => negativeMass b + x) := by
  classical
  let N := negativeIndices b
  have habs : flipCoefficients N b = fun i => |b i| := by
    funext i
    by_cases hi : b i < 0
    · simp [flipCoefficients, N, negativeIndices, hi, abs_of_neg hi]
    · simp [flipCoefficients, N, negativeIndices, hi, abs_of_nonneg (le_of_not_gt hi)]
  let e : Finset α ↪ Finset α := ⟨fun S => N ∆ S, symmDiff_right_injective N⟩
  have hmap : (Finset.univ : Finset α).powerset.map e = Finset.univ.powerset := by
    ext S
    simp only [Finset.mem_map, Finset.mem_powerset, Finset.subset_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => ⟨N ∆ S, by simp [e]⟩⟩
  unfold fullSubsetSums
  conv_rhs => rw [← hmap]
  rw [Finset.map_val, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro S _
  dsimp [e]
  rw [← habs, flip_subset_sum, symmDiff_symmDiff_cancel_left]
  change (∑ i ∈ S, b i) = (∑ i ∈ N, b i) + ((∑ i ∈ S, b i) - ∑ i ∈ N, b i)
  ring

/-- The negative mass is the least value of the full occurrence spectrum,
including when zero coefficients produce several minimizing subsets. -/
theorem full_spectrum_minimum [Fintype α] (b : α → ℝ) :
    IsLeast {x : ℝ | x ∈ fullSubsetSums Finset.univ b} (negativeMass b) := by
  classical
  constructor
  · exact Multiset.mem_map.mpr ⟨negativeIndices b, by simp, rfl⟩
  · intro x hx
    obtain ⟨S, _hS, rfl⟩ := Multiset.mem_map.mp hx
    have hle (i : α) (_hi : i ∈ (Finset.univ : Finset α)) :
        (if b i < 0 then b i else 0) ≤ (if i ∈ S then b i else 0) := by
      by_cases hn : b i < 0 <;> by_cases hs : i ∈ S <;> simp [hn, hs]
      · exact le_of_lt hn
      · exact le_of_not_gt hn
    simpa [negativeMass, negativeIndices, ← Finset.sum_filter] using Finset.sum_le_sum hle

/-- For odd length at least three, equality of even spectra gives equal totals,
equal negative masses, and equal full spectra of the absolute coefficients. -/
theorem even_spectrum_absolute_reduction {m : ℕ} (hm : 3 ≤ m) (hodd : Odd m)
    (b c : Fin m → ℝ)
    (h : evenSubsetSums Finset.univ b = evenSubsetSums Finset.univ c) :
    (∑ i, b i) = (∑ i, c i) ∧ negativeMass b = negativeMass c ∧
      fullSubsetSums Finset.univ (fun i => |b i|) =
        fullSubsetSums Finset.univ (fun i => |c i|) := by
  obtain ⟨htotal, hfull⟩ := even_spectrum_determines_full hm hodd b c h
  have hbmin := full_spectrum_minimum b
  have hcmin := full_spectrum_minimum c
  have hmass : negativeMass b = negativeMass c := le_antisymm
    (hbmin.2 (by rw [hfull]; exact hcmin.1))
    (hcmin.2 (by rw [← hfull]; exact hbmin.1))
  refine ⟨htotal, hmass, ?_⟩
  rw [full_spectrum_signed_normalization b, full_spectrum_signed_normalization c,
    hmass] at hfull
  exact Multiset.map_injective (fun _ _ hh => add_left_cancel hh) hfull

/-- Once the absolute coefficient occurrences are matched, equal even spectra
supply the even zero-sum sign witness for that same occurrence permutation. -/
theorem even_sign_witness_of_absolute_permutation {m : ℕ} (hm : 3 ≤ m) (hodd : Odd m)
    (b c : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (h : evenSubsetSums Finset.univ b = evenSubsetSums Finset.univ c)
    (habs : ∀ i, |c (σ i)| = |b i|) :
    ∃ I : Finset (Fin m), Even I.card ∧ (∑ i ∈ I, b i) = 0 ∧
      ∀ i, c (σ i) = if i ∈ I then -b i else b i := by
  classical
  let I := Finset.univ.filter (fun i => c (σ i) ≠ b i)
  have hc (i : Fin m) : c (σ i) = flipCoefficients I b i := by
    by_cases hi : c (σ i) = b i
    · simp [flipCoefficients, I, hi]
    · simpa [flipCoefficients, I, hi] using (abs_eq_abs.mp (habs i)).resolve_left hi
  have hfun : (fun i => c (σ i)) = flipCoefficients I b := funext hc
  have htotal := (even_spectrum_determines_full hm hodd b c h).1
  have hsumC : (∑ i, c (σ i)) = ∑ i, c i := Equiv.sum_comp σ c
  have hcomp := Finset.sum_compl_add_sum I b
  have hflip := flip_subset_sum I Finset.univ b
  have hsym : I ∆ Finset.univ = Iᶜ := by
    ext i
    simp [Finset.mem_symmDiff]
  rw [hsym, ← hfun, hsumC] at hflip
  have hzero : (∑ i ∈ I, b i) = 0 := by linarith
  have hspec : evenSubsetSums Finset.univ (flipCoefficients I b) =
      evenSubsetSums Finset.univ b := by
    rw [← hfun, even_spectrum_permutation σ c, h]
  obtain ⟨J, hJeven, hJzero, hJflip⟩ := repair_flip_parity I b hzero hspec
  refine ⟨J, hJeven, hJzero, ?_⟩
  intro i
  change c (σ i) = flipCoefficients J b i
  rw [hJflip]
  exact hc i

end D5.S3.Combinatorics.SubsetSpectrum
