/- GID: D5/S3/Combinatorics/SubsetSpectrum/RealClassification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubsetSpectrum/RealClassification
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Odd-length real even spectra classify coefficients up to even zero-sum sign permutations. -/

import D5.S3.Combinatorics.SubsetSpectrum.NonnegativeRecovery
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SubsetSpectrum

private lemma occurrence_permutation {α : Type*} [Fintype α] (f g : α → ℝ)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ σ : Equiv.Perm α, ∀ i, g (σ i) = f i := by
  classical
  have hfiber (x : ℝ) : Fintype.card {i // f i = x} = Fintype.card {i // g i = x} := by
    have hc := congrArg (Multiset.count x) h
    simpa [Multiset.count_map, Fintype.card_subtype, Finset.card, Finset.filter_val,
      eq_comm] using hc
  let e (x : ℝ) : {i // f i = x} ≃ {i // g i = x} := Fintype.equivOfCardEq (hfiber x)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

/-- In every odd length at least three, the real even occurrence spectrum
classifies coefficient families up to coordinate permutation and an even
zero-sum sign change. Zeros and repeated coefficient values are allowed. -/
theorem real_even_spectrum_classification {m : ℕ} (hm : 3 ≤ m) (hodd : Odd m)
    (b c : Fin m → ℝ) :
    evenSubsetSums Finset.univ b = evenSubsetSums Finset.univ c ↔
      ∃ σ : Equiv.Perm (Fin m), ∃ I : Finset (Fin m), Even I.card ∧
        (∑ i ∈ I, b i) = 0 ∧ ∀ i, c (σ i) = if i ∈ I then -b i else b i := by
  classical
  constructor
  · intro h
    have habsspec := (even_spectrum_absolute_reduction hm hodd b c h).2.2
    rw [indexed_full_spectrum, indexed_full_spectrum] at habsspec
    have hcoeff := nonnegative_subset_sum_recovery
      (Finset.univ.val.map (fun i => |b i|)) (Finset.univ.val.map (fun i => |c i|))
      (by
        intro x hx
        obtain ⟨i, _hi, rfl⟩ := Multiset.mem_map.mp hx
        exact abs_nonneg (b i))
      (by
        intro x hx
        obtain ⟨i, _hi, rfl⟩ := Multiset.mem_map.mp hx
        exact abs_nonneg (c i)) habsspec
    obtain ⟨σ, hσ⟩ := occurrence_permutation (fun i => |b i|) (fun i => |c i|) hcoeff
    obtain ⟨I, heven, hzero, hc⟩ :=
      even_sign_witness_of_absolute_permutation hm hodd b c σ h hσ
    exact ⟨σ, I, heven, hzero, hc⟩
  · rintro ⟨σ, I, heven, hzero, hc⟩
    exact even_spectrum_of_sign_permutation b c σ I heven hzero hc

end D5.S3.Combinatorics.SubsetSpectrum
