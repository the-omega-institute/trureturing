/- GID: D5/S3/Quantum/Sharpness/SpectralSharpnessSaturation
   generality: G
   mirror-B: D5/B/S3/Quantum/Sharpness/SpectralSharpnessSaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For a probability spectrum (antitone, nonnegative, unit-sum) on n points, the spectral sharpness — the total variation between the spectrum and its reversal — attains its maximum value 1 exactly when the support has cardinality ≤ ⌊n/2⌋: sharpness = 1 ↔ #nonzero ≤ ⌊n/2⌋. Sharpness 1 is mutual singularity of the spectrum and its reversal; under antitonicity the support is a prefix, so singularity makes support and reversed image disjoint (2·|support| ≤ n) and conversely. This is the saturation clause of the maximal-sharpness law; the pure-state capacity, spectral-pairing closed form, variational supremum, median-cut ±1 witness, and the minimal endpoint sharpness = 0 ⇔ uniform are not covered. -/

import Mathlib
import D5.S3.Quantum.Sharpness.SpectralSharpness

namespace D5.S3.Quantum.Sharpness.SpectralSharpnessSaturation

open Finset
open D5.S3.Quantum.Sharpness.SpectralSharpness

/-- The reversal permutation preserves the total sum of a spectrum. -/
lemma sum_rev {n : ℕ} (r : Fin n → ℝ) : ∑ i, r (Fin.rev i) = ∑ i, r i :=
  Equiv.sum_comp (Fin.revPerm) r

/-- For nonnegative `a, b`, the triangle equality `|a - b| = a + b` holds iff one of them vanishes
(mutual singularity of a two-point pair). -/
lemma abs_sub_eq_add_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| = a + b ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    rcases abs_cases (a - b) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at h; right; linarith
    · rw [he] at h; left; linarith
  · rintro (h | h)
    · subst h; rw [zero_sub, abs_neg, abs_of_nonneg hb]; ring
    · subst h; rw [sub_zero, abs_of_nonneg ha]; ring

/-- Under antitonicity and nonnegativity the support is downward-closed: if `r i ≠ 0` and `j ≤ i`
then `r j ≠ 0` (larger values sit at smaller indices). -/
lemma support_lower {n : ℕ} (r : Fin n → ℝ) (hnn : ∀ i, 0 ≤ r i) (hmono : Antitone r)
    {i j : Fin n} (hi : r i ≠ 0) (hji : j ≤ i) : r j ≠ 0 := by
  have h1 : 0 < r i := lt_of_le_of_ne (hnn i) (Ne.symm hi)
  have h2 : r i ≤ r j := hmono hji
  intro hj; rw [hj] at h2; linarith

/-- **Maximal spectral sharpness characterises the support-at-most-half regime (saturation
criterion).** For a probability spectrum `r : Fin n → ℝ` — antitone, nonnegative, and unit-sum — the
spectral sharpness `spectralSharpness r` attains its **maximum** value `1` exactly when the support
(the set of nonzero entries) has cardinality at most `⌊n / 2⌋`:
`spectralSharpness r = 1 ↔ #{i | r i ≠ 0} ≤ n / 2`.

In words, freedom is maximally saturated without any pure state — it suffices that the support does
not exceed half the dimension. Sharpness `1` is equivalent to mutual singularity of the spectrum and
its reversal (`∀ i, r i = 0 ∨ r (Fin.rev i) = 0`): the total variation `(1/2) ∑ |r i - r (rev i)|`
equals `1` iff every summand saturates `|a - b| ≤ a + b`, which for nonnegative entries forces one of
`r i`, `r (rev i)` to vanish. Under antitonicity the support is a downward-closed prefix, so mutual
singularity makes the support and its reversed image disjoint, giving `2 · #support ≤ n` hence
`#support ≤ ⌊n/2⌋`; conversely a prefix support of size `≤ ⌊n/2⌋` is disjoint from its reversal, which
yields mutual singularity.

Nonnegativity is a genuine load-bearing hypothesis here (used in the triangle-equality step), unlike
the companion zero-endpoint result. This records only the **saturation** clause `sharpness = 1 ⇔
rank ≤ ⌊n/2⌋` of the maximal-sharpness law; the pure-state capacity, the spectral-pairing closed
form `C_ρ`, the variational supremum `μ* = sup C_ρ / dist`, the median-cut `±1` witness, and the
minimal-endpoint characterisation `sharpness = 0 ⇔ uniform` are not covered. -/
theorem spectral_sharpness_one_iff_support_le_half {n : ℕ} (r : Fin n → ℝ)
    (hnn : ∀ i, 0 ≤ r i) (hmono : Antitone r) (hsum : ∑ i, r i = 1) :
    spectralSharpness r = 1 ↔
      (Finset.univ.filter (fun i => r i ≠ 0)).card ≤ n / 2 := by
  set S := Finset.univ.filter (fun i => r i ≠ 0) with hS
  -- Step A: sharpness = 1 ↔ mutual singularity of `r` and its reversal
  have keyA : spectralSharpness r = 1 ↔ ∀ i, r i = 0 ∨ r (Fin.rev i) = 0 := by
    unfold spectralSharpness
    have hle : ∀ i, |r i - r (Fin.rev i)| ≤ r i + r (Fin.rev i) := by
      intro i
      calc |r i - r (Fin.rev i)| ≤ |r i| + |r (Fin.rev i)| := abs_sub _ _
        _ = r i + r (Fin.rev i) := by rw [abs_of_nonneg (hnn i), abs_of_nonneg (hnn _)]
    have hsum2 : ∑ i, (r i + r (Fin.rev i)) = 2 := by
      rw [Finset.sum_add_distrib, sum_rev, hsum]; ring
    constructor
    · intro h
      have hEq : ∑ i, |r i - r (Fin.rev i)| = ∑ i, (r i + r (Fin.rev i)) := by
        have h2 : ∑ i, |r i - r (Fin.rev i)| = 2 := by linarith [h]
        rw [h2, hsum2]
      have hterm := (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hEq
      intro i
      exact (abs_sub_eq_add_iff (hnn i) (hnn _)).mp (hterm i (mem_univ i))
    · intro h
      have hEq : ∀ i ∈ univ, |r i - r (Fin.rev i)| = r i + r (Fin.rev i) := by
        intro i _; exact (abs_sub_eq_add_iff (hnn i) (hnn _)).mpr (h i)
      rw [Finset.sum_congr rfl hEq, hsum2]; norm_num
  set s := S.card with hs
  have hrevcard : (S.image Fin.rev).card = s := by
    rw [Finset.card_image_of_injective _ (Fin.rev_injective)]
  rw [keyA]
  constructor
  · -- forward: singularity ⟹ 2s ≤ n ⟹ s ≤ n/2
    intro h
    have hdisj : Disjoint S (S.image Fin.rev) := by
      rw [Finset.disjoint_left]
      intro a haS haRev
      simp only [Finset.mem_image] at haRev
      obtain ⟨b, hbS, hba⟩ := haRev
      have hrb : r b ≠ 0 := (Finset.mem_filter.mp hbS).2
      have hra : r a ≠ 0 := (Finset.mem_filter.mp haS).2
      rcases h b with hb | hrevb
      · exact hrb hb
      · rw [hba] at hrevb; exact hra hrevb
    have hsn : s + s ≤ n := by
      have hu := Finset.card_union_of_disjoint hdisj
      rw [hrevcard] at hu
      have hle2 : (S ∪ S.image Fin.rev).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      rw [hu, Fintype.card_fin] at hle2
      omega
    omega
  · -- backward: s ≤ n/2 ⟹ singularity (uses `S` is a prefix)
    intro hcard
    have hprefix : ∀ i, i ∈ S → i.val < s := by
      intro i hiS
      by_contra hcon
      have hcon' : s ≤ i.val := not_lt.mp hcon
      have hri : r i ≠ 0 := (Finset.mem_filter.mp hiS).2
      have hsub : Finset.Iic i ⊆ S := by
        intro b hb
        rw [Finset.mem_Iic] at hb
        rw [hS, Finset.mem_filter]
        exact ⟨mem_univ _, support_lower r hnn hmono hri hb⟩
      have hc : (Finset.Iic i).card = i.val + 1 := by simp [Fin.card_Iic]
      have hcle := Finset.card_le_card hsub
      rw [hc] at hcle
      omega
    intro i
    by_cases hri : r i = 0
    · left; exact hri
    · right
      have hiS : i ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨mem_univ _, hri⟩
      have hival : i.val < s := hprefix i hiS
      by_contra hrev
      have hrevS : Fin.rev i ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨mem_univ _, hrev⟩
      have hrevval : (Fin.rev i).val < s := hprefix _ hrevS
      have hrveq : (Fin.rev i).val = n - 1 - i.val := by simp [Fin.rev]; omega
      have hlt := i.isLt
      omega

end D5.S3.Quantum.Sharpness.SpectralSharpnessSaturation
