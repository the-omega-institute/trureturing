/- GID: D5/S3/Entropy/EntropyEquality
   generality: G
   mirror-B: D5/B/S3/Entropy/EntropyEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize both equality cases of the finite Shannon entropy bracket. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep terms: `negMulLog_eq_zero`, `eq_zero.*negMulLog`,
     `negMulLog.*= 0`, `negMulLog_zero`, `negMulLog_one`, `log_eq_zero`,
     `sum_eq_zero_iff_of_nonneg`, finite entropy endpoint names, `point mass`,
     `dirac`, and `PMF.pure`.
   * `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` provides the endpoint simp lemmas
     `Real.negMulLog_zero` and `Real.negMulLog_one`, plus `Real.negMulLog_nonneg`, but no
     iff characterization of all zeros. `Real.binEntropy_eq_zero` characterizes the different
     two-term binary entropy, not one `negMulLog` atom. The lower proof therefore uses
     `Real.log_eq_zero` after unfolding the atom; nonnegativity excludes its root `-1`.
   * `Finset.sum_eq_zero_iff_of_nonneg` is the upstream finite-sum equality criterion.
     Mathlib's `PMF.pure` uses the same point-mass formula, but the repository entropy is
     deliberately defined on raw real-valued functions, so the theorem keeps that native type.
   * Repository-wide `D5/` grep terms: Shannon-entropy names next to zero, log-cardinality,
     uniform laws, point masses, Dirac/delta laws, `negMulLog`, KL divergence next to zero,
     and the displayed if-then-else mass formula in rearranged forms. No duplicate endpoint
     characterization was found. Units are nats because `shannonEntropy` uses `Real.log`.
-/

import D5.S3.Divergence.GibbsEquality
import D5.S3.Entropy.EntropyDivergenceIdentity

namespace D5.S3.Entropy.EntropyEquality

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.GibbsEquality
open D5.S3.Entropy.EntropyDivergenceIdentity
open D5.S3.Entropy.MaxEntropy

/-- Maximum finite Shannon entropy is attained exactly by the uniform law. -/
theorem entropy_eq_log_card_iff_uniform {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℝ) (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) :
    shannonEntropy p = Real.log (Fintype.card ι)
      ↔ p = fun _ => (Fintype.card ι : ℝ)⁻¹ := by
  classical
  have hcard_pos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hu :
      (∀ i : ι, 0 ≤ (Fintype.card ι : ℝ)⁻¹) ∧
        ∑ _ : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
    constructor
    · intro i
      exact (inv_pos.mpr hcard_pos).le
    · simp [hcard_ne]
  have hac : ∀ i : ι, (Fintype.card ι : ℝ)⁻¹ = 0 → p i = 0 := by
    intro i hui
    exact ((inv_ne_zero hcard_ne) hui).elim
  rw [← kl_divergence_eq_zero_iff p
    (fun _ => (Fintype.card ι : ℝ)⁻¹) hp hu hac]
  rw [kl_divergence_uniform_eq p hp]
  constructor
  · intro hentropy
    rw [hentropy, sub_self]
  · intro hdeficit
    exact (sub_eq_zero.mp hdeficit).symm

open Classical in
/-- Finite Shannon entropy vanishes exactly on point masses. -/
theorem entropy_eq_zero_iff_point_mass {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1) :
    shannonEntropy p = 0 ↔ ∃ i, p = fun j => if j = i then 1 else 0 := by
  classical
  have hp_le_one (i : ι) : p i ≤ 1 := by
    calc
      p i ≤ ∑ j, p j :=
        Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
      _ = 1 := hp.2
  have hterm_nonneg (i : ι) : 0 ≤ Real.negMulLog (p i) :=
    Real.negMulLog_nonneg (hp.1 i) (hp_le_one i)
  have hterm_zero_one (i : ι) (hzero : Real.negMulLog (p i) = 0) :
      p i = 0 ∨ p i = 1 := by
    simp only [Real.negMulLog] at hzero
    rcases mul_eq_zero.mp hzero with hp_zero | hlog_zero
    · exact Or.inl (neg_eq_zero.mp hp_zero)
    · rcases Real.log_eq_zero.mp hlog_zero with hp_zero | hp_one | hp_neg_one
      · exact Or.inl hp_zero
      · exact Or.inr hp_one
      · exact (by nlinarith [hp.1 i])
  constructor
  · intro hentropy_zero
    rw [shannonEntropy] at hentropy_zero
    have hall_terms : ∀ i ∈ Finset.univ, Real.negMulLog (p i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm_nonneg i).mp hentropy_zero
    have hexists_one : ∃ i, p i = 1 := by
      by_contra hnone
      have hne_one : ∀ i, p i ≠ 1 := not_exists.mp hnone
      have hall_zero : ∀ i, p i = 0 := by
        intro i
        exact (hterm_zero_one i (hall_terms i (Finset.mem_univ i))).resolve_right (hne_one i)
      have hsum_zero : ∑ i, p i = 0 := by
        simp [hall_zero]
      exact zero_ne_one (hsum_zero.symm.trans hp.2)
    rcases hexists_one with ⟨i, hi⟩
    refine ⟨i, funext fun j => ?_⟩
    by_cases hji : j = i
    · subst j
      simp [hi]
    · have hsplit :
          (∑ k ∈ Finset.univ.erase i, p k) + p i = ∑ k, p k :=
        Finset.sum_erase_add _ _ (Finset.mem_univ i)
      have hrest_zero : ∑ k ∈ Finset.univ.erase i, p k = 0 := by
        calc
          (∑ k ∈ Finset.univ.erase i, p k) = (∑ k, p k) - p i :=
            eq_sub_of_add_eq hsplit
          _ = 0 := by rw [hp.2, hi, sub_self]
      have hrest_terms : ∀ k ∈ Finset.univ.erase i, p k = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hp.1 k).mp hrest_zero
      have hj_zero : p j = 0 :=
        hrest_terms j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
      simp [hji, hj_zero]
  · rintro ⟨i, rfl⟩
    rw [shannonEntropy]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hji : j = i <;> simp [hji]

end D5.S3.Entropy.EntropyEquality
