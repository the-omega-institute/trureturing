/- GID: D5/S3/Quantum/Matrix/JainAbsCosine/Separation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/JainAbsCosine/Separation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict separation of the nonzero absolute-cosine Fourier modes. -/

import D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns

/-! Strict ordering within each nonzero Fourier sign class. -/

open scoped BigOperators
open D5.S3.Quantum.Matrix.JainAbsCosine.Defs
open D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
open D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns

namespace D5.S3.Quantum.Matrix.JainAbsCosine.Separation

private lemma rootProduct_succ (i : ℕ) (r : ℝ) :
    rootProduct (i + 1) r = rootProduct i r * (r - 2 * (i : ℝ)) := by
  exact Finset.prod_range_succ _ _

private lemma rootProduct_zero {i j : ℕ} (hij : i < j) :
    rootProduct j (2 * (i : ℝ)) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hij)
  simp

private lemma rootProduct_step {i j : ℕ} {r : ℝ} (hij : i < j)
    (hsi : SignType.sign (rootProduct i r) = SignType.sign (rootProduct j r))
    (hne : rootProduct i r ≠ 0) :
    ∃ d : ℕ, (d = 1 ∨ d = 2) ∧ i + d ≤ j ∧
      SignType.sign (rootProduct (i + d) r) = SignType.sign (rootProduct i r) := by
  rcases lt_trichotomy r (2 * (i : ℝ)) with hlt | heq | hgt
  · have hnext : SignType.sign (rootProduct (i + 1) r) =
        -SignType.sign (rootProduct i r) := by
      rw [rootProduct_succ, sign_mul, sign_neg (sub_neg.mpr hlt)]
      cases SignType.sign (rootProduct i r) <;> rfl
    have hgap : i + 2 ≤ j := by
      by_contra hn
      have hj : j = i + 1 := by omega
      rw [hj, hnext] at hsi
      have hz : SignType.sign (rootProduct i r) = 0 := by
        cases hs : SignType.sign (rootProduct i r) <;> simp_all
      exact hne (sign_eq_zero_iff.mp hz)
    refine ⟨2, Or.inr rfl, hgap, ?_⟩
    have hlt' : r < 2 * ((i + 1 : ℕ) : ℝ) := by push_cast; linarith
    rw [show i + 2 = (i + 1) + 1 by omega, rootProduct_succ,
      sign_mul, sign_neg (sub_neg.mpr hlt'), hnext]
    cases SignType.sign (rootProduct i r) <;> rfl
  · have hz : rootProduct j r = 0 := by simpa [heq] using rootProduct_zero hij
    exact (hne (sign_eq_zero_iff.mp (by simpa [hz] using hsi))).elim
  · refine ⟨1, Or.inl rfl, hij, ?_⟩
    rw [rootProduct_succ, sign_mul, sign_pos (sub_pos.mpr hgt), mul_one]

private lemma same_sign_ordered (m : ℕ) (r : ℝ)
    (hsign : ∀ k, 1 ≤ k → k ≤ m →
      SignType.sign (modeValue m k r) = SignType.sign (rootProduct k r))
    (hgap : ∀ k d, 1 ≤ k → (d = 1 ∨ d = 2) → k + d ≤ m →
      SignType.sign (modeValue m k r - modeValue m (k + d) r) =
        SignType.sign (rootProduct k r))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hjm : j ≤ m)
    (hsame : SignType.sign (modeValue m i r) = SignType.sign (modeValue m j r))
    (hne : modeValue m i r ≠ 0) :
    (0 < modeValue m i r → modeValue m j r < modeValue m i r) ∧
      (modeValue m i r < 0 → modeValue m i r < modeValue m j r) := by
  generalize hn : j - i = n
  induction n using Nat.strong_induction_on generalizing i j with
  | h n ih =>
    have him : i ≤ m := by omega
    have hpne : rootProduct i r ≠ 0 := by
      intro hz
      exact hne (sign_eq_zero_iff.mp (by simpa [hz] using hsign i hi him))
    have hpij : SignType.sign (rootProduct i r) = SignType.sign (rootProduct j r) :=
      (hsign i hi him).symm.trans (hsame.trans (hsign j (by omega) hjm))
    obtain ⟨d, hd, hkj, hpk⟩ := rootProduct_step hij hpij hpne
    have hdpos : 0 < d := by rcases hd with rfl | rfl <;> omega
    have hkim : i + d ≤ m := by omega
    have hks : SignType.sign (modeValue m (i + d) r) =
        SignType.sign (modeValue m i r) :=
      (hsign (i + d) (by omega) hkim).trans (hpk.trans (hsign i hi him).symm)
    have hdiff : SignType.sign (modeValue m i r - modeValue m (i + d) r) =
        SignType.sign (modeValue m i r) :=
      (hgap i d hi hd hkim).trans (hsign i hi him).symm
    by_cases hkj' : i + d = j
    · rw [hkj'] at hdiff
      constructor
      · intro hp
        have := sign_eq_one_iff.mp (hdiff.trans (sign_pos hp))
        linarith
      · intro hn
        have := sign_eq_neg_one_iff.mp (hdiff.trans (sign_neg hn))
        linarith
    · have hkn : modeValue m (i + d) r ≠ 0 := by
        intro hz
        have := hks.symm
        rw [hz, sign_zero] at this
        exact hne (sign_eq_zero_iff.mp this)
      have hr := ih (j - (i + d)) (by omega) (i := i + d) (j := j)
        (by omega) (by omega) hjm (hks.trans hsame) hkn rfl
      constructor
      · intro hp
        have hkpos := sign_eq_one_iff.mp (hks.trans (sign_pos hp))
        have hdp := sign_eq_one_iff.mp (hdiff.trans (sign_pos hp))
        linarith [hr.1 hkpos]
      · intro hn
        have hkneg := sign_eq_neg_one_iff.mp (hks.trans (sign_neg hn))
        have hdn := sign_eq_neg_one_iff.mp (hdiff.trans (sign_neg hn))
        linarith [hr.2 hkneg]

/-- The constant Fourier mode strictly exceeds every other representative. -/
theorem modeValue_lt_top {m j : ℕ} (hm : 1 ≤ m) (hj : 1 ≤ j) (hjm : j ≤ m)
    (r : ℝ) : modeValue m j r < modeValue m 0 r := by
  have hd : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hθ : 0 < angle m := div_pos Real.pi_pos hd
  have hx : 0 < 2 * (j : ℝ) * angle m := by positivity
  have hxπ : 2 * (j : ℝ) * angle m < Real.pi := by
    rw [angle, ← mul_div_assoc, div_lt_iff₀ hd]
    have hjm' : (j : ℝ) ≤ m := by exact_mod_cast hjm
    nlinarith [mul_le_mul_of_nonneg_right hjm' Real.pi_pos.le, Real.pi_pos]
  have hc : Real.cos (2 * (j : ℝ) * angle m) < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
      hxπ.le hx
  have hsum : (∑ l ∈ Finset.Icc 1 m,
      Real.cos (2 * (j : ℝ) * (l : ℝ) * angle m) *
        Real.cos ((l : ℝ) * angle m) ^ r) <
      ∑ l ∈ Finset.Icc 1 m, Real.cos ((l : ℝ) * angle m) ^ r := by
    apply Finset.sum_lt_sum
    · intro l hl
      exact mul_le_of_le_one_left (Real.rpow_nonneg (cosine_base_bounds
        (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2).1.le _) (Real.cos_le_one _)
    · refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hm⟩, ?_⟩
      simp only [Nat.cast_one, mul_one, one_mul]
      exact mul_lt_of_lt_one_left
        (by simpa using Real.rpow_pos_of_pos (cosine_base_bounds (m := m) (l := 1) le_rfl hm).1 r) hc
  simpa only [modeValue, Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, one_mul]
    using (show 1 + 2 * (∑ l ∈ Finset.Icc 1 m,
      Real.cos (2 * (j : ℝ) * (l : ℝ) * angle m) *
        Real.cos ((l : ℝ) * angle m) ^ r) <
      1 + 2 * ∑ l ∈ Finset.Icc 1 m, Real.cos ((l : ℝ) * angle m) ^ r by linarith)

/-- Equal nonzero Fourier representatives have equal indices. -/
theorem modeValue_injective_nonzero {m i j : ℕ} (hi : 1 ≤ i) (him : i ≤ m)
    (hj : 1 ≤ j) (hjm : j ≤ m) (r : ℝ)
    (heq : modeValue m i r = modeValue m j r) (hne : modeValue m i r ≠ 0) : i = j := by
  have hs : ∀ k, 1 ≤ k → k ≤ m →
      SignType.sign (modeValue m k r) = SignType.sign (rootProduct k r) :=
    fun k hk hkm => modeValue_sign hk hkm r
  have hg : ∀ k d, 1 ≤ k → (d = 1 ∨ d = 2) → k + d ≤ m →
      SignType.sign (modeValue m k r - modeValue m (k + d) r) =
        SignType.sign (rootProduct k r) :=
    fun k d hk hd hkm => modeValue_gap_sign hk hd hkm r
  by_contra hidx
  rcases lt_or_gt_of_ne hidx with hij | hji
  · have ho := same_sign_ordered m r hs hg hi hij hjm (congrArg SignType.sign heq) hne
    rcases lt_or_gt_of_ne hne with hn | hp
    · linarith [ho.2 hn]
    · linarith [ho.1 hp]
  · have hne' : modeValue m j r ≠ 0 := by simpa only [heq] using hne
    have ho := same_sign_ordered m r hs hg hj hji him
      (congrArg SignType.sign heq.symm) hne'
    rcases lt_or_gt_of_ne hne' with hn | hp
    · linarith [ho.2 hn]
    · linarith [ho.1 hp]

end D5.S3.Quantum.Matrix.JainAbsCosine.Separation
