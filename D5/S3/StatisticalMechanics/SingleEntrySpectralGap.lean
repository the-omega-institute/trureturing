/- GID: D5/S3/StatisticalMechanics/SingleEntrySpectralGap
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/SingleEntrySpectralGap
   mirror-E: none(waiver:single-entry-mode-spectrum)
   anchors: []
   utility: none
   digest: Schur elimination identifies the lowest mode-coordinate eigenvalue. -/

import D5.S3.StatisticalMechanics.SingleEntrySecularRoot

/-! # The single-entry secular root in free-mode coordinates

The matrix below is the full rank-one extension of the diagonal free-mode
operator. Its coordinates are free product modes, not configurations. Identifying
this matrix with the configuration generator requires the product change of basis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open Matrix

namespace D5.S3.StatisticalMechanics.SingleEntrySpectralGap
open SingleEntrySecularRoot

/-- Negative generator in free-mode coordinates, with `none` the attached state.
The coordinate functional `∑ S, x (some S)` reads out the empty configuration. -/
def modeNegativeGenerator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (η θ : ℝ) :
    Matrix (Option (Finset ι)) (Option (Finset ι)) ℝ
  | none, none => θ
  | none, some _ => -η
  | some S, none => -θ * modeWeight a b S
  | some S, some T => (if S = T then subsetRate a b S else 0) + η * modeWeight a b S

private theorem action_none {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (η θ : ℝ) (x : Option (Finset ι) → ℝ) :
    (modeNegativeGenerator a b η θ *ᵥ x) none =
      θ * x none - η * ∑ S, x (some S) := by
  simp [mulVec, dotProduct, Fintype.sum_option, modeNegativeGenerator,
    ← Finset.mul_sum]
  ring

private theorem action_some {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (η θ : ℝ) (x : Option (Finset ι) → ℝ) (S : Finset ι) :
    (modeNegativeGenerator a b η θ *ᵥ x) (some S) =
      subsetRate a b S * x (some S) +
        modeWeight a b S * (η * (∑ T, x (some T)) - θ * x none) := by
  simp [mulVec, dotProduct, Fintype.sum_option, modeNegativeGenerator,
    add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private theorem denominators {ι : Type*}
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (l : ℝ) (hl : 0 < l) (hupper : ∀ i, l < siteRate a b i) :
    ∀ S : Finset ι, subsetRate a b S - l ≠ 0 := by
  classical
  intro S
  by_cases hS : S = ∅
  · subst S
    simp [subsetRate, ne_of_gt hl]
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have hsum : siteRate a b i ≤ subsetRate a b S :=
      Finset.single_le_sum (fun j _ => (add_pos (ha j) (hb j)).le) hi
    exact ne_of_gt (by linarith [hupper i])

private theorem secular_full_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (η θ l : ℝ) (hl : l ≠ 0) :
    secular a b η θ l = θ - l -
      η * l * ∑ S : Finset ι, modeWeight a b S / (subsetRate a b S - l) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset ι))]
  simp only [subsetRate, Finset.sum_empty, zero_sub, div_neg]
  unfold secular
  simp only [subsetRate]
  field_simp
  ring

private theorem schur_equivalence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (η θ l : ℝ) (hl : l ≠ 0)
    (hpole : ∀ S : Finset ι, subsetRate a b S - l ≠ 0) :
    (∃ x : Option (Finset ι) → ℝ, x ≠ 0 ∧
      modeNegativeGenerator a b η θ *ᵥ x = l • x) ↔
      secular a b η θ l = 0 := by
  rw [secular_full_sum a b η θ l hl]
  constructor
  · rintro ⟨x, hx, he⟩
    have hR := congrFun he none
    rw [action_none] at hR
    simp only [Pi.smul_apply, smul_eq_mul] at hR
    have hS (S : Finset ι) :
        x (some S) = l * modeWeight a b S * x none / (subsetRate a b S - l) := by
      have hs := congrFun he (some S)
      rw [action_some] at hs
      simp only [Pi.smul_apply, smul_eq_mul] at hs
      apply (eq_div_iff (hpole S)).mpr
      nlinarith [congrArg (fun t : ℝ => modeWeight a b S * t) hR]
    have hxR : x none ≠ 0 := by
      intro hz
      apply hx
      funext i
      cases i with
      | none => exact hz
      | some S => simp [hS S, hz]
    have hsum : (∑ S, x (some S)) =
        l * x none * ∑ S, modeWeight a b S / (subsetRate a b S - l) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [hS]
      ring
    rw [hsum] at hR
    have hz : (θ - l - η * l *
        ∑ S, modeWeight a b S / (subsetRate a b S - l)) * x none = 0 := by
      nlinarith [hR]
    exact (mul_eq_zero.mp hz).resolve_right hxR
  · intro hF
    let x : Option (Finset ι) → ℝ
      | none => 1
      | some S => l * modeWeight a b S / (subsetRate a b S - l)
    have hsum : (∑ S, x (some S)) =
        l * ∑ S, modeWeight a b S / (subsetRate a b S - l) := by
      simp only [x, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring
    refine ⟨x, ?_, ?_⟩
    · intro hx
      have := congrFun hx none
      norm_num [x] at this
    · funext i
      cases i with
      | none =>
        rw [action_none, hsum]
        simp only [x, Pi.smul_apply, smul_eq_mul, mul_one]
        nlinarith [hF]
      | some S =>
        rw [action_some, hsum]
        simp only [x, Pi.smul_apply, smul_eq_mul, mul_one]
        have hrel : η * (l * ∑ T, modeWeight a b T / (subsetRate a b T - l)) - θ = -l := by
          nlinarith [hF]
        rw [hrel]
        field_simp [hpole S]
        ring

/-- The secular root is the least positive real eigenvalue of the explicitly
defined mode matrix. The existence part constructs its eigenvector; the
minimality part eliminates every proposed smaller positive eigenvector. -/
theorem secular_root_least_mode_eigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (a b : ι → ℝ) (η θ : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hη : 0 < η) (hθ : 0 < θ) :
    ∃ l : ℝ, 0 < l ∧ (∀ i, l < siteRate a b i) ∧ secular a b η θ l = 0 ∧
      (∃ x : Option (Finset ι) → ℝ, x ≠ 0 ∧
        modeNegativeGenerator a b η θ *ᵥ x = l • x) ∧
      ∀ μ : ℝ, 0 < μ →
        (∃ y : Option (Finset ι) → ℝ, y ≠ 0 ∧
          modeNegativeGenerator a b η θ *ᵥ y = μ • y) → l ≤ μ := by
  obtain ⟨l, hl, huniq⟩ := (secular_unique_root a b η θ ha hb hη hθ).1
  refine ⟨l, hl.1, hl.2.1, hl.2.2, ?_, ?_⟩
  · exact (schur_equivalence a b η θ l (ne_of_gt hl.1)
      (denominators a b ha hb l hl.1 hl.2.1)).mpr hl.2.2
  · intro μ hμ he
    by_contra hnot
    have hlt : μ < l := lt_of_not_ge hnot
    have hupper : ∀ i, μ < siteRate a b i := fun i => hlt.trans (hl.2.1 i)
    have hF := (schur_equivalence a b η θ μ (ne_of_gt hμ)
      (denominators a b ha hb μ hμ hupper)).mp he
    have heq := huniq μ ⟨hμ, hupper, hF⟩
    linarith

#print axioms secular_root_least_mode_eigenvalue


end D5.S3.StatisticalMechanics.SingleEntrySpectralGap
