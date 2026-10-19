/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ThreeValueConservedComparison
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ThreeValueConservedComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three real emissions admit a reversible conserved comparison with simultaneous bounds. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators
open Finset

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ThreeValueConservedComparison

private lemma ordered_centers (u : Fin 3 → ℝ) (t : ℝ) (ht : 0 < t)
    (hmono : Monotone u) (hu : ∀ i, (1 : ℝ) / 3 ≤ u i ∧ u i ≤ 2 / 5) :
    ∃ w : Fin 3 → ℝ, (∀ i, (1 : ℝ) / 3 ≤ w i ∧ w i ≤ 2 / 5) ∧
      (∀ i, |u i - w i| ≤ t) ∧
      (∀ i j, w i ≠ w j → t ≤ |u i-u j|) := by
  have h01 : u 0 ≤ u 1 := hmono (by decide)
  have h12 : u 1 ≤ u 2 := hmono (by decide)
  have h0 := hu 0
  have h1 := hu 1
  have h2 := hu 2
  by_cases ha : u 1 - u 0 ≤ t
  · by_cases hb : u 2 - u 1 ≤ t
    · refine ⟨fun _ => (u 0 + u 2)/2, ?_, ?_, ?_⟩
      · intro i; constructor <;> linarith
      · intro i; fin_cases i <;> apply abs_le.mpr <;> constructor <;> dsimp <;> linarith
      · intro i j h; exact (h rfl).elim
    · refine ⟨![(u 0+u 1)/2, (u 0+u 1)/2, u 2], ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp <;> constructor <;> linarith
      · intro i; fin_cases i <;> simp <;> first | exact ht.le | (apply abs_le.mpr; constructor <;> linarith)
      · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢
        all_goals first | (rw [abs_of_nonneg (by linarith)]; linarith) |
          (rw [abs_of_nonpos (by linarith)]; linarith)
  · by_cases hb : u 2 - u 1 ≤ t
    · refine ⟨![u 0, (u 1+u 2)/2, (u 1+u 2)/2], ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp <;> constructor <;> linarith
      · intro i; fin_cases i <;> simp <;> first | exact ht.le | (apply abs_le.mpr; constructor <;> linarith)
      · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢
        all_goals first | (rw [abs_of_nonneg (by linarith)]; linarith) |
          (rw [abs_of_nonpos (by linarith)]; linarith)
    · refine ⟨u, hu, ?_, ?_⟩
      · intro i; simp; exact ht.le
      · intro i j h; fin_cases i <;> fin_cases j <;> simp at h ⊢
        all_goals first | (rw [abs_of_nonneg (by linarith)]; linarith) |
          (rw [abs_of_nonpos (by linarith)]; linarith)

private lemma three_centers (u : Fin 3 → ℝ) (t : ℝ) (ht : 0 < t)
    (hu : ∀ i, (1 : ℝ) / 3 ≤ u i ∧ u i ≤ 2 / 5) :
    ∃ w : Fin 3 → ℝ, (∀ i, (1 : ℝ) / 3 ≤ w i ∧ w i ≤ 2 / 5) ∧
      (∀ i, |u i - w i| ≤ t) ∧
      (∀ i j, w i ≠ w j → t ≤ |u i-u j|) := by
  let e := Tuple.sort u
  obtain ⟨z, hz, he, hs⟩ := ordered_centers (u ∘ e) t ht
    (Tuple.monotone_sort u) (fun i => hu (e i))
  refine ⟨z ∘ e.symm, (fun i => hz (e.symm i)), ?_, ?_⟩
  · intro i
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using he (e.symm i)
  · intro i j hij
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hs (e.symm i) (e.symm j) hij



/-- A single reversible comparison table with all three simultaneous estimates. -/
theorem three_value_conserved_comparison
    (pi : Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) (u v : Fin 3 → ℝ)
    (hp : ∀ i, 0 < pi i) (hpsum : ∑ i, pi i = 1)
    (hB : ∀ i j, 0 ≤ B i j) (hrow : ∀ i, ∑ j, B i j = 1)
    (hbal : ∀ i j, pi i * B i j = pi j * B j i)
    (hu : ∀ i, (1 : ℝ) / 3 ≤ u i ∧ u i ≤ 2 / 5)
    (hv : ∀ i, (1 : ℝ) / 3 ≤ v i ∧ v i ≤ 2 / 5)
    (t : ℝ) (ht : 0 < t) :
    ∃ (T : ConstantSuspensionSeparator.StationaryTable (Fin 3)) (w : Fin 3 → ℝ)
      (Ah : Fin 3 → Fin 3 → ℝ) (vh tauh : Fin 3 → ℝ),
      T.pi = pi ∧ Ah = (fun i j => if i = j then 1 else 0) ∧ vh = v ∧ tauh = pi ∧
      (∀ i, (1 : ℝ) / 3 ≤ w i ∧ w i ≤ 2 / 5) ∧
      (∀ i, (1 : ℝ) / 3 ≤ vh i ∧ vh i ≤ 2 / 5) ∧
      (∀ i j, 0 ≤ T.C i j) ∧ (∀ i, ∑ j, T.C i j = 1) ∧
      (∀ i j, pi i * T.C i j = pi j * T.C j i) ∧
      (∀ j, ∑ i, pi i * T.C i j = pi j) ∧
      (∀ i j, 0 < T.C i j → w i = w j) ∧
      (∑ i, pi i * |u i - w i|) ≤ t ∧
      (∑ i, pi i * ((1 / 2 : ℝ) * ∑ j, |B i j - T.C i j|)) ≤
        2 * ((1 / 2 : ℝ) * ∑ i, ∑ j, pi i * B i j * (u i - u j)^2) / t^2 ∧
      ((1 / 2 : ℝ) * ∑ i, ∑ j, pi i * T.C i j * (w i - w j)^2) = 0 := by
  classical
  obtain ⟨w, hw, he, hs⟩ := three_centers u t ht hu
  let lost (i : Fin 3) : ℝ := ∑ j, if w i = w j then 0 else B i j
  let H (i j : Fin 3) : ℝ :=
    (if w i = w j then B i j else 0) + (if i = j then lost i else 0)
  have hlost (i : Fin 3) : 0 ≤ lost i := by
    apply Finset.sum_nonneg
    intro j hj
    split_ifs
    · exact le_refl 0
    · exact hB i j
  have hnonneg (i j : Fin 3) : 0 ≤ H i j := by
    dsimp [H]
    apply add_nonneg
    · split_ifs
      · exact hB i j
      · exact le_refl 0
    · split_ifs
      · exact hlost i
      · exact le_refl 0
  have hrows (i : Fin 3) : ∑ j, H i j = 1 := by
    calc
      ∑ j, H i j = (∑ j, if w i = w j then B i j else 0) + lost i := by
        simp [H, Finset.sum_add_distrib]
      _ = ∑ j, B i j := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs <;> simp
      _ = 1 := hrow i
  have hbalance (i j : Fin 3) : pi i * H i j = pi j * H j i := by
    by_cases hij : i = j
    · subst j; rfl
    · by_cases hw : w i = w j
      · simpa only [H, if_pos hw, if_pos hw.symm, if_neg hij,
          if_neg (Ne.symm hij), add_zero] using hbal i j
      · simp [H, hij, Ne.symm hij, hw, Ne.symm hw]
  have hstationary (j : Fin 3) : ∑ i, pi i * H i j = pi j := by
    calc
      ∑ i, pi i * H i j = ∑ i, pi j * H j i :=
        Finset.sum_congr rfl (fun i _ => hbalance i j)
      _ = pi j := by rw [← Finset.mul_sum, hrows, mul_one]
  have hsupport (i j : Fin 3) (hij : 0 < H i j) : w i = w j := by
    by_contra hn
    have hne : i ≠ j := by intro h; subst j; exact hn rfl
    simp [H, hn, hne] at hij
  have htv (i : Fin 3) : (1 / 2 : ℝ) * ∑ j, |B i j - H i j| = lost i := by
    have hcoord (j : Fin 3) :
        |B i j - H i j| =
          (if w i = w j then 0 else B i j) + (if i = j then lost i else 0) := by
      by_cases hij : i = j
      · subst j
        simp [H, abs_of_nonneg (hlost i)]
      · by_cases hw : w i = w j
        · simp [H, hij, hw]
        · simp [H, hij, hw, abs_of_nonneg (hB i j)]
    simp_rw [hcoord]
    rw [Finset.sum_add_distrib]
    have hdiag : (∑ j : Fin 3, if i = j then lost i else 0) = lost i := by simp
    rw [hdiag]
    change (1 / 2 : ℝ) * (lost i + lost i) = lost i
    ring
  have hmass : (∑ i, pi i * |u i - w i|) ≤ t := by
    calc
      (∑ i, pi i * |u i - w i|) ≤ ∑ i, pi i * t :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (he i) (hp i).le
      _ = t := by rw [← Finset.sum_mul, hpsum, one_mul]
  have hcost :
      (∑ i, pi i * lost i) * t^2 ≤
        ∑ i, ∑ j, pi i * B i j * (u i - u j)^2 := by
    calc
      (∑ i, pi i * lost i) * t^2 =
          ∑ i, ∑ j, pi i * (if w i = w j then 0 else B i j) * t^2 := by
        simp only [lost, Finset.sum_mul, Finset.mul_sum]
      _ ≤ ∑ i, ∑ j, pi i * B i j * (u i - u j)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hw : w i = w j
        · simp only [if_pos hw, mul_zero, zero_mul]
          exact mul_nonneg (mul_nonneg (hp i).le (hB i j)) (sq_nonneg _)
        · simp only [if_neg hw]
          have hd := hs i j hw
          have hsq : t^2 ≤ (u i-u j)^2 := by
            have hm := mul_nonneg (sub_nonneg.mpr hd)
              (show 0 ≤ |u i-u j| + t by positivity)
            nlinarith [sq_abs (u i-u j)]
          exact mul_le_mul_of_nonneg_left hsq (mul_nonneg (hp i).le (hB i j))
  have hq :
      (∑ i, pi i * ((1 / 2 : ℝ) * ∑ j, |B i j - H i j|)) ≤
        2 * ((1 / 2 : ℝ) * ∑ i, ∑ j, pi i * B i j * (u i - u j)^2) / t^2 := by
    simp_rw [htv]
    apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
    have htwo : 2 * ((1 / 2 : ℝ) *
        ∑ i, ∑ j, pi i * B i j * (u i-u j)^2) =
        ∑ i, ∑ j, pi i * B i j * (u i-u j)^2 := by ring
    rw [htwo]
    exact hcost
  have hzero : ((1 / 2 : ℝ) * ∑ i, ∑ j, pi i * H i j * (w i - w j)^2) = 0 := by
    have hz (i j : Fin 3) : pi i * H i j * (w i-w j)^2 = 0 := by
      by_cases hh : H i j = 0
      · simp [hh]
      · have heq := hsupport i j (lt_of_le_of_ne (hnonneg i j) (Ne.symm hh))
        simp [heq]
    simp [hz]
  let T : ConstantSuspensionSeparator.StationaryTable (Fin 3) := {
    pi := pi, C := H, pi_nonneg := fun i => (hp i).le, pi_sum := hpsum,
    C_nonneg := hnonneg, C_sum := hrows, stationary := hstationary }
  exact ⟨T, w, (fun i j => if i = j then 1 else 0), v, pi,
    rfl, rfl, rfl, rfl, hw, hv, hnonneg, hrows, hbalance, hstationary,
    hsupport, hmass, hq, hzero⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ThreeValueConservedComparison
