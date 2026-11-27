/- GID: D5/S3/Quantum/Algebra/Comparison/DiscreteLeastAction
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Comparison/DiscreteLeastAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The discrete cosine action on a finite simplex is minimized by equal steps. -/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-! The finite action bound and its equality cases through total angle pi. -/

namespace D5.S3.Quantum.Algebra.Comparison.DiscreteLeastAction

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

private theorem cos_jensen [Nonempty ι] {t : ι → ℝ} {θ : ℝ}
    (hn : ∀ i, 0 ≤ t i) (hu : ∀ i, t i ≤ π / 2) (hs : ∑ i, t i = θ) :
    (∑ i, cos (t i)) ≤ (Fintype.card ι : ℝ) * cos (θ / Fintype.card ι) ∧
      ((∑ i, cos (t i)) = (Fintype.card ι : ℝ) * cos (θ / Fintype.card ι) →
        ∀ i, t i = θ / Fintype.card ι) := by
  let n : ℝ := Fintype.card ι
  have hn' : 0 < n := by
    change (0 : ℝ) < (Fintype.card ι : ℝ)
    exact_mod_cast Fintype.card_pos (α := ι)
  have hw : ∀ i ∈ (univ : Finset ι), 0 < (fun _ : ι ↦ n⁻¹) i :=
    fun _ _ ↦ inv_pos.mpr hn'
  have hw' : ∑ i : ι, n⁻¹ = 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn'.ne'
  have ht : ∀ i ∈ (univ : Finset ι), t i ∈ Set.Icc (-(π / 2)) (π / 2) :=
    fun i _ ↦ ⟨(neg_nonpos.mpr pi_div_two_pos.le).trans (hn i), hu i⟩
  have hmean : (∑ i, n⁻¹ • t i) = θ / n := by
    simp only [smul_eq_mul, ← mul_sum, hs]
    rw [div_eq_mul_inv, mul_comm]
  have hle := strictConcaveOn_cos_Icc.concaveOn.le_map_sum
    (fun i hi ↦ (hw i hi).le) hw' ht
  change (∑ i, n⁻¹ • cos (t i)) ≤ cos (∑ i, n⁻¹ • t i) at hle
  rw [hmean] at hle
  simp only [smul_eq_mul, ← mul_sum] at hle
  refine ⟨?_, ?_⟩
  · change _ ≤ n * _
    rw [inv_mul_eq_div, div_le_iff₀ hn', mul_comm] at hle
    exact hle
  · intro heq
    have hz : cos (∑ i, n⁻¹ • t i) = ∑ i, n⁻¹ • cos (t i) := by
      change (∑ i, cos (t i)) = n * cos (θ / n) at heq
      rw [hmean]
      simp only [smul_eq_mul, ← mul_sum, heq, ← mul_assoc,
        inv_mul_cancel₀ hn'.ne', one_mul]
    intro i
    simpa only [hmean] using
      (strictConcaveOn_cos_Icc.map_sum_eq_iff hw hw' ht).mp hz i (mem_univ i)

private theorem sum_pair_add_compl [DecidableEq ι] (f : ι → ℝ) {i j : ι} (hij : i ≠ j) :
    (∑ k, f k) = (∑ k ∈ (univ : Finset ι) \ {i, j}, f k) + (f i + f j) := by
  rw [← sum_pair hij]
  exact (sum_sdiff (subset_univ _)).symm

private theorem cos_pair_improvement {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a + b ≤ π) :
    cos a + cos b ≤ 2 * cos ((a + b) / 2) ∧
      (cos a + cos b = 2 * cos ((a + b) / 2) → a = b ∨ a + b = π) := by
  rw [cos_add_cos]
  have hm : 0 ≤ cos ((a + b) / 2) :=
    cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith⟩
  refine ⟨?_, ?_⟩
  · simpa using mul_le_mul_of_nonneg_left (cos_le_one ((a - b) / 2)) (by positivity :
      0 ≤ 2 * cos ((a + b) / 2))
  · intro he
    by_contra! hne
    have hhalf : 0 < cos ((a + b) / 2) :=
      cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by
        linarith [lt_of_le_of_ne h hne.2]⟩
    have hd : 0 < |(a - b) / 2| := abs_pos.mpr (by intro he; apply hne.1; linarith)
    have hdiff : |(a - b) / 2| ≤ π := abs_le.mpr ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    have hc := cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hdiff hd
    rw [cos_zero, cos_abs] at hc
    have := mul_lt_mul_of_pos_left hc (by positivity : 0 < 2 * cos ((a + b) / 2))
    linarith

private theorem cos_bound_and_rigidity [Nonempty ι] {t : ι → ℝ} {θ : ℝ}
    (hn : ∀ i, 0 ≤ t i) (hs : ∑ i, t i = θ) (hθ : θ ≤ π) :
    (∑ i, cos (t i)) ≤ (Fintype.card ι : ℝ) * cos (θ / Fintype.card ι) ∧
      ((∑ i, cos (t i)) = (Fintype.card ι : ℝ) * cos (θ / Fintype.card ι) →
        (∀ i, t i = θ / Fintype.card ι) ∨ Fintype.card ι = 2 ∧ θ = π) := by
  classical
  by_cases hsmall : ∀ i, t i ≤ π / 2
  · obtain ⟨hle, he⟩ := cos_jensen hn hsmall hs
    exact ⟨hle, fun h ↦ Or.inl (he h)⟩
  push Not at hsmall
  obtain ⟨i, hi⟩ := hsmall
  by_cases hsingle : Fintype.card ι = 1
  · obtain ⟨j, hj⟩ := Fintype.card_eq_one_iff.mp hsingle
    have ht : ∀ k, t k = θ := by
      have hsum : (∑ k, t k) = t j := by
        calc
          (∑ k, t k) = ∑ _ : ι, t j := sum_congr rfl (fun k _ ↦ congrArg t (hj k))
          _ = t j := by rw [sum_const, card_univ, hsingle, one_nsmul]
      intro k
      rw [hj k, ← hsum, hs]
    simp [ht, hsingle]
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp
    (lt_of_le_of_ne (Nat.succ_le_of_lt Fintype.card_pos) (Ne.symm hsingle))
  obtain ⟨j, hj⟩ := exists_ne i
  have hij : i ≠ j := Ne.symm hj
  have hpair (k : ι) (hk : i ≠ k) : t i + t k ≤ θ := by
    rw [← hs, sum_pair_add_compl t hk]
    exact le_add_of_nonneg_left (sum_nonneg fun l _ ↦ hn l)
  have hother (k : ι) (hk : i ≠ k) : t k < π / 2 := by linarith [hpair k hk]
  let m := (t i + t j) / 2
  let u (k : ι) := if k = i ∨ k = j then m else t k
  have hui : u i = m := by simp [u]
  have huj : u j = m := by simp [u]
  have huout {k : ι} (hk : k ∈ (univ : Finset ι) \ {i, j}) : u k = t k := by
    have hk' : ¬ (k = i ∨ k = j) := by simpa using hk
    simp [u, hk']
  have hsum_u (f : ℝ → ℝ) :
      (∑ k, f (u k)) = (∑ k ∈ (univ : Finset ι) \ {i, j}, f (t k)) + (f m + f m) := by
    rw [sum_pair_add_compl (fun k ↦ f (u k)) hij, hui, huj]
    congr 1
    exact sum_congr rfl (fun k hk ↦ congrArg f (huout hk))
  have huθ : ∑ k, u k = θ := by
    change (∑ k, id (u k)) = θ
    rw [← hs, hsum_u id, sum_pair_add_compl t hij]
    simp only [id_eq]
    dsimp [m]
    ring
  have hmu : m ≤ π / 2 := by dsimp [m]; linarith [hpair j hij]
  have hml : 0 ≤ m := by dsimp [m]; linarith only [hn i, hn j]
  have ⟨hju, hej⟩ := cos_jensen (t := u) (fun k ↦ by
    by_cases hk : k = i ∨ k = j <;> simp [u, hk, hml, hn k])
    (fun k ↦ by
      by_cases hk : k = i ∨ k = j
      · simpa [u, hk] using hmu
      · simpa [u, hk] using (hother k (Ne.symm (not_or.mp hk).1)).le) huθ
  have ⟨himp, heimp⟩ := cos_pair_improvement (hn i) (hn j) ((hpair j hij).trans hθ)
  have hle : (∑ k, cos (t k)) ≤ ∑ k, cos (u k) := by
    rw [sum_pair_add_compl (fun k ↦ cos (t k)) hij, hsum_u cos]
    linarith
  refine ⟨hle.trans hju, ?_⟩
  intro he
  have heu : (∑ k, cos (u k)) = (Fintype.card ι : ℝ) * cos (θ / Fintype.card ι) :=
    le_antisymm hju (he ▸ hle)
  have he_pair : cos (t i) + cos (t j) = 2 * cos m := by
    have hc := he.trans heu.symm
    rw [sum_pair_add_compl (fun k ↦ cos (t k)) hij, hsum_u cos] at hc
    linarith
  have hp : t i + t j = π :=
    (heimp he_pair).resolve_left (by linarith [hother j hij])
  have huniv : (univ : Finset ι) = {i, j} := by
    ext k
    simp only [mem_univ, true_iff, mem_insert, mem_singleton]
    by_contra hk
    have hmem : k ∈ (univ : Finset ι) \ {i, j} := by simpa using hk
    have hk_eq : t k = m := (huout hmem).symm.trans ((hej heu k).trans
      ((hej heu i).symm.trans hui))
    have hk_le : t k ≤ ∑ l ∈ (univ : Finset ι) \ {i, j}, t l :=
      single_le_sum (fun l _ ↦ hn l) hmem
    have hsum := (sum_pair_add_compl t hij).symm.trans hs
    dsimp [m] at hk_eq
    linarith [pi_pos]
  right
  refine ⟨?_, le_antisymm hθ (hp ▸ hpair j hij)⟩
  rw [← card_univ, huniv, card_pair hij]

/-- Equal steps minimize the cosine action up to total angle π. At total angle π
with two steps every split has the same action. -/
theorem sum_one_sub_cos_least_action (t : ι → ℝ) (θ : ℝ)
    (hn : ∀ i, 0 ≤ t i) (hs : ∑ i, t i = θ) (hθ : θ ≤ π) :
    (Fintype.card ι : ℝ) * (1 - cos (θ / Fintype.card ι)) ≤ ∑ i, (1 - cos (t i)) ∧
      ((∑ i, (1 - cos (t i))) = (Fintype.card ι : ℝ) * (1 - cos (θ / Fintype.card ι)) ↔
        (∀ i, t i = θ / Fintype.card ι) ∨ Fintype.card ι = 2 ∧ θ = π) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => simp [Fintype.card_eq_zero_iff.mpr h]
  | inr h =>
    obtain ⟨hle, he⟩ := cos_bound_and_rigidity hn hs hθ
    have hsum_one : (∑ _ : ι, (1 : ℝ)) = Fintype.card ι := by simp
    simp only [sum_sub_distrib, hsum_one, mul_sub, mul_one]
    refine ⟨sub_le_sub_left hle _, fun h ↦ he (by linarith), ?_⟩
    rintro (ht | ⟨hn', rfl⟩)
    · simp [ht]
    · obtain ⟨i, j, hij, huv⟩ := Finset.card_eq_two.mp (show (univ : Finset ι).card = 2 by simpa)
      have hsum : t i + t j = π := by rwa [huv, sum_pair hij] at hs
      have hcos : cos (t j) = -cos (t i) := by
        rw [show t j = π - t i by linarith, cos_pi_sub]
      rw [huv, sum_pair hij, hcos, hn']
      norm_num [cos_pi_div_two]

end D5.S3.Quantum.Algebra.Comparison.DiscreteLeastAction
