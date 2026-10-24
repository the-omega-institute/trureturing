/- GID: D5/S3/QuantumBounds/NetworkCoherenceClassicalBound
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/NetworkCoherenceClassicalBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp classical coherence bound for mixtures of two binary product laws. -/

import D5.S3.TotalVariation.CycleSingleCutMinimax
import D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant

/-! The sharp parity coherence bound for convex mixtures of two binary product laws. -/

open scoped BigOperators

noncomputable section

namespace D5.S3.QuantumBounds.NetworkCoherenceClassicalBound

open D5.S3.TotalVariation.CycleSingleCutMinimax (Probability)
open D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy (windowLaw windowLaw_sum_eq_one)
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (occupationCount)

def parity {n : ℕ} (a : Fin n → Bool) : ℕ := occupationCount a % 2

def classicalMixture (n : ℕ) (γ : ℝ) (p q : Fin n → Bool → ℝ) :
    (Fin n → Bool) → ℝ :=
  fun a => γ * windowLaw p a + (1 - γ) * windowLaw q a

def coherenceMerit (n : ℕ) (r : (Fin n → Bool) → ℝ) : ℝ :=
  (1 / 2) * |(∑ a ∈ Finset.univ.filter (fun a => parity a = 0),
    ∑ b ∈ Finset.univ.filter (fun b => parity b = 0),
      if a ≠ b then r a * r b else 0) -
    ∑ a ∈ Finset.univ.filter (fun a => parity a = 1),
    ∑ b ∈ Finset.univ.filter (fun b => parity b = 1),
      if a ≠ b then r a * r b else 0|

def claim : Prop := ∀ n : ℕ, 2 ≤ n →
  IsGreatest {c : ℝ | ∃ γ ∈ Set.Icc (0 : ℝ) 1, ∃ p q : Fin n → Bool → ℝ,
    (∀ i, Probability (p i)) ∧ (∀ i, Probability (q i)) ∧
      c = coherenceMerit n (classicalMixture n γ p q)} (1 / 4)

private lemma off_diagonal {α : Type*} [DecidableEq α] (s : Finset α) (r : α → ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, if a ≠ b then r a * r b else 0) =
      (∑ a ∈ s, r a) ^ 2 - ∑ a ∈ s, (r a) ^ 2 := by
  have hrow (a : α) (ha : a ∈ s) :
      (∑ b ∈ s, if a ≠ b then r a * r b else 0) =
        r a * (∑ b ∈ s, r b) - (r a) ^ 2 := by
    calc
      _ = ∑ b ∈ s, (r a * r b - if b = a then (r a) ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro b _
        by_cases h : b = a
        · subst b; simp; ring
        · simp [h, Ne.symm h]
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp [ha]
  simp_rw [Finset.sum_congr rfl hrow]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

private lemma signed_sum (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    (∑ a, (-1 : ℝ) ^ (∑ i, (a i).toNat) * f a) =
      (∑ a ∈ Finset.univ.filter (fun a => parity a = 0), f a) -
      ∑ a ∈ Finset.univ.filter (fun a => parity a = 1), f a := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [neg_one_pow_eq_pow_mod_two]
  change (-1 : ℝ) ^ parity a * f a = _
  have hm : parity a < 2 := Nat.mod_lt _ (by decide)
  interval_cases parity a <;> simp

private lemma parity_total (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    (∑ a ∈ Finset.univ.filter (fun a => parity a = 0), f a) +
      (∑ a ∈ Finset.univ.filter (fun a => parity a = 1), f a) = ∑ a, f a := by
  classical
  have h (a : Fin n → Bool) : (¬ parity a = 0) ↔ parity a = 1 :=
    Nat.mod_two_not_eq_zero
  simpa only [h] using Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun a : Fin n → Bool => parity a = 0) f

private lemma parity_reduction (n : ℕ) (r : (Fin n → Bool) → ℝ)
    (hr : ∑ a, r a = 1) :
    coherenceMerit n r = (1 / 2) * |(∑ a, (-1 : ℝ) ^ (∑ i, (a i).toNat) * r a) -
      ∑ a, (-1 : ℝ) ^ (∑ i, (a i).toNat) * (r a) ^ 2| := by
  classical
  unfold coherenceMerit
  rw [off_diagonal, off_diagonal, signed_sum, signed_sum]
  have ht := parity_total n r
  rw [hr] at ht
  congr 2
  nlinarith

private lemma signed_product (n : ℕ) (w : Fin n → Bool → ℝ) :
    (∑ a : Fin n → Bool, (-1 : ℝ) ^ (∑ i, (a i).toNat) * ∏ i, w i (a i)) =
      ∏ i, (w i false - w i true) := by
  simp_rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) => (-1 : ℝ) ^ b.toNat * w i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp [sub_eq_add_neg, add_comm]

private lemma mixture_factorization (n : ℕ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (p q : Fin n → Bool → ℝ) (hp : ∀ i, Probability (p i))
    (hq : ∀ i, Probability (q i)) :
    coherenceMerit n (classicalMixture n γ p q) = γ * (1 - γ) / 2 *
      |(∏ i, (p i false - p i true)) + (∏ i, (q i false - q i true)) -
        2 * ∏ i, ((p i false - p i true + (q i false - q i true)) / 2)| := by
  classical
  have hm : (∑ a : Fin n → Bool, classicalMixture n γ p q a) = 1 := by
    unfold classicalMixture
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      windowLaw_sum_eq_one p (fun i => (hp i).2),
      windowLaw_sum_eq_one q (fun i => (hq i).2)]
    ring
  rw [parity_reduction n _ hm]
  have hT : (∑ a : Fin n → Bool, (-1 : ℝ) ^ (∑ i, (a i).toNat) * classicalMixture n γ p q a) =
      γ * (∏ i, (p i false - p i true)) +
        (1 - γ) * (∏ i, (q i false - q i true)) := by
    calc
      _ = γ * (∑ a : Fin n → Bool, (-1 : ℝ) ^ (∑ i, (a i).toNat) * ∏ i, p i (a i)) +
          (1 - γ) * (∑ a : Fin n → Bool, (-1 : ℝ) ^ (∑ i, (a i).toNat) * ∏ i, q i (a i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        unfold classicalMixture windowLaw
        ring
      _ = _ := by rw [signed_product, signed_product]
  have hp2 : (∑ a : Fin n → Bool, (-1 : ℝ) ^ (∑ i, (a i).toNat) * (∏ i, p i (a i)) ^ 2) =
      ∏ i, (p i false - p i true) := by
    simp_rw [← Finset.prod_pow]
    rw [signed_product n (fun i b => p i b ^ 2)]
    apply Finset.prod_congr rfl
    intro i _
    have hi : p i false + p i true = 1 := by simpa [add_comm] using (hp i).2
    nlinarith
  have hq2 : (∑ a : Fin n → Bool, (-1 : ℝ) ^ (∑ i, (a i).toNat) * (∏ i, q i (a i)) ^ 2) =
      ∏ i, (q i false - q i true) := by
    simp_rw [← Finset.prod_pow]
    rw [signed_product n (fun i b => q i b ^ 2)]
    apply Finset.prod_congr rfl
    intro i _
    have hi : q i false + q i true = 1 := by simpa [add_comm] using (hq i).2
    nlinarith
  have hpq : (∑ a : Fin n → Bool, (-1 : ℝ) ^ (∑ i, (a i).toNat) *
      ((∏ i, p i (a i)) * ∏ i, q i (a i))) =
      ∏ i, ((p i false - p i true + (q i false - q i true)) / 2) := by
    simp_rw [← Finset.prod_mul_distrib]
    rw [signed_product n (fun i b => p i b * q i b)]
    apply Finset.prod_congr rfl
    intro i _
    have hi : p i true = 1 - p i false := by
      have hs : p i false + p i true = 1 := by simpa [add_comm] using (hp i).2
      linarith
    have hj : q i true = 1 - q i false := by
      have hs : q i false + q i true = 1 := by simpa [add_comm] using (hq i).2
      linarith
    rw [hi, hj]
    ring
  have hU : (∑ a : Fin n → Bool, (-1 : ℝ) ^ (∑ i, (a i).toNat) * (classicalMixture n γ p q a) ^ 2) =
      γ ^ 2 * (∏ i, (p i false - p i true)) +
      (1 - γ) ^ 2 * (∏ i, (q i false - q i true)) +
      2 * γ * (1 - γ) * ∏ i, ((p i false - p i true + (q i false - q i true)) / 2) := by
    calc
      _ = γ ^ 2 * (∑ a : Fin n → Bool, (-1 : ℝ) ^ (∑ i, (a i).toNat) * (∏ i, p i (a i)) ^ 2) +
          (1 - γ) ^ 2 * (∑ a : Fin n → Bool, (-1 : ℝ) ^ (∑ i, (a i).toNat) * (∏ i, q i (a i)) ^ 2) +
          2 * γ * (1 - γ) * (∑ a : Fin n → Bool, (-1 : ℝ) ^ (∑ i, (a i).toNat) *
            ((∏ i, p i (a i)) * ∏ i, q i (a i))) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        unfold classicalMixture windowLaw
        ring
      _ = _ := by rw [hp2, hq2, hpq]
  rw [hT, hU]
  have hid (A B D : ℝ) : γ * A + (1 - γ) * B -
      (γ ^ 2 * A + (1 - γ) ^ 2 * B + 2 * γ * (1 - γ) * D) =
      γ * (1 - γ) * (A + B - 2 * D) := by ring
  rw [hid, abs_mul, abs_of_nonneg (mul_nonneg hγ.1 (sub_nonneg.mpr hγ.2))]
  ring

private lemma cube_bound (n : ℕ) (x y : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1)
    (hy : ∀ i, y i ∈ Set.Icc (-1 : ℝ) 1) :
    |(∏ i, x i) + (∏ i, y i) - 2 * ∏ i, ((x i + y i) / 2)| ≤ 2 := by
  classical
  have aux (s : Finset (Fin n)) :
      |(∏ i ∈ s, x i) + (∏ i ∈ s, y i) - 2 * ∏ i ∈ s, ((x i + y i) / 2)| ≤ 2 := by
    induction s using Finset.induction_on with
    | empty => norm_num
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
      let P := ∏ j ∈ s, x j
      let Q := ∏ j ∈ s, y j
      let D := ∏ j ∈ s, ((x j + y j) / 2)
      let F := P + Q - 2 * D
      let u := (1 + x i) / 2
      let v := (1 + y i) / 2
      have hu : 0 ≤ u := by dsimp [u]; linarith [(hx i).1]
      have hu' : 0 ≤ 1 - u := by dsimp [u]; linarith [(hx i).2]
      have hv : 0 ≤ v := by dsimp [v]; linarith [(hy i).1]
      have hv' : 0 ≤ 1 - v := by dsimp [v]; linarith [(hy i).2]
      have hP : |P| ≤ 1 := by
        dsimp [P]
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) (fun j _ => abs_le.mpr (hx j))
      have hQ : |Q| ≤ 1 := by
        dsimp [Q]
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) (fun j _ => abs_le.mpr (hy j))
      have hPQ : |P - Q| ≤ 2 := (abs_sub P Q).trans (by linarith)
      have hQP : |Q - P| ≤ 2 := by rw [abs_sub_comm]; exact hPQ
      have hF : |F| ≤ 2 := ih
      change |x i * P + y i * Q - 2 * (((x i + y i) / 2) * D)| ≤ 2
      calc
        _ = |u * v * F + u * (1 - v) * (P - Q) +
            (1 - u) * v * (Q - P) + (1 - u) * (1 - v) * (-F)| := by
          congr 1
          dsimp [u, v, F]
          ring
        _ ≤ |u * v * F| + |u * (1 - v) * (P - Q)| +
            |(1 - u) * v * (Q - P)| + |(1 - u) * (1 - v) * (-F)| := by
          calc
            _ ≤ |u * v * F + u * (1 - v) * (P - Q) +
                (1 - u) * v * (Q - P)| + |(1 - u) * (1 - v) * (-F)| := abs_add_le _ _
            _ ≤ (|u * v * F + u * (1 - v) * (P - Q)| +
                |(1 - u) * v * (Q - P)|) + |(1 - u) * (1 - v) * (-F)| := by
              gcongr
              exact abs_add_le _ _
            _ ≤ _ := by gcongr; exact abs_add_le _ _
        _ = u * v * |F| + u * (1 - v) * |P - Q| +
            (1 - u) * v * |Q - P| + (1 - u) * (1 - v) * |F| := by
          simp only [abs_mul, abs_of_nonneg hu, abs_of_nonneg hu', abs_of_nonneg hv,
            abs_of_nonneg hv', abs_neg]
        _ ≤ u * v * 2 + u * (1 - v) * 2 +
            (1 - u) * v * 2 + (1 - u) * (1 - v) * 2 := by
          gcongr
        _ = 2 := by ring
  exact aux Finset.univ

private lemma upper_bound (n : ℕ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (p q : Fin n → Bool → ℝ) (hp : ∀ i, Probability (p i))
    (hq : ∀ i, Probability (q i)) :
    coherenceMerit n (classicalMixture n γ p q) ≤ 1 / 4 := by
  rw [mixture_factorization n γ hγ p q hp hq]
  have hb := cube_bound n (fun i => p i false - p i true)
    (fun i => q i false - q i true)
    (fun i => by
      have hs : p i false + p i true = 1 := by simpa [add_comm] using (hp i).2
      constructor <;> linarith [(hp i).1 false, (hp i).1 true])
    (fun i => by
      have hs : q i false + q i true = 1 := by simpa [add_comm] using (hq i).2
      constructor <;> linarith [(hq i).1 false, (hq i).1 true])
  have hnon : 0 ≤ γ * (1 - γ) := mul_nonneg hγ.1 (sub_nonneg.mpr hγ.2)
  nlinarith [sq_nonneg (γ - 1 / 2)]

private lemma attainment (n : ℕ) (hn : 2 ≤ n) :
    ∃ γ ∈ Set.Icc (0 : ℝ) 1, ∃ p q : Fin n → Bool → ℝ,
      (∀ i, Probability (p i)) ∧ (∀ i, Probability (q i)) ∧
        (1 / 4 : ℝ) = coherenceMerit n (classicalMixture n γ p q) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  let p : Fin (k + 2) → Bool → ℝ := fun _ b => if b then 0 else 1
  let q : Fin (k + 2) → Bool → ℝ :=
    fun i b => if i.val < 2 then (if b then 1 else 0) else (if b then 0 else 1)
  have hp : ∀ i, Probability (p i) := by
    intro i
    unfold Probability
    norm_num [p, Bool.forall_bool]
  have hq : ∀ i, Probability (q i) := by
    intro i
    unfold Probability
    simp only [Bool.forall_bool, Fintype.sum_bool]
    dsimp [q]
    split_ifs <;> norm_num
  refine ⟨1 / 2, by norm_num, p, q, hp, hq, ?_⟩
  rw [mixture_factorization (k + 2) (1 / 2) (by norm_num) p q hp hq]
  have hP : (∏ i, (p i false - p i true)) = 1 := by simp [p]
  have hQ : (∏ i, (q i false - q i true)) = 1 := by
    simp only [Fin.prod_univ_succ]
    simp [q]
  have hD : (∏ i, ((p i false - p i true + (q i false - q i true)) / 2)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, by omega⟩ : Fin (k + 2)))
    norm_num [p, q]
  rw [hP, hQ, hD]
  norm_num

theorem result : claim := by
  intro n hn
  refine ⟨attainment n hn, ?_⟩
  rintro c ⟨γ, hγ, p, q, hp, hq, rfl⟩
  exact upper_bound n γ hγ p q hp hq

end D5.S3.QuantumBounds.NetworkCoherenceClassicalBound
