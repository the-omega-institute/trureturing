/- GID: D5/S3/Quantum/QuantumChannels/MarkovianDivisibilityMaximalIndex
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/MarkovianDivisibilityMaximalIndex
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The maximal arithmetic-geometric entry index is 2d-5 for d >= 5, and 2 for d=3. -/

import Mathlib.Algebra.BigOperators.Field
import D5.S3.Constants.PowerMeanKernel
import D5.S3.TotalVariation.CycleSingleCutMinimax

/-! The two mean matrices are optimized over independent sets of ordered positions. -/

noncomputable section
open scoped BigOperators
open D5.S3.TotalVariation.CycleSingleCutMinimax (Probability)
namespace D5.S3.Quantum.QuantumChannels.MarkovianDivisibilityMaximalIndex

/-- The arithmetic-mean matrix of the source probability vector. -/
def arith {d : ℕ} (p : Fin d → ℝ) (ij : Fin d × Fin d) : ℝ :=
  D5.S3.Constants.PowerMeanKernel.meanOne (p ij.1) (p ij.2)

/-- The geometric-mean matrix, counting both ordered positions. -/
def geom {d : ℕ} (p : Fin d → ℝ) (ij : Fin d × Fin d) : ℝ :=
  D5.S3.Constants.PowerMeanKernel.meanZero (p ij.1) (p ij.2)

/-- The sum of the `m` largest entries, with multiplicity. This maximum over position
sets equals the sorted-prefix sum for every real-valued `f`; it includes all entries
when `m ≥ d*d`. -/
def topSum {d : ℕ} (f : Fin d × Fin d → ℝ) (m : ℕ) : ℝ :=
  (Finset.univ.powersetCard (min m (d * d))).sup'
    (Finset.powersetCard_nonempty.mpr (by simpa using Nat.min_le_right m (d * d)))
    (fun s => ∑ ij ∈ s, f ij)

/-- Indices for which the source inequality holds for every probability vector. -/
def admissibleIndices (d : ℕ) : Set ℕ :=
  {m | ∀ p : Fin d → ℝ, Probability p → topSum (arith p) m + topSum (geom p) m ≤ d}

private lemma top_sum_le {d m : ℕ} (f : Fin d × Fin d → ℝ) (a : ℝ)
    (h : ∀ s : Finset (Fin d × Fin d), s.card = min m (d * d) →
      ∑ ij ∈ s, f ij ≤ a) : topSum f m ≤ a := by
  classical
  unfold topSum
  apply Finset.sup'_le
  intro s hs
  exact h s (Finset.mem_powersetCard.mp hs).2

private lemma sum_le_top_sum {d m : ℕ} (f : Fin d × Fin d → ℝ)
    (s : Finset (Fin d × Fin d)) (hs : s.card = min m (d * d)) :
    ∑ ij ∈ s, f ij ≤ topSum f m := by
  classical
  unfold topSum
  exact Finset.le_sup' (fun s : Finset (Fin d × Fin d) => ∑ ij ∈ s, f ij)
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hs⟩)

private lemma top_sum_attained {d m : ℕ} (f : Fin d × Fin d → ℝ) :
    ∃ s : Finset (Fin d × Fin d), s.card = min m (d * d) ∧
      topSum f m = ∑ ij ∈ s, f ij := by
  classical
  unfold topSum
  obtain ⟨s, hs, he⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.univ.powersetCard (min m (d * d)))
    (Finset.powersetCard_nonempty.mpr (by simp))
    (fun s : Finset (Fin d × Fin d) => ∑ ij ∈ s, f ij)
  exact ⟨s, (Finset.mem_powersetCard.mp hs).2, he⟩

private lemma top_sum_mono {d : ℕ} (f : Fin d × Fin d → ℝ) (hf : ∀ ij, 0 ≤ f ij) :
    Monotone (topSum f) := by
  classical
  intro a b hab
  apply top_sum_le
  intro s hs
  obtain ⟨t, hst, _, ht⟩ := Finset.exists_subsuperset_card_eq (n := min b (d * d))
    (Finset.subset_univ s) (hs.trans_le (min_le_min_right (d * d) hab))
    (by simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      using Nat.min_le_right b (d * d))
  exact (Finset.sum_le_sum_of_subset_of_nonneg hst (fun ij _ _ => hf ij)).trans
    (sum_le_top_sum f t ht)

private lemma probability_le_one {d : ℕ} {p : Fin d → ℝ} (hp : Probability p)
    (i : Fin d) : p i ≤ 1 := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) =>
    hp.1 j) (Finset.mem_univ i)
  exact h.trans_eq hp.2

private lemma probability_pair_le_one {d : ℕ} {p : Fin d → ℝ}
    (hp : Probability p) {i j : Fin d} (hij : i ≠ j) : p i + p j ≤ 1 := by
  classical
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ ({i, j} : Finset (Fin d))) (fun a _ _ => hp.1 a)
  simpa only [Finset.sum_pair hij, hp.2] using h

private lemma incidence_bound {d : ℕ} (s : Finset (Fin d × Fin d))
    (q : Finset (Fin d)) :
    (∑ ab ∈ s, ((if ab.1 ∈ q then (1 : ℝ) else 0) +
      (if ab.2 ∈ q then (1 : ℝ) else 0))) ≤ s.card + (q.card : ℝ) ^ 2 := by
  classical
  have hpoint (ab : Fin d × Fin d) :
      (if ab.1 ∈ q then (1 : ℝ) else 0) + (if ab.2 ∈ q then 1 else 0) ≤
        1 + if ab ∈ q ×ˢ q then 1 else 0 := by
    by_cases ha : ab.1 ∈ q <;> by_cases hb : ab.2 ∈ q <;>
      simp only [Finset.mem_product, ha, hb, and_self, ite_true, ite_false] <;> norm_num
  have hr : (∑ ab : Fin d × Fin d, if ab ∈ q ×ˢ q then (1 : ℝ) else 0) =
      (q.card : ℝ) ^ 2 := by
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_product, Nat.cast_mul, pow_two]
  calc
    _ ≤ ∑ ab ∈ s, (1 + if ab ∈ q ×ˢ q then (1 : ℝ) else 0) :=
      Finset.sum_le_sum (fun ab _ => hpoint ab)
    _ = s.card + ∑ ab ∈ s, if ab ∈ q ×ˢ q then (1 : ℝ) else 0 := by
      rw [Finset.sum_add_distrib]; simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ s.card + ∑ ab : Fin d × Fin d, if ab ∈ q ×ˢ q then (1 : ℝ) else 0 := by
      apply add_le_add le_rfl
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun ab _ _ => by split_ifs <;> norm_num)
    _ = _ := by rw [hr]

private lemma arithmetic_coefficients {d : ℕ} (s : Finset (Fin d × Fin d))
    (p : Fin d → ℝ) :
    ∃ c : Fin d → ℝ,
      (∑ ab ∈ s, arith p ab) = ∑ i, c i * p i ∧
      (∀ i, c i ≤ ((s.card : ℝ) + 1) / 2) ∧
      (∀ i j, i ≠ j → c i + c j ≤ (s.card : ℝ) / 2 + 2) := by
  classical
  let c : Fin d → ℝ := fun i =>
    (∑ ab ∈ s, ((if ab.1 = i then (1 : ℝ) else 0) +
      (if ab.2 = i then (1 : ℝ) else 0))) / 2
  refine ⟨c, ?_, ?_, ?_⟩
  · dsimp only [c]
    simp only [div_mul_eq_mul_div, Finset.sum_mul, ← Finset.sum_div]
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ab hab
    dsimp only [arith, D5.S3.Constants.PowerMeanKernel.meanOne]
    congr 1
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · intro i
    have h := incidence_bound s {i}
    simp only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one, one_pow] at h
    dsimp only [c]
    linarith
  · intro i j hij
    have h := incidence_bound s {i, j}
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.card_pair hij,
      Nat.cast_ofNat] at h
    have hpoint (ab : Fin d × Fin d) :
        ((if ab.1 = i then (1 : ℝ) else 0) + (if ab.2 = i then 1 else 0)) +
          ((if ab.1 = j then 1 else 0) + (if ab.2 = j then 1 else 0)) =
        (if ab.1 = i ∨ ab.1 = j then 1 else 0) +
          (if ab.2 = i ∨ ab.2 = j then 1 else 0) := by
      by_cases hai : ab.1 = i <;> by_cases haj : ab.1 = j <;>
        by_cases hbi : ab.2 = i <;> by_cases hbj : ab.2 = j <;> simp_all
    have he := Finset.sum_congr (s₁ := s) rfl (fun ab _ => hpoint ab)
    rw [Finset.sum_add_distrib] at he
    dsimp only [c]
    linarith

private lemma probability_weighted_bound {d : ℕ} {p : Fin d → ℝ}
    (hp : Probability p) (c : Fin d → ℝ) (u v t : ℝ)
    (hu : ∀ i, c i ≤ u) (hv : ∀ i j, i ≠ j → c i + c j ≤ v)
    (ht : 1 / 2 ≤ t) (hmax : ∀ i, p i ≤ t) (hvu : v ≤ 2 * u) :
    (∑ i, c i * p i) ≤ (2 * t - 1) * u + (1 - t) * v := by
  classical
  by_cases hall : ∀ i, c i ≤ v / 2
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_right (hall i) (hp.1 i))
    rw [← Finset.mul_sum, hp.2, mul_one] at hh
    nlinarith
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    have hh : (∑ i, c i * p i) ≤ (v - c j) + (2 * c j - v) * p j := by
      calc
        _ ≤ ∑ i, ((v - c j) * p i + if i = j then (2 * c j - v) * p j else 0) := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hij : i = j
          · subst i; rw [ite_eq_left rfl]; nlinarith
          · rw [ite_eq_right hij, add_zero]
            exact mul_le_mul_of_nonneg_right (by linarith [hv i j hij]) (hp.1 i)
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, mul_one]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have htj := mul_le_mul_of_nonneg_left (hmax j) (by linarith : 0 ≤ 2 * c j - v)
    have htu := mul_le_mul_of_nonneg_left (hu j) (by linarith : 0 ≤ 2 * t - 1)
    nlinarith

private lemma geometric_square_sum {d : ℕ} {p : Fin d → ℝ} (hp : Probability p) :
    (∑ ab : Fin d × Fin d, (geom p ab) ^ 2) = 1 := by
  have hpoint (ab : Fin d × Fin d) : (geom p ab) ^ 2 = p ab.1 * p ab.2 := by
    dsimp only [geom, D5.S3.Constants.PowerMeanKernel.meanZero]
    exact Real.sq_sqrt (mul_nonneg (hp.1 _) (hp.1 _))
  simp_rw [hpoint]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hp.2, mul_one]
  exact hp.2

private lemma geometric_coarse_bound {d : ℕ} {p : Fin d → ℝ} (hp : Probability p)
    (s : Finset (Fin d × Fin d)) : (∑ ab ∈ s, geom p ab) ≤ Real.sqrt s.card := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s (fun _ => 1) (geom p)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hh := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun ab _ _ => sq_nonneg (geom p ab))
  rw [geometric_square_sum hp] at hh
  have hs := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_one] at hs
  nlinarith [Real.sqrt_nonneg (s.card : ℝ)]

private lemma selection_with_center {d : ℕ} (g : Fin d × Fin d → ℝ)
    (s : Finset (Fin d × Fin d)) (hs : s.Nonempty) (a : Fin d × Fin d)
    (hmax : ∀ b, g b ≤ g a) :
    ∃ t : Finset (Fin d × Fin d), t.card = s.card ∧ a ∈ t ∧
      (∑ b ∈ s, g b) ≤ ∑ b ∈ t, g b := by
  classical
  by_cases ha : a ∈ s
  · exact ⟨s, rfl, ha, le_rfl⟩
  obtain ⟨b, hb⟩ := hs
  have hae : a ∉ s.erase b := fun h => ha (Finset.mem_of_mem_erase h)
  refine ⟨insert a (s.erase b), ?_, Finset.mem_insert_self _ _, ?_⟩
  · rw [Finset.card_insert_of_notMem hae, Finset.card_erase_of_mem hb]
    have := Finset.card_pos.mpr ⟨b, hb⟩
    omega
  · rw [Finset.sum_insert hae]
    have hh := Finset.sum_erase_add s g hb
    linarith [hmax b]

private lemma geometric_refined_bound {d : ℕ} {p : Fin d → ℝ} (hp : Probability p)
    (i : Fin d) (hi : ∀ j, p j ≤ p i) (s : Finset (Fin d × Fin d))
    (hs : s.Nonempty) :
    (∑ ab ∈ s, geom p ab) ≤ p i + Real.sqrt (s.card - 1 : ℕ) *
      Real.sqrt (1 - (p i) ^ 2) := by
  classical
  have hdiag : geom p (i, i) = p i := by
    dsimp only [geom, D5.S3.Constants.PowerMeanKernel.meanZero]
    exact Real.sqrt_mul_self (hp.1 i)
  have hmax (ab : Fin d × Fin d) : geom p ab ≤ geom p (i, i) := by
    dsimp only [geom, D5.S3.Constants.PowerMeanKernel.meanZero]
    apply Real.sqrt_le_sqrt
    exact mul_le_mul (hi ab.1) (hi ab.2) (hp.1 _) (hp.1 _)
  obtain ⟨t, ht, hai, hh⟩ := selection_with_center (geom p) s hs (i, i) hmax
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (t.erase (i, i)) (fun _ => 1) (geom p)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_erase_of_mem hai, ht] at hcs
  have hsq : (∑ ab ∈ t.erase (i, i), (geom p ab) ^ 2) ≤ 1 - (p i) ^ 2 := by
    have hsub : t.erase (i, i) ⊆ Finset.univ.erase (i, i) :=
      Finset.erase_subset_erase _ (Finset.subset_univ t)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun ab _ _ => sq_nonneg (geom p ab))
    have he := Finset.sum_erase_add Finset.univ (fun ab => (geom p ab) ^ 2)
      (Finset.mem_univ (i, i))
    rw [geometric_square_sum hp, hdiag] at he
    linarith
  have hroot := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq)
    (Real.sqrt_nonneg (s.card - 1 : ℕ))
  have he := Finset.sum_erase_add t (geom p) hai
  rw [hdiag] at he
  linarith

private lemma selected_mean_bound {d : ℕ} (hd : 5 ≤ d) (p : Fin d → ℝ)
    (hp : Probability p) (s t : Finset (Fin d × Fin d))
    (hs : s.card = 2 * d - 5) (ht : t.card = 2 * d - 5) :
    (∑ ab ∈ s, arith p ab) + (∑ ab ∈ t, geom p ab) ≤ d := by
  classical
  have hdd : (5 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨c, he, hu, hv⟩ := arithmetic_coefficients s p
  have hm : ((2 * d - 5 : ℕ) : ℝ) = 2 * (d : ℝ) - 5 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num
  rw [hs, hm] at hu hv
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ p
    (by exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)
  have hmax (j : Fin d) : p j ≤ p i := hi j (Finset.mem_univ j)
  by_cases hsmall : p i ≤ 1 / 2
  · have ha := probability_weighted_bound hp c (((2 * d - 5 : ℕ) + 1 : ℝ) / 2)
      (((2 * d - 5 : ℕ) : ℝ) / 2 + 2) (1 / 2)
      (by rw [hm]; exact hu) (by rw [hm]; exact hv) le_rfl
      (fun j => (hmax j).trans hsmall) (by rw [hm]; nlinarith)
    have hg := geometric_coarse_bound hp t
    rw [hm] at ha
    rw [ht, hm] at hg
    rw [he]
    have hr : Real.sqrt (2 * (d : ℝ) - 5) ≤ (d : ℝ) / 2 - 1 / 4 := by
      have hdd : (5 : ℝ) ≤ d := by exact_mod_cast hd
      have hh := Real.sq_sqrt (show 0 ≤ 2 * (d : ℝ) - 5 by linarith)
      nlinarith [Real.sqrt_nonneg (2 * (d : ℝ) - 5), sq_nonneg ((d : ℝ) - 9 / 2)]
    linarith
  · have hlarge : 1 / 2 ≤ p i := le_of_lt (lt_of_not_ge hsmall)
    have ha := probability_weighted_bound hp c (((2 * d - 5 : ℕ) + 1 : ℝ) / 2)
      (((2 * d - 5 : ℕ) : ℝ) / 2 + 2) (p i)
      (by rw [hm]; exact hu) (by rw [hm]; exact hv) hlarge hmax
      (by rw [hm]; nlinarith)
    have hg := geometric_refined_bound hp i hmax t
      (Finset.card_pos.mp (by rw [ht]; omega))
    have hmc : ((t.card - 1 : ℕ) : ℝ) = 2 * (d : ℝ) - 6 := by
      rw [ht, Nat.cast_sub (by omega), hm]; norm_num <;> ring
    rw [hm] at ha
    rw [hmc] at hg
    rw [he]
    have hdd : (5 : ℝ) ≤ d := by exact_mod_cast hd
    have hpi := probability_le_one hp i
    have hs0 : 0 ≤ 1 - (p i) ^ 2 := by nlinarith [hp.1 i]
    have hb := Real.sq_sqrt (show 0 ≤ 2 * (d : ℝ) - 6 by linarith)
    have hc := Real.sq_sqrt hs0
    have hcs : (((d : ℝ) - 5 / 2) * p i +
        Real.sqrt (2 * (d : ℝ) - 6) * Real.sqrt (1 - (p i) ^ 2)) ^ 2 ≤
        ((d : ℝ) - 5 / 2) ^ 2 + (2 * (d : ℝ) - 6) := by
      nlinarith [sq_nonneg (((d : ℝ) - 5 / 2) * Real.sqrt (1 - (p i) ^ 2) -
        Real.sqrt (2 * (d : ℝ) - 6) * p i)]
    have hlin : ((d : ℝ) - 5 / 2) * p i +
        Real.sqrt (2 * (d : ℝ) - 6) * Real.sqrt (1 - (p i) ^ 2) ≤ (d : ℝ) - 3 / 2 := by
      nlinarith
    linarith

private lemma main_bound {d : ℕ} (hd : 5 ≤ d) (p : Fin d → ℝ)
    (hp : Probability p) :
    topSum (arith p) (2 * d - 5) + topSum (geom p) (2 * d - 5) ≤ d := by
  obtain ⟨s, hs, he⟩ := top_sum_attained (arith p) (m := 2 * d - 5)
  obtain ⟨t, ht, hf⟩ := top_sum_attained (geom p) (m := 2 * d - 5)
  have hm : min (2 * d - 5) (d * d) = 2 * d - 5 := by
    apply Nat.min_eq_left
    have : 2 * d ≤ d * d := by nlinarith
    omega
  rw [hm] at hs ht
  rw [he, hf]
  exact selected_mean_bound hd p hp s t hs ht

private lemma star_card_sum {d : ℕ} (j : Finset (Fin d)) (o : Fin d) (ho : o ∉ j) :
    let c := insert (o, o) (({o} ×ˢ j) ∪ (j ×ˢ {o}))
    c.card = 2 * j.card + 1 ∧
      ∀ g : Fin d × Fin d → ℝ,
        (∑ ab ∈ c, g ab) = g (o, o) + ∑ a ∈ j, (g (o, a) + g (a, o)) := by
  classical
  have hdj : Disjoint ({o} ×ˢ j) (j ×ˢ {o}) := by
    apply Finset.disjoint_left.mpr
    intro ab ha hb
    have ha := Finset.mem_product.mp ha
    have hb := Finset.mem_product.mp hb
    exact ho ((Finset.mem_singleton.mp ha.1) ▸ hb.1)
  have hdiag : (o, o) ∉ ({o} ×ˢ j) ∪ (j ×ˢ {o}) := by
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_singleton, ho,
      and_false, false_and, or_self, not_false_eq_true]
  constructor
  · rw [Finset.card_insert_of_notMem hdiag, Finset.card_union_of_disjoint hdj,
      Finset.card_product, Finset.card_product, Finset.card_singleton]
    omega
  · intro g
    rw [Finset.sum_insert hdiag, Finset.sum_union hdj, Finset.sum_product,
      Finset.sum_product]
    simp only [Finset.sum_singleton]
    rw [Finset.sum_add_distrib]

private lemma failure_next {d : ℕ} (hd : 5 ≤ d) :
    ∃ p : Fin d → ℝ, Probability p ∧
      (d : ℝ) < topSum (arith p) (2 * d - 4) + topSum (geom p) (2 * d - 4) := by
  classical
  let o : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  let z : Fin d := ⟨d - 2, by omega⟩
  let q : Finset (Fin d) := Finset.Ioo o z
  have hq : q.card = d - 3 := by
    dsimp only [q]
    rw [Fin.card_Ioo]
    dsimp only [o, z]
    omega
  have ho : o ∉ q := by simp only [q, Finset.mem_Ioo, lt_self_iff_false, false_and,
    not_false_eq_true]
  have hz : z ∉ q := by simp only [q, Finset.mem_Ioo, lt_self_iff_false, and_false,
    not_false_eq_true]
  have hj : j ∈ q := by
    simp only [q, Finset.mem_Ioo, Fin.lt_def]
    dsimp only [o, j, z]
    constructor <;> omega
  have hjo : j ≠ o := by intro h; exact ho (h ▸ hj)
  have hzo : z ≠ o := by
    intro h
    have hh := congrArg Fin.val h
    dsimp only [z, o] at hh
    omega
  let r : ℝ := (d : ℝ) - 2
  let k : ℝ := (d : ℝ) - 3
  let n : ℝ := r ^ 2 + k
  have hdd : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hr : 0 < r := by dsimp only [r]; linarith
  have hn : 0 < n := by dsimp only [n, k]; nlinarith [sq_nonneg r]
  have hk : ((d - 3 : ℕ) : ℝ) = k := by
    dsimp only [k]
    rw [Nat.cast_sub (by omega)]; norm_num
  let p : Fin d → ℝ := fun a =>
    (if a = o then r ^ 2 / n else 0) + (if a ∈ q then 1 / n else 0)
  have hpo : p o = r ^ 2 / n := by simp only [p, ite_true, ite_eq_right ho, add_zero]
  have hpq (a : Fin d) (ha : a ∈ q) : p a = 1 / n := by
    have hao : a ≠ o := by intro h; exact ho (h ▸ ha)
    simp only [p, ite_eq_right hao, ite_eq_left ha, zero_add]
  have hpz : p z = 0 := by simp only [p, ite_eq_right hzo, ite_eq_right hz, add_zero]
  have hp : Probability p := by
    constructor
    · intro a
      dsimp only [p]
      split_ifs <;> positivity
    · dsimp only [p]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_ite,
        Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul, hq, hk]
      field_simp [ne_of_gt hn] <;> dsimp only [n] <;> ring
  let c := insert (o, o) (({o} ×ˢ q) ∪ (q ×ˢ {o}))
  have hc := star_card_sum q o ho
  have hzc : (o, z) ∉ c := by
    simp only [c, Finset.mem_insert, Prod.mk.injEq, Finset.mem_union,
      Finset.mem_product, Finset.mem_singleton, hz, ho, hzo,
      and_false, or_self, not_false_eq_true]
  have hjc : (j, j) ∉ c := by
    simp only [c, Finset.mem_insert, Prod.mk.injEq, Finset.mem_union,
      Finset.mem_product, Finset.mem_singleton, hjo, false_and, and_false,
      or_self, not_false_eq_true]
  have hcard (a : Fin d × Fin d) (ha : a ∉ c) :
      (insert a c).card = min (2 * d - 4) (d * d) := by
    rw [Finset.card_insert_of_notMem ha, hc.1, hq]
    have hdim : 2 * d ≤ d * d := by nlinarith
    rw [Nat.min_eq_left (by omega)]
    omega
  have hacross (a : Fin d) (ha : a ∈ q) :
      arith p (o, a) + arith p (a, o) = (r ^ 2 + 1) / n := by
    dsimp only [arith, D5.S3.Constants.PowerMeanKernel.meanOne]
    rw [hpo, hpq a ha]
    ring
  have hgcross (a : Fin d) (ha : a ∈ q) :
      geom p (o, a) + geom p (a, o) = 2 * r / n := by
    have hsqrt : Real.sqrt ((r ^ 2 / n) * (1 / n)) = r / n := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
      field_simp <;> ring
    dsimp only [geom, D5.S3.Constants.PowerMeanKernel.meanZero]
    rw [hpo, hpq a ha, hsqrt, mul_comm (1 / n), hsqrt]
    ring
  have ha := sum_le_top_sum (arith p) (insert (o, z) c) (hcard _ hzc)
  have hg := sum_le_top_sum (geom p) (insert (j, j) c) (hcard _ hjc)
  have hea : (∑ ab ∈ insert (o, z) c, arith p ab) =
      r ^ 2 / (2 * n) + r ^ 2 / n + k * ((r ^ 2 + 1) / n) := by
    rw [Finset.sum_insert hzc, hc.2 (arith p)]
    have hh := Finset.sum_congr (s₁ := q) rfl (fun a ha => hacross a ha)
    rw [hh, Finset.sum_const, nsmul_eq_mul, hq, hk]
    dsimp only [arith, D5.S3.Constants.PowerMeanKernel.meanOne]
    rw [hpo, hpz]
    ring
  have heg : (∑ ab ∈ insert (j, j) c, geom p ab) =
      1 / n + r ^ 2 / n + k * (2 * r / n) := by
    rw [Finset.sum_insert hjc, hc.2 (geom p)]
    have hh := Finset.sum_congr (s₁ := q) rfl (fun a ha => hgcross a ha)
    rw [hh, Finset.sum_const, nsmul_eq_mul, hq, hk]
    dsimp only [geom, D5.S3.Constants.PowerMeanKernel.meanZero]
    rw [Real.sqrt_mul_self (hp.1 j), Real.sqrt_mul_self (hp.1 o), hpq j hj, hpo]
    ring
  have hidentity : r ^ 2 / (2 * n) + r ^ 2 / n + k * ((r ^ 2 + 1) / n) +
      (1 / n + r ^ 2 / n + k * (2 * r / n)) =
      (d : ℝ) + ((d : ℝ) - 4) ^ 2 / (2 * n) := by
    field_simp [ne_of_gt hn]
    dsimp only [n, r, k]
    ring
  rw [hea] at ha
  rw [heg] at hg
  have hpos : 0 < ((d : ℝ) - 4) ^ 2 / (2 * n) :=
    div_pos (sq_pos_of_pos (by linarith)) (by positivity)
  exact ⟨p, hp, by linarith⟩

private lemma geom_le_arith {d : ℕ} {p : Fin d → ℝ} (hp : Probability p)
    (ab : Fin d × Fin d) : geom p ab ≤ arith p ab := by
  rw [geom.eq_1, arith.eq_1]
  unfold D5.S3.Constants.PowerMeanKernel.meanZero
  unfold D5.S3.Constants.PowerMeanKernel.meanOne
  have hs := Real.sq_sqrt (mul_nonneg (hp.1 ab.1) (hp.1 ab.2))
  have hn := Real.sqrt_nonneg (p ab.1 * p ab.2)
  nlinarith [sq_nonneg (p ab.1 - p ab.2), hp.1 ab.1, hp.1 ab.2]

private lemma arithmetic_two_bound {d : ℕ} {p : Fin d → ℝ} (hp : Probability p)
    (s : Finset (Fin d × Fin d)) (hs : s.card = 2) :
    (∑ ab ∈ s, arith p ab) ≤ 3 / 2 := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
  rw [Finset.sum_pair hab]
  have hone (ab : Fin d × Fin d) : arith p ab ≤ 1 := by
    dsimp only [arith, D5.S3.Constants.PowerMeanKernel.meanOne]
    linarith [probability_le_one hp ab.1, probability_le_one hp ab.2]
  have hoff (ab : Fin d × Fin d) (h : ab.1 ≠ ab.2) : arith p ab ≤ 1 / 2 := by
    dsimp only [arith, D5.S3.Constants.PowerMeanKernel.meanOne]
    linarith [probability_pair_le_one hp h]
  by_cases ha : a.1 = a.2
  · by_cases hb : b.1 = b.2
    · have hij : a.1 ≠ b.1 := by
        intro hh
        apply hab
        exact Prod.ext hh (ha.symm.trans (hh.trans hb))
      have hh := probability_pair_le_one hp hij
      dsimp only [arith, D5.S3.Constants.PowerMeanKernel.meanOne]
      rw [ha, hb] at *
      linarith
    · linarith [hone a, hoff b hb]
  · linarith [hoff a ha, hone b]

private lemma three_bound (p : Fin 3 → ℝ) (hp : Probability p) :
    topSum (arith p) 2 + topSum (geom p) 2 ≤ 3 := by
  have ha : topSum (arith p) 2 ≤ 3 / 2 := by
    apply top_sum_le
    intro s hs
    apply arithmetic_two_bound hp s
    norm_num at hs
    exact hs
  have hg : topSum (geom p) 2 ≤ 3 / 2 := by
    apply top_sum_le
    intro s hs
    have hs : s.card = 2 := by norm_num at hs; exact hs
    exact (Finset.sum_le_sum (fun ab _ => geom_le_arith hp ab)).trans
      (arithmetic_two_bound hp s hs)
  linarith

private lemma three_failure :
    ∃ p : Fin 3 → ℝ, Probability p ∧
      3 < topSum (arith p) 3 + topSum (geom p) 3 := by
  classical
  let p : Fin 3 → ℝ := ![4 / 5, 1 / 5, 0]
  let s : Finset (Fin 3 × Fin 3) := {(0, 0), (0, 1), (1, 0)}
  have hp : Probability p := by
    constructor
    · intro i; fin_cases i <;> norm_num [p]
    · norm_num [p, Fin.sum_univ_succ]
  have hs : s.card = min 3 (3 * 3) := by norm_num [s]
  have ha := sum_le_top_sum (arith p) s hs
  have hg := sum_le_top_sum (geom p) s hs
  have hea : (∑ ab ∈ s, arith p ab) = 9 / 5 := by
    norm_num [s, arith, D5.S3.Constants.PowerMeanKernel.meanOne, p]
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  have h16 : Real.sqrt (16 : ℝ) = 4 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  have h25 : Real.sqrt (25 : ℝ) = 5 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  have heg : (∑ ab ∈ s, geom p ab) = 8 / 5 := by
    norm_num [s, geom, D5.S3.Constants.PowerMeanKernel.meanZero, p, h4, h16, h25]
  exact ⟨p, hp, by linarith⟩

private lemma greatest_of_bound_failure {d m : ℕ}
    (hb : m ∈ admissibleIndices d)
    (hf : ∃ p : Fin d → ℝ, Probability p ∧
      (d : ℝ) < topSum (arith p) (m + 1) + topSum (geom p) (m + 1)) :
    IsGreatest (admissibleIndices d) m := by
  refine ⟨hb, ?_⟩
  intro n hn
  by_contra hmn
  have hmn : m + 1 ≤ n := by omega
  obtain ⟨p, hp, hf⟩ := hf
  have ha := top_sum_mono (arith p) (fun ij => by
    dsimp only [arith, D5.S3.Constants.PowerMeanKernel.meanOne]
    exact div_nonneg (add_nonneg (hp.1 _) (hp.1 _)) (by norm_num)) hmn
  have hg := top_sum_mono (geom p) (fun _ => Real.sqrt_nonneg _) hmn
  have hh := hn p hp
  linarith

/-- The Caro–Graswald maximal-index conjecture in dimensions at least five,
and its corrected three-dimensional boundary. -/
theorem result :
    (∀ d : ℕ, 5 ≤ d → IsGreatest (admissibleIndices d) (2 * d - 5)) ∧
      IsGreatest (admissibleIndices 3) 2 := by
  constructor
  · intro d hd
    apply greatest_of_bound_failure
    · exact fun p hp => main_bound hd p hp
    · have h : 2 * d - 5 + 1 = 2 * d - 4 := by omega
      rw [h]
      exact failure_next hd
  · apply greatest_of_bound_failure
    · exact three_bound
    · exact three_failure

end D5.S3.Quantum.QuantumChannels.MarkovianDivisibilityMaximalIndex
