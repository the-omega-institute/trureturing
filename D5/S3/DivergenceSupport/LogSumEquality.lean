/- GID: D5/S3/DivergenceSupport/LogSumEquality
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/LogSumEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize equality in finite log-sum by common positive-support ratios. -/

import D5.S3.DivergenceSupport.LogSumInequality

namespace D5.S3.DivergenceSupport.LogSumEquality

open D5.S3.DivergenceSupport.LogSumInequality
open InformationTheory

/-!
The easy equality direction is stated using global proportionality, `a i = c * b i`. This form
is convenient for downstream use and needs no sign hypotheses: at `b i = 0`, totalized division
makes the summand zero, while at `b i != 0` the ratio is `c`.

Repository searches for `log_sum` equality, common ratios, and proportional masses found no
existing equality characterization. In pinned mathlib, `strictConvexOn_klFun` and the finite
Jensen lemmas `StrictConvexOn.map_sum_lt`, `StrictConvexOn.eq_of_le_map_sum`,
`StrictConvexOn.map_sum_eq_iff_of_nonneg`, and `StrictConvexOn.map_sum_eq_iff'` exist in
`Mathlib.Analysis.Convex.Jensen`. The searched name `inner_le_nnorm` does not exist. Thus the
converse below uses the available nonnegative-weight Jensen equality criterion rather than
rebuilding strict Jensen.
-/

/-- Proportional finite families attain equality in log-sum, including totalized zero terms. -/
theorem log_sum_eq_of_proportional {ι : Type*} [Fintype ι]
    (a b : ι -> Real) (c : Real)
    (hprop : ∀ i, a i = c * b i) :
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) =
      ∑ i, a i * Real.log (a i / b i) := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  fail_if_success linarith
  classical
  have hsum_a : (∑ i, a i) = c * ∑ i, b i := by
    calc
      (∑ i, a i) = ∑ i, c * b i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hprop i
      _ = c * ∑ i, b i := by rw [Finset.mul_sum]
  have hterm (i : ι) :
      a i * Real.log (a i / b i) = (c * Real.log c) * b i := by
    rw [hprop i]
    by_cases hbi : b i = 0
    · simp [hbi]
    · have hratio : c * b i / b i = c := by field_simp
      rw [hratio]
      ring
  have hsum_term :
      (∑ i, a i * Real.log (a i / b i)) = (c * Real.log c) * ∑ i, b i := by
    calc
      (∑ i, a i * Real.log (a i / b i)) =
          ∑ i, (c * Real.log c) * b i := by
            apply Finset.sum_congr rfl
            intro i _
            exact hterm i
      _ = (c * Real.log c) * ∑ i, b i := by rw [Finset.mul_sum]
  rw [hsum_a, hsum_term]
  by_cases hsum_b : (∑ i, b i) = 0
  · simp [hsum_b]
  · have hratio : (c * ∑ i, b i) / (∑ i, b i) = c := by field_simp
    rw [hratio]
    ring

/-- Equality in log-sum forces all ratios with positive reference mass to agree. -/
theorem ratios_eq_of_log_sum_eq {ι : Type*} [Fintype ι]
    (a b : ι -> Real)
    (ha : ∀ i, 0 <= a i)
    (hb : ∀ i, 0 <= b i)
    (hac : ∀ i, b i = 0 -> a i = 0)
    (heq :
      (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) =
        ∑ i, a i * Real.log (a i / b i)) :
    ∀ j k, 0 < b j -> 0 < b k -> a j / b j = a k / b k := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  fail_if_success linarith
  classical
  by_cases hsum_b : (∑ i, b i) = 0
  · have hb_zero (i : ι) : b i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hb j).mp hsum_b i
        (Finset.mem_univ i)
    intro j _ hj _
    simp [hb_zero j] at hj
  have hsum_b_nonneg : 0 <= ∑ i, b i := Finset.sum_nonneg fun i _ => hb i
  have hsum_b_pos : 0 < ∑ i, b i :=
    lt_of_le_of_ne hsum_b_nonneg (Ne.symm hsum_b)
  have hweighted_ratio (i : ι) :
      b i / (∑ j, b j) * (a i / b i) = a i / (∑ j, b j) := by
    by_cases hbi : b i = 0
    · simp [hbi, hac i hbi]
    · field_simp [hsum_b, hbi]
  have hweighted_sum :
      (∑ i, b i / (∑ j, b j) * (a i / b i)) =
        (∑ i, a i) / (∑ i, b i) := by
    calc
      (∑ i, b i / (∑ j, b j) * (a i / b i)) =
          ∑ i, a i / (∑ j, b j) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hweighted_ratio i
      _ = (∑ i, a i) / (∑ i, b i) := by rw [Finset.sum_div]
  have hleft :
      (∑ i, b i) * klFun ((∑ i, a i) / (∑ i, b i)) =
        (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) +
          (∑ i, b i) - ∑ i, a i := by
    rw [klFun_apply]
    field_simp [hsum_b]
  have hterm (i : ι) :
      b i * klFun (a i / b i) =
        a i * Real.log (a i / b i) + b i - a i := by
    by_cases hbi : b i = 0
    · simp [hbi, hac i hbi, klFun_apply]
    · rw [klFun_apply]
      field_simp [hbi]
  have hright :
      (∑ i, b i * klFun (a i / b i)) =
        (∑ i, a i * Real.log (a i / b i)) + (∑ i, b i) - ∑ i, a i := by
    calc
      (∑ i, b i * klFun (a i / b i)) =
          ∑ i, (a i * Real.log (a i / b i) + b i - a i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hterm i
      _ = (∑ i, a i * Real.log (a i / b i)) +
          (∑ i, b i) - ∑ i, a i := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hperspective_eq :
      (∑ i, b i) * klFun ((∑ i, a i) / (∑ i, b i)) =
        ∑ i, b i * klFun (a i / b i) := by
    calc
      (∑ i, b i) * klFun ((∑ i, a i) / (∑ i, b i)) =
          (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) +
            (∑ i, b i) - ∑ i, a i := hleft
      _ = (∑ i, a i * Real.log (a i / b i)) +
          (∑ i, b i) - ∑ i, a i := by rw [heq]
      _ = ∑ i, b i * klFun (a i / b i) := hright.symm
  have hweighted_kl :
      (∑ i, b i) *
          (∑ i, b i / (∑ j, b j) * klFun (a i / b i)) =
        ∑ i, b i * klFun (a i / b i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hsum_b]
  have hjensen_eq :
      klFun (∑ i, b i / (∑ j, b j) * (a i / b i)) =
        ∑ i, b i / (∑ j, b j) * klFun (a i / b i) := by
    rw [hweighted_sum]
    apply (mul_left_cancel₀ hsum_b)
    exact hperspective_eq.trans hweighted_kl.symm
  have hratios :=
    (strictConvexOn_klFun.map_sum_eq_iff_of_nonneg
      (t := Finset.univ)
      (w := fun i => b i / (∑ j, b j))
      (p := fun i => a i / b i)
      (fun i _ => div_nonneg (hb i) hsum_b_nonneg)
      (by rw [← Finset.sum_div, div_self hsum_b])
      (fun i _ => div_nonneg (ha i) (hb i))).mp (by
        simpa only [smul_eq_mul] using hjensen_eq)
  intro j k hj hk
  exact hratios (Finset.mem_univ j) (div_ne_zero (ne_of_gt hj) hsum_b)
    (Finset.mem_univ k) (div_ne_zero (ne_of_gt hk) hsum_b)

/-- Finite log-sum is an equality exactly when positive-reference ratios agree pairwise. -/
theorem log_sum_eq_iff_ratios_eq {ι : Type*} [Fintype ι]
    (a b : ι -> Real)
    (ha : ∀ i, 0 <= a i)
    (hb : ∀ i, 0 <= b i)
    (hac : ∀ i, b i = 0 -> a i = 0) :
    ((∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) =
        ∑ i, a i * Real.log (a i / b i)) ↔
      ∀ j k, 0 < b j -> 0 < b k -> a j / b j = a k / b k := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  fail_if_success linarith
  constructor
  · exact ratios_eq_of_log_sum_eq a b ha hb hac
  · intro hratios
    classical
    by_cases hsum_b : (∑ i, b i) = 0
    · have hb_zero (i : ι) : b i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hb j).mp hsum_b i
          (Finset.mem_univ i)
      exact log_sum_eq_of_proportional a b 0 fun i => by
        simp [hb_zero i, hac i (hb_zero i)]
    have hsum_b_nonneg : 0 <= ∑ i, b i := Finset.sum_nonneg fun i _ => hb i
    have hsum_b_pos : 0 < ∑ i, b i :=
      lt_of_le_of_ne hsum_b_nonneg (Ne.symm hsum_b)
    obtain ⟨k, _, hk⟩ :=
      (Finset.sum_pos_iff_of_nonneg fun i (_ : i ∈ Finset.univ) => hb i).mp hsum_b_pos
    apply log_sum_eq_of_proportional a b (a k / b k)
    intro i
    by_cases hbi : b i = 0
    · simp [hbi, hac i hbi]
    have hbi_pos : 0 < b i := lt_of_le_of_ne (hb i) (Ne.symm hbi)
    calc
      a i = (a i / b i) * b i := by field_simp [hbi]
      _ = (a k / b k) * b i := by rw [hratios i k hbi_pos hk]

#print axioms log_sum_eq_of_proportional
#print axioms ratios_eq_of_log_sum_eq
#print axioms log_sum_eq_iff_ratios_eq

/- Equality is attained at `a = (2, 4)` and `b = (1, 2)`, with common ratio two. -/
example :
    let a : Bool -> Real := fun i => if i then 4 else 2
    let b : Bool -> Real := fun i => if i then 2 else 1
    (∑ i, a i) * Real.log ((∑ i, a i) / (∑ i, b i)) =
      ∑ i, a i * Real.log (a i / b i) := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact log_sum_eq_of_proportional
    (fun i : Bool => if i then 4 else 2)
    (fun i : Bool => if i then 2 else 1)
    2 (by intro i; cases i <;> norm_num)

end D5.S3.DivergenceSupport.LogSumEquality
