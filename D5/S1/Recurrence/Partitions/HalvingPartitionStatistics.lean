/- GID: D5/S1/Recurrence/Partitions/HalvingPartitionStatistics
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/HalvingPartitionStatistics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact uniform length moments and balanced residue classes of actual dyadic halving lists. -/

import D5.S1.Recurrence.Partitions.HalvingPartitionProfile
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Nat.ModEq

/-! Uniform statistics are finite averages over the original source carrier.
The interval enumeration is Alekseyev's Theorem 5 specialized to 2^m+1. -/

namespace D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity

/-- The uniform mean over actual lists, with rational arithmetic. -/
noncomputable def meanLength (n : ℕ) : ℚ :=
  (∑ p : SourceLists n, (p.val.length : ℚ)) / count n

/-- The uniform central second moment over those same lists. -/
noncomputable def varianceLength (n : ℕ) : ℚ :=
  (∑ p : SourceLists n, ((p.val.length : ℚ) - meanLength n) ^ 2) / count n

/-- Exact mean, including every m>=2 endpoint. -/
theorem meanLength_dyadic (m : ℕ) (hm : 2 ≤ m) :
    meanLength (2 ^ m + 1) = m + 1 - (thresholdCount m : ℚ) / 2 := by
  have ht := totalParts_twice m hm
  have hr := thresholdCount_lt m hm
  have hsub : (2 * m + 2 - thresholdCount m : ℕ) + thresholdCount m = 2 * m + 2 := by
    omega
  have htQ : 2 * (totalParts (2 ^ m + 1) : ℚ) =
      (thresholdCount m + 3 : ℚ) * (2 * m + 2 - thresholdCount m) := by
    have hcast : 2 * (totalParts (2 ^ m + 1) : ℚ) =
        ((thresholdCount m + 3 : ℕ) : ℚ) * ((2 * m + 2 - thresholdCount m : ℕ) : ℚ) := by
      exact_mod_cast ht
    simpa only [Nat.cast_sub (by omega : thresholdCount m ≤ 2 * m + 2),
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hcast
  have hc : (count (2 ^ m + 1) : ℚ) = thresholdCount m + 3 := by
    rw [dyadic_source_count m hm]
    simp only [Nat.cast_add, Nat.cast_ofNat, thresholdCount]
    ring
  unfold meanLength
  have hs : (∑ p : SourceLists (2 ^ m + 1), (p.val.length : ℚ)) =
      (totalParts (2 ^ m + 1) : ℚ) := by simp [totalParts]
  rw [hs, hc]
  apply (div_eq_iff (by positivity : (thresholdCount m + 3 : ℚ) ≠ 0)).mpr
  linarith

/-- Exact variance under uniform choice of a source list. -/
theorem varianceLength_dyadic (m : ℕ) (hm : 2 ≤ m) :
    varianceLength (2 ^ m + 1) = (((thresholdCount m : ℚ) + 3) ^ 2 - 1) / 12 := by
  classical
  have hr := thresholdCount_lt m hm
  have ha : (m - thresholdCount m : ℕ) = (m : ℚ) - thresholdCount m := by
    rw [Nat.cast_sub (by omega)]
  have hs₁ := sum_range_pow (thresholdCount m + 3) 1
  have hs₂ := sum_range_pow (thresholdCount m + 3) 2
  conv_rhs at hs₁ => norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one]
  conv_rhs at hs₂ => norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one, bernoulli_two]
  simp only [pow_one] at hs₁
  unfold varianceLength
  rw [sum_source_lengths m hm (fun ell => ((ell : ℚ) - meanLength (2 ^ m + 1)) ^ 2),
    meanLength_dyadic m hm,
    Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      (((m - thresholdCount m + i : ℕ) : ℚ) - (m + 1 - (thresholdCount m : ℚ) / 2)) ^ 2)]
  simp only [Nat.cast_add, ha]
  have hexpand : (∑ i ∈ Finset.range (thresholdCount m + 3),
      ((m : ℚ) - thresholdCount m + i - (m + 1 - (thresholdCount m : ℚ) / 2)) ^ 2) =
      (∑ i ∈ Finset.range (thresholdCount m + 3), (i : ℚ) ^ 2) -
      (thresholdCount m + 2) * (∑ i ∈ Finset.range (thresholdCount m + 3), (i : ℚ)) +
      (thresholdCount m + 3) * ((thresholdCount m : ℚ) / 2 + 1) ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range (thresholdCount m + 3),
          ((i : ℚ) ^ 2 - (thresholdCount m + 2) * i +
            ((thresholdCount m : ℚ) / 2 + 1) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hexpand, hs₁, hs₂, dyadic_source_count m hm]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  change _ / (3 + (thresholdCount m : ℚ)) = _
  field_simp
  <;> ring

/-- Literal count of source lists whose length belongs to a residue class. -/
noncomputable def lengthResidueCount (n b r : ℕ) : ℕ :=
  Nat.card {p : SourceLists n // p.val.length % b = r}

/-- Any two length classes modulo any positive modulus differ by at most one.
The injection shifts each length to the next target residue; at most the last
source length can leave the interval. -/
theorem lengthResidueCount_balanced (m b : ℕ) (hm : 2 ≤ m) (hb : 0 < b)
    (r s : Fin b) :
    lengthResidueCount (2 ^ m + 1) b r.val ≤
      lengthResidueCount (2 ^ m + 1) b s.val + 1 := by
  classical
  have sameLength (p q : SourceLists (2 ^ m + 1))
      (he : p.val.length = q.val.length) : p = q := by
    let fiber := {x : SourceLists (2 ^ m + 1) // x.val.length = p.val.length}
    have hc : Nat.card fiber = 1 := by
      change lengthCount (2 ^ m + 1) p.val.length = 1
      rw [lengthCount_dyadic m p.val.length hm]
      exact if_pos ((source_length_support m p.val.length hm).mp ⟨p, rfl⟩)
    have hu : Subsingleton fiber := (Nat.card_eq_one_iff_unique.mp hc).1
    exact congrArg Subtype.val (hu.elim (⟨p, rfl⟩ : fiber) ⟨q, he.symm⟩)
  let d := if r.val ≤ s.val then s.val - r.val else b + s.val - r.val
  have hd : d < b := by dsimp [d]; split_ifs <;> omega
  have hmod (x : ℕ) (hx : x % b = r.val) : (x + d) % b = s.val := by
    rw [Nat.add_mod, hx]
    by_cases h : r.val ≤ s.val
    · have he : r.val + d = s.val := by dsimp [d]; rw [if_pos h]; omega
      rw [Nat.mod_eq_of_lt hd, he, Nat.mod_eq_of_lt s.isLt]
    · have he : r.val + d = b + s.val := by dsimp [d]; rw [if_neg h]; omega
      rw [Nat.mod_eq_of_lt hd, he, Nat.add_mod_left, Nat.mod_eq_of_lt s.isLt]
  let A := {p : SourceLists (2 ^ m + 1) // p.val.length % b = r.val}
  let B := {p : SourceLists (2 ^ m + 1) // p.val.length % b = s.val}
  have target (p : A) (hp : p.val.val.length + d ≤ m + 2) :
      ∃ q : B, q.val.val.length = p.val.val.length + d := by
    have hlo := ((source_length_interval m p.val.val.length hm).mp ⟨p.val, rfl⟩).1
    obtain ⟨q, hq⟩ := (source_length_interval m (p.val.val.length + d) hm).mpr
      ⟨by omega, hp⟩
    exact ⟨⟨q, by change q.val.length % b = _; rw [hq]; exact hmod _ p.prop⟩, hq⟩
  let f : A → Option B := fun p =>
    if hp : p.val.val.length + d ≤ m + 2 then some (Classical.choose (target p hp))
    else none
  have hinj : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    apply sameLength
    change p.val.val.length = q.val.val.length
    by_cases hp : p.val.val.length + d ≤ m + 2
    · have hq : q.val.val.length + d ≤ m + 2 := by
        by_contra hn
        simp [f, hp, hn] at he
      have hv := congrArg (fun o : Option B => o.map (fun x => x.val.val.length)) he
      simp only [f, dif_pos hp, dif_pos hq, Option.map_some, Option.some.injEq] at hv
      rw [Classical.choose_spec (target p hp), Classical.choose_spec (target q hq)] at hv
      omega
    · have hq : ¬ q.val.val.length + d ≤ m + 2 := by
        intro hq
        simp [f, hp, hq] at he
      have hpl := ((source_length_interval m p.val.val.length hm).mp ⟨p.val, rfl⟩).2
      have hql := ((source_length_interval m q.val.val.length hm).mp ⟨q.val, rfl⟩).2
      have hcong : Nat.ModEq b p.val.val.length q.val.val.length :=
        p.prop.trans q.prop.symm
      apply hcong.eq_of_abs_lt
      rw [abs_lt]
      constructor <;> omega
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_option, A, B, lengthResidueCount, Nat.card_eq_fintype_card] using hc

end D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
