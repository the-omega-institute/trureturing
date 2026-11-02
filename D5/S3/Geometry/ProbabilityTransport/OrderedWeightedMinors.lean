/- GID: D5/S3/Geometry/ProbabilityTransport/OrderedWeightedMinors
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/OrderedWeightedMinors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Increasing-index weighted two-minor and three-minor comparison -/
import D5.S3.Geometry.ProbabilityTransport.WeightedMinorThresholds

noncomputable section
open scoped BigOperators
namespace AlternatingArrayContraction
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

private theorem pair_ordering (f : ι → ι → ℝ)
    (hs : ∀ i j, f j i = f i j) (hz : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * (∑ i, ∑ j, if i < j then f i j else 0) := by
  have hp (i j : ι) : f i j = (if i < j then f i j else 0) +
      (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp [hz]
    · simp [h, not_lt.mpr h.le, hs]
  calc
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f j i else 0) := by
      simp_rw [hp]
      simp only [Finset.sum_add_distrib]
    _ = _ := by rw [Finset.sum_comm (f := fun i j => if j < i then f j i else 0)]; ring

private theorem triple_ordering (f : ι → ι → ι → ℝ)
    (hs : ∀ i j k, f j i k = f i j k)
    (hc : ∀ i j k, f k i j = f i j k)
    (hz : ∀ i k, f i i k = 0) :
    (∑ i, ∑ j, ∑ k, f i j k) =
      6 * (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then f i j k else 0) := by
  have ht (i j k : ι) : f i k j = f i j k := by rw [← hc i k j, hs j i k]
  have hz' (i k : ι) : f i k i = 0 := by rw [← hc i k i, hz]
  have hz'' (i k : ι) : f k i i = 0 := by rw [hc i i k, hz]
  let g : ι → ι → ι → ℝ := fun i j k => if i < j ∧ i < k then f i j k else 0
  have hp (i j k : ι) : f i j k = g i j k + g j i k + g k i j := by
    by_cases hij : i = j
    · subst j; simp [g, hz, hz'']
    by_cases hik : i = k
    · subst k; simp [g, hz, hz', hs]
    by_cases hjk : j = k
    · subst k; simp [g, hz, hz'', hs]
    rcases lt_or_gt_of_ne hij with hij | hij
    · rcases lt_or_gt_of_ne hik with hik | hik
      · simp [g, hij, hik, not_lt.mpr hij.le, not_lt.mpr hik.le]
      · have hkj := hik.trans hij
        simp [g, hij, hik, hkj, not_lt.mpr hij.le, not_lt.mpr hik.le,
          not_lt.mpr hkj.le, hc i j k]
    · rcases lt_or_gt_of_ne hjk with hjk | hjk
      · simp [g, hij, hjk, not_lt.mpr hij.le, not_lt.mpr hjk.le, hs i j k]
      · have hki := hjk.trans hij
        simp [g, hij, hjk, hki, not_lt.mpr hij.le, not_lt.mpr hjk.le,
          not_lt.mpr hki.le, hc i j k]
  have htotal : (∑ i, ∑ j, ∑ k, f i j k) = 3 * (∑ i, ∑ j, ∑ k, g i j k) := by
    calc
      _ = (∑ i, ∑ j, ∑ k, g i j k) + (∑ i, ∑ j, ∑ k, g j i k) +
          (∑ i, ∑ j, ∑ k, g k i j) := by
        conv_lhs => arg 2; ext i; arg 2; ext j; arg 2; ext k; rw [hp]
        simp only [Finset.sum_add_distrib]
      _ = _ := by
        have hswap : (∑ i, ∑ j, ∑ k, g j i k) = ∑ i, ∑ j, ∑ k, g i j k := by
          rw [Finset.sum_comm]
        have hrot : (∑ i, ∑ j, ∑ k, g k i j) = ∑ i, ∑ j, ∑ k, g i j k := by
          calc
            _ = ∑ i, ∑ k, ∑ j, g k i j := by
              apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
            _ = _ := by rw [Finset.sum_comm]
        rw [hswap, hrot]; ring
  have hg (i j k : ι) : g i j k =
      (if i < j ∧ j < k then f i j k else 0) +
      (if i < k ∧ k < j then f i k j else 0) := by
    rcases lt_trichotomy j k with hjk | rfl | hjk
    · by_cases hij : i < j
      · simp [g, hij, hjk, hij.trans hjk, not_lt.mpr hjk.le]
      · simp [g, hij, hjk, not_lt.mpr hjk.le]
    · simp [g, ht, hz'']
    · by_cases hik : i < k
      · simp [g, hik, hjk, hik.trans hjk, not_lt.mpr hjk.le, ht]
      · simp [g, hik, hjk, not_lt.mpr hjk.le]
  have hsplit : (∑ i, ∑ j, ∑ k, g i j k) =
      2 * (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then f i j k else 0) := by
    have he (i : ι) : (∑ j, ∑ k, g i j k) =
        2 * (∑ j, ∑ k, if i < j ∧ j < k then f i j k else 0) := by
      simp_rw [hg]
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun j k => if i < k ∧ k < j then f i k j else 0)]
      ring
    simp_rw [he]
    rw [Finset.mul_sum]
  rw [htotal, hsplit]
  ring

/-- The exact increasing-index comparison, with unrestricted real weights. -/
theorem weighted_minors (x y z : ι → ℝ) (hz : ∑ k, z k ^ 2 = 1)
    (hzx : ∑ k, z k * x k = 0) (hzy : ∑ k, z k * y k = 0)
    (A : ι → ι → ℝ) (hA : ∀ i j, A i j = A j i) (hpos : ∀ i j, 0 < A i j) :
    (∑ i, ∑ j, if i < j then A i j * pairMinor x y i j ^ 2 else 0) ≤
      ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then
        max (A i j) (max (A i k) (A j k)) * tripleMinor x y z i j k ^ 2 else 0 := by
  let p := fun i j => A i j * pairMinor x y i j ^ 2
  let q := fun i j k => max (A i j) (max (A i k) (A j k)) * tripleMinor x y z i j k ^ 2
  have hp : (∑ i, ∑ j, p i j) = 2 * (∑ i, ∑ j, if i < j then p i j else 0) := by
    apply pair_ordering
    · intro i j
      dsimp [p, pairMinor]
      rw [hA j i]
      ring
    · intro i
      simp [p, pairMinor]
  have hb : Alt (tripleMinor x y z) := by
    rw [triple_lift]
    exact lift_alt z (pair_skew x y)
  have hzero (i k : ι) : tripleMinor x y z i i k = 0 := by
    have h := hb.1 i i k
    linarith
  have hq : (∑ i, ∑ j, ∑ k, q i j k) =
      6 * (∑ i, ∑ j, ∑ k, if i < j ∧ j < k then q i j k else 0) := by
    apply triple_ordering
    · intro i j k
      dsimp [q]
      rw [hA j i, hb.1 i j k, max_comm (A j k) (A i k)]
      ring
    · intro i j k
      dsimp [q]
      rw [hA k i, hA k j, hb.2 i j k]
      congr 1
      exact max_left_comm _ _ _
    · intro i k
      simp only [q, hzero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  have h := weighted_minors_all_tuples x y z hz hzx hzy A hA (fun i j => (hpos i j).le)
  change 3 * (∑ i, ∑ j, p i j) ≤ ∑ i, ∑ j, ∑ k, q i j k at h
  rw [hp, hq] at h
  change (∑ i, ∑ j, if i < j then p i j else 0) ≤
    ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then q i j k else 0
  linarith

end AlternatingArrayContraction
