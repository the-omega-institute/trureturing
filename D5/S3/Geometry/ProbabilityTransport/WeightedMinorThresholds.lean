/- GID: D5/S3/Geometry/ProbabilityTransport/WeightedMinorThresholds
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/WeightedMinorThresholds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact finite threshold decomposition for arbitrary real minor weights -/
import D5.S3.Geometry.ProbabilityTransport.AlternatingArrayContraction

noncomputable section
open scoped BigOperators
namespace AlternatingArrayContraction
variable {ι : Type*} [Fintype ι]

private theorem threshold_expansion (s : Finset ℝ) (hs : ∀ r ∈ s, 0 ≤ r) :
    ∃ c : ℝ → ℝ, (∀ r, 0 ≤ c r) ∧
      ∀ x ∈ s, (∑ r ∈ s, if r ≤ x then c r else 0) = x := by
  classical
  induction s using Finset.induction_on_max with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | insert a s hlt ih =>
    obtain ⟨c, hc, hrep⟩ := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
    have ha : a ∉ s := by intro h; exact (lt_irrefl a) (hlt a h)
    by_cases hne : s.Nonempty
    · let m := s.max' hne
      have hm : m ∈ s := Finset.max'_mem s hne
      have hma : m < a := hlt m hm
      have htotal : (∑ r ∈ s, c r) = m := by
        have hr := hrep m hm
        have heq : (∑ r ∈ s, if r ≤ m then c r else 0) = ∑ r ∈ s, c r := by
          apply Finset.sum_congr rfl; intro r hr
          rw [if_pos (Finset.le_max' s r hr)]
        rwa [heq] at hr
      refine ⟨fun r => if r = a then a - m else c r, ?_, ?_⟩
      · intro r
        split_ifs
        · exact sub_nonneg.mpr hma.le
        · exact hc r
      · intro x hx
        rw [Finset.sum_insert ha]
        have hold : (∑ r ∈ s, if r ≤ x then (if r = a then a - m else c r) else 0) =
            ∑ r ∈ s, if r ≤ x then c r else 0 := by
          apply Finset.sum_congr rfl; intro r hr
          simp only [if_neg (ne_of_lt (hlt r hr))]
        rw [hold]
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simp only [le_refl, if_pos, ite_true]
          have hsum : (∑ r ∈ s, if r ≤ a then c r else 0) = ∑ r ∈ s, c r := by
            apply Finset.sum_congr rfl; intro r hr
            rw [if_pos (hlt r hr).le]
          rw [hsum, htotal]
          ring
        · rw [if_neg (not_le.mpr (hlt x hx)), zero_add]
          exact hrep x hx
    · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst s
      refine ⟨fun r => if r = a then a else 0, ?_, ?_⟩
      · intro r
        split_ifs
        · exact hs a (by simp)
        · exact le_refl 0
      · intro x hx
        simp only [Finset.mem_insert, Finset.not_mem_empty, or_false] at hx
        subst x
        simp

private theorem weighted_threshold {α β : Type*} [Fintype α] [Fintype β]
    (a p : α → ℝ) (w q : β → ℝ) (ha : ∀ i, 0 ≤ a i) (hw : ∀ j, 0 ≤ w j)
    (h : ∀ r : ℝ, (∑ i, if r ≤ a i then p i else 0) ≤
      ∑ j, if r ≤ w j then q j else 0) :
    (∑ i, a i * p i) ≤ ∑ j, w j * q j := by
  classical
  let s := Finset.univ.image a ∪ Finset.univ.image w
  have hs : ∀ r ∈ s, 0 ≤ r := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
      exact ha i
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
      exact hw j
  obtain ⟨c, hc, hrep⟩ := threshold_expansion s hs
  have hp : (∑ i, a i * p i) =
      ∑ r ∈ s, c r * (∑ i, if r ≤ a i then p i else 0) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [← hrep (a i) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)),
      Finset.sum_mul]
    apply Finset.sum_congr rfl; intro r _
    split_ifs <;> ring
  have hq : (∑ j, w j * q j) =
      ∑ r ∈ s, c r * (∑ j, if r ≤ w j then q j else 0) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [← hrep (w j) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, by simp, rfl⟩)),
      Finset.sum_mul]
    apply Finset.sum_congr rfl; intro r _
    split_ifs <;> ring
  rw [hp, hq]
  apply Finset.sum_le_sum; intro r _
  exact mul_le_mul_of_nonneg_left (h r) (hc r)

/-- The arbitrary real-weight comparison in ordered-tuple coordinates. -/
theorem weighted_minors_all_tuples (x y z : ι → ℝ) (hz : ∑ k, z k ^ 2 = 1)
    (hzx : ∑ k, z k * x k = 0) (hzy : ∑ k, z k * y k = 0)
    (A : ι → ι → ℝ) (hA : ∀ i j, A i j = A j i) (hpos : ∀ i j, 0 ≤ A i j) :
    3 * (∑ i, ∑ j, A i j * pairMinor x y i j ^ 2) ≤
      ∑ i, ∑ j, ∑ k, max (A i j) (max (A i k) (A j k)) * tripleMinor x y z i j k ^ 2 := by
  classical
  have ht (r : ℝ) := family_domination x y z hz hzx hzy
    (fun i j => r ≤ A i j) (fun i j => by rw [hA i j])
  have hthreshold (r : ℝ) :
      (∑ p : ι × ι, if r ≤ A p.1 p.2 then 3 * pairMinor x y p.1 p.2 ^ 2 else 0) ≤
      ∑ p : ι × ι × ι,
        if r ≤ max (A p.1 p.2.1) (max (A p.1 p.2.2) (A p.2.1 p.2.2))
        then tripleMinor x y z p.1 p.2.1 p.2.2 ^ 2 else 0 := by
    have h := ht r
    unfold mass₂ mass₃ pairProjection tripleProjection at h
    simp only [Fintype.sum_prod_type]
    have hi (a : ℝ) (P : Prop) [Decidable P] : (if P then a else 0) ^ 2 =
        if P then a ^ 2 else 0 := by split_ifs <;> simp
    simp_rw [hi] at h
    simp only [le_max_iff, ite_mul, zero_mul, ← Finset.mul_sum]
    linarith
  have hw := weighted_threshold
    (fun p : ι × ι => A p.1 p.2)
    (fun p : ι × ι => 3 * pairMinor x y p.1 p.2 ^ 2)
    (fun p : ι × ι × ι => max (A p.1 p.2.1) (max (A p.1 p.2.2) (A p.2.1 p.2.2)))
    (fun p : ι × ι × ι => tripleMinor x y z p.1 p.2.1 p.2.2 ^ 2)
    (fun p => hpos _ _)
    (fun p => (hpos p.1 p.2.1).trans (le_max_left _ _)) hthreshold
  simp only [Fintype.sum_prod_type] at hw
  calc
    _ = ∑ i, ∑ j, A i j * (3 * pairMinor x y i j ^ 2) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    _ ≤ _ := hw

end AlternatingArrayContraction
