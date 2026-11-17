/- GID: D5/S3/StatisticalMechanics/InversePowerLinePowerPacking
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/InversePowerLinePowerPacking
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Power-law interval packing and weighted moment estimates. -/

/-
admission_basis: escape-witness
question_answered: https://github.com/the-omega-institute/trureturing/issues/27202
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27401
interval_comparison:
  proof_shape: content; escape_witness: interval_comparison.
  consumers: finite_interval_packing.
finite_interval_packing:
  proof_shape: content; escape_witness: interval_comparison.
  consumers: right_power_sum, left_power_sum.
finite_length_packing:
  proof_shape: bind-only; escape_witness: none.
  consumers: window_gap_mass.
right_power_sum:
  proof_shape: content; escape_witness: interval_comparison.
  consumers: full_weighted_distance.
left_power_sum:
  proof_shape: content; escape_witness: interval_comparison.
  consumers: full_weighted_distance.
window_gap_mass:
  proof_shape: content; escape_witness: window_gap_mass.
  consumers: InversePowerLineEquilibria.reciprocal_constant_of_power_bound.
full_weighted_distance:
  proof_shape: content; escape_witness: right_power_sum.
  consumers: InversePowerLineEquilibria.reciprocal_constant_of_power_bound.
inverse_power_second_moment:
  proof_shape: bind-only; escape_witness: none.
  consumers: InversePowerLineEquilibria.reciprocal_constant_of_power_bound.
-/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Interval packing estimates for inverse powers
-/

namespace D5.S3.StatisticalMechanics.InversePowerLinePowerPacking


open Set MeasureTheory

private theorem interval_comparison {p q l u : ℝ} (hp : 1 < p) (hq : 0 < q)
    (hl : 0 < l) (hlu : l ≤ u) (huq : u ≤ q * l) :
    (u - l) * l ^ (-p) ≤ q ^ p * (∫ t in Ioc l u, t ^ (-p)) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (-p)) (Ioc l u) := by
    apply (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) (by linarith : 0 < l / 2)).mono_set
    intro t ht
    exact lt_of_lt_of_le (by linarith : l / 2 < l) ht.1.le
  have hconst : IntegrableOn (fun _ : ℝ => l ^ (-p)) (Ioc l u) := integrableOn_const (hs := by simp [Real.volume_Ioc])
  have hpoint (t : ℝ) (ht : t ∈ Ioc l u) : l ^ (-p) ≤ q ^ p * t ^ (-p) := by
    have htpos : 0 < t := hl.trans ht.1
    have hmono := Real.rpow_le_rpow_of_nonpos htpos (ht.2.trans huq) (by linarith : -p ≤ 0)
    have heq : q ^ p * (q * l) ^ (-p) = l ^ (-p) := by
      rw [Real.mul_rpow hq.le hl.le]
      rw [← mul_assoc, ← Real.rpow_add hq]
      simp
    rw [← heq]
    exact mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hq.le p)
  have h := setIntegral_mono_on hconst (hi.const_mul (q ^ p)) measurableSet_Ioc hpoint
  rw [setIntegral_const, Real.volume_real_Ioc_of_le hlu, smul_eq_mul,
    integral_const_mul] at h
  exact h

private theorem finite_interval_packing {ι : Type*} (S : Finset ι) (l u : ι → ℝ)
    (p q δ : ℝ) (hp : 1 < p) (hq : 0 < q) (hδ : 0 < δ)
    (hl : ∀ j ∈ S, δ ≤ l j) (hlu : ∀ j ∈ S, l j ≤ u j)
    (huq : ∀ j ∈ S, u j ≤ q * l j)
    (hdisjoint : Set.Pairwise (↑S : Set ι) (fun j k => Disjoint (Ioc (l j) (u j)) (Ioc (l k) (u k)))) :
    (∑ j ∈ S, (u j - l j) * (l j) ^ (-p)) ≤
      q ^ p * δ ^ (1 - p) / (p - 1) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (-p)) (Ioi δ) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hδ
  have hsubset (j : ι) (hj : j ∈ S) : Ioc (l j) (u j) ⊆ Ioi δ := by
    exact Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi (hl j hj))
  have hinterval (j : ι) (hj : j ∈ S) : IntegrableOn (fun t : ℝ => t ^ (-p)) (Ioc (l j) (u j)) :=
    hi.mono_set (hsubset j hj)
  have hsum : (∑ j ∈ S, ∫ t in Ioc (l j) (u j), t ^ (-p)) ≤
      ∫ t in Ioi δ, t ^ (-p) := by
    rw [← integral_biUnion_finset S (fun _ _ => measurableSet_Ioc) hdisjoint hinterval]
    apply setIntegral_mono_set hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg (hδ.trans ht).le (-p)
    · exact Filter.Eventually.of_forall (fun t ht => by
        obtain ⟨j, hj, ht⟩ := Set.mem_iUnion₂.mp ht
        exact hsubset j hj ht)
  calc
    _ ≤ ∑ j ∈ S, q ^ p * (∫ t in Ioc (l j) (u j), t ^ (-p)) :=
      Finset.sum_le_sum (fun j hj => interval_comparison hp hq (hδ.trans_le (hl j hj)) (hlu j hj) (huq j hj))
    _ = q ^ p * (∑ j ∈ S, ∫ t in Ioc (l j) (u j), t ^ (-p)) := (Finset.mul_sum S _ _).symm
    _ ≤ q ^ p * (∫ t in Ioi δ, t ^ (-p)) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hq.le p)
    _ = q ^ p * δ ^ (1 - p) / (p - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -p < -1) hδ]
      rw [show -p + 1 = 1 - p by ring]
      field_simp [show 1 - p ≠ 0 by linarith, show p - 1 ≠ 0 by linarith]
      <;> ring

private theorem finite_length_packing {ι : Type*} (S : Finset ι) (l u : ι → ℝ)
    (L U : ℝ) (hLU : L ≤ U) (hlu : ∀ j ∈ S, l j ≤ u j)
    (hl : ∀ j ∈ S, L ≤ l j) (hu : ∀ j ∈ S, u j ≤ U)
    (hdisjoint : Set.Pairwise (↑S : Set ι) (fun j k => Disjoint (Ioc (l j) (u j)) (Ioc (l k) (u k)))) :
    (∑ j ∈ S, (u j - l j)) ≤ U - L := by
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc L U) :=
    integrableOn_const (hs := by simp [Real.volume_Ioc])
  have hsub (j : ι) (hj : j ∈ S) : Ioc (l j) (u j) ⊆ Ioc L U := by
    exact Set.Ioc_subset_Ioc (hl j hj) (hu j hj)
  have hsum := setIntegral_mono_set hi (Filter.Eventually.of_forall (fun _ => zero_le_one))
    (Filter.Eventually.of_forall (fun t ht => by
      obtain ⟨j, hj, ht⟩ := mem_iUnion₂.mp ht
      exact hsub j hj ht))
  rw [integral_biUnion_finset S (fun _ _ => measurableSet_Ioc) hdisjoint
    (fun j hj => hi.mono_set (hsub j hj))] at hsum
  simp only [setIntegral_const, smul_eq_mul, mul_one] at hsum
  rw [Real.volume_real_Ioc_of_le hLU] at hsum
  have heq : (∑ j ∈ S, volume.real (Ioc (l j) (u j))) = ∑ j ∈ S, (u j - l j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Real.volume_real_Ioc_of_le (hlu j hj)
  rwa [heq] at hsum

private theorem right_power_sum {a : ℤ → ℝ} (ha : StrictMono a) (r s δ : ℝ)
    (hr : 1 ≤ r) (hs : 2 < s) (hδ : 0 < δ)
    (hratio : ∀ j : ℤ, a (j + 1) - a j ≤ r * (a j - a (j - 1)))
    (n : ℤ) (hgap : δ ≤ a (n + 1) - a n) :
    Summable (fun j : {j : ℤ // n < j} =>
      (a (j.val + 1) - a j.val) * (a j.val - a n) ^ (1 - s)) ∧
    (∑' j : {j : ℤ // n < j},
      (a (j.val + 1) - a j.val) * (a j.val - a n) ^ (1 - s)) ≤
      (1 + r) ^ (s - 1) * δ ^ (2 - s) / (s - 2) := by
  let J := {j : ℤ // n < j}
  let l : J → ℝ := fun j => a j.val - a n
  let u : J → ℝ := fun j => a (j.val + 1) - a n
  have hdl (j : J) : δ ≤ l j := by
    have hj : n + 1 ≤ j.val := by omega
    dsimp [l]
    linarith [ha.monotone hj]
  have hlu (j : J) : l j ≤ u j := by
    dsimp [l, u]
    linarith [ha (show j.val < j.val + 1 by omega)]
  have huq (j : J) : u j ≤ (1 + r) * l j := by
    have hj : n ≤ j.val - 1 := by omega
    have hprev : a j.val - a (j.val - 1) ≤ l j := by
      dsimp [l]
      linarith [ha.monotone hj]
    have hbound := (hratio j.val).trans (mul_le_mul_of_nonneg_left hprev (by linarith))
    dsimp [u, l] at *
    linarith
  have hd (S : Finset J) : Set.Pairwise (↑S)
      (fun j k => Disjoint (Ioc (l j) (u j)) (Ioc (l k) (u k))) := by
    intro j hj k hk hne
    have hne' : j.val ≠ k.val := fun h => hne (Subtype.ext h)
    rcases lt_or_gt_of_ne hne' with h | h
    · apply Ioc_disjoint_Ioc_of_le
      dsimp [u, l]
      linarith [ha.monotone (show j.val + 1 ≤ k.val by omega)]
    · apply Disjoint.symm
      apply Ioc_disjoint_Ioc_of_le
      dsimp [u, l]
      linarith [ha.monotone (show k.val + 1 ≤ j.val by omega)]
  let F : J → ℝ := fun j => (a (j.val + 1) - a j.val) * (a j.val - a n) ^ (1 - s)
  have hnonneg : ∀ j : J, 0 ≤ F j := by
    intro j
    apply mul_nonneg (sub_nonneg.mpr (ha.monotone (by omega)))
    exact Real.rpow_nonneg (hδ.trans_le (hdl j)).le _
  have hfinite (S : Finset J) : (∑ j ∈ S, F j) ≤
      (1 + r) ^ (s - 1) * δ ^ (2 - s) / (s - 2) := by
    have H := finite_interval_packing S l u (s - 1) (1 + r) δ
      (by linarith) (by linarith) hδ (fun j _ => hdl j) (fun j _ => hlu j)
      (fun j _ => huq j) (hd S)
    have hF : ∀ j : J, (u j - l j) * l j ^ (-(s - 1)) = F j := by
      intro j
      dsimp [u, l, F]
      rw [show -(s - 1) = 1 - s by ring]
      congr 1
      ring
    simp_rw [hF] at H
    simpa only [show 1 - (s - 1) = 2 - s by ring, show s - 1 - 1 = s - 2 by ring] using H
  exact ⟨summable_of_sum_le hnonneg hfinite, Real.tsum_le_of_sum_le hnonneg hfinite⟩

private theorem left_power_sum {a : ℤ → ℝ} (ha : StrictMono a) (r s δ : ℝ)
    (hr : 1 ≤ r) (hs : 2 < s) (hδ : 0 < δ)
    (hratio : ∀ j : ℤ, a (j + 1) - a j ≤ r * (a j - a (j - 1)))
    (hreverse : ∀ j : ℤ, a j - a (j - 1) ≤ r * (a (j + 1) - a j))
    (n : ℤ) (hgap : δ ≤ a n - a (n - 1)) :
    Summable (fun j : {j : ℤ // j < n} =>
      (a (j.val + 1) - a j.val) * (a n - a j.val) ^ (1 - s)) ∧
    (∑' j : {j : ℤ // j < n},
      (a (j.val + 1) - a j.val) * (a n - a j.val) ^ (1 - s)) ≤
      r * ((1 + r) ^ (s - 1) * δ ^ (2 - s) / (s - 2)) := by
  let J := {j : ℤ // j < n}
  let l : J → ℝ := fun j => a n - a j.val
  let u : J → ℝ := fun j => a n - a (j.val - 1)
  have hdl (j : J) : δ ≤ l j := by
    have hj : j.val ≤ n - 1 := by omega
    dsimp [l]
    linarith [ha.monotone hj]
  have hlu (j : J) : l j ≤ u j := by
    dsimp [l, u]
    linarith [ha (show j.val - 1 < j.val by omega)]
  have huq (j : J) : u j ≤ (1 + r) * l j := by
    have hj : j.val + 1 ≤ n := by omega
    have hnext : a (j.val + 1) - a j.val ≤ l j := by
      dsimp [l]
      linarith [ha.monotone hj]
    have hbound := (hreverse j.val).trans (mul_le_mul_of_nonneg_left hnext (by linarith))
    dsimp [u, l] at *
    linarith
  have hd (S : Finset J) : Set.Pairwise (↑S : Set J)
      (fun j k => Disjoint (Ioc (l j) (u j)) (Ioc (l k) (u k))) := by
    intro j hj k hk hne
    have hne' : j.val ≠ k.val := fun h => hne (Subtype.ext h)
    rcases lt_or_gt_of_ne hne' with h | h
    · apply Disjoint.symm
      apply Ioc_disjoint_Ioc_of_le
      dsimp [u, l]
      linarith [ha.monotone (show j.val ≤ k.val - 1 by omega)]
    · apply Ioc_disjoint_Ioc_of_le
      dsimp [u, l]
      linarith [ha.monotone (show k.val ≤ j.val - 1 by omega)]
  let H : J → ℝ := fun j => (u j - l j) * l j ^ (1 - s)
  have hHnonneg : ∀ j : J, 0 ≤ H j := by
    intro j
    exact mul_nonneg (sub_nonneg.mpr (hlu j)) (Real.rpow_nonneg (hδ.trans_le (hdl j)).le _)
  have hfinite (S : Finset J) : (∑ j ∈ S, H j) ≤
      (1 + r) ^ (s - 1) * δ ^ (2 - s) / (s - 2) := by
    have H := finite_interval_packing S l u (s - 1) (1 + r) δ
      (by linarith) (by linarith) hδ (fun j _ => hdl j) (fun j _ => hlu j)
      (fun j _ => huq j) (hd S)
    simpa only [show -(s - 1) = 1 - s by ring,
      show 1 - (s - 1) = 2 - s by ring, show s - 1 - 1 = s - 2 by ring] using H
  have hHs : Summable H := summable_of_sum_le hHnonneg hfinite
  let F : J → ℝ := fun j => (a (j.val + 1) - a j.val) * (a n - a j.val) ^ (1 - s)
  have hFnonneg : ∀ j : J, 0 ≤ F j := by
    intro j
    exact mul_nonneg (sub_nonneg.mpr (ha.monotone (by omega)))
      (Real.rpow_nonneg (hδ.trans_le (hdl j)).le _)
  have hFH (j : J) : F j ≤ r * H j := by
    have h := mul_le_mul_of_nonneg_right (hratio j.val)
      (Real.rpow_nonneg (hδ.trans_le (hdl j)).le (1 - s))
    dsimp [F, H, u, l] at *
    nlinarith
  have hFs : Summable F := Summable.of_nonneg_of_le hFnonneg hFH (hHs.mul_left r)
  refine ⟨hFs, ?_⟩
  calc
    (∑' j, F j) ≤ ∑' j, r * H j := hFs.tsum_le_tsum hFH (hHs.mul_left r)
    _ = r * ∑' j, H j := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.tsum_le_of_sum_le hHnonneg hfinite) (by linarith)

theorem window_gap_mass {a : ℤ → ℝ} (ha : StrictMono a) {r R : ℝ}
    (hr : 1 ≤ r) (hR : 0 ≤ R)
    (hratio : ∀ j : ℤ, a (j + 1) - a j ≤ r * (a j - a (j - 1)))
    (m k : ℤ) (hmk : m < k) (hm : |a m| ≤ 2 * R) (hk : |a k| ≤ 2 * R)
    (S : Finset ℤ) (hS : ∀ j ∈ S, |a j| ≤ 2 * R) :
    (∑ j ∈ S, (a (j + 1) - a j)) ≤ (4 + 4 * r) * R := by
  have hbound (j : ℤ) (hj : j ∈ S) : a (j + 1) ≤ 2 * R + 4 * r * R := by
    have hjb := abs_le.mp (hS j hj)
    rcases lt_or_ge j k with hjk | hkj
    · have hnext : a (j + 1) ≤ a k := ha.monotone (by omega)
      have hku := (abs_le.mp hk).2
      nlinarith
    · have hprev : a m ≤ a (j - 1) := ha.monotone (by omega)
      have hml := (abs_le.mp hm).1
      have hgap : a j - a (j - 1) ≤ 4 * R := by linarith
      have hrp : 0 ≤ r := by linarith
      have h := (hratio j).trans (mul_le_mul_of_nonneg_left hgap hrp)
      linarith
  have hd : Set.Pairwise (↑S : Set ℤ)
      (fun j k => Disjoint (Ioc (a j) (a (j + 1))) (Ioc (a k) (a (k + 1)))) := by
    intro j hj k hk hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact Ioc_disjoint_Ioc_of_le (ha.monotone (by omega))
    · exact Disjoint.symm (Ioc_disjoint_Ioc_of_le (ha.monotone (by omega)))
  have h := finite_length_packing S a (fun j => a (j + 1)) (-2 * R) (2 * R + 4 * r * R)
    (by nlinarith) (fun j _ => (ha.monotone (by omega)))
    (fun j hj => by linarith [(abs_le.mp (hS j hj)).1]) hbound hd
  nlinarith

theorem full_weighted_distance {a : ℤ → ℝ} (ha : StrictMono a) (r s δ : ℝ)
    (hr : 1 ≤ r) (hs : 2 < s) (hδ : 0 < δ)
    (hratio : ∀ j : ℤ, a (j + 1) - a j ≤ r * (a j - a (j - 1)))
    (hreverse : ∀ j : ℤ, a j - a (j - 1) ≤ r * (a (j + 1) - a j))
    (n : ℤ) (hgap : δ ≤ a (n + 1) - a n) (hprev : δ ≤ a n - a (n - 1)) :
    Summable (fun j : ℤ => (a (j + 1) - a j) * |a j - a n| ^ (1 - s)) ∧
    (∑' j : ℤ, (a (j + 1) - a j) * |a j - a n| ^ (1 - s)) ≤
      (1 + r) * ((1 + r) ^ (s - 1) * δ ^ (2 - s) / (s - 2)) := by
  classical
  let F : ℤ → ℝ := fun j => (a (j + 1) - a j) * |a j - a n| ^ (1 - s)
  have hright := right_power_sum ha r s δ hr hs hδ hratio n hgap
  have hleft := left_power_sum ha r s δ hr hs hδ hratio hreverse n hprev
  have hRs : Summable (fun j : {j : ℤ // n < j} => F j.val) := by
    convert hright.1 using 1
    ext j
    simp only [F, abs_of_pos (sub_pos.mpr (ha j.property))]
  have hLs : Summable (fun j : {j : ℤ // j < n} => F j.val) := by
    convert hleft.1 using 1
    ext j
    simp only [F, abs_of_neg (sub_neg.mpr (ha j.property)), neg_sub]
  have hR := (hasSum_subtype_iff_indicator (f := F) (s := {j : ℤ | n < j})).mp hRs.hasSum
  have hL := (hasSum_subtype_iff_indicator (f := F) (s := {j : ℤ | j < n})).mp hLs.hasSum
  have hF : F = (fun j => {j : ℤ | n < j}.indicator F j + {j : ℤ | j < n}.indicator F j) := by
    funext j
    rcases lt_trichotomy j n with h | h | h
    · simp [Set.indicator, h, not_lt_of_ge h.le]
    · subst j
      simp [F, Real.zero_rpow (by linarith : (1:ℝ) - s ≠ 0)]
    · simp [Set.indicator, h, not_lt_of_ge h.le]
  have hsum : HasSum F ((∑' j : {j : ℤ // n < j}, F j.val) +
      (∑' j : {j : ℤ // j < n}, F j.val)) := by
    convert hR.add hL using 1
  refine ⟨hsum.summable, ?_⟩
  change (∑' j, F j) ≤ _
  rw [hsum.tsum_eq]
  have hRbound : (∑' j : {j : ℤ // n < j}, F j.val) ≤
      (1 + r) ^ (s - 1) * δ ^ (2 - s) / (s - 2) := by
    convert hright.2 using 1
    congr 1
    funext j
    simp only [F, abs_of_pos (sub_pos.mpr (ha j.property))]
  have hLbound : (∑' j : {j : ℤ // j < n}, F j.val) ≤
      r * ((1 + r) ^ (s - 1) * δ ^ (2 - s) / (s - 2)) := by
    convert hleft.2 using 1
    congr 1
    funext j
    simp only [F, abs_of_neg (sub_neg.mpr (ha j.property)), neg_sub]
  nlinarith

theorem inverse_power_second_moment {V : Type*}
    (C : V → V → ℝ) (hnonneg : ∀ x y, 0 ≤ C x y)
    (a g : V → ℝ) (K B : ℝ) (hK : 0 ≤ K) (hg : ∀ x, 0 ≤ g x)
    (hbound : ∀ x y, x ≠ y → C x y ≤ K * g x * g y * |a y - a x| ^ (-B - 1))
    (hainj : Function.Injective a) (x : V)
    (hsum : Summable (fun y => g y * |a y - a x| ^ (1 - B))) :
    Summable (fun y => C x y * (a x - a y)^2) ∧
    (∑' y, C x y * (a x - a y)^2) ≤
      K * g x * (∑' y, g y * |a y - a x| ^ (1 - B)) := by
  have hpoint (y : V) : C x y * (a x - a y)^2 ≤
      K * g x * (g y * |a y - a x| ^ (1 - B)) := by
    by_cases hxy : x = y
    · subst y
      simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
      exact mul_nonneg (mul_nonneg hK (hg x))
        (mul_nonneg (hg x) (Real.rpow_nonneg (abs_nonneg _) _))
    have hD : 0 < |a y - a x| := abs_pos.mpr (sub_ne_zero.mpr (fun h => hxy (hainj h).symm))
    have H := mul_le_mul_of_nonneg_right (hbound x y hxy) (sq_nonneg (a x - a y))
    have hid : |a y - a x| ^ (-B - 1) * (a x - a y)^2 = |a y - a x| ^ (1 - B) := by
      rw [show (a x - a y)^2 = |a y - a x|^2 by rw [sq_abs]; ring,
        ← Real.rpow_natCast, ← Real.rpow_add hD]
      congr 1
      norm_num
      ring
    calc
      _ ≤ (K * g x * g y * |a y - a x| ^ (-B - 1)) * (a x - a y)^2 := H
      _ = K * g x * g y * (|a y - a x| ^ (-B - 1) * (a x - a y)^2) := by
        exact mul_assoc (K * g x * g y) (|a y - a x| ^ (-B - 1)) ((a x - a y)^2)
      _ = _ := by rw [hid]; ring
  have hs := Summable.of_nonneg_of_le (fun y => mul_nonneg (hnonneg x y) (sq_nonneg _))
    hpoint (hsum.mul_left (K * g x))
  exact ⟨hs, (hs.tsum_le_tsum hpoint (hsum.mul_left (K * g x))).trans_eq tsum_mul_left⟩

end D5.S3.StatisticalMechanics.InversePowerLinePowerPacking
