/- GID: D5/S3/Weil/Mertens/ThirtyWheelSquarefree
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/ThirtyWheelSquarefree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Universal count and first-moment lower bounds for squarefree integers in the thirty-wheel. -/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace D5.S3.Weil.Mertens.ThirtyWheelSquarefree

/-- The literal squarefree thirty-wheel interval, including empty small intervals. -/
noncomputable def good (X : ℕ) : Finset ℕ := by
  classical
  exact (Icc 7 X).filter (fun d => Nat.Coprime d 30 ∧ Squarefree d)

private def wheel (X : ℕ) : Finset ℕ :=
  (range (X + 1)).filter (fun d => Nat.Coprime d 30)

private def U (X : ℕ) : ℚ := (wheel X).card
private def J (X : ℕ) : ℚ := ∑ d ∈ wheel X, (d : ℚ)

private lemma coprime_mod (n : ℕ) : n.Coprime 30 ↔ (n % 30).Coprime 30 := by
  have h := Nat.coprime_add_mul_left_left (n % 30) 30 (n / 30)
  simpa only [Nat.mod_add_div] using h

private lemma wheel_step (n : ℕ) (f : ℕ → ℚ) :
    (∑ d ∈ wheel (n+1), f d) = (∑ d ∈ wheel n, f d) +
      if (n+1).Coprime 30 then f (n+1) else 0 := by
  simp only [wheel, sum_filter, sum_range_succ]

private lemma U_step (n : ℕ) :
    U (n+1) = U n + if (n+1).Coprime 30 then 1 else 0 := by
  simpa [U] using wheel_step n (fun _ => 1)

private lemma J_step (n : ℕ) :
    J (n+1) = J n + if (n+1).Coprime 30 then (n+1 : ℕ) else 0 := by
  by_cases h : (n+1).Coprime 30
  · simpa only [J, if_pos h] using wheel_step n (fun d => (d : ℚ))
  · simpa only [J, if_neg h, Nat.cast_zero] using wheel_step n (fun d => (d : ℚ))

set_option maxHeartbeats 800000 in
-- The local budget covers expansion of the finite wheel at 29.
/-- The finite remainder data give exact formulas, rather than asymptotic densities. -/
private lemma wheel_exact (Y : ℕ) :
    U Y = 8 * (Y / 30 : ℕ) + U (Y % 30) ∧
    J Y = 120 * (Y / 30 : ℕ)^2 + 30 * (Y / 30 : ℕ) * U (Y % 30) + J (Y % 30) := by
  induction Y with
  | zero => norm_num [U, J, wheel]
  | succ n ih =>
    have hr : n % 30 < 30 := Nat.mod_lt _ (by decide)
    have hn := Nat.mod_add_div n 30
    by_cases h : n % 30 = 29
    · have hd : (n+1)/30 = n/30+1 := by omega
      have hm : (n+1)%30 = 0 := by omega
      have hc : ¬ (n+1).Coprime 30 := by rw [coprime_mod, hm]; decide
      rw [U_step, J_step, if_neg hc, if_neg hc, hd, hm, ih.1, ih.2, h]
      have hu29 : U 29 = 8 := by decide
      have hj29 : J 29 = 120 := by decide +kernel
      have hu0 : U 0 = 0 := by decide
      have hj0 : J 0 = 0 := by decide
      simp only [hu29, hj29, hu0, hj0]
      push_cast
      constructor <;> ring
    · have hd : (n+1)/30 = n/30 := by omega
      have hm : (n+1)%30 = n%30+1 := by omega
      have hc : (n+1).Coprime 30 ↔ (n%30+1).Coprime 30 := by rw [coprime_mod, hm]
      rw [U_step, J_step, hd, hm, U_step, J_step, ih.1, ih.2]
      by_cases hh : (n%30+1).Coprime 30
      · simp only [if_pos hh, if_pos (hc.mpr hh)]
        have he : (n : ℚ) = (n%30 : ℕ) + 30*(n/30 : ℕ) := by exact_mod_cast hn.symm
        push_cast
        constructor <;> nlinarith
      · constructor <;>
          simp only [if_neg hh, if_neg ((not_congr hc).mpr hh), Nat.cast_zero, add_zero]

set_option maxHeartbeats 800000 in
-- The local budget covers the thirty explicit finite-range calculations.
private lemma residue_certificate (r : ℕ) (hr : r < 30) :
    -10 ≤ 15 * U r - 4 * r ∧ 15 * U r - 4 * r ≤ 14 ∧
    0 ≤ 15 * J r - 2 * (r : ℚ)^2 + 10 * r ∧
    0 ≤ 2 * (r : ℚ)^2 + 16 * r - 15 * J r := by
  interval_cases r <;> decide +kernel

private lemma wheel_bounds (Y : ℕ) :
    (4 * (Y : ℚ) - 10)/15 ≤ U Y ∧ U Y ≤ (4 * Y + 14)/15 ∧
    (2 * (Y : ℚ)^2 - 10 * Y)/15 ≤ J Y ∧ J Y ≤ (2 * (Y : ℚ)^2 + 16 * Y)/15 := by
  obtain ⟨hc, hj⟩ := wheel_exact Y
  obtain ⟨hlo, hhi, hjlo, hjhi⟩ := residue_certificate (Y%30) (Nat.mod_lt _ (by decide))
  have he : (Y : ℚ) = (Y%30 : ℕ) + 30*(Y/30 : ℕ) := by exact_mod_cast (Nat.mod_add_div Y 30).symm
  have hm : (0 : ℚ) ≤ (Y/30 : ℕ) := Nat.cast_nonneg _
  have hml := mul_nonneg hm (show 0 ≤ 15 * U (Y%30) - 4 * (Y%30 : ℕ) + 10 by linarith)
  have hmu := mul_nonneg hm (show 0 ≤ 16 - (15 * U (Y%30) - 4 * (Y%30 : ℕ)) by linarith)
  rw [hc, hj, he]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> nlinarith

private def bases : Finset ℕ := {7,11,13,17,19,23,29,31}
private def indices (K : ℕ) : Finset ℕ := (Icc 7 K).filter (fun k => k.Coprime 30)

private lemma wheel_representation {k : ℕ} (hk : 7 ≤ k) (hc : k.Coprime 30) :
    ∃ b ∈ bases, ∃ t ≤ k, k = b + 30*t := by
  let r := (k-7)%30
  let t := (k-7)/30
  have hr : r < 30 := Nat.mod_lt _ (by decide)
  have he : k = (r+7) + 30*t := by
    have := Nat.mod_add_div (k-7) 30
    dsimp [r, t]
    omega
  have hb : (r+7).Coprime 30 := by
    rw [he, Nat.coprime_add_mul_left_left] at hc
    exact hc
  refine ⟨r+7, ?_, t, Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _), he⟩
  interval_cases r <;> norm_num at hb
  all_goals norm_num [bases]

private lemma reciprocal_step (a : ℚ) (ha : 0 < a) :
    1/(a+30)^2 ≤ 1/(30*a) - 1/(30*(a+30)) := by
  have ha30 : 0 < a+30 := by linarith
  have he : 1/(30*a) - 1/(30*(a+30)) = 1/(a*(a+30)) := by
    field_simp [ne_of_gt ha, ne_of_gt ha30]
    ring
  rw [he]
  exact one_div_le_one_div_of_le (mul_pos ha ha30) (by nlinarith)

private lemma reciprocal_tail (b n : ℕ) :
    (∑ t ∈ range n, (1 : ℚ) / (b+60+30*t : ℕ)^2) ≤
      1/(30*((b:ℚ)+30)) - 1/(30*((b:ℚ)+30+30*n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h := reciprocal_step ((b:ℚ)+30+30*n) (by positivity)
    have he : ((b+60+30*n : ℕ):ℚ) = ((b:ℚ)+30+30*n)+30 := by push_cast; ring
    rw [he]
    push_cast at ih h ⊢
    have he2 : (b:ℚ)+30+30*((n:ℚ)+1) = ((b:ℚ)+30+30*n)+30 := by ring
    rw [he2]
    linarith

private lemma progression_bound (b n : ℕ) :
    (∑ t ∈ range n, (1 : ℚ)/(b+30*t : ℕ)^2) ≤
      1/(b:ℚ)^2 + 1/((b:ℚ)+30)^2 + 1/(30*((b:ℚ)+30)) := by
  have hsub : range n ⊆ range (n+2) := range_mono (by omega)
  calc
    _ ≤ ∑ t ∈ range (n+2), (1 : ℚ)/(b+30*t : ℕ)^2 :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = 1/(b:ℚ)^2 + 1/((b:ℚ)+30)^2 +
        ∑ t ∈ range n, (1 : ℚ)/(b+60+30*t : ℕ)^2 := by
      rw [show n+2 = 2+n by omega, sum_range_add]
      norm_num [sum_range_succ]
      congr 1
      funext t
      congr 2
      ring
    _ ≤ _ := by
      have := reciprocal_tail b n
      have : 0 ≤ (1 : ℚ)/(30*((b:ℚ)+30+30*n)) := by positivity
      linarith [reciprocal_tail b n]

private lemma reciprocal_bound (K : ℕ) :
    (∑ k ∈ indices K, (1 : ℚ)/(k:ℚ)^2) < 1/18 := by
  let rectangle := bases ×ˢ range (K+1)
  let value : ℕ × ℕ → ℕ := fun p => p.1 + 30*p.2
  have hsub : indices K ⊆ rectangle.image value := by
    intro k hk
    obtain ⟨hi, hc⟩ := mem_filter.mp hk
    obtain ⟨b, hb, t, ht, he⟩ := wheel_representation (mem_Icc.mp hi).1 hc
    exact mem_image.mpr ⟨(b,t), mem_product.mpr
      ⟨hb, mem_range.mpr (by have := (mem_Icc.mp hi).2; omega)⟩, he.symm⟩
  calc
    _ ≤ ∑ k ∈ rectangle.image value, (1 : ℚ)/(k:ℚ)^2 :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ ∑ p ∈ rectangle, (1 : ℚ)/(value p : ℚ)^2 :=
      sum_image_le_of_nonneg (by intros; positivity)
    _ = ∑ b ∈ bases, ∑ t ∈ range (K+1), (1 : ℚ)/(b+30*t : ℕ)^2 := by
      rw [sum_product]
    _ ≤ ∑ b ∈ bases, (1/(b:ℚ)^2 + 1/((b:ℚ)+30)^2 + 1/(30*((b:ℚ)+30))) := by
      apply sum_le_sum
      intro b hb
      exact progression_bound b (K+1)
    _ < 1/18 := by norm_num [bases]

private lemma small_unit {d : ℕ} (hd : d < 7) (hc : d.Coprime 30) : d = 1 := by
  interval_cases d <;> norm_num at hc
  all_goals norm_num

private lemma wheel_split (K : ℕ) (hK : 1 ≤ K) :
    wheel K = insert 1 (indices K) := by
  ext d
  simp only [wheel, indices, mem_filter, mem_range, mem_insert, mem_Icc]
  constructor
  · rintro ⟨hd, hc⟩
    by_cases h : d < 7
    · exact Or.inl (small_unit h hc)
    · exact Or.inr ⟨⟨by omega, by omega⟩, hc⟩
  · rintro (rfl | ⟨⟨hd, hdK⟩, hc⟩)
    · exact ⟨by omega, by decide⟩
    · exact ⟨by omega, hc⟩

private lemma indices_card (K : ℕ) (hK : 1 ≤ K) :
    ((indices K).card : ℚ) ≤ (4*(K:ℚ)-1)/15 := by
  have hn : 1 ∉ indices K := by simp [indices]
  have he : U K = 1 + ((indices K).card : ℚ) := by
    rw [U, wheel_split K hK, card_insert_of_notMem hn]
    push_cast
    ring
  linarith [(wheel_bounds K).2.1]

private noncomputable def bad (X : ℕ) : Finset ℕ := by
  classical
  exact (wheel X).filter (fun d => ¬ Squarefree d)

private def multiples (X k : ℕ) : Finset ℕ := (wheel X).filter (fun d => k*k ∣ d)

private lemma prime_square_cover (X d : ℕ) (hd : d ∈ bad X) :
    ∃ k ∈ indices (Nat.sqrt X), k*k ∣ d := by
  classical
  obtain ⟨hw, hns⟩ := mem_filter.mp hd
  obtain ⟨hdX, hc⟩ := mem_filter.mp hw
  have hdpos : 0 < d := by
    by_contra h
    have hz : d=0 := by omega
    subst d
    norm_num at hc
  have hn := mt Nat.squarefree_iff_prime_squarefree.mpr hns
  push Not at hn
  obtain ⟨p, hp, hpd⟩ := hn
  have hpc : p.Coprime 30 := hc.of_dvd_left (dvd_trans (dvd_mul_right p p) hpd)
  have hp7 : 7 ≤ p := by
    by_contra h
    have he := small_unit (by omega : p < 7) hpc
    exact hp.ne_one he
  refine ⟨p, mem_filter.mpr ⟨mem_Icc.mpr ⟨hp7, ?_⟩, hpc⟩, hpd⟩
  apply Nat.le_sqrt.mpr
  exact (Nat.le_of_dvd hdpos hpd).trans (by simpa only [mem_range, Nat.lt_succ_iff] using hdX)

/-- The same finite, nonnegative union argument applies to count and first moment. -/
private lemma bad_union (X : ℕ) (f : ℕ → ℚ) (hf : ∀ d, 0 ≤ f d) :
    (∑ d ∈ bad X, f d) ≤
      ∑ k ∈ indices (Nat.sqrt X), ∑ d ∈ multiples X k, f d := by
  classical
  calc
    _ = ∑ d ∈ wheel X, if ¬ Squarefree d then f d else 0 := by
      simp [bad, sum_filter]
    _ ≤ ∑ d ∈ wheel X, ∑ k ∈ indices (Nat.sqrt X), if k*k ∣ d then f d else 0 := by
      apply sum_le_sum
      intro d hd
      by_cases hs : Squarefree d
      · simp only [not_not.mpr hs, if_false]
        exact sum_nonneg (by
          intro k hk
          split_ifs
          · exact hf d
          · exact le_rfl)
      · obtain ⟨k, hk, hkd⟩ := prime_square_cover X d (mem_filter.mpr ⟨hd, hs⟩)
        simp only [hs, not_false_eq_true, if_true]
        have h := single_le_sum (s := indices (Nat.sqrt X))
          (f := fun k => if k*k ∣ d then f d else 0)
          (by
            intro k hk
            split_ifs
            · exact hf d
            · exact le_rfl) hk
        simpa only [if_pos hkd] using h
    _ = _ := by rw [sum_comm]; simp only [multiples, sum_filter]

private lemma multiples_sum (X k : ℕ) (hk : 0 < k) (hc : k.Coprime 30) (f : ℕ → ℚ) :
    (∑ d ∈ multiples X k, f d) = ∑ t ∈ wheel (X/(k*k)), f (k*k*t) := by
  have hkk : 0 < k*k := Nat.mul_pos hk hk
  symm
  apply sum_bij (fun t _ => k*k*t)
  · intro t ht
    obtain ⟨htX, htc⟩ := mem_filter.mp ht
    have htle : t ≤ X/(k*k) := by simpa only [mem_range, Nat.lt_succ_iff] using htX
    have hle : k*k*t ≤ X := by
      have h := (Nat.le_div_iff_mul_le hkk).mp htle
      simpa [mul_comm] using h
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, dvd_mul_right _ _⟩
    exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_mul_iff_left.mpr ⟨hc,hc⟩,htc⟩
  · intro a ha b hb he
    exact Nat.eq_of_mul_eq_mul_left hkk he
  · intro d hd
    obtain ⟨hw, hdvd⟩ := mem_filter.mp hd
    obtain ⟨hdX, hdc⟩ := mem_filter.mp hw
    have hle : d ≤ X := by simpa only [mem_range, Nat.lt_succ_iff] using hdX
    refine ⟨d/(k*k), mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩, Nat.mul_div_cancel' hdvd⟩
    · have := Nat.div_le_div_right (c := k*k) hle
      omega
    · exact hdc.of_dvd_left (Nat.div_dvd_of_dvd hdvd)
  · intro t ht
    rfl

private lemma square_multiple_bounds (X k : ℕ) (hk : 0 < k) :
    U (X/(k*k)) ≤ (4*(X:ℚ)/15)*(1/(k:ℚ)^2)+14/15 ∧
    (k:ℚ)^2 * J (X/(k*k)) ≤ (2*(X:ℚ)^2/15)*(1/(k:ℚ)^2)+16*(X:ℚ)/15 := by
  let a : ℚ := (k:ℚ)^2
  let y : ℚ := (X/(k*k) : ℕ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hy : 0 ≤ y := Nat.cast_nonneg _
  have hx : 0 ≤ (X:ℚ) := Nat.cast_nonneg _
  have hfloor : a*y ≤ X := by
    have h : ((X/(k*k):ℕ):ℚ) * ((k:ℚ)*(k:ℚ)) ≤ (X:ℚ) := by
      exact_mod_cast Nat.div_mul_le_self X (k*k)
    dsimp [a,y]
    nlinarith
  have hquad : (a*y)^2 ≤ (X:ℚ)^2 := by
    have h := mul_nonneg (sub_nonneg.mpr hfloor) (show 0 ≤ (X:ℚ)+a*y by positivity)
    nlinarith
  obtain ⟨_, hu, _, hj⟩ := wheel_bounds (X/(k*k))
  change U (X/(k*k)) ≤ (4*(X:ℚ)/15)*(1/a)+14/15 ∧
    a * J (X/(k*k)) ≤ (2*(X:ℚ)^2/15)*(1/a)+16*(X:ℚ)/15
  constructor
  · rw [show (4*(X:ℚ)/15)*(1/a)+14/15 = (4*(X:ℚ)/15+(14/15)*a)/a by
      field_simp [ne_of_gt ha]]
    apply (le_div_iff₀ ha).mpr
    have h := mul_le_mul_of_nonneg_left hu ha.le
    change a * U (X/(k*k)) ≤ a * ((4*y+14)/15) at h
    nlinarith
  · rw [show (2*(X:ℚ)^2/15)*(1/a)+16*(X:ℚ)/15 =
        (2*(X:ℚ)^2/15+(16*(X:ℚ)/15)*a)/a by field_simp [ne_of_gt ha]]
    apply (le_div_iff₀ ha).mpr
    have h := mul_le_mul_of_nonneg_left hj (sq_nonneg a)
    change a^2 * J (X/(k*k)) ≤ a^2 * ((2*y^2+16*y)/15) at h
    have hh := mul_le_mul_of_nonneg_left hfloor ha.le
    nlinarith

private lemma bad_bounds (X : ℕ) (hX : 1 ≤ X) :
    ((bad X).card : ℚ) ≤ 2*(X:ℚ)/135 + 56*(Nat.sqrt X : ℚ)/225 - 14/225 ∧
    (∑ d ∈ bad X, (d:ℚ)) ≤ (X:ℚ)^2/135 + 64*(X:ℚ)*Nat.sqrt X/225 - 16*(X:ℚ)/225 := by
  classical
  let A := indices (Nat.sqrt X)
  let R : ℚ := ∑ k ∈ A, (1:ℚ)/(k:ℚ)^2
  have hR : R ≤ 1/18 := (reciprocal_bound (Nat.sqrt X)).le
  have hK : 1 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by simpa using hX)
  have hA : (A.card : ℚ) ≤ (4*(Nat.sqrt X:ℚ)-1)/15 := indices_card _ hK
  have hcount : ((bad X).card : ℚ) ≤ (4*(X:ℚ)/15)*R+(14/15)*(A.card:ℚ) := by
    calc
      _ = ∑ d ∈ bad X, (1:ℚ) := by simp
      _ ≤ ∑ k ∈ A, ∑ d ∈ multiples X k, (1:ℚ) := bad_union X _ (by intro; norm_num)
      _ = ∑ k ∈ A, U (X/(k*k)) := by
        apply sum_congr rfl
        intro k hk
        obtain ⟨hi, hc⟩ := mem_filter.mp hk
        have hpos : 0 < k := by have := (mem_Icc.mp hi).1; omega
        simpa [U] using multiples_sum X k hpos hc (fun _ => 1)
      _ ≤ ∑ k ∈ A, ((4*(X:ℚ)/15)*(1/(k:ℚ)^2)+14/15) := by
        apply sum_le_sum
        intro k hk
        exact (square_multiple_bounds X k (by have := (mem_Icc.mp (mem_filter.mp hk).1).1; omega)).1
      _ = _ := by
        simp [R, sum_add_distrib, mul_sum]
        ring
  have hweight : (∑ d ∈ bad X, (d:ℚ)) ≤ (2*(X:ℚ)^2/15)*R+(16*(X:ℚ)/15)*(A.card:ℚ) := by
    calc
      _ ≤ ∑ k ∈ A, ∑ d ∈ multiples X k, (d:ℚ) := bad_union X _ (fun _ => Nat.cast_nonneg _)
      _ = ∑ k ∈ A, (k:ℚ)^2 * J (X/(k*k)) := by
        apply sum_congr rfl
        intro k hk
        obtain ⟨hi, hc⟩ := mem_filter.mp hk
        have hpos : 0 < k := by have := (mem_Icc.mp hi).1; omega
        rw [multiples_sum X k hpos hc]
        simp [J, pow_two, mul_sum, Nat.cast_mul, mul_assoc]
      _ ≤ ∑ k ∈ A, ((2*(X:ℚ)^2/15)*(1/(k:ℚ)^2)+16*(X:ℚ)/15) := by
        apply sum_le_sum
        intro k hk
        exact (square_multiple_bounds X k (by have := (mem_Icc.mp (mem_filter.mp hk).1).1; omega)).2
      _ = _ := by
        simp [R, sum_add_distrib, mul_sum]
        ring
  constructor
  · have hr := mul_le_mul_of_nonneg_left hR (show 0 ≤ 4*(X:ℚ)/15 by positivity)
    have hc := mul_le_mul_of_nonneg_left hA (show (0:ℚ) ≤ 14/15 by norm_num)
    linarith
  · have hr := mul_le_mul_of_nonneg_left hR (show 0 ≤ 2*(X:ℚ)^2/15 by positivity)
    have hc := mul_le_mul_of_nonneg_left hA (show 0 ≤ 16*(X:ℚ)/15 by positivity)
    nlinarith

private lemma good_bad_split (X : ℕ) (hX : 1 ≤ X) (f : ℕ → ℚ) :
    (∑ d ∈ wheel X, f d) = f 1 + (∑ d ∈ good X, f d) + ∑ d ∈ bad X, f d := by
  classical
  have hs : (wheel X).filter Squarefree = insert 1 (good X) := by
    ext d
    simp only [wheel, good, mem_filter, mem_range, mem_insert, mem_Icc]
    constructor
    · rintro ⟨⟨hd, hc⟩, hsq⟩
      by_cases h : d < 7
      · exact Or.inl (small_unit h hc)
      · exact Or.inr ⟨⟨by omega, by omega⟩,hc,hsq⟩
    · rintro (rfl | ⟨⟨hd, hdX⟩,hc,hsq⟩)
      · exact ⟨⟨by omega,by decide⟩,squarefree_one⟩
      · exact ⟨⟨by omega,hc⟩,hsq⟩
  have hn : 1 ∉ good X := by simp [good]
  simpa only [bad, hs, sum_insert hn] using
    (sum_filter_add_sum_filter_not (wheel X) Squarefree f).symm

/-- Both estimates hold for every natural cutoff; every subtraction is rational. -/
theorem count_weight_lower_bound (X : ℕ) :
    (170*(X:ℚ) - 168*(Nat.sqrt X:ℚ) - 1083)/675 ≤ ((good X).card:ℚ) ∧
    (85*(X:ℚ)^2 - 192*(X:ℚ)*Nat.sqrt X - 402*(X:ℚ) - 675)/675 ≤
      ∑ d ∈ good X, (d:ℚ) := by
  classical
  by_cases hz : X = 0
  · subst X
    norm_num [good]
  have hX : 1 ≤ X := by omega
  obtain ⟨hB,hE⟩ := bad_bounds X hX
  obtain ⟨hU,_,hJ,_⟩ := wheel_bounds X
  have hc := good_bad_split X hX (fun _ => 1)
  have hw := good_bad_split X hX (fun d => (d:ℚ))
  have hc' : U X = 1 + ((good X).card:ℚ) + ((bad X).card:ℚ) := by simpa [U] using hc
  change J X = (1:ℚ) + (∑ d ∈ good X, (d:ℚ)) + ∑ d ∈ bad X, (d:ℚ) at hw
  constructor <;> nlinarith

#print axioms count_weight_lower_bound

end D5.S3.Weil.Mertens.ThirtyWheelSquarefree
