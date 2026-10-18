/- GID: D5/S3/Estimation/DataProcessing/FiniteIidStrictPeakLower
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/FiniteIidStrictPeakLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite independent strict peaks have a sharp determinant lower surface. -/

import D5.S3.Estimation.DataProcessing.IidStrictPeakSource
import D5.S3.Estimation.DataProcessing.StrictPeakAnalyticLower

set_option autoImplicit false
namespace D5.S3.Estimation.DataProcessing.FiniteIidStrictPeakLower
open scoped BigOperators
open MeasureTheory Set
open IidStrictPeakSource StrictPeakAnalyticLower
noncomputable section
local instance propDecidable (P : Prop) : Decidable P := Classical.propDecidable P
variable {A : Type*} [Fintype A] [LinearOrder A]

/-- Tail on the uniform quantile coordinate, independently anchored in the letter law. -/
def tail (p : A → ℝ) (u : ℝ) : ℝ :=
  ∑ i, (Iic (lowerMass p i)).indicator (fun _ => p i * lowerMass p i) u

private theorem lower_nonneg (p : A → ℝ) (hp : ∀ i, 0 ≤ p i) (i : A) :
    0 ≤ lowerMass p i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hp j
  · norm_num

private theorem lower_mono (p : A → ℝ) (hp : ∀ i, 0 ≤ p i) : Monotone (lowerMass p) := by
  intro i j hij
  apply Finset.sum_le_sum
  intro k _
  by_cases hki : k < i
  · simp [hki, lt_of_lt_of_le hki hij]
  · simp only [if_neg hki]
    split_ifs
    · exact hp k
    · norm_num

private theorem lower_le_total (p : A → ℝ) (hp : ∀ i, 0 ≤ p i) (i : A) :
    lowerMass p i ≤ ∑ j, p j := by
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_rfl
  · exact hp j

private theorem triangle_square (p : A → ℝ) :
    (∑ i, p i)^2 = 2*(∑ j, p j * lowerMass p j) + ∑ i, p i^2 := by
  have point (i j : A) : p j*p i =
      (if i < j then p j*p i else 0) + (if j < i then p i*p j else 0) +
        (if i = j then p j^2 else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le, ne_of_lt h]
    · subst j; simp; ring
    · simp [h, not_lt.mpr h.le, ne_of_gt h, mul_comm]
  have he : (∑ i, p i)^2 = ∑ j, ∑ i, p j*p i := by
    simp [pow_two, Finset.mul_sum, Finset.sum_mul, mul_comm]
  have he' : (∑ j, ∑ i, p j*p i) = ∑ j, ∑ i,
      ((if i < j then p j*p i else 0) + (if j < i then p i*p j else 0) +
        (if i = j then p j^2 else 0)) := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    exact point i j
  rw [he,he']
  simp only [Finset.sum_add_distrib]
  have swap : (∑ j, ∑ i, if j < i then p i*p j else 0) =
      ∑ j, ∑ i, if i < j then p j*p i else 0 := Finset.sum_comm
  rw [swap]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hL : (∑ j, p j*lowerMass p j) =
      ∑ j, ∑ i, if i < j then p j*p i else 0 := by
    simp only [lowerMass,Finset.mul_sum,mul_ite,mul_zero]
  rw [hL]
  ring

private theorem suffix_bound (p : A → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (b : A) :
    2*(∑ j, if b ≤ j then p j*lowerMass p j else 0) ≤ 1-(lowerMass p b)^2 := by
  let r := fun i => if b ≤ i then p i else 0
  have hpoint (i : A) : r i + (if i < b then p i else 0) = p i := by
    by_cases hi : b ≤ i
    · simp [r,hi,not_lt.mpr hi]
    · simp [r,hi,lt_of_not_ge hi]
  have htotal : (∑ i, r i)+lowerMass p b = 1 := by
    unfold lowerMass
    rw [← Finset.sum_add_distrib]
    simpa only [hpoint] using hs
  have hlower (j : A) (hbj : b ≤ j) :
      lowerMass p j = lowerMass p b + lowerMass r j := by
    unfold lowerMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i < b
    · simp [hi,lt_of_lt_of_le hi hbj,r,not_le.mpr hi]
    · simp [hi,r,le_of_not_gt hi]
  have htail : (∑ j, if b ≤ j then p j*lowerMass p j else 0) =
      lowerMass p b*(∑ j, r j)+(∑ j, r j*lowerMass r j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : b ≤ j
    · rw [if_pos hj,hlower j hj]
      dsimp [r]
      rw [if_pos hj]
      ring
    · simp [r,hj]
  have hsquare := triangle_square r
  have hdiag : 0 ≤ ∑ i, r i^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [htail]
  nlinarith [sq_nonneg (lowerMass p b)]

private theorem tail_bounds (p : A → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ tail p u ∧ tail p u ≤ cap u := by
  have hn : 0 ≤ tail p u := by
    unfold tail
    apply Finset.sum_nonneg
    intro i _
    exact indicator_nonneg (fun _ _ => mul_nonneg (hp i) (lower_nonneg p hp i)) _
  refine ⟨hn,?_⟩
  by_cases h : ∃ i, u ≤ lowerMass p i
  · let S := Finset.univ.filter (fun i => u ≤ lowerMass p i)
    have hS : S.Nonempty := by
      obtain ⟨i,hi⟩ := h
      exact ⟨i,by simp [S,hi]⟩
    let b := S.min' hS
    have hb : u ≤ lowerMass p b := by
      have := Finset.min'_mem S hS
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using this
    have hcut (i : A) : u ≤ lowerMass p i ↔ b ≤ i := by
      constructor
      · intro hi
        exact Finset.min'_le S i (by simp [S,hi])
      · intro hi
        exact hb.trans (lower_mono p hp hi)
    have ht : tail p u = ∑ j, if b ≤ j then p j*lowerMass p j else 0 := by
      unfold tail
      apply Finset.sum_congr rfl
      intro i _
      simp only [indicator_apply,mem_Iic,hcut]
    have hm := suffix_bound p hp hs b
    rw [← ht] at hm
    have hsq : u^2 ≤ (lowerMass p b)^2 := pow_le_pow_left₀ hu.1 hb 2
    unfold cap
    linarith
  · have ht : tail p u = 0 := by
      unfold tail
      apply Finset.sum_eq_zero
      intro i _
      simp only [indicator_apply,mem_Iic]
      rw [if_neg (fun hi => h ⟨i,hi⟩)]
    rw [ht]
    unfold cap
    have : u^2 ≤ 1 := by nlinarith [hu.1,hu.2,sq_nonneg (1-u)]
    linarith

private theorem indicator_integrable (t k : ℝ) :
    IntervalIntegrable ((Iic t).indicator (fun _ : ℝ => k)) volume 0 1 := by
  have hc : IntervalIntegrable (fun _ : ℝ => k) volume 0 1 := intervalIntegrable_const
  exact ⟨hc.1.indicator measurableSet_Iic, hc.2.indicator measurableSet_Iic⟩

private theorem indicator_integral (t k : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ u in (0 : ℝ)..1, (Iic t).indicator (fun _ => k) u) = k*t := by
  change (∫ u in (0 : ℝ)..1, ({x : ℝ | x ≤ t}).indicator (fun _ => k) u) = _
  rw [intervalIntegral.integral_indicator ht, intervalIntegral.integral_const]
  simp
  ring

private theorem tail_as_sum (p : A → ℝ) : tail p =
    ∑ i, (Iic (lowerMass p i)).indicator (fun _ : ℝ => p i*lowerMass p i) := by
  funext u
  simp [tail]

private theorem tail_integrable (p : A → ℝ) : IntervalIntegrable (tail p) volume 0 1 := by
  rw [tail_as_sum]
  apply IntervalIntegrable.sum
  intro i _
  exact indicator_integrable _ _

private theorem lower_min (p : A → ℝ) (hp : ∀ i, 0 ≤ p i) (i j : A) :
    lowerMass p (min i j) = min (lowerMass p i) (lowerMass p j) := by
  rcases le_total i j with h | h
  · rw [min_eq_left h,min_eq_left (lower_mono p hp h)]
  · rw [min_eq_right h,min_eq_right (lower_mono p hp h)]

private theorem tail_first_moment (p : A → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) :
    (∫ u in (0 : ℝ)..1, tail p u) = ∑ i, p i * lowerMass p i ^ 2 := by
  rw [tail_as_sum]
  simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [indicator_integral _ _ ⟨lower_nonneg p hp i, (lower_le_total p hp i).trans_eq hs⟩]
    ring
  · intro i _
    exact indicator_integrable _ _

private theorem tail_square_sum (p : A → ℝ) : (fun u => tail p u ^ 2) =
    ∑ i, ∑ j, (Iic (min (lowerMass p i) (lowerMass p j))).indicator
      (fun _ : ℝ => (p i*lowerMass p i)*(p j*lowerMass p j)) := by
  funext u
  simp only [tail, pow_two, Finset.sum_mul_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [indicator_apply,mem_Iic,le_min_iff]
  by_cases hi : u ≤ lowerMass p i <;> by_cases hj : u ≤ lowerMass p j <;> simp [hi,hj]

private theorem tail_square_integrable (p : A → ℝ) :
    IntervalIntegrable (fun u => tail p u ^ 2) volume 0 1 := by
  rw [tail_square_sum]
  apply IntervalIntegrable.sum
  intro i _
  apply IntervalIntegrable.sum
  intro j _
  exact indicator_integrable _ _

private theorem valley_expansion (p : A → ℝ) :
    (∑ c, p c*wingMass p c ^ 2) =
      ∑ i, ∑ j, ((p i*lowerMass p i)*(p j*lowerMass p j))*lowerMass p (min i j) := by
  have he : (∑ c, p c*wingMass p c ^ 2) = ∑ c, ∑ i, ∑ j,
      p c*((if c < i then p i*lowerMass p i else 0)*
        (if c < j then p j*lowerMass p j else 0)) := by
    simp only [wingMass,pow_two,Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
  rw [he,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ c, _) = ((p i*lowerMass p i)*(p j*lowerMass p j))*
    (∑ c, if c < min i j then p c else 0)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp only [lt_min_iff]
  by_cases hi : c < i <;> by_cases hj : c < j <;> simp [hi,hj] <;> ring

private theorem tail_second_moment (p : A → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) :
    (∫ u in (0 : ℝ)..1, tail p u ^ 2) = ∑ c, p c*wingMass p c ^ 2 := by
  have heval : (fun u => tail p u ^ 2) = fun u =>
      ∑ i, ∑ j, (Iic (min (lowerMass p i) (lowerMass p j))).indicator
        (fun _ : ℝ => (p i*lowerMass p i)*(p j*lowerMass p j)) u := by
    rw [tail_square_sum]
    funext u
    simp
  rw [heval, intervalIntegral.integral_finsetSum]
  · rw [valley_expansion]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      have hi := (lower_le_total p hp i).trans_eq hs
      have hj := (lower_le_total p hp j).trans_eq hs
      rw [indicator_integral _ _ ⟨le_min (lower_nonneg p hp i) (lower_nonneg p hp j),
        (min_le_left _ _).trans hi⟩, lower_min p hp]
    · intro j _
      exact indicator_integrable _ _
  · intro i _
    have hi := IntervalIntegrable.sum Finset.univ (fun j (_ : j ∈ Finset.univ) =>
      indicator_integrable (min (lowerMass p i) (lowerMass p j))
        ((p i*lowerMass p i)*(p j*lowerMass p j)))
    convert hi using 1
    funext u
    simp


private theorem positive_letter (p : A → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) : ∃ i, 0 < p i := by
  by_contra h
  push_neg at h
  have hz : ∀ i, p i = 0 := fun i => le_antisymm (h i) (hp i)
  simp [hz] at hs

private theorem strict_first_moment (p : A → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) : (∫ u in (0 : ℝ)..1, tail p u) < 1/3 := by
  let S := Finset.univ.filter (fun i => 0 < p i)
  have hS : S.Nonempty := by
    obtain ⟨i,hi⟩ := positive_letter p hp hs
    exact ⟨i,by simp [S,hi]⟩
  let b := S.max' hS
  have hb : 0 < p b := by
    have := Finset.max'_mem S hS
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using this
  have himax (i : A) (hi : p i ≠ 0) : i ≤ b := by
    exact Finset.le_max' S i (by simp [S,lt_of_le_of_ne (hp i) (Ne.symm hi)])
  let t := lowerMass p b
  have ht0 : 0 ≤ t := lower_nonneg p hp b
  have ht1 : t < 1 := by
    have hplus : lowerMass p b+p b ≤ ∑ i, p i := by
      have he : p b = ∑ i, if i = b then p i else 0 := by simp
      rw [he,lowerMass,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i = b
      · subst i; simp
      · by_cases hlt : i < b <;> simp [hi,hlt,hp i]
    linarith [hplus,hs]
  have hzero (u : ℝ) (hu : t < u) : tail p u = 0 := by
    unfold tail
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : p i = 0
    · simp [hi]
    · have hlow : lowerMass p i ≤ t := lower_mono p hp (himax i hi)
      exact indicator_of_notMem (not_le.mpr (hlow.trans_lt hu)) _
  have htint : (∫ u in t..(1 : ℝ), tail p u) = 0 := by
    calc
      _ = ∫ u in t..(1 : ℝ), (0 : ℝ) :=
        intervalIntegral.integral_congr_Ioo_of_le ht1.le (fun u hu => hzero u hu.1)
      _ = 0 := by simp
  have hcapc : Continuous cap := by unfold cap; fun_prop
  have hcapPos : 0 < ∫ u in t..(1 : ℝ), cap u := by
    apply intervalIntegral.integral_pos ht1 hcapc.continuousOn
    · intro u hu
      unfold cap
      have hu0 : 0 ≤ u := ht0.trans hu.1.le
      have hu1 : u ≤ 1 := hu.2
      nlinarith [sq_nonneg (1-u)]
    · refine ⟨(t+1)/2,⟨by linarith,by linarith⟩,?_⟩
      unfold cap
      have hprod : 0 < (1-(t+1)/2)*(1+(t+1)/2) :=
        mul_pos (by linarith) (by linarith)
      nlinarith
  have hsubset : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le ht0,uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl ht1.le
  have hsubset' : uIcc t (1 : ℝ) ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le ht1.le,uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc ht0 le_rfl
  have hle : (∫ u in (0 : ℝ)..t, tail p u) ≤ ∫ u in (0 : ℝ)..t, cap u := by
    apply intervalIntegral.integral_mono_on ht0 ((tail_integrable p).mono_set hsubset)
      (hcapc.intervalIntegrable _ _)
    intro u hu
    exact (tail_bounds p hp hs u ⟨hu.1,hu.2.trans ht1.le⟩).2
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    ((tail_integrable p).mono_set hsubset) ((tail_integrable p).mono_set hsubset')
  have hcadj := intervalIntegral.integral_add_adjacent_intervals
    (hcapc.intervalIntegrable (μ := volume) 0 t) (hcapc.intervalIntegrable (μ := volume) t 1)
  rw [htint] at hadj
  rw [cap_integral] at hcadj
  linarith

private theorem zero_peak_iff_dirac (p : A → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) :
    (∑ i, p i*lowerMass p i ^ 2) = 0 ↔
      ∃ i, p i = 1 ∧ ∀ j, j ≠ i → p j = 0 := by
  have hlow (a b : A) (hab : a < b) : p a ≤ lowerMass p b := by
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => if j < b then p j else 0)
      (fun j _ => by split_ifs; exact hp j; norm_num) (Finset.mem_univ a)
    simpa only [if_pos hab,lowerMass] using hh
  constructor
  · intro hz
    obtain ⟨i,hi⟩ := positive_letter p hp hs
    have hterm (j : A) : p j*lowerMass p j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hp j) (sq_nonneg _))).mp hz j
        (Finset.mem_univ j)
    have hother (j : A) (hji : j ≠ i) : p j = 0 := by
      by_contra hj0
      have hj : 0 < p j := lt_of_le_of_ne (hp j) (Ne.symm hj0)
      rcases lt_or_gt_of_ne hji with h | h
      · have hl : 0 < lowerMass p i := hj.trans_le (hlow j i h)
        exact (ne_of_gt (mul_pos hi (pow_pos hl 2))) (hterm i)
      · have hl : 0 < lowerMass p j := hi.trans_le (hlow i j h)
        exact (ne_of_gt (mul_pos hj (pow_pos hl 2))) (hterm j)
    refine ⟨i,?_,hother⟩
    have he : (∑ j, p j) = p i := by
      apply Finset.sum_eq_single i
      · intro j _ hj; exact hother j hj
      · simp
    linarith
  · rintro ⟨i,hi,hother⟩
    apply Finset.sum_eq_zero
    intro j _
    by_cases hji : j = i
    · subst j
      have he : lowerMass p i = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        by_cases hai : a = i
        · subst a; simp
        · simp [hother a hai]
      simp [he]
    · simp [hother j hji]

/-- The complete refined lower bound and equality criterion for every finite
ordered source, with its determinant taken from the actual five-mode law. -/
theorem finite_iid_lower_surface (p : A → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) :
    let X := modeLaw p 1 + modeLaw p 3
    let D := modeLaw p 0*modeLaw p 3-modeLaw p 1*modeLaw p 2
    0 ≤ X ∧ X < 1/3 ∧
    (X = 0 ↔ ∃ i, p i = 1 ∧ ∀ j, j ≠ i → p j = 0) ∧
    (∃ s ∈ Icc (0 : ℝ) 1, s^3 = 1-3*X ∧
      s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4) ≤ D+X/15 ∧
      0 ≤ s^3/45*(1-s)*(1+s+7*s^2-3*s^3-3*s^4)) ∧
    -X/15 ≤ D ∧ -1/45 < D ∧
    (D = -X/15 ↔ ∃ i, p i = 1 ∧ ∀ j, j ≠ i → p j = 0) := by
  dsimp only
  obtain ⟨_,hn,_,hx,_,_,hj,_,hd⟩ := iid_peak_source p hp hs
  have hfirst := tail_first_moment p hp hs
  have hsecond := tail_second_moment p hp hs
  have ha := bounded_tail_lower_surface (tail p) (tail_integrable p)
    (tail_square_integrable p) (tail_bounds p hp hs)
  dsimp only at ha
  have hdet : determinant (tail p) =
      modeLaw p 0*modeLaw p 3-modeLaw p 1*modeLaw p 2 := by
    unfold determinant
    rw [hfirst,hsecond,hd]
  have hmarg : (∫ u in (0 : ℝ)..1, tail p u) = modeLaw p 1+modeLaw p 3 := hfirst.trans hx.symm
  rw [hmarg,hdet] at ha
  obtain ⟨hX0,hX1,s,hs0,hs3,hcor,hcor0,hlower,hstrict⟩ := ha
  have hXlt : modeLaw p 1+modeLaw p 3 < 1/3 := by
    rw [← hmarg]
    exact strict_first_moment p hp hs
  have hdirac : (modeLaw p 1+modeLaw p 3 = 0) ↔
      ∃ i, p i = 1 ∧ ∀ j, j ≠ i → p j = 0 := by
    rw [hx]
    exact zero_peak_iff_dirac p hp hs
  refine ⟨hX0,hXlt,hdirac,⟨s,hs0,hs3,hcor,hcor0⟩,hlower,by linarith,?_⟩
  rw [← hdirac]
  constructor
  · intro he
    by_contra hx0
    have hxpos : 0 < modeLaw p 1+modeLaw p 3 := lt_of_le_of_ne hX0 (Ne.symm hx0)
    exact (ne_of_gt (hstrict hxpos hXlt)) he
  · intro hx0
    have hκ : modeLaw p 3 = 0 := by linarith [hn 1,hn 3]
    rw [hκ] at hx0
    simp only [add_zero] at hx0
    simp [hκ,hx0]

#print axioms finite_iid_lower_surface

end
end D5.S3.Estimation.DataProcessing.FiniteIidStrictPeakLower
