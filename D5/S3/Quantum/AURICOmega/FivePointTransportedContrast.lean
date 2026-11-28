/- GID: D5/S3/Quantum/AURICOmega/FivePointTransportedContrast
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/FivePointTransportedContrast
   mirror-E: none(waiver:exact-symbolic-proof)
   anchors: []
   utility: none
   digest: Classify rational reading differences with both local transported points. -/

import OmegaBuild.Commands
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.WLOG

compile_only_with_mathlib

namespace D5.S3.Quantum.AURICOmega.FivePointTransportedContrast

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

private def gramForm (t a b c x y z w : R) : R :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 +
    2 * (t * (x * y + z * w) + a * x * z + b * (x * w + y * z) + c * y * w)

private theorem binaryForm_iff (A B C : R) :
    (∀ u v : R, 0 ≤ A * u ^ 2 + 2 * B * u * v + C * v ^ 2) ↔
      0 ≤ A ∧ 0 ≤ C ∧ B ^ 2 ≤ A * C := by
  constructor
  · intro h
    have hdiscrim := discrim_le_zero (a := A) (b := 2 * B) (c := C) (fun u => by
      simpa [pow_two] using h u 1)
    refine ⟨by simpa using h 1 0, by simpa using h 0 1, ?_⟩
    simp only [discrim] at hdiscrim
    nlinarith only [hdiscrim]
  · rintro ⟨hA, hC, hdet⟩ u v
    rcases hA.eq_or_lt with hAzero | hApos
    · have hB : B = 0 := by
        rw [← hAzero, zero_mul] at hdet
        by_contra hB
        exact (not_lt_of_ge hdet) (sq_pos_of_ne_zero hB)
      rw [← hAzero, hB]
      simpa using mul_nonneg hC (sq_nonneg v)
    · have heq : A * (A * u ^ 2 + 2 * B * u * v + C * v ^ 2) =
          (A * u + B * v) ^ 2 + (A * C - B ^ 2) * v ^ 2 := by ring
      apply nonneg_of_mul_nonneg_right _ hApos
      rw [heq]
      exact add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hdet) (sq_nonneg _))

private theorem gramForm_nonneg_iff (t a b c : R) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (∀ x y z w, 0 ≤ gramForm t a b c x y z w) ↔
      a ≤ 1 ∧ c ≤ 1 ∧
      (t + b) ^ 2 ≤ (1 + a) * (1 + c) ∧ (t - b) ^ 2 ≤ (1 - a) * (1 - c) := by
  constructor
  · intro h
    have hplus := (binaryForm_iff (1 + a) (t + b) (1 + c)).mp (fun u v => by
      have hq := h u v u v
      unfold gramForm at hq
      nlinarith only [hq])
    have hminus := (binaryForm_iff (1 - a) (t - b) (1 - c)).mp (fun u v => by
      have hq := h u v (-u) (-v)
      unfold gramForm at hq
      nlinarith only [hq])
    exact ⟨sub_nonneg.mp hminus.1, sub_nonneg.mp hminus.2.1, hplus.2.2, hminus.2.2⟩
  · rintro ⟨ha1, hc1, hp, hm⟩ x y z w
    have hplus := (binaryForm_iff (1 + a) (t + b) (1 + c)).mpr
      ⟨by positivity, by positivity, hp⟩ (x + z) (y + w)
    have hminus := (binaryForm_iff (1 - a) (t - b) (1 - c)).mpr
      ⟨sub_nonneg.mpr ha1, sub_nonneg.mpr hc1, hm⟩ (x - z) (y - w)
    unfold gramForm
    nlinarith only [hplus, hminus]

private theorem gramForm_scale (t a b c s : R) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (h : ∀ x y z w, 0 ≤ gramForm t a b c x y z w) :
    ∀ x y z w, 0 ≤ gramForm t (s * a) (s * b) (s * c) x y z w := by
  have hzero : ∀ x y z w, 0 ≤ gramForm t 0 0 0 x y z w := by
    have htsq : t ^ 2 ≤ 1 := by nlinarith only [mul_nonneg ht (sub_nonneg.mpr ht1), ht1]
    apply (gramForm_nonneg_iff t 0 0 0 le_rfl le_rfl).mpr
    simpa using htsq
  intro x y z w
  unfold gramForm at *
  nlinarith only [mul_nonneg hs (h x y z w),
    mul_nonneg (sub_nonneg.mpr hs1) (hzero x y z w)]

private theorem gramForm_constraints (t a b c : R) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ x y z w, 0 ≤ gramForm t a b c x y z w) :
    a + (t - b) ^ 2 ≤ 1 ∧ (a - b) ^ 2 + 2 * (1 - t) * a * b ≤ 1 - t ^ 2 := by
  obtain ⟨ha1, _, hp, hm⟩ := (gramForm_nonneg_iff t a b c ha hc).mp h
  constructor
  · nlinarith only [hm, mul_nonneg (sub_nonneg.mpr ha1) hc]
  · have hmulPlus := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr ha1)
    have hmulMinus := mul_le_mul_of_nonneg_left hm (show 0 ≤ 1 + a by positivity)
    nlinarith only [hmulPlus, hmulMinus]

private theorem high_overlap_bound (t d a b : R) (ht : 1 / 2 < t) (ht1 : t ≤ 1)
    (hhigh : 1 - t ^ 2 < (t - 1 / 2) ^ 2) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (hab : a - b = d) (hminus : a + (t - b) ^ 2 ≤ 1)
    (hthree : (a - b) ^ 2 + 2 * (1 - t) * a * b ≤ 1 - t ^ 2) :
    d ^ 2 ≤ (2 * t - 1) ^ 2 * (1 - t ^ 2) := by
  let m := t - 1 / 2
  have hm : 0 < m := sub_pos.mpr ht
  let q := d / (2 * m)
  have hq : 0 ≤ q := div_nonneg hd (by positivity)
  have hqd : q * (2 * m) = d := div_mul_cancel₀ d (by positivity)
  have hcap : d ≤ 1 - t ^ 2 + 2 * m * b - b ^ 2 := by
    dsimp [m]
    nlinarith only [hminus, hab]
  have hq_lt : q < m := by
    have hvertex : d ≤ 1 - t ^ 2 + m ^ 2 := by
      nlinarith only [hcap, sq_nonneg (b - m)]
    have hd_lt : d < m * (2 * m) := by
      change 1 - t ^ 2 < m ^ 2 at hhigh
      nlinarith only [hvertex, hhigh]
    exact (div_lt_iff₀ (show 0 < 2 * m by positivity)).mpr hd_lt
  by_contra! hbad
  have hqSq : 1 - t ^ 2 < q ^ 2 := by
    have htwo : 2 * t - 1 = 2 * m := by dsimp [m]; ring
    rw [htwo, ← hqd] at hbad
    apply lt_of_mul_lt_mul_right _ (sq_nonneg (2 * m))
    nlinarith only [hbad]
  have hbq : q ≤ b := by
    by_contra! hbq
    have hmono : 2 * m * b - b ^ 2 ≤ 2 * m * q - q ^ 2 := by
      have hpos : 0 ≤ 2 * m - q - b := by linarith only [hbq, hq_lt]
      nlinarith only [mul_nonneg hpos (sub_nonneg.mpr hbq.le)]
    nlinarith only [hcap, hmono, hqSq, hqd]
  have hproduct : q * (q + d) ≤ b * a := by
    have hae : a = b + d := by linarith only [hab]
    rw [hae]
    exact mul_le_mul hbq (by simpa only [add_comm] using add_le_add_right hbq d) (by positivity) hb
  have hsmall : d ^ 2 + 2 * (1 - t) * (q * (q + d)) ≤ 1 - t ^ 2 := by
    rw [hab] at hthree
    have hscaled := mul_le_mul_of_nonneg_left hproduct
      (mul_nonneg zero_le_two (sub_nonneg.mpr ht1))
    linarith only [hthree, hscaled]
  have heq : d ^ 2 + 2 * (1 - t) * (q * (q + d)) = q ^ 2 := by
    rw [← hqd]
    dsimp [m]
    ring
  rw [heq] at hsmall
  exact (not_lt_of_ge hsmall) hqSq

private def squaredCap (t : R) : R :=
  if t ≤ 1 / 2 then (1 - t ^ 2) ^ 2
  else if (t - 1 / 2) ^ 2 ≤ 1 - t ^ 2 then (5 / 4 - t) ^ 2
  else (2 * t - 1) ^ 2 * (1 - t ^ 2)

private theorem fourPoint_bound (t a b c : R) (ht1 : t ≤ 1)
    (hba : b ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (gram : ∀ x y z w, 0 ≤ gramForm t a b c x y z w) :
    (a - b) ^ 2 ≤ squaredCap t := by
  have hd := sub_nonneg.mpr hba
  obtain ⟨hminus, hthree⟩ := gramForm_constraints t a b c (hb.trans hba) hc gram
  unfold squaredCap
  split_ifs with hlow hmid
  · have hterm := mul_nonpos_of_nonpos_of_nonneg (show 2 * t - 1 ≤ 0 by linarith only [hlow]) hb
    have hcap : a - b ≤ 1 - t ^ 2 := by
      nlinarith only [hminus, hterm, sq_nonneg b]
    exact pow_le_pow_left₀ hd hcap _
  · have hcap : a - b ≤ 5 / 4 - t := by
      nlinarith only [hminus, sq_nonneg (b - (t - 1 / 2))]
    exact pow_le_pow_left₀ hd hcap _
  · exact high_overlap_bound t (a - b) a b (lt_of_not_ge hlow) ht1
      (lt_of_not_ge hmid) hd hb rfl hminus hthree

private theorem fourPoint_witness (t d : R) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hd : 0 ≤ d)
    (h : d ^ 2 ≤ squaredCap t) :
    ∃ a b : R, 0 ≤ b ∧ b ≤ a ∧ a ≤ 1 ∧ b ≤ t ∧ b < 1 ∧ a - b = d ∧
      ∀ x y z w, 0 ≤ gramForm t a b 0 x y z w := by
  have htsq : 0 ≤ 1 - t ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr ht1) (show 0 ≤ 1 + t by positivity)]
  unfold squaredCap at h
  split_ifs at h with hlow hmid
  · have hcap : d ≤ 1 - t ^ 2 := le_of_pow_le_pow_left₀ two_ne_zero htsq h
    have hd1 : d ≤ 1 := by nlinarith only [hcap, sq_nonneg t]
    refine ⟨d, 0, le_rfl, hd, hd1, ht, zero_lt_one, sub_zero _, ?_⟩
    apply (gramForm_nonneg_iff t d 0 0 hd le_rfl).mpr
    refine ⟨hd1, zero_le_one, ?_, ?_⟩ <;> nlinarith only [hcap, hd, htsq]
  · let b := t - 1 / 2
    let cap := 5 / 4 - t
    let s := d / cap
    have hb : 0 ≤ b := sub_nonneg.mpr (le_of_not_ge hlow)
    have hcap : 0 < cap := by dsimp [cap]; linarith only [ht1]
    have hbound : d ≤ cap := le_of_pow_le_pow_left₀ two_ne_zero hcap.le h
    have hs : 0 ≤ s := div_nonneg hd hcap.le
    have hs1 : s ≤ 1 := (div_le_one hcap).mpr hbound
    have hbase : ∀ x y z w, 0 ≤ gramForm t (3 / 4) b 0 x y z w := by
      apply (gramForm_nonneg_iff t (3 / 4) b 0 (by norm_num) le_rfl).mpr
      refine ⟨by norm_num, zero_le_one, ?_, ?_⟩ <;> dsimp [b] <;>
        nlinarith only [hmid]
    have hdiff : s * (3 / 4) - s * b = d := by
      have heq : 3 / 4 - b = cap := by dsimp [b, cap]; ring
      rw [← mul_sub, heq, div_mul_cancel₀ d hcap.ne']
    have hsb := mul_le_of_le_one_left hb hs1
    refine ⟨s * (3 / 4), s * b, mul_nonneg hs hb, sub_nonneg.mp (hdiff ▸ hd),
      by nlinarith only [hs1], ?_, ?_, hdiff, ?_⟩
    · exact hsb.trans (by dsimp [b]; linarith)
    · exact hsb.trans_lt (by dsimp [b]; linarith)
    · simpa only [mul_zero] using gramForm_scale t (3 / 4) b 0 s ht ht1 hs hs1 hbase
  · let b := d / (2 * t - 1)
    let a := 2 * t * b
    have ht' : 0 < 2 * t - 1 := by linarith only [lt_of_not_ge hlow]
    have hb : 0 ≤ b := div_nonneg hd ht'.le
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hbSq : b ^ 2 ≤ 1 - t ^ 2 := by
      dsimp [b]
      rw [div_pow]
      exact (div_le_iff₀ (sq_pos_of_pos ht')).mpr (by simpa only [mul_comm] using h)
    have ha1 : a ≤ 1 := by dsimp [a]; nlinarith only [hbSq, sq_nonneg (t - b)]
    have hab : a - b = d := by
      have heq : a - b = b * (2 * t - 1) := by dsimp [a]; ring
      rw [heq, div_mul_cancel₀ d ht'.ne']
    have hbsmall : b < t - 1 / 2 :=
      lt_of_pow_lt_pow_left₀ 2 (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hlow)))
        (hbSq.trans_lt (lt_of_not_ge hmid))
    refine ⟨a, b, hb, sub_nonneg.mp (hab ▸ hd), ha1,
      by linarith only [hbsmall], by linarith only [hbsmall, ht1], hab, ?_⟩
    apply (gramForm_nonneg_iff t a b 0 ha le_rfl).mpr
    refine ⟨ha1, zero_le_one, ?_, ?_⟩ <;> dsimp [a] <;> nlinarith only [hbSq]

/-- Both transported points can occur in one normalized nonnegative rational Gram
form. The four prescribed entries in the transported columns are b, t and a, t.
The signed difference has the stated exact range. -/
theorem exists_transported_readings_iff (t d : ℚ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∃ a b c e r : ℚ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ e ∧ 0 ≤ r ∧ a - b = d ∧
      ∀ x y z w v : ℚ, 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 + v ^ 2 +
        2 * (t * (x * y + z * w + z * v) + a * (x * z + y * v) +
          b * (y * z + x * w) + c * y * w + e * x * v + r * w * v)) ↔
    d ^ 2 ≤ if t ≤ 1 / 2 then (1 - t ^ 2) ^ 2
      else if (t - 1 / 2) ^ 2 ≤ 1 - t ^ 2 then (5 / 4 - t) ^ 2
      else (2 * t - 1) ^ 2 * (1 - t ^ 2) := by
  wlog hd : 0 ≤ d generalizing d
  · have hn : 0 ≤ -d := neg_nonneg.mpr (le_of_not_ge hd)
    have h := this (-d) hn
    rw [neg_sq] at h
    constructor
    · rintro ⟨a, b, c, e, r, ha, hb, hc, he, hr, hab, gram⟩
      apply h.mp
      refine ⟨b, a, e, c, r, hb, ha, he, hc, hr, by linarith only [hab], ?_⟩
      intro x y z w v
      nlinarith only [gram y x z v w]
    · intro hbound
      obtain ⟨a, b, c, e, r, ha, hb, hc, he, hr, hab, gram⟩ := h.mpr hbound
      refine ⟨b, a, e, c, r, hb, ha, he, hc, hr, by linarith only [hab], ?_⟩
      intro x y z w v
      nlinarith only [gram y x z v w]
  change _ ↔ d ^ 2 ≤ squaredCap t
  constructor
  · rintro ⟨a, b, c, e, r, ha, hb, hc, he, hr, rfl, gram⟩
    apply fourPoint_bound t a b c ht1 (sub_nonneg.mp hd) hb hc
    intro x y z w
    simpa [gramForm, mul_assoc, add_comm (x * w) (y * z)] using gram x y z w 0
  · intro h
    obtain ⟨a, b, hb, hba, ha1, hbt, hb1, hab, gram⟩ := fourPoint_witness t d ht ht1 hd h
    have ha := hb.trans hba
    let α := (a - b * t) / (1 - b ^ 2)
    let β := (t - b * a) / (1 - b ^ 2)
    have hden : 0 < 1 - b ^ 2 := by
      nlinarith only [mul_pos (sub_pos.mpr hb1) (show 0 < 1 + b by positivity)]
    have hα : 0 ≤ α := div_nonneg (sub_nonneg.mpr
      (le_trans (mul_le_of_le_one_right hb ht1) hba)) hden.le
    have hβ : 0 ≤ β := div_nonneg (sub_nonneg.mpr
      (le_trans (mul_le_of_le_one_right hb ha1) hbt)) hden.le
    have hαden : α * (1 - b ^ 2) = a - b * t := div_mul_cancel₀ _ hden.ne'
    have hβden : β * (1 - b ^ 2) = t - b * a := div_mul_cancel₀ _ hden.ne'
    have hαeq : α + b * β = a := by
      apply mul_right_cancel₀ hden.ne'
      linear_combination hαden + b * hβden
    have hβeq : b * α + β = t := by
      apply mul_right_cancel₀ hden.ne'
      linear_combination b * hαden + hβden
    -- Projecting x into the span of y and z reverses the two coefficients.
    have hslack : 0 ≤ 1 - α * a - β * t := by
      have hres := gram 1 (-β) (-α) 0
      unfold gramForm at hres
      nlinarith only [hres, congrArg (α * ·) hαeq, congrArg (β * ·) hβeq]
    -- Add a vector with projection α y + β z and independent diagonal slack.
    refine ⟨a, b, 0, t * α + a * β, t * β, ha, hb, le_rfl,
      by positivity, by positivity, hab, ?_⟩
    intro x y z w v
    have hform : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 + v ^ 2 +
        2 * (t * (x * y + z * w + z * v) + a * (x * z + y * v) +
          b * (y * z + x * w) + 0 * y * w + (t * α + a * β) * x * v + (t * β) * w * v) =
        gramForm t a b 0 x (y + α * v) (z + β * v) w +
          (1 - α * a - β * t) * v ^ 2 := by
      unfold gramForm
      linear_combination (-α * v ^ 2 - 2 * y * v) * hαeq +
        (-β * v ^ 2 - 2 * z * v) * hβeq
    rw [hform]
    exact add_nonneg (gram x (y + α * v) (z + β * v) w)
      (mul_nonneg hslack (sq_nonneg v))

end D5.S3.Quantum.AURICOmega.FivePointTransportedContrast
