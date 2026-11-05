/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLowXTail/Intervals
   generality: I
   mirror-B: none(waiver:private-consumed-implementation)
   mirror-E: none(waiver:private-consumed-implementation)
   anchors: [mathlib/module/Mathlib.Data.Rat.Defs]
   utility: none
   digest: Affine and concave interpolation of the exact low-X margins. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Certificates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail

open private qHead qNewHead qModulus qMask qMass qTerminal qPeak qSeam qSlack margin smallTZero smallTPositive largeTZero largeTPositive cap bend second from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Model
open private cert_smallt_smalle_t1_old_0_seam cert_smallt_smalle_t1_old_1_seam cert_smallt_smalle_t1_old_2_seam cert_smallt_smalle_t1_new_0_slack cert_smallt_smalle_t1_new_1_slack cert_smallt_largee_t1_old_0_seam cert_smallt_largee_t1_old_1_seam cert_smallt_largee_t1_old_2_seam cert_smallt_largee_t1_new_0_slack cert_smallt_largee_t1_new_1_slack cert_smallt_largee_t1_new_2_slack cert_smallt_smalle_tmax_old_0_seam cert_smallt_smalle_tmax_old_1_seam cert_smallt_smalle_tmax_old_2_seam cert_smallt_smalle_tmax_new_0_slack cert_smallt_smalle_tmax_new_1_slack cert_smallt_largee_tmax_old_0_seam cert_smallt_largee_tmax_old_1_seam cert_smallt_largee_tmax_old_2_seam cert_smallt_largee_tmax_new_0_slack cert_smallt_largee_tmax_new_1_slack cert_smallt_largee_tmax_new_2_slack cert_larget_smalle_1_old_0_seam cert_larget_smalle_1_old_1_seam cert_larget_smalle_1_old_2_seam cert_larget_smalle_1_new_0_slack cert_larget_smalle_1_new_1_slack cert_larget_largee_1_old_0_seam cert_larget_largee_1_old_1_seam cert_larget_largee_1_old_2_seam cert_larget_largee_1_new_0_slack cert_larget_largee_1_new_2_slack cert_larget_smalle_2_old_0_seam cert_larget_smalle_2_old_1_seam cert_larget_smalle_2_old_2_seam cert_larget_smalle_2_new_0_slack cert_larget_smalle_2_new_1_slack cert_larget_largee_2_old_0_seam cert_larget_largee_2_old_1_seam cert_larget_largee_2_old_2_seam cert_larget_largee_2_new_0_slack cert_larget_largee_2_new_2_slack cert_small_e_exception_new_2_slack cert_concavity_1_new_lower cert_concavity_1_new_upper cert_concavity_2_new_lower cert_concavity_2_new_upper from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Certificates


-- Cross-multiplied affine identities avoid division by an interval width.
private theorem affine_t (z x h t : ℚ) (i : Fin 6) (hz : z ≠ 0) :
    (z^2/4-1)*smallTZero z x h t i =
      (z^2/4-t)*smallTZero z x h 1 i +
      (t-1)*smallTZero z x h (z^2/4) i := by
  fin_cases i <;> norm_num [smallTZero, margin, qSeam, qSlack, qPeak,
    qTerminal, qMass, qMask, qHead, qNewHead, qModulus, Fin.sum_univ_succ]
  <;> field_simp [hz] <;> ring

private theorem affine_h (z x e h : ℚ) (i : Fin 6) (hz : z ≠ 0) :
    (x*e/4-x*e/z^2)*smallTPositive z x e h i =
      (x*e/4-h)*smallTPositive z x e (x*e/z^2) i +
      (h-x*e/z^2)*smallTPositive z x e (x*e/4) i := by
  fin_cases i <;> norm_num [smallTPositive, margin, qSeam, qSlack, qPeak,
    qTerminal, qMass, qMask, qHead, qNewHead, qModulus, Fin.sum_univ_succ]
  <;> field_simp [hz] <;> ring

private theorem third_slack_independent (z x h q r : ℚ) :
    margin z x h q r 0 5 = margin z x h q 0 0 5 := by
  norm_num [margin, qSlack, qPeak, qTerminal, qMass, qMask, qHead,
    qNewHead, qModulus, Fin.sum_univ_succ]
  <;> ring

-- For nonzero h, second is exactly quadratic, with leading coefficient -bend.
-- This chord identity is valid for both beta=1 and beta=2, including their collision.
private theorem second_chord (z x e h beta : ℚ)
    (hz : z ≠ 0) (hx : x ≠ 0) (he : e ≠ 0) (hh : h ≠ 0) :
    (cap z x e-1)*second z x e h beta =
      (cap z x e-h)*second z x e 1 beta +
      (h-1)*second z x e (cap z x e) beta +
      bend z x*(h-1)*(cap z x e-h)*(cap z x e-1) := by
  norm_num [second, largeTPositive, cap, bend, margin, qSlack, qPeak,
    qTerminal, qMass, qMask, qHead, qNewHead, qModulus, Fin.sum_univ_succ]
  <;> field_simp [hz, hx, he, hh] <;> ring


private theorem small_e_third (z x h t r : ℚ)
    (hz : 4 ≤ z) (hh : 1 ≤ h) (ht : 1 ≤ t) (hsmall : 0 ≤ x-8*h*t) :
    0 ≤ margin z x h (h*t) r 0 5 := by
  rw [third_slack_independent]
  have hid : 8*h*t+(x-8*h*t) = x := by ring
  have hc := cert_small_e_exception_new_2_slack (z-4) (t-1) 0 (h-1) (x-8*h*t) (by linarith) (by linarith) (by norm_num) (by linarith) hsmall
  simpa only [sub_add_cancel, hid] using hc


private theorem second_nonnegative (Z T R h beta : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hbeta : beta = 1 ∨ beta = 2) (hh : 1 ≤ h)
    (hcap : h ≤ cap (Z+4) (2*(Z+4)^2*(T+1)) (R+1)) :
    0 ≤ largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) h beta 4 := by
  let z := Z+4
  let x := 2*z^2*(T+1)
  let e := R+1
  let J := cap z x e
  have hz : 0 < z := by dsimp [z]; linarith
  have hx : 0 < x := by dsimp [x]; positivity
  have he : 0 < e := by dsimp [e]; linarith
  have hJ : h ≤ J := hcap
  have hlower : 0 ≤ second z x e 1 beta := by
    rcases hbeta with rfl | rfl
    · exact cert_concavity_1_new_lower Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
    · exact cert_concavity_2_new_lower Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
  have hupper : 0 ≤ second z x e J beta := by
    rcases hbeta with rfl | rfl
    · exact cert_concavity_1_new_upper Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
    · exact cert_concavity_2_new_upper Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
  have hF : 0 ≤ second z x e h beta := by
    by_cases hJone : J = 1
    · have hhOne : h = 1 := by linarith
      rw [hhOne]
      exact hlower
    · have hwidth : 0 < J-1 := by
        rcases lt_or_eq_of_le (le_trans hh hJ) with hlt | heq
        · exact sub_pos.mpr hlt
        · exact (hJone heq.symm).elim
      have hb : 0 ≤ bend z x := by
        have hz4 : 4 ≤ z := by dsimp [z]; linarith
        have hp : 0 < z^2-z+1 := by
          nlinarith only [hz4, sq_nonneg (z-1)]
        dsimp [bend]
        positivity
      have identity := second_chord z x e h beta (ne_of_gt hz)
        (ne_of_gt hx) (ne_of_gt he) (by linarith)
      have hm : 0 ≤ (J-1)*second z x e h beta := by
        rw [identity]
        exact add_nonneg
          (add_nonneg (mul_nonneg (by linarith) hlower)
            (mul_nonneg (by linarith) hupper))
          (mul_nonneg (mul_nonneg (mul_nonneg hb (by linarith))
            (by linarith)) (le_of_lt hwidth))
      exact (mul_nonneg_iff_of_pos_left hwidth).mp hm
  change 0 ≤ h * largeTPositive z x e h beta 4 at hF
  exact (mul_nonneg_iff_of_pos_left (by linarith : 0 < h)).mp hF


-- Five endpoint pairs and the independent small-e third peak supply all six margins.
private theorem small_t_small_e (Z T H t : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hH : 0 ≤ H) (ht : 1 ≤ t)
    (htop : t ≤ (Z+4)^2/4)
    (hsmall : 0 ≤ 2*(Z+4)^2*(T+1)-8*(H+1)*t) :
    ∀ i : Fin 6, 0 ≤ smallTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) t i := by
  intro i
  let z := Z+4
  let x := 2*z^2*(T+1)
  let h := H+1
  by_cases hi : i = 5
  · subst i
    exact small_e_third z x h t 0 (by dsimp [z]; linarith)
      (by dsimp [h]; linarith) ht hsmall
  · have hlower : 0 ≤ smallTZero z x h 1 i := by
      fin_cases i
      · exact cert_smallt_smalle_t1_old_0_seam Z T 0 H 0 hZ hT (by norm_num) hH (by norm_num)
      · exact cert_smallt_smalle_t1_old_1_seam Z T 0 H 0 hZ hT (by norm_num) hH (by norm_num)
      · exact cert_smallt_smalle_t1_old_2_seam Z T 0 H 0 hZ hT (by norm_num) hH (by norm_num)
      · exact cert_smallt_smalle_t1_new_0_slack Z T 0 H 0 hZ hT (by norm_num) hH (by norm_num)
      · exact cert_smallt_smalle_t1_new_1_slack Z T 0 H 0 hZ hT (by norm_num) hH (by norm_num)
      · exact (hi rfl).elim
    have hupper : 0 ≤ smallTZero z x h (z^2/4) i := by
      fin_cases i
      · exact cert_smallt_smalle_tmax_old_0_seam Z T 0 H 0 hZ hT (by norm_num) hH (by norm_num)
      · exact cert_smallt_smalle_tmax_old_1_seam Z T 0 H 0 hZ hT (by norm_num) hH (by norm_num)
      · exact cert_smallt_smalle_tmax_old_2_seam Z T 0 H 0 hZ hT (by norm_num) hH (by norm_num)
      · exact cert_smallt_smalle_tmax_new_0_slack Z T 0 H 0 hZ hT (by norm_num) hH (by norm_num)
      · exact cert_smallt_smalle_tmax_new_1_slack Z T 0 H 0 hZ hT (by norm_num) hH (by norm_num)
      · exact (hi rfl).elim
    have hz4 : 4 ≤ z := by dsimp [z]; linarith
    have hwidth : 0 < z^2/4-1 := by
      nlinarith only [hz4, sq_nonneg (z-4)]
    have identity := affine_t z x h t i (by linarith)
    have hm : 0 ≤ (z^2/4-1)*smallTZero z x h t i := by
      rw [identity]
      exact add_nonneg (mul_nonneg (by exact sub_nonneg.mpr htop) hlower)
        (mul_nonneg (sub_nonneg.mpr ht) hupper)
    exact (mul_nonneg_iff_of_pos_left hwidth).mp hm


private theorem small_t_large_e (Z T R h : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hlow : (2*(Z+4)^2*(T+1))*(R+1)/(Z+4)^2 ≤ h)
    (hhigh : h ≤ (2*(Z+4)^2*(T+1))*(R+1)/4) :
    ∀ i : Fin 6, 0 ≤ smallTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) h i := by
  intro i
  let z := Z+4
  let x := 2*z^2*(T+1)
  let e := R+1
  have hlower : 0 ≤ smallTPositive z x e (x*e/z^2) i := by
    fin_cases i
    · exact cert_smallt_largee_tmax_old_0_seam Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
    · exact cert_smallt_largee_tmax_old_1_seam Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
    · exact cert_smallt_largee_tmax_old_2_seam Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
    · exact cert_smallt_largee_tmax_new_0_slack Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
    · exact cert_smallt_largee_tmax_new_1_slack Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
    · exact cert_smallt_largee_tmax_new_2_slack Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
  have hupper : 0 ≤ smallTPositive z x e (x*e/4) i := by
    fin_cases i
    · exact cert_smallt_largee_t1_old_0_seam Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
    · exact cert_smallt_largee_t1_old_1_seam Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
    · exact cert_smallt_largee_t1_old_2_seam Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
    · exact cert_smallt_largee_t1_new_0_slack Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
    · exact cert_smallt_largee_t1_new_1_slack Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
    · exact cert_smallt_largee_t1_new_2_slack Z T R 0 0 hZ hT hR (by norm_num) (by norm_num)
  have hz4 : 4 ≤ z := by dsimp [z]; linarith
  have hz : z ≠ 0 := by linarith
  have hx : 0 < x := by dsimp [x]; positivity
  have he : 0 < e := by dsimp [e]; linarith
  have hp : 0 < z^2-4 := by nlinarith only [hz4, sq_nonneg (z-4)]
  have width_identity : x*e/4-x*e/z^2 = x*e*(z^2-4)/(4*z^2) := by
    field_simp [hz]
    <;> ring
  have hwidth : 0 < x*e/4-x*e/z^2 := by
    rw [width_identity]
    positivity
  have identity := affine_h z x e h i hz
  have hm : 0 ≤ (x*e/4-x*e/z^2)*smallTPositive z x e h i := by
    rw [identity]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hhigh) hlower)
      (mul_nonneg (sub_nonneg.mpr hlow) hupper)
  exact (mul_nonneg_iff_of_pos_left hwidth).mp hm


private theorem large_t_small_e (Z T R H beta : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hbeta : beta = 1 ∨ beta = 2)
    (hsmall : 0 ≤ 2*(Z+4)^2*(T+1)-8*((H+1)*(Z+4)^2*(R+1)/2)) :
    ∀ i : Fin 6, 0 ≤ largeTZero (Z+4) (2*(Z+4)^2*(T+1)) (H+1) (R+1) beta i := by
  intro i
  let z := Z+4
  let x := 2*z^2*(T+1)
  let h := H+1
  let t := z^2*(R+1)/2
  by_cases hi : i = 5
  · subst i
    have hz4 : 4 ≤ z := by dsimp [z]; linarith
    have ht : 1 ≤ t := by
      dsimp [t]
      nlinarith only [hz4, sq_nonneg (z-4), mul_nonneg (sq_nonneg z) hR]
    have hs : 0 ≤ x-8*h*t := by
      have heq : x-8*h*t = x-8*(h*z^2*(R+1)/2) := by dsimp [t]; ring
      rw [heq]
      exact hsmall
    have hc := small_e_third z x h t (beta*(R+1)) hz4
      (by dsimp [h]; linarith) ht hs
    have heq : h*t = h*z^2*(R+1)/2 := by dsimp [t]; ring
    change 0 ≤ margin z x h (h*z^2*(R+1)/2) (beta*(R+1)) 0 5
    rwa [heq] at hc
  · rcases hbeta with rfl | rfl
    · fin_cases i
      · exact cert_larget_smalle_1_old_0_seam Z T R H 0 hZ hT hR hH (by norm_num)
      · exact cert_larget_smalle_1_old_1_seam Z T R H 0 hZ hT hR hH (by norm_num)
      · exact cert_larget_smalle_1_old_2_seam Z T R H 0 hZ hT hR hH (by norm_num)
      · exact cert_larget_smalle_1_new_0_slack Z T R H 0 hZ hT hR hH (by norm_num)
      · exact cert_larget_smalle_1_new_1_slack Z T R H 0 hZ hT hR hH (by norm_num)
      · exact (hi rfl).elim
    · fin_cases i
      · exact cert_larget_smalle_2_old_0_seam Z T R H 0 hZ hT hR hH (by norm_num)
      · exact cert_larget_smalle_2_old_1_seam Z T R H 0 hZ hT hR hH (by norm_num)
      · exact cert_larget_smalle_2_old_2_seam Z T R H 0 hZ hT hR hH (by norm_num)
      · exact cert_larget_smalle_2_new_0_slack Z T R H 0 hZ hT hR hH (by norm_num)
      · exact cert_larget_smalle_2_new_1_slack Z T R H 0 hZ hT hR hH (by norm_num)
      · exact (hi rfl).elim


private theorem large_t_large_e (Z T R H beta : ℚ)
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hbeta : beta = 1 ∨ beta = 2)
    (hcap : H+1 ≤ cap (Z+4) (2*(Z+4)^2*(T+1)) (R+1)) :
    ∀ i : Fin 6, 0 ≤ largeTPositive (Z+4) (2*(Z+4)^2*(T+1)) (R+1) (H+1) beta i := by
  intro i
  by_cases hi : i = 4
  · subst i
    exact second_nonnegative Z T R (H+1) beta hZ hT hR hbeta (by linarith) hcap
  · rcases hbeta with rfl | rfl
    · fin_cases i
      · exact cert_larget_largee_1_old_0_seam Z T R H 0 hZ hT hR hH (by norm_num)
      · exact cert_larget_largee_1_old_1_seam Z T R H 0 hZ hT hR hH (by norm_num)
      · exact cert_larget_largee_1_old_2_seam Z T R H 0 hZ hT hR hH (by norm_num)
      · exact cert_larget_largee_1_new_0_slack Z T R H 0 hZ hT hR hH (by norm_num)
      · exact (hi rfl).elim
      · exact cert_larget_largee_1_new_2_slack Z T R H 0 hZ hT hR hH (by norm_num)
    · fin_cases i
      · exact cert_larget_largee_2_old_0_seam Z T R H 0 hZ hT hR hH (by norm_num)
      · exact cert_larget_largee_2_old_1_seam Z T R H 0 hZ hT hR hH (by norm_num)
      · exact cert_larget_largee_2_old_2_seam Z T R H 0 hZ hT hR hH (by norm_num)
      · exact cert_larget_largee_2_new_0_slack Z T R H 0 hZ hT hR hH (by norm_num)
      · exact (hi rfl).elim
      · exact cert_larget_largee_2_new_2_slack Z T R H 0 hZ hT hR hH (by norm_num)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail
