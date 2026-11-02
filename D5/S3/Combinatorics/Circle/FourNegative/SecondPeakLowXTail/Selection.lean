/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLowXTail/Selection
   generality: I
   mirror-B: none(waiver:private-consumed-implementation)
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.Rat.Defs]
   utility: none
   digest: All six rational low-X margins hold at the actual physical dyadic reservations. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Intervals
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.PhysicalArithmetic

/-! Physical dyadic margins on the complete low-X domain. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail

open private physicalDomain eOn rOn collide eExponent rExponent eWeight rWeight
  reservation_bounds reservation_choices physical_coordinates physical_regimes dyadic_quotient
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.PhysicalArithmetic
open private margin smallTZero smallTPositive largeTZero largeTPositive cap
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Model
open private small_t_small_e small_t_large_e large_t_small_e large_t_large_e
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail.Intervals

private theorem qpow_mono (m n : ℕ) (hmn : m ≤ n) :
    (2 : ℚ)^m ≤ 2^n := by
  exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hmn

private theorem qpow_sub_div (n j : ℕ) (hj : j ≤ n) :
    (2 : ℚ)^(n-j) = 2^n / 2^j := by
  symm
  exact dyadic_quotient n j hj

private theorem qpow_cutoff_of_not_e_general (a b c d : ℕ)
    (h : physicalDomain a b c d) (hne : ¬ eOn a b) :
    8 * (2 : ℚ)^(b-a-1) ≤ 2^a := by
  rcases h with ⟨hc, ha, hd, hb⟩
  have hexp : (b-a-1)+3 ≤ a := by
    dsimp [eOn] at hne
    omega
  have hp := qpow_mono (b-a-1+3) a (by omega : b-a-1+3 ≤ a)
  rw [← show (8 : ℚ) * 2^(b-a-1) = 2^(b-a-1+3) by
    rw [show (8 : ℚ) = 2^3 by norm_num, ← pow_add]; ring] at hp
  exact hp

private theorem qpow_t_upper_of_not_r (a b c d : ℕ)
    (h : physicalDomain a b c d) (hnr : ¬ rOn b c d) :
    (2 : ℚ)^(b-d-1) ≤ ((2 : ℚ)^c)^2 / 4 := by
  rcases h with ⟨hc, ha, hd, hb⟩
  have hexp : b-d-1 ≤ 2*c-2 := by
    dsimp [rOn] at hnr
    omega
  have hp := qpow_mono (b-d-1+2) (2*c) (by omega : b-d-1+2 ≤ 2*c)
  rw [← show (4 : ℚ) * 2^(b-d-1) = 2^(b-d-1+2) by
    rw [show (4 : ℚ) = 2^2 by norm_num, ← pow_add]; ring] at hp
  have hzsq : ((2 : ℚ)^c)^2 = 2^(2*c) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hzsq]
  exact (le_div_iff₀ (by norm_num : (0 : ℚ) < 4)).2 (by nlinarith only [hp])

private theorem qpow_h_lower_of_not_r (a b c d : ℕ)
    (h : physicalDomain a b c d) (hnr : ¬ rOn b c d) (he : eOn a b) :
    (2 : ℚ)^a * eWeight a b / ((2 : ℚ)^c)^2 ≤ (2 : ℚ)^(d-a) := by
  rcases h with ⟨hc, ha, hd, hb⟩
  have hbd : b-d ≤ 2*c-1 := by
    dsimp [rOn] at hnr
    omega
  have hexp : b+1-a-2*c ≤ d-a := by omega
  have hp : (2 : ℚ)^(b+1-a-2*c) ≤ 2^(d-a) := qpow_mono _ _ (by omega)
  have hepow : eWeight a b = (2 : ℚ)^(b+1-2*a) := by
    simp [eWeight, he, eExponent]
  rw [hepow]
  have hzsq : ((2 : ℚ)^c)^2 = 2^(2*c) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hzsq]
  have hsum : 2*c ≤ a + (b+1-2*a) := by omega
  have hident : (2 : ℚ)^a * 2^(b+1-2*a) / 2^(2*c) =
      2^(b+1-a-2*c) := by
    rw [← pow_add, ← qpow_sub_div (a + (b+1-2*a)) (2*c) hsum]
    congr 1
    omega
  rw [hident]
  exact hp

private theorem qpow_h_upper_of_domain (a b c d : ℕ)
    (h : physicalDomain a b c d) (he : eOn a b) :
    (2 : ℚ)^(d-a) ≤ (2 : ℚ)^a * eWeight a b / 4 := by
  rcases h with ⟨hc, ha, hd, hb⟩
  have hexp : d-a ≤ b-a-1 := by omega
  have hp : (2 : ℚ)^(d-a) ≤ 2^(b-a-1) := qpow_mono _ _ hexp
  have hepow : eWeight a b = (2 : ℚ)^(b+1-2*a) := by
    simp [eWeight, he, eExponent]
  rw [hepow]
  have hsum : 2 ≤ a + (b+1-2*a) := by omega
  have hident : (2 : ℚ)^a * 2^(b+1-2*a) / 4 =
      2^(b-a-1) := by
    rw [show (4 : ℚ) = 2^2 by norm_num, ← pow_add,
      ← qpow_sub_div (a + (b+1-2*a)) 2 hsum]
    congr 1
    omega
  rw [hident]
  exact hp

private theorem qpow_h_cap_of_r (a b c d : ℕ)
    (h : physicalDomain a b c d) (hr : rOn b c d) (he : eOn a b) :
    (2 : ℚ)^(d-a) ≤
      (2 : ℚ)^a * eWeight a b / (2 * ((2 : ℚ)^c)^2) := by
  rcases h with ⟨hc, ha, hd, hb⟩
  have hexp : d-a ≤ b-a-2*c := by
    dsimp [rOn] at hr
    omega
  have hp : (2 : ℚ)^(d-a) ≤ 2^(b-a-2*c) := qpow_mono _ _ hexp
  have hepow : eWeight a b = (2 : ℚ)^(b+1-2*a) := by
    simp [eWeight, he, eExponent]
  rw [hepow]
  have hzsq : ((2 : ℚ)^c)^2 = 2^(2*c) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hzsq]
  have hsum : 2*c+1 ≤ a + (b+1-2*a) := by omega
  have hident : (2 : ℚ)^a * 2^(b+1-2*a) /
      (2 * 2^(2*c)) = 2^(b-a-2*c) := by
    rw [show (2 : ℚ) * 2^(2*c) = 2^(2*c+1) by
      rw [← pow_succ']]
    rw [← pow_add, ← qpow_sub_div (a + (b+1-2*a)) (2*c+1) hsum]
    congr 1
    omega
  rw [hident]
  exact hp

private theorem beta_spec (a b c d : ℕ) (h : physicalDomain a b c d)
    (hr : rOn b c d) :
    (if collide a b c d then (2 : ℚ) else 1) = 1 ∨
      (if collide a b c d then (2 : ℚ) else 1) = 2 := by
  by_cases hc : collide a b c d <;> simp [hc]

private theorem rweight_as_beta (a b c d : ℕ) (h : physicalDomain a b c d)
    (hr : rOn b c d) :
    rWeight a b c d =
      (if collide a b c d then (2 : ℚ) else 1) * (2 : ℚ)^(b-d-2*c) := by
  have hc : 2 ≤ c := h.1
  have hn : ¬ b-d ≤ 2*c-1 := by dsimp [rOn] at hr; omega
  rw [(reservation_choices a b c d h).2, if_neg hn]
  change (if collide a b c d then 2*(2:ℚ)^(b-d-2*c) else 2^(b-d-2*c)) = _
  split_ifs <;> ring


private theorem rweight_large_formula (a b c d : ℕ) (h : physicalDomain a b c d)
    (hr : rOn b c d) (he : eOn a b) :
    rWeight a b c d =
      (if collide a b c d then (2 : ℚ) else 1) *
        ((2 : ℚ)^a * eWeight a b) /
          (2 * (2 : ℚ)^(d-a) * ((2 : ℚ)^c)^2) := by
  have hru := rweight_as_beta a b c d h hr
  have hq := (physical_regimes a b c d h).2.2 hr
  have heq := (physical_regimes a b c d h).2.1 he
  rw [hru]
  have hh : (2 : ℚ)^(d-a) ≠ 0 := by positivity
  have hzs : (2 : ℚ)^c ≠ 0 := by positivity
  have hpow : (2 : ℚ)^(b-d-2*c) =
      ((2 : ℚ)^a * eWeight a b) /
        (2 * (2 : ℚ)^(d-a) * ((2 : ℚ)^c)^2) := by
    rw [heq] at hq
    field_simp [hh, hzs]
    nlinarith only [hq]
  rw [hpow]
  ring

private theorem qweight_large_formula (a b c d : ℕ) (h : physicalDomain a b c d)
    (he : eOn a b) :
    (2 : ℚ)^(b-a-1) = (2 : ℚ)^a * eWeight a b / 4 :=
  (physical_regimes a b c d h).2.1 he

private theorem qweight_small_formula (a b c d : ℕ) (h : physicalDomain a b c d) :
    (2 : ℚ)^(b-a-1) = (2 : ℚ)^(d-a) * (2 : ℚ)^(b-d-1) :=
  (physical_regimes a b c d h).1.symm

private theorem rweight_zero_of_not_r (a b c d : ℕ) (hnr : ¬ rOn b c d) :
    rWeight a b c d = 0 := by
  simp [rWeight, hnr]

private theorem eweight_zero_of_not_e (a b : ℕ) (hne : ¬ eOn a b) :
    eWeight a b = 0 := by
  simp [eWeight, hne]

private theorem physical_margins (a b c d : ℕ) (h : physicalDomain a b c d) :
    ∀ i : Fin 6, 0 ≤ margin ((2 : ℚ)^c) (2^a) (2^(d-a))
      (2^(b-a-1)) (rWeight a b c d) (eWeight a b) i := by
  let z : ℚ := (2 : ℚ)^c
  let x : ℚ := (2 : ℚ)^a
  let hh : ℚ := (2 : ℚ)^(d-a)
  let tt : ℚ := (2 : ℚ)^(b-d-1)
  let EE : ℚ := (2 : ℚ)^(a-2*c-1)
  let ee : ℚ := (2 : ℚ)^(b+1-2*a)
  let uu : ℚ := (2 : ℚ)^(b-d-2*c)
  let beta : ℚ := if collide a b c d then 2 else 1
  have hz4 : 4 ≤ z := by
    dsimp [z]
    have hc : 2 ≤ c := h.1
    have hp := qpow_mono 2 c hc
    norm_num only [show (2:ℚ)^2=4 by norm_num] at hp
    exact hp
  have hZ : 0 ≤ z-4 := by linarith
  have hT : 0 ≤ EE-1 := by
    dsimp [EE]
    have hca : 2*c+1 ≤ a := h.2.1
    have hp := qpow_mono 0 (a-2*c-1) (by omega)
    norm_num at hp ⊢
    exact hp
  have hH : 0 ≤ hh-1 := by
    dsimp [hh]
    have hp : (1 : ℚ) ≤ 2^(d-a) := qpow_mono 0 (d-a) (by omega)
    exact sub_nonneg.mpr hp
  have hqsmall : (2 : ℚ)^(b-a-1) = hh*tt := by
    dsimp [hh,tt]
    exact qweight_small_formula a b c d h
  have hxcoord : x = 2*z^2*(EE) := by
    dsimp [x,z,EE]
    have hzsq : ((2 : ℚ)^c)^2 = 2^(2*c) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [hzsq, ← pow_succ', ← pow_add]
    congr 1
    have ha := h.2.1
    omega
  have hnotEcut : ¬ eOn a b → 0 ≤ x-8*hh*tt := by
    intro hne
    have hc := qpow_cutoff_of_not_e_general a b c d h hne
    rw [hqsmall] at hc
    change 0 ≤ (2:ℚ)^a - 8*hh*tt
    nlinarith only [hc]
  have hsmallT : ¬ rOn b c d → tt ≤ z^2/4 := by
    intro hnr
    exact qpow_t_upper_of_not_r a b c d h hnr
  have hsmallE : ¬ eOn a b → eWeight a b = 0 := fun he => eweight_zero_of_not_e a b he
  have hlargeE : eOn a b → eWeight a b = ee := by
    intro he
    simp [eWeight, he, eExponent, ee]
  have hEe : eOn a b → 0 ≤ ee-1 := by
    intro he
    dsimp [ee]
    have heexp : 0 ≤ b+1-2*a := by
      dsimp [eOn] at he
      omega
    exact sub_nonneg.mpr (qpow_mono 0 _ heexp)
  have hz : z ≠ 0 := by positivity
  intro i
  change 0 ≤ margin z x hh ((2:ℚ)^(b-a-1)) (rWeight a b c d) (eWeight a b) i
  by_cases he : eOn a b
  · have hew := hlargeE he
    have hq : (2 : ℚ)^(b-a-1) = x*ee/4 := by
      simpa only [hew] using qweight_large_formula a b c d h he
    by_cases hr : rOn b c d
    · have hbeta : beta = 1 ∨ beta = 2 := beta_spec a b c d h hr
      have hcap : hh ≤ x * ee / (2*z^2) := by
        simpa only [hew] using qpow_h_cap_of_r a b c d h hr he
      have hi := large_t_large_e (z-4) (EE-1) (ee-1) (hh-1) beta
        hZ hT (hEe he) hH hbeta (by
          simpa only [sub_add_cancel, ← hxcoord, cap] using hcap)
      have hrw : rWeight a b c d = beta*x*ee/(2*hh*z^2) := by
        simpa only [hew, mul_assoc] using rweight_large_formula a b c d h hr he
      rw [hq,hrw,hew]
      simpa only [sub_add_cancel, ← hxcoord, largeTPositive] using hi i
    · have hlow : x*ee/z^2 ≤ hh := by
        simpa only [hew] using qpow_h_lower_of_not_r a b c d h hr he
      have hhigh : hh ≤ x*ee/4 := by
        simpa only [hew] using qpow_h_upper_of_domain a b c d h he
      have hi := small_t_large_e (z-4) (EE-1) (ee-1) hh
        hZ hT (hEe he) (by
          simpa only [sub_add_cancel, ← hxcoord] using hlow) (by
          simpa only [sub_add_cancel, ← hxcoord] using hhigh)
      rw [hq,rweight_zero_of_not_r a b c d hr,hew]
      simpa only [sub_add_cancel, ← hxcoord, smallTPositive] using hi i
  · have hew : eWeight a b = 0 := hsmallE he
    by_cases hr : rOn b c d
    · have hbeta : beta = 1 ∨ beta = 2 := beta_spec a b c d h hr
      have hq : (2 : ℚ)^(b-a-1) = hh*z^2*uu/2 :=
        (physical_regimes a b c d h).2.2 hr
      have hsmall : 0 ≤ x-8*(hh*z^2*uu/2) := by
        have hc := hnotEcut he
        have hqt : hh*tt = hh*z^2*uu/2 := hqsmall.symm.trans hq
        calc
          0 ≤ x-8*(hh*tt) := by nlinarith only [hc]
          _ = x-8*(hh*z^2*uu/2) := by rw [hqt]
      have hU : 0 ≤ uu-1 := by
        exact sub_nonneg.mpr (qpow_mono 0 (b-d-2*c) (Nat.zero_le _))
      have hi := large_t_small_e (z-4) (EE-1) (uu-1) (hh-1) beta
        hZ hT hU hH hbeta (by
          simpa only [sub_add_cancel, ← hxcoord] using hsmall)
      have hrw : rWeight a b c d = beta*uu := rweight_as_beta a b c d h hr
      rw [hq,hrw,hew]
      simpa only [sub_add_cancel, ← hxcoord, largeTZero] using hi i
    · have htop : tt ≤ z^2/4 := hsmallT hr
      have hsmall := hnotEcut he
      have hi := small_t_small_e (z-4) (EE-1) (hh-1) tt
        hZ hT hH (qpow_mono 0 (b-d-1) (Nat.zero_le _)) (by
          simpa only [sub_add_cancel] using htop) (by
          simpa only [sub_add_cancel, ← hxcoord] using hsmall)
      rw [hqsmall,rweight_zero_of_not_r a b c d hr,hew]
      simpa only [sub_add_cancel, ← hxcoord, smallTZero] using hi i

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLowXTail
