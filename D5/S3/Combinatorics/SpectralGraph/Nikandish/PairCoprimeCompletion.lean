/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairCoprimeCompletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/PairCoprimeCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/SpectralGraph/Nikandish/PairCoprimeCompletion.actual_nonintegral; premises=D5/S3/Combinatorics/SpectralGraph/Nikandish/PairCoprimeCompletion.small_three_nonzero
   digest: Complete coprime repeated-minimum obstruction with all unbounded-tail quadratic rows. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairLowArithmetic

/-! Source: four-prime-coprime-completion, supplied PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. All eleven original
quadratic rows are retained. The a=7 branch is proved by its two
complete quadratic rows instead of borrowing an unproved modular
theorem. No upper bound is imposed on the other tail. -/
set_option autoImplicit false
noncomputable section
open Matrix
namespace D5.S3.Combinatorics.SpectralGraph.PairCoprimeCompletion
open PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants
open PairedIdealIntersectionLift IdealIntersectionSupport IdealIntersectionObstructions

theorem two_nonzero (a b c : ℤ) (ha : 5≤a)
    (hcop : IsCoprime ((a-1)*(a-2)) (b*c)) :
    (tensorK a b c-(2:ℤ) • 1).det≠0 := by
  intro hr
  have hd:=PairRootArithmetic.root_divides a b c 2 hr
  have hd' : a-1∣3*(b*c)^2 := by convert hd using 1 <;> ring
  have hdiv:=hcop.of_mul_left_left.pow_right (n:=2) |>.dvd_of_dvd_mul_right hd'
  have hh:=Int.le_of_dvd (by norm_num : (0:ℤ)<3) hdiv
  omega

theorem three_exception (a b c : ℤ) (ha : 5≤a)
    (hcop : IsCoprime ((a-1)*(a-2)) (b*c))
    (hr : (tensorK a b c-(3:ℤ) • 1).det=0) :
    a=6 ∨ a=7 ∨ a=12 ∨ a=22 := by
  have hd:=PairRootArithmetic.root_divides a b c 3 hr
  have hd' : a-2∣20*(b*c)^2 := by convert hd using 1 <;> ring
  have hdiv:=hcop.of_mul_left_right.pow_right (n:=2) |>.dvd_of_dvd_mul_right hd'
  have hh:=Int.le_of_dvd (by norm_num : (0:ℤ)<20) hdiv
  have hu : a≤22 := by omega
  interval_cases a <;> norm_num at hdiv <;> norm_num

/-- Complete small-tail reduction. All other integer tails remain
unbounded; the eleven supplied rows and the two a=7 rows are exact. -/
theorem small_three_nonzero (a b c : ℤ)
    (ha : a=6 ∨ a=7 ∨ a=12 ∨ a=22)
    (hb : a≤b) (hu : b≤2*a-3)
    (hcop : IsCoprime ((a-1)*(a-2)) b) :
    (tensorK a b c-(3:ℤ) • 1).det≠0 := by
  rcases ha with rfl | rfl | rfl | rfl
  · have hlist : b=7 ∨ b=9 := by
      interval_cases b <;> norm_num [Int.isCoprime_iff_gcd_eq_one] at hcop <;> norm_num
    rcases hlist with rfl | rfl
    · have he : (tensorK (6:ℤ) 7 c-(3:ℤ) • 1).det=
          4*(-1085*c^2+8417*c-848) := by rw [det_tensorK_sub_scalar]; ring
      rw [he]
      exact mul_ne_zero (by norm_num) (PairFourEndpoints.quadratic_gap _ _ _ c
        8195 (by norm_num) (by norm_num) (by norm_num))
    · have he : (tensorK (6:ℤ) 9 c-(3:ℤ) • 1).det=
          4*(-1847*c^2+11381*c-2144) := by rw [det_tensorK_sub_scalar]; ring
      rw [he]
      exact mul_ne_zero (by norm_num) (PairFourEndpoints.quadratic_gap _ _ _ c
        10662 (by norm_num) (by norm_num) (by norm_num))
  · have hlist : b=7 ∨ b=11 := by
      interval_cases b <;> norm_num [Int.isCoprime_iff_gcd_eq_one] at hcop <;> norm_num
    rcases hlist with rfl | rfl
    · have he : (tensorK (7:ℤ) 7 c-(3:ℤ) • 1).det=
          15*(-353*c^2+4338*c-61) := by rw [det_tensorK_sub_scalar]; ring
      rw [he]
      exact mul_ne_zero (by norm_num) (PairFourEndpoints.quadratic_gap _ _ _ c
        4328 (by norm_num) (by norm_num) (by norm_num))
    · have he : (tensorK (7:ℤ) 11 c-(3:ℤ) • 1).det=
          15*(-937*c^2+7438*c-1209) := by rw [det_tensorK_sub_scalar]; ring
      rw [he]
      exact mul_ne_zero (by norm_num) (PairFourEndpoints.quadratic_gap _ _ _ c
        7126 (by norm_num) (by norm_num) (by norm_num))
  · have hlist : b=13 ∨ b=17 ∨ b=19 ∨ b=21 := by
      interval_cases b <;> norm_num [Int.isCoprime_iff_gcd_eq_one] at hcop <;> norm_num
    rcases hlist with rfl | rfl | rfl | rfl
    · have he : (tensorK (12:ℤ) 13 c-(3:ℤ) • 1).det=
          10*(-4238*c^2+121085*c+6802) := by rw [det_tensorK_sub_scalar]; ring
      rw [he]
      exact mul_ne_zero (by norm_num) (PairFourEndpoints.quadratic_gap _ _ _ c
        121560 (by norm_num) (by norm_num) (by norm_num))
    · have he : (tensorK (12:ℤ) 17 c-(3:ℤ) • 1).det=
          90*(-874*c^2+18581*c-462) := by rw [det_tensorK_sub_scalar]; ring
      rw [he]
      exact mul_ne_zero (by norm_num) (PairFourEndpoints.quadratic_gap _ _ _ c
        18537 (by norm_num) (by norm_num) (by norm_num))
    · have he : (tensorK (12:ℤ) 19 c-(3:ℤ) • 1).det=
          10*(-10100*c^2+192017*c-11822) := by rw [det_tensorK_sub_scalar]; ring
      rw [he]
      exact mul_ne_zero (by norm_num) (PairFourEndpoints.quadratic_gap _ _ _ c
        190769 (by norm_num) (by norm_num) (by norm_num))
    · have he : (tensorK (12:ℤ) 21 c-(3:ℤ) • 1).det=
          10*(-12614*c^2+217949*c-20942) := by rw [det_tensorK_sub_scalar]; ring
      rw [he]
      exact mul_ne_zero (by norm_num) (PairFourEndpoints.quadratic_gap _ _ _ c
        215511 (by norm_num) (by norm_num) (by norm_num))
  · have hlist : b=23 ∨ b=29 ∨ b=31 ∨ b=37 ∨ b=41 := by
      interval_cases b <;> norm_num [Int.isCoprime_iff_gcd_eq_one] at hcop <;> norm_num
    rcases hlist with rfl | rfl | rfl | rfl | rfl
    · have he : (tensorK (22:ℤ) 23 c-(3:ℤ) • 1).det=
          180*(-2001*c^2+142585*c+17568) := by rw [det_tensorK_sub_scalar]; ring
      rw [he]
      exact mul_ne_zero (by norm_num) (PairFourEndpoints.quadratic_gap _ _ _ c
        143077 (by norm_num) (by norm_num) (by norm_num))
    · have he : (tensorK (22:ℤ) 29 c-(3:ℤ) • 1).det=
          180*(-3551*c^2+188573*c+10992) := by rw [det_tensorK_sub_scalar]; ring
      rw [he]
      exact mul_ne_zero (by norm_num) (PairFourEndpoints.quadratic_gap _ _ _ c
        188986 (by norm_num) (by norm_num) (by norm_num))
    · have he : (tensorK (22:ℤ) 31 c-(3:ℤ) • 1).det=
          60*(-12491*c^2+614283*c+23456) := by rw [det_tensorK_sub_scalar]; ring
      rw [he]
      exact mul_ne_zero (by norm_num) (PairFourEndpoints.quadratic_gap _ _ _ c
        615236 (by norm_num) (by norm_num) (by norm_num))
    · have he : (tensorK (22:ℤ) 37 c-(3:ℤ) • 1).det=
          60*(-18869*c^2+767703*c-13936) := by rw [det_tensorK_sub_scalar]; ring
      rw [he]
      exact mul_ne_zero (by norm_num) (PairFourEndpoints.quadratic_gap _ _ _ c
        767017 (by norm_num) (by norm_num) (by norm_num))
    · have he : (tensorK (22:ℤ) 41 c-(3:ℤ) • 1).det=
          180*(-7947*c^2+292141*c-15408) := by rw [det_tensorK_sub_scalar]; ring
      rw [he]
      exact mul_ne_zero (by norm_num) (PairFourEndpoints.quadratic_gap _ _ _ c
        291301 (by norm_num) (by norm_num) (by norm_num))

private theorem large_tail_two (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 5≤a)
    (hb : 2*a-2≤b) (hc : 2*a-2≤c)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a b c))) :
    (tensorK (a:ℤ) b c-(2:ℤ) • 1).det=0 := by
  obtain ⟨e,hel,heu,v,hv,hS⟩:=PairLowArithmetic.large_tail_low
    (a:ℝ) b c (by exact_mod_cast (show 2≤a by omega))
    (by have hi : (2:ℝ)*a≤b+2 := by exact_mod_cast (show 2*a≤b+2 by omega)
        linarith)
    (by have hi : (2:ℝ)*a≤c+2 := by exact_mod_cast (show 2*a≤c+2 by omega)
        linarith)
  obtain ⟨h,hh,hT⟩:=tensor_eigenpair_of_symmetric (a:ℝ) b c
    (by exact_mod_cast (show 0<b by omega)) (by exact_mod_cast (show 0<c by omega))
    e v hv hS
  obtain ⟨z,hz⟩:=PairTailSpectrum.integer_tensor_root p hp hinj a b c
    (by omega) (by omega) (by omega) H e h hh hT
  have hzl : (1:ℤ)<z := by exact_mod_cast (hz ▸ hel)
  have hzu : z<(3:ℤ) := by exact_mod_cast (hz ▸ heu)
  have he : z=2 := by omega
  have hd:=PairTailSpectrum.integer_det_zero a b c (z-a-1) e
    (by push_cast; linarith) h hh hT
  have ht : (a:ℤ)+1+(z-a-1)=2 := by omega
  rwa [ht] at hd

/-- Every positive repeated-minimum vector with the original endpoint
coprimality condition is nonintegral. Neither tail is bounded above. -/
theorem actual_nonintegral (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 5≤a) (hb : a≤b) (hc : a≤c)
    (hcop : Nat.Coprime ((a-1)*(a-2)) (b*c)) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a b c)) := by
  have hI : IsCoprime (((a:ℤ)-1)*((a:ℤ)-2)) ((b:ℤ)*c) := by
    simpa only [Nat.cast_mul,Nat.cast_sub (by omega : 1≤a),
      Nat.cast_sub (by omega : 2≤a),Nat.cast_one,Nat.cast_ofNat] using hcop.isCoprime
  have h2:=two_nonzero (a:ℤ) b c (by exact_mod_cast ha) hI
  intro H
  by_cases hlarge : 2*a-2≤b ∧ 2*a-2≤c
  · exact h2 (large_tail_two p hp hinj a b c ha hlarge.1 hlarge.2 H)
  have h3 := (PairLowArithmetic.actual_low_root p hp hinj a b c ha hb hc H).resolve_left h2
  have hex:=three_exception (a:ℤ) b c (by exact_mod_cast ha) hI h3
  by_cases hbs : b<2*a-2
  · exact small_three_nonzero (a:ℤ) b c hex (by exact_mod_cast hb)
      (by omega) hI.of_mul_right_left h3
  · have hcs : c<2*a-2 := by omega
    have hswap : (tensorK (a:ℤ) c b-(3:ℤ) • 1).det=
        (tensorK (a:ℤ) b c-(3:ℤ) • 1).det := by
      rw [det_tensorK_sub_scalar,det_tensorK_sub_scalar]; ring
    exact small_three_nonzero (a:ℤ) c b hex (by exact_mod_cast hc)
      (by omega) hI.of_mul_right_right (hswap.trans h3)

end D5.S3.Combinatorics.SpectralGraph.PairCoprimeCompletion
