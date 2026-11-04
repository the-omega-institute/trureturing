/- GID: D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionEndpoints
   mirror-E: none(waiver:source-only-positive-theorem)
   anchors: []
   utility: none
   digest: General integer endpoint exclusions for paired ideal-intersection operators. -/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic

/-!
The paired endpoint polynomials are from `paper/sections/unit-exponent.tex`,
`the-omega-institute/ideal-intersection-laplacian`, public revision
`b93becea662a746badeadba42fdc3d3eb3db9382`. The general parity, sign and integer-gap
arguments follow the completed source note `mathematical-result.md` supplied on
2026-11-02. These independently authored formal proofs use no discriminant
nonsquare table, exponent sample or exceptional mod-17 certificate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionEndpoints

/-- The exact endpoint determinant for the paired exponent two. -/
def P2 {R : Type*} [CommRing R] (b c : R) : R :=
  -5*b^2*c^2 + 12*b^2*c - 3*b^2 + 12*b*c^2 + 48*b*c + 8*b - 3*c^2 + 8*c + 3

/-- The exact endpoint determinant for the paired exponent three. -/
def P3 {R : Type*} [CommRing R] (b c : R) : R :=
  -7*b^2*c^2 + 48*b^2*c - 8*b^2 + 48*b*c^2 + 302*b*c + 76*b - 8*c^2 + 76*c + 40

private lemma P2_symm {R : Type*} [CommRing R] (b c : R) : P2 b c = P2 c b := by
  unfold P2; ring

private lemma P3_symm {R : Type*} [CommRing R] (b c : R) : P3 b c = P3 c b := by
  unfold P3; ring

private lemma P2_not_both_even (b c : ℤ) (hz : P2 b c = 0) : ¬(Even b ∧ Even c) := by
  rintro ⟨hb, hc⟩
  obtain ⟨u, hu⟩ := even_iff_two_dvd.mp hb
  obtain ⟨v, hv⟩ := even_iff_two_dvd.mp hc
  subst b
  subst c
  have he : (2 : ℤ) ∣ P2 (2*u) (2*v) - 1 := by
    refine ⟨-40*u^2*v^2+48*u^2*v-6*u^2+48*u*v^2+96*u*v+8*u-6*v^2+8*v+1, ?_⟩
    unfold P2
    ring
  rw [hz] at he
  norm_num at he

private lemma P2_excludes_one_mod_three (b c : ℤ) (hb : (b : ZMod 3) = 1) :
    P2 b c ≠ 0 := by
  intro hz
  have he := congrArg (fun z : ℤ => (z : ZMod 3)) hz
  simp only [P2, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
    Int.cast_ofNat, Int.cast_neg, Int.cast_zero] at he
  rw [hb] at he
  norm_num at he
  have h3 : (3 : ZMod 3) = 0 := by decide
  have hsq : ((c : ZMod 3) + 1)^2 = -1 := by
    linear_combination he - ((c : ZMod 3)^2 + 22*(c : ZMod 3) + 2)*h3
  have hcontra := ZMod.mod_four_ne_three_of_sq_eq_neg_one hsq
  norm_num at hcontra

private lemma P2_negative_region (b c : ℤ) (hb : 6 ≤ b) (hc : 7 ≤ c) : P2 b c < 0 := by
  let d := 5*b^2-12*b+3
  let e := (3*b+1)*(b-3)
  let q := 12*b^2+48*b+8
  have hbb : 0 ≤ b*(b-6) := mul_nonneg (by omega) (by omega)
  have hd : 0 < d := by dsimp [d]; nlinarith
  have he : 0 < e := mul_pos (by omega) (by omega)
  have h7 : 0 < 7*d-q := by dsimp [d,q]; nlinarith
  have hdc : 0 < d*c-q := by
    have hh := mul_nonneg hd.le (show 0 ≤ c-7 by omega)
    nlinarith
  have hid : P2 b c = -c*(d*c-q)-e := by dsimp [P2,d,q,e]; ring
  rw [hid]
  have hh : 0 < c*(d*c-q) := mul_pos (by omega) hdc
  linarith

private lemma P2_row_two (c : ℤ) : P2 2 c = c^2+152*c+7 := by unfold P2; ring
private lemma P2_row_three (c : ℤ) : P2 3 c = 4*c*(65-3*c) := by unfold P2; ring
private lemma P2_row_five (c : ℤ) : P2 5 c = -4*(c-8)*(17*c-1) := by unfold P2; ring

private lemma P2_zero_ordered (b c : ℤ) (hb : 2 ≤ b) (hbc : b ≤ c)
    (hz : P2 b c = 0) : b = 5 ∧ c = 8 := by
  have hb5 : b ≤ 5 := by
    by_contra! hh
    by_cases hc7 : 7 ≤ c
    · exact (P2_negative_region b c hh hc7).ne hz
    · have h6b : b = 6 := by omega
      have h6c : c = 6 := by omega
      exact P2_not_both_even b c hz ⟨h6b ▸ (by decide), h6c ▸ (by decide)⟩
  have hb4 : b ≠ 4 := by
    intro h
    apply P2_excludes_one_mod_three b c ?_ hz
    rw [h]
    decide
  have hcases : b = 2 ∨ b = 3 ∨ b = 5 := by omega
  rcases hcases with h | h | h
  · rw [h, P2_row_two] at hz
    nlinarith [sq_nonneg c]
  · rw [h, P2_row_three] at hz
    have hc0 : c ≠ 0 := by omega
    have hh : 65-3*c = 0 := by
      rcases mul_eq_zero.mp hz with hh | hh
      · rcases mul_eq_zero.mp hh with hh | hh
        · norm_num at hh
        · exact (hc0 hh).elim
      · exact hh
    omega
  · refine ⟨h, ?_⟩
    rw [h, P2_row_five] at hz
    have hc : 5 ≤ c := by omega
    have hp : 17*c-1 ≠ 0 := by omega
    have h8 : -4*(c-8) = 0 := (mul_eq_zero.mp hz).resolve_right hp
    omega

/-- The paired-two endpoint has exactly the two exchanged exceptional pairs,
throughout the unbounded integer quadrant. -/
theorem P2_zero_iff (b c : ℤ) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    P2 b c = 0 ↔ (b = 5 ∧ c = 8) ∨ (b = 8 ∧ c = 5) := by
  constructor
  · intro hz
    rcases le_total b c with hbc | hcb
    · exact Or.inl (P2_zero_ordered b c hb hbc hz)
    · have hh := P2_zero_ordered c b hc hcb (by rwa [P2_symm])
      exact Or.inr ⟨hh.2, hh.1⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rw [P2_row_five]; ring
    · rw [P2_symm, P2_row_five]; ring


private lemma P3_in_product_sum (b c : ℤ) :
    P3 b c = -7*(b*c)^2+48*(b*c)*(b+c)-8*(b+c)^2+
      318*(b*c)+76*(b+c)+40 := by unfold P3; ring

private lemma P3_even_coordinates (b c : ℤ) (hz : P3 b c = 0) : Even b ∧ Even c := by
  let p := b*c
  let s := b+c
  have he : -7*p^2+48*p*s-8*s^2+318*p+76*s+40 = 0 := by
    simpa only [p,s, ← P3_in_product_sum] using hz
  have hp2 : (2 : ℤ) ∣ p^2 := by
    refine ⟨-3*p^2+24*p*s-4*s^2+159*p+38*s+20, ?_⟩
    linear_combination -he
  have hprime : Prime (2 : ℤ) := by norm_num
  have hp : (2 : ℤ) ∣ p := hprime.dvd_of_dvd_pow hp2
  obtain ⟨r, hr⟩ := hp
  have h8 : (8 : ℤ) ∣ p^2+6*p+4*s := by
    refine ⟨p^2-6*p*s+s^2-39*p-9*s-5, ?_⟩
    linear_combination he
  have hrr : Even (r*(r+3)) := by
    obtain ⟨z,hz⟩ := Int.even_mul_succ_self r
    refine ⟨z+r, ?_⟩
    calc
      r*(r+3) = r*(r+1)+2*r := by ring
      _ = (z+r)+(z+r) := by rw [hz]; ring
  obtain ⟨z,hz⟩ := even_iff_two_dvd.mp hrr
  have h8p : (8 : ℤ) ∣ p^2+6*p := by
    refine ⟨z, ?_⟩
    rw [hr]
    calc
      (2*r)^2+6*(2*r) = 4*(r*(r+3)) := by ring
      _ = 8*z := by rw [hz]; ring
  have h8s : (8 : ℤ) ∣ 4*s := by
    convert dvd_sub h8 h8p using 1 <;> ring
  have hs : (2 : ℤ) ∣ s := by
    obtain ⟨w,hw⟩ := h8s
    exact ⟨w, by omega⟩
  have hbc : (2 : ℤ) ∣ b*c := by simpa only [p] using (show (2 : ℤ) ∣ p from ⟨r,hr⟩)
  rcases hprime.dvd_or_dvd hbc with hb | hc
  · refine ⟨even_iff_two_dvd.mpr hb, even_iff_two_dvd.mpr ?_⟩
    simpa only [s, add_sub_cancel_left] using dvd_sub hs hb
  · refine ⟨even_iff_two_dvd.mpr ?_, even_iff_two_dvd.mpr hc⟩
    simpa only [s, add_sub_cancel_right] using dvd_sub hs hc

private def Q (u v : ℤ) : ℤ :=
  -(14*u^2-48*u+4)*v^2+(48*u^2+151*u+19)*v-(4*u+1)*(u-5)

private lemma P3_even_substitution (u v : ℤ) : P3 (2*u) (2*v) = 8*Q u v := by
  unfold P3 Q
  ring

private lemma Q_positive_initial (u v : ℤ) (hu : 1 ≤ u) (hu3 : u ≤ 3)
    (huv : u ≤ v) : 0 < Q u v := by
  have hu0 : 0 ≤ u := by omega
  have hv : 0 < v := by omega
  have ha : 0 ≤ (u-1)*(3-u) := mul_nonneg (by omega) (by omega)
  have hb : 0 ≤ u*(4-u) := mul_nonneg hu0 (by omega)
  have hd : 0 < -(14*u^2-48*u+4) := by nlinarith
  have hB : 0 < 48*u^2+151*u+19 := by nlinarith [sq_nonneg u]
  have hC : 0 < -(4*u+1)*(u-5) := by nlinarith
  have h1 := mul_nonneg hd.le (sq_nonneg v)
  have h2 := mul_pos hB hv
  unfold Q
  nlinarith

private lemma Q_negative_tail (u v : ℤ) (hu : 9 ≤ u) (huv : u ≤ v) : Q u v < 0 := by
  let d := 14*u^2-48*u+4
  let B := 48*u^2+151*u+19
  let C := -(4*u+1)*(u-5)
  have hu0 : 0 ≤ u := by omega
  have hv : 0 < v := by omega
  have h2 : 0 ≤ u*(u-9) := mul_nonneg hu0 (by omega)
  have h3 : 0 ≤ u^2*(u-9) := mul_nonneg (sq_nonneg _) (by omega)
  have hd : 0 < d := by dsimp [d]; nlinarith
  have hC : C < 0 := by
    dsimp [C]
    have hh : 0 < (4*u+1)*(u-5) := mul_pos (by omega) (by omega)
    nlinarith
  have hquad : 0 < 30*u^2-147*u-19 := by nlinarith
  have hud : 0 < u*d-B := by dsimp [d,B]; nlinarith
  have hvd : 0 < d*v-B := by
    have hh := mul_nonneg hd.le (show 0 ≤ v-u by omega)
    nlinarith
  have hh := mul_pos hv hvd
  have he : Q u v = -v*(d*v-B)+C := by dsimp [Q,d,B,C]; ring
  rw [he]
  linarith

private lemma Q_row_four (v : ℤ) : Q 4 v = v*(36*(38-v)+23)+17 := by unfold Q; ring
private lemma Q_row_five (v : ℤ) : Q 5 v = -6*v*(19*v-329) := by unfold Q; ring
private lemma Q_row_six (v : ℤ) : Q 6 v = v*(220*(12-v)+13)-25 := by unfold Q; ring
private lemma Q_row_seven (v : ℤ) : Q 7 v = -2*(3*v-29)*(59*v-1) := by unfold Q; ring
private lemma Q_row_eight (v : ℤ) : Q 8 v = v*(516*(8-v)+171)-99 := by unfold Q; ring

private lemma Q_four_ne (v : ℤ) (hv : 4 ≤ v) : Q 4 v ≠ 0 := by
  rw [Q_row_four]
  by_cases h : v ≤ 38
  · have hh := mul_nonneg (show 0 ≤ v by omega) (show 0 ≤ 38-v by omega)
    nlinarith
  · have hh := mul_nonneg (show 0 ≤ v by omega) (show 0 ≤ v-39 by omega)
    nlinarith

private lemma Q_five_ne (v : ℤ) (hv : 5 ≤ v) : Q 5 v ≠ 0 := by
  rw [Q_row_five]
  intro h
  have hv0 : v ≠ 0 := by omega
  have hf : 19*v-329 = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · norm_num at h
      · exact (hv0 h).elim
    · exact h
  omega

private lemma Q_six_ne (v : ℤ) (hv : 6 ≤ v) : Q 6 v ≠ 0 := by
  rw [Q_row_six]
  by_cases h : v ≤ 12
  · have hh := mul_nonneg (show 0 ≤ v by omega) (show 0 ≤ 12-v by omega)
    nlinarith
  · have hh := mul_nonneg (show 0 ≤ v by omega) (show 0 ≤ v-13 by omega)
    nlinarith

private lemma Q_seven_ne (v : ℤ) (hv : 7 ≤ v) : Q 7 v ≠ 0 := by
  rw [Q_row_seven]
  intro h
  have h59 : 59*v-1 ≠ 0 := by omega
  have h3 : -2*(3*v-29) = 0 := (mul_eq_zero.mp h).resolve_right h59
  omega

private lemma Q_eight_ne (v : ℤ) (hv : 8 ≤ v) : Q 8 v ≠ 0 := by
  rw [Q_row_eight]
  by_cases h : v ≤ 8
  · have hh := mul_nonneg (show 0 ≤ v by omega) (show 0 ≤ 8-v by omega)
    nlinarith
  · have hh := mul_nonneg (show 0 ≤ v by omega) (show 0 ≤ v-9 by omega)
    nlinarith

private lemma Q_nonzero (u v : ℤ) (hu : 1 ≤ u) (huv : u ≤ v) : Q u v ≠ 0 := by
  by_cases h3 : u ≤ 3
  · exact (Q_positive_initial u v hu h3 huv).ne'
  by_cases h9 : 9 ≤ u
  · exact (Q_negative_tail u v h9 huv).ne
  have hh : u = 4 ∨ u = 5 ∨ u = 6 ∨ u = 7 ∨ u = 8 := by omega
  rcases hh with rfl | rfl | rfl | rfl | rfl
  · exact Q_four_ne v huv
  · exact Q_five_ne v huv
  · exact Q_six_ne v huv
  · exact Q_seven_ne v huv
  · exact Q_eight_ne v huv

private lemma P3_nonzero_ordered (b c : ℤ) (hb : 2 ≤ b) (hbc : b ≤ c) : P3 b c ≠ 0 := by
  intro hz
  obtain ⟨hbEven,hcEven⟩ := P3_even_coordinates b c hz
  obtain ⟨u,hu⟩ := even_iff_two_dvd.mp hbEven
  obtain ⟨v,hv⟩ := even_iff_two_dvd.mp hcEven
  subst b
  subst c
  rw [P3_even_substitution] at hz
  have hQ : Q u v = 0 := by omega
  exact Q_nonzero u v (by omega) (by omega) hQ

/-- The paired-three endpoint never vanishes anywhere in the unbounded integer quadrant. -/
theorem P3_nonzero (b c : ℤ) (hb : 2 ≤ b) (hc : 2 ≤ c) : P3 b c ≠ 0 := by
  rcases le_total b c with hbc | hcb
  · exact P3_nonzero_ordered b c hb hbc
  · rw [P3_symm]
    exact P3_nonzero_ordered c b hc hcb

end D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionEndpoints
