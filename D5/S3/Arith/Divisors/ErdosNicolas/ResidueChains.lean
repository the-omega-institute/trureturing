/- GID: D5/S3/Arith/Divisors/ErdosNicolas/ResidueChains
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/ErdosNicolas/ResidueChains
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Modular pair and triple estimates for the doubled-period residual. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Residual
import D5.S3.Arith.Divisors.ErdosNicolas.ChainBound
import D5.S3.Arith.Divisors.ErdosNicolas.TentKernel
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Induction

/-! Residue estimates used in prime-power divisor chains. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- The closed reciprocal expression for a residual with window length `2 * p`. -/
def residueProfile (p r : ℚ) : ℚ :=
  1 / r + 1 / (p - r) + 1 / (p + r) + 1 / (2 * p - r) - 3 / p

theorem residueProfile_symm (p r : ℚ) :
    residueProfile p (p - r) = residueProfile p r := by
  unfold residueProfile
  have h₁ : p - (p - r) = r := by ring
  have h₂ : p + (p - r) = 2 * p - r := by ring
  have h₃ : 2 * p - (p - r) = p + r := by ring
  rw [h₁, h₂, h₃]
  ring

private theorem reciprocal_pair_antitone {a p r s : ℚ} (ha : 0 ≤ a)
    (hr : 0 < r) (hrs : r ≤ s) (hs : r + s ≤ p) :
    1 / (a + s) + 1 / (a + p - s) ≤
      1 / (a + r) + 1 / (a + p - r) := by
  have hsr : 0 < s := lt_of_lt_of_le hr hrs
  have hp : 0 < p := by linarith
  have har : 0 < a + r := by linarith
  have has : 0 < a + s := by linarith
  have hapr : 0 < a + p - r := by linarith
  have haps : 0 < a + p - s := by linarith
  have heq (x : ℚ) (hx : 0 < a + x) (hpx : 0 < a + p - x) :
      1 / (a + x) + 1 / (a + p - x) =
        (2 * a + p) / ((a + x) * (a + p - x)) := by
    field_simp
    ring
  rw [heq s has haps, heq r har hapr]
  apply (div_le_div_iff₀ (mul_pos has haps) (mul_pos har hapr)).mpr
  have hprod : 0 ≤ (s - r) * (p - r - s) := by
    exact mul_nonneg (sub_nonneg.mpr hrs) (by linarith)
  have hcoef : 0 ≤ 2 * a + p := by linarith
  nlinarith [mul_nonneg hcoef hprod]

/-- The comparison includes the exact equality cases at both symmetric endpoints. -/
theorem residueProfile_antitone {p r s : ℚ} (hr : 0 < r)
    (hrs : r ≤ s) (hs : r + s ≤ p) :
    residueProfile p s ≤ residueProfile p r ∧
      (residueProfile p s = residueProfile p r ↔ r = s ∨ r + s = p) := by
  have hp : 0 ≤ p := by linarith
  have h₁ := reciprocal_pair_antitone (a := 0) (by norm_num) hr hrs hs
  have h₂ := reciprocal_pair_antitone hp hr hrs hs
  simp only [zero_add] at h₁
  have heq : p + p = 2 * p := by ring
  rw [heq] at h₂
  have hle : residueProfile p s ≤ residueProfile p r := by
    unfold residueProfile
    linarith
  refine ⟨hle, ?_⟩
  constructor
  · intro he
    by_contra h
    have hrs' : r < s := lt_of_le_of_ne hrs (by tauto)
    have hs' : r + s < p := lt_of_le_of_ne hs (by tauto)
    have hsp : 0 < p - s := by linarith
    have hrp : 0 < p - r := by linarith
    have hs0 : 0 < s := by linarith
    have hid : (1 / r + 1 / (p - r) - (1 / s + 1 / (p - s))) *
        (r * (p - r) * s * (p - s)) = p * (s - r) * (p - r - s) := by
      field_simp
      ring
    have hpos : 0 < p * (s - r) * (p - r - s) :=
      mul_pos (mul_pos (by linarith) (sub_pos.mpr hrs')) (by linarith)
    have hdpos : 0 < r * (p - r) * s * (p - s) := by positivity
    have hlt : 1 / s + 1 / (p - s) < 1 / r + 1 / (p - r) := by
      nlinarith only [hid, hpos, hdpos]
    unfold residueProfile at he
    linarith
  · rintro (rfl | he)
    · rfl
    · have he' : s = p - r := by linarith
      rw [he', residueProfile_symm]

private theorem profile_gap {p r : ℚ} (hp : p ≠ 0)
    (hpr : p - r ≠ 0) (hplus : p + r ≠ 0) (hdouble : 2 * p - r ≠ 0) :
    1 / r - residueProfile p r =
      (p ^ 3 - r * p ^ 2 - 5 * r ^ 2 * p + 3 * r ^ 3) /
        (p * (p - r) * (p + r) * (2 * p - r)) := by
  have hc : 1 / r - residueProfile p r =
      3 / p - 1 / (p - r) - 1 / (p + r) - 1 / (2 * p - r) := by
    unfold residueProfile
    ring
  rw [hc]
  have hd : p * 2 - r ≠ 0 := by simpa [mul_comm] using hdouble
  field_simp [hp, hpr, hplus, hdouble, hd]
  ring

/-- Both profile comparisons are exact at every nonsingular parameter pair. -/
theorem residueProfile_small {p r : ℚ}
    (hD : p * (p - r) * (p + r) * (2 * p - r) ≠ 0) :
    (residueProfile p r ≤ 1 / r ↔
      0 ≤ (p ^ 3 - r * p ^ 2 - 5 * r ^ 2 * p + 3 * r ^ 3) *
        (p * (p - r) * (p + r) * (2 * p - r))) ∧
    (residueProfile p r < 1 / r ↔
      0 < (p ^ 3 - r * p ^ 2 - 5 * r ^ 2 * p + 3 * r ^ 3) *
        (p * (p - r) * (p + r) * (2 * p - r))) := by
  have hn := hD
  have hd := (mul_ne_zero_iff.mp hn).2
  have hn' := (mul_ne_zero_iff.mp hn).1
  have hplus := (mul_ne_zero_iff.mp hn').2
  have hn'' := (mul_ne_zero_iff.mp hn').1
  have hpr := (mul_ne_zero_iff.mp hn'').2
  have hp := (mul_ne_zero_iff.mp hn'').1
  have he : 1 / r - residueProfile p r =
      ((p ^ 3 - r * p ^ 2 - 5 * r ^ 2 * p + 3 * r ^ 3) *
        (p * (p - r) * (p + r) * (2 * p - r))) /
        (p * (p - r) * (p + r) * (2 * p - r)) ^ 2 := by
    rw [profile_gap hp hpr hplus hd]
    field_simp <;> ring
  have hsq := sq_pos_of_ne_zero hD
  constructor
  · rw [← sub_nonneg, he, le_div_iff₀ hsq, zero_mul]
  · rw [← sub_pos, he, lt_div_iff₀ hsq, zero_mul]

#print axioms residueProfile_symm
#print axioms residueProfile_antitone
#print axioms residueProfile_small

/-- The four-site sum has an exact reciprocal closed form. -/
private theorem f_two_periods_eq_profile_interior {p r : ℕ} (hr : 0 < r) (hrp : r < p) :
    f p (2 * p) r = residueProfile p r := by
  have hp : 0 < p := by omega
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  have hrpq : (r : ℚ) < p := by exact_mod_cast hrp
  have hp0 : (p : ℚ) ≠ 0 := hpq.ne'
  have hr0 : (r : ℚ) ≠ 0 := hrq.ne'
  have hw (g : ℕ) (hg : 0 < g) (hgl : g ≤ 2 * p) :
      w (2 * p) g = 1 / (g : ℚ) - 2 / ((2 * p : ℕ) : ℚ) +
        (g : ℚ) / ((2 * p : ℕ) : ℚ) ^ 2 := by
    have he := inv_eq_K_add_w (L := 2 * p) hg
    rw [K_of_le hgl] at he
    rw [one_div]
    linarith
  rw [f_eq_four_terms hrp.le, hw r hr (by omega),
    hw (p - r) (by omega) (by omega), hw (p + r) (by omega) (by omega),
    hw (2 * p - r) (by omega) (by omega)]
  unfold residueProfile
  rw [Nat.cast_sub hrp.le, Nat.cast_sub (by omega : r ≤ 2 * p)]
  push_cast
  have hpr : (p : ℚ) - r ≠ 0 := by linarith
  have hplus : (p : ℚ) + r ≠ 0 := by linarith
  have hd : 2 * (p : ℚ) - r ≠ 0 := by linarith
  field_simp
  ring

private theorem residue_zero_weight (p : ℕ) :
    f p (2 * p) 0 = 1 / (2 * (p : ℚ)) := by
  rw [f_eq_four_terms (Nat.zero_le p)]
  by_cases hp : p = 0
  · simp [hp, w]
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  simp only [w, Nat.sub_zero, Nat.sub_self, Nat.cast_zero, mul_zero, div_zero,
    zero_add, add_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [show 2 * p - p = p by omega]
  push_cast
  field_simp
  ring

/-- The closed profile formula includes both endpoints with their exact correction. -/
theorem f_two_periods_eq_profile {p r : ℕ} (hrp : r ≤ p) :
    f p (2 * p) r = residueProfile p r +
      if r = 0 ∨ r = p then 1 / (p : ℚ) else 0 := by
  by_cases hp : p = 0
  · subst p
    have : r = 0 := by omega
    subst r
    norm_num [f, w, residueProfile]
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hzero : residueProfile p 0 + 1 / (p : ℚ) = 1 / (2 * (p : ℚ)) := by
    unfold residueProfile
    field_simp
    ring
  by_cases hr : r = 0
  · subst r
    simp only [true_or, if_true, Nat.cast_zero]
    rw [residue_zero_weight, hzero]
  by_cases he : r = p
  · subst r
    have hf : f p (2 * p) p = f p (2 * p) 0 := by
      rw [f_eq_four_terms le_rfl, f_eq_four_terms (Nat.zero_le p)]
      simp [w, Nat.mul_succ, two_mul, add_comm, add_left_comm]
    rw [hf, residue_zero_weight]
    simp only [or_true, if_true]
    have heq := residueProfile_symm (p : ℚ) 0
    simp only [sub_zero] at heq
    rw [heq]
    exact hzero.symm
  · simp only [hr, he, or_self, if_false, add_zero]
    exact f_two_periods_eq_profile_interior (by omega) (by omega)

private theorem profile_le_small {p r k : ℚ} (hp : 7 ≤ p)
    (hk : k = 1 ∨ k = 2 ∨ k = 4) (hp₄ : k = 4 → 41 / 4 ≤ p) (hkr : k ≤ r) (hkp : k ≤ p - r) :
    residueProfile p r < 1 / k := by
  have hkpos : 0 < k := by rcases hk with rfl | rfl | rfl <;> norm_num
  have hsmall : residueProfile p k < 1 / k := by
    have hp0 : 0 < p := by linarith
    have hpk : 0 < p - k := by
      rcases hk with rfl | rfl | rfl <;> linarith
    have hplus : 0 < p + k := by linarith
    have hd : 0 < 2 * p - k := by linarith
    apply (residueProfile_small (by positivity)).2.mpr
    apply mul_pos _ (by positivity)
    rcases hk with rfl | rfl | rfl
    · obtain ⟨t, ht, rfl⟩ := exists_nonneg_add_of_le hp
      ring_nf
      positivity
    · obtain ⟨t, ht, rfl⟩ := exists_nonneg_add_of_le hp
      ring_nf
      positivity
    · obtain ⟨t, ht, rfl⟩ := exists_nonneg_add_of_le (hp₄ rfl)
      ring_nf
      positivity
  by_cases hhalf : 2 * r ≤ p
  · exact (residueProfile_antitone hkpos hkr (by linarith)).1.trans_lt hsmall
  · rw [← residueProfile_symm p r]
    exact (residueProfile_antitone hkpos hkp (by linarith)).1.trans_lt hsmall

private def signedOne {p : ℕ} (x : ZMod p) : Prop := x = 1 ∨ x = -1

private theorem val_eq_neg_of_sub {p : ℕ} [NeZero p] {x : ZMod p} {j : ℕ}
    (h : p - x.val = j) : x = -(j : ZMod p) := by
  have hv : x.val < p := ZMod.val_lt x
  have heq : x.val + j = p := by omega
  have hz : x + (j : ZMod p) = 0 := by
    rw [← ZMod.natCast_zmod_val x, ← Nat.cast_add, heq]
    simp
  exact eq_neg_of_add_eq_zero_left hz

private theorem weight_le_one {p : ℕ} (hp : 7 ≤ p) [NeZero p]
    {x : ZMod p} : f p (2 * p) x.val < 1 := by
  by_cases hx : x = 0
  · subst x
    rw [ZMod.val_zero, residue_zero_weight]
    have hpq : (7 : ℚ) ≤ p := by exact_mod_cast hp
    have hp0 : (0 : ℚ) < p := by linarith
    apply (div_lt_iff₀ (by positivity)).2
    norm_num
    linarith
  have hv : 0 < x.val := Nat.pos_of_ne_zero ((ZMod.val_eq_zero x).not.mpr hx)
  have hvp : x.val < p := ZMod.val_lt x
  rw [f_two_periods_eq_profile hvp.le, if_neg (by omega), add_zero]
  have he := profile_le_small (p := (p : ℚ)) (r := (x.val : ℚ))
    (k := 1) (by
      exact_mod_cast hp) (Or.inl rfl) (by norm_num)
    (by exact_mod_cast hv) (by
      rw [← Nat.cast_sub hvp.le]
      exact_mod_cast (by omega : 1 ≤ p - x.val))
  simpa using he

private theorem weight_le_half {p : ℕ} (hp : 7 ≤ p) [NeZero p]
    {x : ZMod p} (hx₁ : ¬signedOne x) :
    f p (2 * p) x.val < 1 / 2 := by
  by_cases hx : x = 0
  · subst x
    rw [ZMod.val_zero, residue_zero_weight]
    have hpq : (7 : ℚ) ≤ p := by exact_mod_cast hp
    have hp0 : (0 : ℚ) < p := by linarith
    apply (div_lt_iff₀ (by positivity)).2
    norm_num
    linarith
  have hv : 0 < x.val := Nat.pos_of_ne_zero ((ZMod.val_eq_zero x).not.mpr hx)
  have hvp : x.val < p := ZMod.val_lt x
  have hv₁ : x.val ≠ 1 := by
    intro h
    apply hx₁
    left
    rw [← ZMod.natCast_zmod_val x, h]
    simp
  have hv₂ : p - x.val ≠ 1 := by
    intro h
    apply hx₁
    right
    simpa only [Nat.cast_one] using val_eq_neg_of_sub h
  rw [f_two_periods_eq_profile hvp.le, if_neg (by omega), add_zero]
  apply profile_le_small (by
      exact_mod_cast hp) (Or.inr (Or.inl rfl)) (by norm_num)
  · exact_mod_cast (by omega : 2 ≤ x.val)
  · rw [← Nat.cast_sub hvp.le]
    exact_mod_cast (by omega : 2 ≤ p - x.val)

private theorem weight_le_quarter {p : ℕ} (hp : 11 ≤ p) [NeZero p]
    {x : ZMod p}
    (hsmall : ∀ j : ℕ, 1 ≤ j → j ≤ 3 → x ≠ (j : ZMod p) ∧ x ≠ -(j : ZMod p)) :
    f p (2 * p) x.val < 1 / 4 := by
  by_cases hx : x = 0
  · subst x
    rw [ZMod.val_zero, residue_zero_weight]
    have hpq : (11 : ℚ) ≤ p := by exact_mod_cast hp
    have hp0 : (0 : ℚ) < p := by linarith
    apply (div_lt_iff₀ (by positivity)).2
    norm_num
    linarith
  have hv : 0 < x.val := Nat.pos_of_ne_zero ((ZMod.val_eq_zero x).not.mpr hx)
  have hvp : x.val < p := ZMod.val_lt x
  have hlow : 4 ≤ x.val := by
    by_contra h
    have hle : x.val ≤ 3 := by omega
    exact (hsmall x.val hv hle).1 (ZMod.natCast_zmod_val x).symm
  have hhigh : 4 ≤ p - x.val := by
    by_contra h
    have hpos : 1 ≤ p - x.val := by omega
    have hle : p - x.val ≤ 3 := by omega
    exact (hsmall (p - x.val) hpos hle).2 (val_eq_neg_of_sub rfl)
  rw [f_two_periods_eq_profile hvp.le, if_neg (by omega), add_zero]
  apply profile_le_small (by
      have : (11 : ℚ) ≤ p := by exact_mod_cast hp
      linarith) (Or.inr (Or.inr rfl)) (by
        intro _
        have : (11 : ℚ) ≤ p := by exact_mod_cast hp
        linarith)
  · exact_mod_cast hlow
  · rw [← Nat.cast_sub hvp.le]
    exact_mod_cast hhigh

private theorem not_adjacent_ones {p : ℕ} {q x : ZMod p}
    (hq : ¬signedOne q) (hx : signedOne x) : ¬signedOne (q * x) := by
  rcases hx with rfl | rfl
  · simpa [signedOne] using hq
  · intro h
    rcases h with h | h
    · apply hq
      right
      simpa using congrArg Neg.neg h
    · apply hq
      left
      simpa using congrArg Neg.neg h

private theorem middle_not_small {p : ℕ} (hp : 11 ≤ p) [NeZero p]
    {q x : ZMod p} (hq : ¬signedOne q) (hx : signedOne x)
    (hlast : signedOne (q * (q * x))) :
    ∀ j : ℕ, 1 ≤ j → j ≤ 3 → q * x ≠ (j : ZMod p) ∧ q * x ≠ -(j : ZMod p) := by
  have hnot (j : ℕ) (hj : j = 3 ∨ j = 5 ∨ j = 8 ∨ j = 10) :
      (j : ZMod p) ≠ 0 := by
    have hjpos : 0 < j := by rcases hj with rfl | rfl | rfl | rfl <;> omega
    have hjp : j < p := by rcases hj with rfl | rfl | rfl | rfl <;> omega
    simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using
      (show ¬p ∣ j from fun hd => (Nat.le_of_dvd hjpos hd).not_gt hjp)
  have hs : (q * x) ^ 2 = (1 : ZMod p) ∨ (q * x) ^ 2 = -1 := by
    have heq : (q * x) ^ 2 = (q * (q * x)) * x := by ring
    rcases hx with hx | hx <;> rcases hlast with hl | hl
    · left
      calc
        _ = (q * (q * x)) * x := heq
        _ = 1 := by rw [hl, hx]; norm_num
    · right
      calc
        _ = (q * (q * x)) * x := heq
        _ = -1 := by rw [hl, hx]; norm_num
    · right
      calc
        _ = (q * (q * x)) * x := heq
        _ = -1 := by rw [hl, hx]; norm_num
    · left
      calc
        _ = (q * (q * x)) * x := heq
        _ = 1 := by rw [hl, hx]; norm_num
  intro j hj hj₃
  have hjcases : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hjcases with rfl | rfl | rfl
  · simpa only [Nat.cast_one] using not_or.mp (not_adjacent_ones hq hx)
  all_goals
    constructor <;> intro he <;>
      rcases hs with hs | hs <;> rw [he] at hs <;> norm_num at hs
    all_goals
      first
      | exact hnot 3 (by omega) (by linear_combination hs)
      | exact hnot 5 (by omega) (by linear_combination hs)
      | exact hnot 8 (by omega) (by linear_combination hs)
      | exact hnot 10 (by omega) (by linear_combination hs)

/-- A nontrivial multiplier cannot put two consecutive residues at the endpoints. -/
private theorem residue_pair_bound {p : ℕ} (hp : 7 ≤ p) [NeZero p]
    {q x : ZMod p} (hq : q ≠ 1 ∧ q ≠ -1) :
    f p (2 * p) x.val + f p (2 * p) (q * x).val < 3 / 2 := by
  have hq' : ¬signedOne q := not_or.mpr hq
  by_cases hx₁ : signedOne x
  · have h₁ := weight_le_one hp (x := x)
    have h₂ := weight_le_half hp (not_adjacent_ones hq' hx₁)
    linarith
  · have h₁ := weight_le_half hp hx₁
    have h₂ := weight_le_one hp (x := q * x)
    linarith

/-- If the endpoints both have distance one, the middle has distance at least four. -/
private theorem residue_triple_bound {p : ℕ} (hp : 11 ≤ p) [NeZero p]
    {q x : ZMod p} (hq : q ≠ 1 ∧ q ≠ -1) :
    f p (2 * p) x.val + f p (2 * p) (q * x).val +
      f p (2 * p) (q * (q * x)).val < 9 / 4 := by
  have hp₇ : 7 ≤ p := by omega
  have hq' : ¬signedOne q := not_or.mpr hq
  have h₁ := weight_le_one hp₇ (x := x)
  have h₂ := weight_le_one hp₇ (x := q * x)
  have h₃ := weight_le_one hp₇ (x := q * (q * x))
  by_cases hx₁ : signedOne x
  · have hmid := not_adjacent_ones hq' hx₁
    by_cases hx₃ : signedOne (q * (q * x))
    · have hm := weight_le_quarter hp (middle_not_small hp hq' hx₁ hx₃)
      linarith
    · have hm := weight_le_half hp₇ hmid
      have hl := weight_le_half hp₇ hx₃
      linarith
  · have hfirst := weight_le_half hp₇ hx₁
    by_cases hx₂ : signedOne (q * x)
    · have hl := weight_le_half hp₇ (not_adjacent_ones hq' hx₂)
      linarith
    · have hm := weight_le_half hp₇ hx₂
      linarith

private theorem residue_orbit_bounds {p : ℕ} (hp : 2 ≤ p) (hp₄ : p ≠ 4) (hp₅ : p ≠ 5) :
    ∀ q x : ZMod p, q ≠ 1 ∧ q ≠ -1 →
      f p (2 * p) x.val + f p (2 * p) (q * x).val < 3 / 2 ∧
      f p (2 * p) x.val + f p (2 * p) (q * x).val +
        f p (2 * p) (q * (q * x)).val < 9 / 4 := by
  by_cases hlarge : 11 ≤ p
  · let : NeZero p := ⟨by omega⟩
    intro q x hq
    exact ⟨residue_pair_bound (by omega) hq, residue_triple_bound hlarge hq⟩
  have hsmall : p = 2 ∨ p = 3 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 := by omega
  rcases hsmall with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem signedOne_of_prime_factors {p n : ℕ} (hn : n ≠ 0)
    (h : ∀ q, q.Prime → q ∣ n → signedOne (q : ZMod p)) :
    signedOne (n : ZMod p) := by
  induction n using Nat.recOnMul with
  | zero => exact False.elim (hn rfl)
  | one => simp [signedOne]
  | prime q hq => exact h q hq dvd_rfl
  | mul a b ha hb =>
    have ha' := ha (mul_ne_zero_iff.mp hn).1
      (fun q hq hd => h q hq (hd.trans (dvd_mul_right a b)))
    have hb' := hb (mul_ne_zero_iff.mp hn).2
      (fun q hq hd => h q hq (hd.trans (dvd_mul_left b a)))
    rw [Nat.cast_mul]
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;>
      simp [signedOne, ha', hb']

/-- Any divisor outside the two signed residue classes forces the strict average bound. -/
private theorem residue_average_from_divisor {p q m : ℕ} (hp : 2 ≤ p)
    (hp₄ : p ≠ 4) (hp₅ : p ≠ 5) (hqm : q ∣ m) (hm : m ≠ 0)
    (hqmod : (q : ZMod p) ≠ 1 ∧ (q : ZMod p) ≠ -1) :
    (∑ d ∈ m.divisors, f p (2 * p) (d % p)) < (3 / 4 : ℚ) * m.divisors.card := by
  let : NeZero p := ⟨by omega⟩
  have hq0 : q ≠ 0 := fun h => hm (by simpa [h] using hqm)
  have hex : ∃ s, s.Prime ∧ s ∣ q ∧ ¬signedOne (s : ZMod p) := by
    by_contra! h
    exact (not_or.mpr hqmod) (signedOne_of_prime_factors hq0 h)
  obtain ⟨s, hs, hsq, hsmod⟩ := hex
  apply divisor_chain_average_lt (Or.inr hs) (hsq.trans hqm) hm
    (fun d => f p (2 * p) (d % p)) (3 / 4)
  · intro r _
    have he := (residue_orbit_bounds hp hp₄ hp₅ (s : ZMod p) (r : ZMod p)
      (not_or.mp hsmod)).1
    norm_num only [← Nat.cast_mul, ZMod.val_natCast] at he ⊢
    exact he
  · intro r _
    have he := (residue_orbit_bounds hp hp₄ hp₅ (s : ZMod p) (r : ZMod p)
      (not_or.mp hsmod)).2
    have hmul : s * (s * r) = s ^ 2 * r := by ring
    norm_num only [← Nat.cast_mul, ZMod.val_natCast, hmul] at he ⊢
    exact he

private theorem profile_one_gt_three_quarters {p : ℕ} (hp : 2 ≤ p) :
    (3 / 4 : ℚ) < residueProfile p 1 := by
  have hpq : (2 : ℚ) ≤ p := by exact_mod_cast hp
  have hp0 : (p : ℚ) ≠ 0 := by positivity
  have hminus : (p : ℚ) - 1 ≠ 0 := by linarith
  have hplus : (p : ℚ) + 1 ≠ 0 := by positivity
  have hdouble : 2 * (p : ℚ) - 1 ≠ 0 := by linarith
  have hid : (residueProfile p 1 - 3 / 4) *
      (4 * (p : ℚ) * (p - 1) * (p + 1) * (2 * p - 1)) =
      2 * (p : ℚ) ^ 4 - 5 * p ^ 3 + 2 * p ^ 2 + 21 * p - 12 := by
    unfold residueProfile
    have hd' : (p : ℚ) * 2 - 1 ≠ 0 := by linarith
    field_simp [hp0, hminus, hplus, hdouble, hd']
    ring
  have hpoly : 0 < 2 * (p : ℚ) ^ 4 - 5 * p ^ 3 + 2 * p ^ 2 + 21 * p - 12 := by
    obtain ⟨t, ht, heq⟩ := exists_nonneg_add_of_le hpq
    rw [← heq]
    ring_nf
    positivity
  have hD : 0 < 4 * (p : ℚ) * (p - 1) * (p + 1) * (2 * p - 1) := by
    apply mul_pos (mul_pos (mul_pos (by positivity) (by linarith)) (by positivity))
      (by linarith)
  have hprod : 0 < (residueProfile p 1 - 3 / 4) *
      (4 * (p : ℚ) * (p - 1) * (p + 1) * (2 * p - 1)) := by
    rw [hid]
    exact hpoly
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hD).mp hprod)

private theorem weight_signedOne {p : ℕ} (hp : 2 ≤ p) {x : ZMod p}
    (hx : signedOne x) : f p (2 * p) x.val = residueProfile p 1 := by
  rcases hx with rfl | rfl
  · rw [ZMod.val_one'' (by omega)]
    exact f_two_periods_eq_profile_interior (by omega) (by omega)
  · have hv : (-1 : ZMod p).val = p - 1 := by
      cases p with
      | zero => omega
      | succ n => simpa using ZMod.val_neg_one n
    rw [hv, f_two_periods_eq_profile_interior (by omega)
      (by omega), Nat.cast_sub (by omega)]
    norm_num only [Nat.cast_one]
    exact residueProfile_symm (p : ℚ) 1

/-- Strict, equality and weak average bounds classify all divisor residue patterns. -/
theorem residue_average_three_quarters {p m : ℕ} (hp : 2 ≤ p)
    (hp₄ : p ≠ 4) (hp₅ : p ≠ 5) :
    ((∑ d ∈ m.divisors, f p (2 * p) (d % p)) < (3 / 4 : ℚ) * m.divisors.card ↔
      ∃ q ∈ m.divisors, (q : ZMod p) ≠ 1 ∧ (q : ZMod p) ≠ -1) ∧
    ((∑ d ∈ m.divisors, f p (2 * p) (d % p)) = (3 / 4 : ℚ) * m.divisors.card ↔
      m = 0) ∧
    ((∑ d ∈ m.divisors, f p (2 * p) (d % p)) ≤ (3 / 4 : ℚ) * m.divisors.card ↔
      m = 0 ∨ ∃ q ∈ m.divisors, (q : ZMod p) ≠ 1 ∧ (q : ZMod p) ≠ -1) := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hE : ∃ q ∈ m.divisors, (q : ZMod p) ≠ 1 ∧ (q : ZMod p) ≠ -1
  · obtain ⟨q, hq, hqmod⟩ := hE
    have hlt := residue_average_from_divisor hp hp₄ hp₅ (Nat.dvd_of_mem_divisors hq)
      (Nat.mem_divisors.mp hq).2 hqmod
    exact ⟨iff_of_true hlt ⟨q, hq, hqmod⟩, iff_of_false (ne_of_lt hlt) hm,
      iff_of_true hlt.le (Or.inr ⟨q, hq, hqmod⟩)⟩
  · have heq : (∑ d ∈ m.divisors, f p (2 * p) (d % p)) =
        (m.divisors.card : ℚ) * residueProfile p 1 := by
      calc
        _ = ∑ _d ∈ m.divisors, residueProfile p 1 := by
          apply sum_congr rfl
          intro d hd
          have hx : signedOne (d : ZMod p) := by
            by_cases hd1 : (d : ZMod p) = 1
            · exact Or.inl hd1
            · exact Or.inr (by
                by_contra hdneg
                exact hE ⟨d, hd, hd1, hdneg⟩)
          simpa only [ZMod.val_natCast] using weight_signedOne hp hx
        _ = _ := by simp
    have ht : (0 : ℚ) < m.divisors.card := by
      exact_mod_cast card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm⟩
    have hmul := mul_lt_mul_of_pos_right (profile_one_gt_three_quarters hp) ht
    have hgt : (3 / 4 : ℚ) * m.divisors.card <
        ∑ d ∈ m.divisors, f p (2 * p) (d % p) := by
      rw [heq]
      nlinarith
    exact ⟨iff_of_false (not_lt_of_ge hgt.le) hE,
      iff_of_false (Ne.symm (ne_of_lt hgt)) hm,
      iff_of_false (not_le_of_gt hgt) (not_or.mpr ⟨hm, hE⟩)⟩

#print axioms f_two_periods_eq_profile
#print axioms residue_pair_bound
#print axioms residue_triple_bound
#print axioms residue_average_three_quarters

end D5.S3.Arith.ErdosNicolas
