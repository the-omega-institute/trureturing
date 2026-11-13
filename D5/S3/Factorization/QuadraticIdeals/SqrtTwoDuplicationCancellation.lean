/- GID: D5/S3/Factorization/QuadraticIdeals/SqrtTwoDuplicationCancellation
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/SqrtTwoDuplicationCancellation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local cancellation bounds for primitive square-root-two duplication forms. -/

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic

/-! Local prime-power cancellation for the duplication forms in the explicit quadratic order. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.SqrtTwoDuplicationCancellation

/-- The explicit quadratic order, without an identification with a number field's integers. -/
abbrev Order := Zsqrtd 2

/-- The ramified square root of two. -/
def root : Order := Zsqrtd.sqrtd

/-- The norm-seven factor used by the model curve. -/
def delta : Order := 3 - root

/-- Numerator of duplication in homogeneous x-coordinates. -/
def numerator (a b : Order) : Order := (a ^ 2 + delta ^ 2 * b ^ 2) ^ 2

/-- Denominator of duplication in homogeneous x-coordinates. -/
def denominator (a b : Order) : Order := 4 * a * b * (a ^ 2 - delta ^ 2 * b ^ 2)

/-- The common ideal of the two homogeneous duplication forms. -/
def commonIdeal (a b : Order) : Ideal Order := Ideal.span {numerator a b, denominator a b}

private instance : Zsqrtd.Nonsquare 2 := ⟨by
  intro n hn
  have hn' : n ≤ 1 := by nlinarith
  interval_cases n <;> norm_num at hn⟩

private instance : IsDomain Order := inferInstanceAs (IsDomain (Zsqrtd (2 : ℕ)))

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem root_sq : root ^ 2 = (2 : Order) := by
  ext <;> norm_num [root, pow_two]

private theorem root_dvd_iff (z : Order) : root ∣ z ↔ (2 : ℤ) ∣ z.re := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.im, by simp [root]⟩
  · rintro ⟨k, hk⟩
    refine ⟨⟨z.im, k⟩, ?_⟩
    ext <;> simp [root, hk]

private theorem even_of_four_dvd_norm (x y : ℤ) (h : 4 ∣ x ^ 2 + 2 * y ^ 2) :
    2 ∣ x ∧ 2 ∣ y := by
  have hm := Int.emod_eq_zero_of_dvd h
  have hx := Int.sq_emod_four x
  have hy := Int.sq_emod_four y
  constructor <;> apply Int.dvd_of_emod_eq_zero <;> omega

private theorem four_dvd_of_sixteen_dvd_norm (x y : ℤ)
    (h : 16 ∣ x ^ 2 + 2 * y ^ 2) : 4 ∣ x ∧ 4 ∣ y := by
  obtain ⟨hx, hy⟩ := even_of_four_dvd_norm x y (dvd_trans (by norm_num) h)
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have h' : 4 ∣ u ^ 2 + 2 * v ^ 2 := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by nlinarith [hk]⟩
  obtain ⟨hu, hv⟩ := even_of_four_dvd_norm u v h'
  obtain ⟨u', hu'⟩ := hu
  obtain ⟨v', hv'⟩ := hv
  exact ⟨⟨u', by omega⟩, ⟨v', by omega⟩⟩

private theorem even_re_of_sum_squares (a c : Order)
    (hr : (4 : ℤ) ∣ (a ^ 2 + c ^ 2).re)
    (hi : (4 : ℤ) ∣ (a ^ 2 + c ^ 2).im) :
    (2 : ℤ) ∣ a.re ∧ (2 : ℤ) ∣ c.re := by
  have hr' := Int.emod_eq_zero_of_dvd hr
  have hr4 : (a.re ^ 2 + 2 * a.im ^ 2 + c.re ^ 2 + 2 * c.im ^ 2) % 4 = 0 := by
    convert hr' using 1 <;> simp only [pow_two, Zsqrtd.re_add, Zsqrtd.re_mul] <;> congr 1 <;> ring
  have har := Int.sq_emod_four a.re
  have hai := Int.sq_emod_four a.im
  have hcr := Int.sq_emod_four c.re
  have hci := Int.sq_emod_four c.im
  have hi2 : (a.re * a.im + c.re * c.im) % 2 = 0 := by
    have : (4 : ℤ) ∣ 2 * (a.re * a.im + c.re * c.im) := by
      convert hi using 1 <;> simp only [pow_two, Zsqrtd.im_add, Zsqrtd.im_mul] <;> ring
    obtain ⟨k, hk⟩ := this
    apply Int.emod_eq_zero_of_dvd
    exact ⟨k, by omega⟩
  rw [Int.add_emod, Int.mul_emod a.re a.im, Int.mul_emod c.re c.im] at hi2
  have ha : a.re % 2 = 0 := by
    by_contra h
    have ha1 : a.re % 2 = 1 := by omega
    have hc1 : c.re % 2 = 1 := by omega
    rw [ha1, hc1] at hi2
    norm_num at hi2
    omega
  exact ⟨Int.dvd_of_emod_eq_zero ha, Int.dvd_of_emod_eq_zero (by omega)⟩

private theorem dyadic_numerator (a b : Order) (hab : IsCoprime a b) :
    ¬ root ^ 7 ∣ numerator a b := by
  rintro ⟨w, hw⟩
  let c := delta * b
  let h := a ^ 2 + c ^ 2
  have hre : (16 : ℤ) ∣ (h ^ 2).re := by
    have heq : numerator a b = h ^ 2 := by dsimp [numerator, h, c]; ring
    rw [heq] at hw
    have hw' := congrArg Zsqrtd.re hw
    norm_num [root, pow_succ, Zsqrtd.re_mul, Zsqrtd.im_mul] at hw'
    exact ⟨w.im, by simpa [pow_two] using hw'⟩
  have hh : (16 : ℤ) ∣ h.re ^ 2 + 2 * h.im ^ 2 := by
    convert hre using 1 <;> simp only [pow_two, Zsqrtd.re_mul] <;> ring
  obtain ⟨hr, hi⟩ := four_dvd_of_sixteen_dvd_norm h.re h.im hh
  obtain ⟨ha, hc⟩ := even_re_of_sum_squares a c hr hi
  have hb : (2 : ℤ) ∣ b.re := by
    change (2 : ℤ) ∣ (delta * b).re at hc
    simp only [delta, root, Zsqrtd.re_mul, Zsqrtd.re_sub,
      Zsqrtd.im_sub, Zsqrtd.re_ofNat, Zsqrtd.im_ofNat,
      Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd] at hc
    obtain ⟨k, hk⟩ := hc
    exact ⟨k - b.re + b.im, by omega⟩
  have hunit := hab.isUnit_of_dvd' ((root_dvd_iff a).mpr ha) ((root_dvd_iff b).mpr hb)
  have hn : Zsqrtd.norm root = -2 := by norm_num [root, Zsqrtd.norm]
  have hnormunit := Zsqrtd.norm_eq_one_iff.mpr hunit
  norm_num [hn] at hnormunit

private def residueSeven : Order →+* ZMod 7 := Zsqrtd.lift ⟨3, by decide⟩

private theorem residue_delta : residueSeven delta = 0 := by
  norm_num [residueSeven, delta, root, Zsqrtd.lift_apply_apply]

private theorem delta_dvd_iff (z : Order) : delta ∣ z ↔ residueSeven z = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    simp [residue_delta]
  · intro hz
    have hz' : (7 : ℤ) ∣ z.re + 3 * z.im := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      simpa [residueSeven, Zsqrtd.lift_apply_apply, Int.cast_add, Int.cast_mul, mul_comm] using hz
    obtain ⟨k, hk⟩ := hz'
    refine ⟨⟨3 * k - z.im, k⟩, ?_⟩
    ext <;> simp [delta, root] <;> omega

private theorem delta_prime : Prime delta := by
  have hker : RingHom.ker residueSeven = Ideal.span {delta} := by
    ext z
    simp only [RingHom.mem_ker, Ideal.mem_span_singleton, delta_dvd_iff]
  have hp : (Ideal.span {delta}).IsPrime := hker ▸ RingHom.ker_isPrime residueSeven
  exact (Ideal.span_singleton_prime (by
    intro h
    have := congrArg Zsqrtd.re h
    norm_num [delta, root] at this)).mp hp

private theorem sum_squares_mod_seven (x y : ZMod 7) (h : x ^ 2 + y ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  have hfinite : ∀ x y : ZMod 7, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
  exact hfinite x y h

private theorem delta_numerator (a b : Order) (hab : IsCoprime a b) :
    ¬ delta ^ 5 ∣ numerator a b := by
  intro hd
  have hH : delta ∣ a ^ 2 + delta ^ 2 * b ^ 2 :=
    delta_prime.dvd_of_dvd_pow ((dvd_pow_self delta (by decide : 5 ≠ 0)).trans hd)
  have ha0 : residueSeven a = 0 := by
    have h := (delta_dvd_iff _).mp hH
    simp only [map_add, map_mul, map_pow, residue_delta, zero_pow (by decide : 2 ≠ 0),
      zero_mul, add_zero] at h
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp h
  obtain ⟨c, hc⟩ := (delta_dvd_iff a).mpr ha0
  have hb0 : residueSeven b ≠ 0 := by
    intro hb
    have hcop := hab.map residueSeven
    rw [ha0, hb] at hcop
    exact not_isCoprime_zero_zero hcop
  have hfactor : numerator a b = delta ^ 4 * (c ^ 2 + b ^ 2) ^ 2 := by
    rw [numerator, hc]
    ring
  have hcancel : delta ∣ (c ^ 2 + b ^ 2) ^ 2 := by
    rw [hfactor, show (5 : ℕ) = 4 + 1 from rfl, pow_add, pow_one] at hd
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ delta_prime.ne_zero)).mp hd
  have hzero := (delta_dvd_iff _).mp (delta_prime.dvd_of_dvd_pow hcancel)
  simp only [map_add, map_pow] at hzero
  exact hb0 (sum_squares_mod_seven _ _ hzero).2

private theorem prime_support (a b : Order) (hab : IsCoprime a b)
    (q : Ideal Order) (hq : q.IsPrime)
    (hf : numerator a b ∈ q) (hg : denominator a b ∈ q) :
    (2 : Order) ∈ q ∨ delta ∈ q := by
  by_contra h
  push_neg at h
  obtain ⟨h2, hd⟩ := h
  have h4 : (4 : Order) ∉ q := by
    intro hm
    apply h2
    apply hq.mem_of_pow_mem 2
    convert hm using 1 <;> norm_num
  have hs : a ^ 2 + delta ^ 2 * b ^ 2 ∈ q := hq.mem_of_pow_mem 2 hf
  have hbad : a ∈ q → b ∈ q → False := by
    intro ha hb
    obtain ⟨u, v, huv⟩ := hab
    exact hq.one_notMem (huv ▸ q.add_mem (q.mul_mem_left u ha) (q.mul_mem_left v hb))
  have hnot_a : a ∉ q := by
    intro ha
    have hdb : delta ^ 2 * b ^ 2 ∈ q := by
      convert q.sub_mem hs (q.pow_mem_of_mem ha 2 (by decide)) using 1 <;> ring
    have hb2 : b ^ 2 ∈ q :=
      (hq.mem_or_mem hdb).resolve_left (fun h => hd (hq.mem_of_pow_mem 2 h))
    exact hbad ha (hq.mem_of_pow_mem 2 hb2)
  have hnot_b : b ∉ q := by
    intro hb
    have ha2 : a ^ 2 ∈ q := by
      convert q.sub_mem hs (q.mul_mem_left (delta ^ 2) (q.pow_mem_of_mem hb 2 (by decide)))
        using 1 <;> ring
    exact hnot_a (hq.mem_of_pow_mem 2 ha2)
  have hdiff : a ^ 2 - delta ^ 2 * b ^ 2 ∈ q := by
    have h1 := (hq.mem_or_mem hg).resolve_left (fun hm =>
      (hq.mem_or_mem hm).elim
        (fun hm => (hq.mem_or_mem hm).elim h4 hnot_a) hnot_b)
    exact h1
  have ha2 : (2 : Order) * a ^ 2 ∈ q := by
    convert q.add_mem hs hdiff using 1 <;> ring
  exact hnot_a (hq.mem_of_pow_mem 2 ((hq.mem_or_mem ha2).resolve_left h2))

private theorem residue_seven_surjective : Function.Surjective residueSeven := by
  intro x
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  exact ⟨n, by simp⟩

private theorem delta_maximal : (Ideal.span {delta} : Ideal Order).IsMaximal := by
  have hker : RingHom.ker residueSeven = Ideal.span {delta} := by
    ext z
    simp only [RingHom.mem_ker, Ideal.mem_span_singleton, delta_dvd_iff]
  exact hker ▸ RingHom.ker_isMaximal_of_surjective residueSeven residue_seven_surjective

private def residueTwo : Order →+* ZMod 2 := Zsqrtd.lift ⟨0, by decide⟩

private theorem root_maximal : (Ideal.span {root} : Ideal Order).IsMaximal := by
  have hker : RingHom.ker residueTwo = Ideal.span {root} := by
    ext z
    simp only [RingHom.mem_ker, Ideal.mem_span_singleton, root_dvd_iff]
    simp [residueTwo, Zsqrtd.lift_apply_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hsurj : Function.Surjective residueTwo := by
    intro x
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    exact ⟨n, by simp⟩
  exact hker ▸ RingHom.ker_isMaximal_of_surjective residueTwo hsurj

/-- For every primitive pair in the explicit square-root-two order, the common
duplication ideal is not contained in the seventh power of (sqrt(2)) or the fifth
power of (3-sqrt(2)); every prime ideal containing it is one of these two ideals.
No assertion identifying this order with a number field's ring of integers or
converting these bounds to a projective height is included here. -/
theorem primitive_duplication_local (a b : Order) (hab : Ideal.span {a, b} = ⊤) :
    ¬ commonIdeal a b ≤ (Ideal.span {root}) ^ 7 ∧
    ¬ commonIdeal a b ≤ (Ideal.span {delta}) ^ 5 ∧
    ∀ q : Ideal Order, q.IsPrime → commonIdeal a b ≤ q →
      q = Ideal.span {root} ∨ q = Ideal.span {delta} := by
  have hcop : IsCoprime a b := by
    apply Ideal.mem_span_pair.mp
    rw [hab]
    trivial
  have hf : numerator a b ∈ commonIdeal a b := Ideal.subset_span (by simp)
  have hg : denominator a b ∈ commonIdeal a b := Ideal.subset_span (by simp)
  refine ⟨?_, ?_, ?_⟩
  · intro hi
    have hmem := hi hf
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    exact dyadic_numerator a b hcop hmem
  · intro hi
    have hmem := hi hf
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    exact delta_numerator a b hcop hmem
  · intro q hq hi
    rcases prime_support a b hcop q hq (hi hf) (hi hg) with h2 | hd
    · left
      have hr : root ∈ q := hq.mem_of_pow_mem 2 (root_sq ▸ h2)
      exact (root_maximal.eq_of_le hq.ne_top ((Ideal.span_singleton_le_iff_mem q).2 hr)).symm
    · right
      exact (delta_maximal.eq_of_le hq.ne_top ((Ideal.span_singleton_le_iff_mem q).2 hd)).symm

#print axioms primitive_duplication_local

end D5.S3.Factorization.QuadraticIdeals.SqrtTwoDuplicationCancellation
