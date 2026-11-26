/- GID: D5/S3/ArithUnits/GolovanovBareDrazinEqualities
   generality: G
   mirror-B: D5/B/S3/ArithUnits/GolovanovBareDrazinEqualities
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.Idempotent]
   utility: none
   digest: Three tests characterize the bare Drazin sum equality in a unital associative ring. -/

module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.NoncommRing

/-! The finite Drazin inverse of the parallel sum with arbitrary input core idempotents. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

public section

namespace D5.S3.ArithUnits.GolovanovBareDrazinEqualities

variable {R : Type*} [Ring R]

/-- The finite Drazin relation by outer inverse, commutation, and nilpotent remainder. -/
def FD (x y : R) : Prop :=
  (y * x) * y = y ∧ x * y = y * x ∧ IsNilpotent (x - (x * y) * x)

private theorem fd_mul (x y : R) (h : FD x y) : (x * y) * y = y := by
  rw [h.2.1, h.1]

private theorem ordered_products (a c b : R) (hab : (a + c) * b = 1)
    (hba : b * (a + c) = 1) :
    a - a * b * a = a * b * c ∧ a - a * b * a = c * b * a := by
  have h₁ : a * b + c * b = 1 := by simpa only [add_mul] using hab
  have h₂ : b * a + b * c = 1 := by simpa only [mul_add] using hba
  constructor
  · calc
      a - a * b * a = a * (b * a + b * c) - a * b * a := by rw [h₂, mul_one]
      _ = a * b * c := by noncomm_ring
  · calc
      a - a * b * a = (a * b + c * b) * a - a * b * a := by rw [h₁, one_mul]
      _ = c * b * a := by noncomm_ring

private theorem ordered_defects (a c u v b : R) (hab : (a + c) * b = 1)
    (hba : b * (a + c) = 1) (ha : FD a u) (hc : FD c v) :
    let p := a * u
    let r := c * v
    let z := r - p
    let nₐ := a - p * a
    let nc := c - r * c
    let t := a - a * b * a
    let s := u + v
    let P := c * b * nₐ * b * c + a * b * nc * b * a
    t * s = p + a * b * z ∧ s * t = p + z * b * a ∧
      (s * t) * s - s = -(z * b * z) ∧ t - (t * s) * t = P := by
  dsimp only
  let p := a * u
  let r := c * v
  let z := r - p
  let t := a - a * b * a
  let s := u + v
  change t * s = p + a * b * z ∧ s * t = p + z * b * a ∧
    (s * t) * s - s = -(z * b * z) ∧
    t - (t * s) * t = c * b * (a - p * a) * b * c + a * b * (c - r * c) * b * a
  obtain ⟨ht₁, ht₂⟩ := ordered_products a c b hab hba
  change t = a * b * c at ht₁
  change t = c * b * a at ht₂
  have h₁ : a * b + c * b = 1 := by simpa only [add_mul] using hab
  have h₂ : b * a + b * c = 1 := by simpa only [mul_add] using hba
  have hcb : c * b = 1 - a * b := by rw [← h₁]; noncomm_ring
  have hbc : b * c = 1 - b * a := by rw [← h₂]; noncomm_ring
  have hba' : b * a = 1 - b * c := by rw [← h₂]; noncomm_ring
  have hts : t * s = p + a * b * z := by
    calc
      t * s = t * u + t * v := mul_add t u v
      _ = (c * b) * p + (a * b) * r := by
        change t * u + t * v = (c * b) * (a * u) + (a * b) * (c * v)
        conv_lhs =>
          congr
          · rw [ht₂]
          · rw [ht₁]
        simp only [mul_assoc]
      _ = p + a * b * z := by rw [hcb]; dsimp [z]; noncomm_ring
  have hst : s * t = p + z * b * a := by
    calc
      s * t = u * t + v * t := add_mul u v t
      _ = p * (b * c) + r * (b * a) := by
        change u * t + v * t = (a * u) * (b * c) + (c * v) * (b * a)
        conv_lhs =>
          congr
          · rw [ht₁, ← mul_assoc u, ← mul_assoc u, ← ha.2.1]
          · rw [ht₂, ← mul_assoc v, ← mul_assoc v, ← hc.2.1]
        noncomm_ring
      _ = p + z * b * a := by rw [hbc]; dsimp [z]; noncomm_ring
  have hpu : p * u = u := fd_mul a u ha
  have hrv : r * v = v := fd_mul c v hc
  have houter : (s * t) * s - s = -(z * b * z) := by
    calc
      (s * t) * s - s = p * u + (p + z) * v + z * b * p - z * b * r - u - v := by
        rw [hst]
        change (p + z * b * a) * (u + v) - (u + v) =
          p * u + (p + z) * v + z * b * (a * u) - z * b * (c * v) - u - v
        have hv : z * b * a * v = z * (1 - b * c) * v := by rw [mul_assoc z, hba']
        calc
          (p + z * b * a) * (u + v) - (u + v) =
              p * u + p * v + z * b * (a * u) + z * b * a * v - u - v := by noncomm_ring
          _ = _ := by rw [hv]; noncomm_ring
      _ = -(z * b * z) := by
        have hpz : p + z = r := by dsimp [z]; noncomm_ring
        rw [hpu, hpz, hrv]
        dsimp [z]
        noncomm_ring
  have hcompl : 1 - t * s = c * b * (1 - p) + a * b * (1 - r) := by
    rw [hts, hcb]
    dsimp [z]
    noncomm_ring
  have hrem : t - (t * s) * t =
      c * b * (a - p * a) * b * c + a * b * (c - r * c) * b * a := by
    calc
      t - (t * s) * t = (1 - t * s) * t := by rw [sub_mul 1, one_mul]
      _ = c * b * (1 - p) * t + a * b * (1 - r) * t := by rw [hcompl, add_mul]
      _ = _ := by
        conv_lhs =>
          congr
          · rw [ht₁]
          · rw [ht₂]
        noncomm_ring
  exact ⟨hts, hst, houter, hrem⟩

private theorem three_test_iff (a c u v b : R) (hab : (a + c) * b = 1)
    (hba : b * (a + c) = 1) (ha : FD a u) (hc : FD c v) :
    let p := a * u
    let r := c * v
    let z := r - p
    let nₐ := a - p * a
    let nc := c - r * c
    let t := a - a * b * a
    let s := u + v
    let P := c * b * nₐ * b * c + a * b * nc * b * a
    FD t s ↔ (a * b * z = z * b * a) ∧ z * b * z = 0 ∧ IsNilpotent P := by
  dsimp only
  obtain ⟨hts, hst, houter, hrem⟩ := ordered_defects a c u v b hab hba ha hc
  have outer := sub_eq_zero.symm.trans ((Iff.of_eq (congrArg (· = 0) houter)).trans neg_eq_zero)
  unfold FD
  rw [outer, hrem, hts, hst, add_left_cancel_iff, and_left_comm]

private theorem fd_powers {x y : R} (h : FD x y) {n : ℕ} (hn : n ≠ 0)
    (hz : (x - (x * y) * x) ^ n = 0) :
    x ^ n * (x * y) = x ^ n ∧ (x * y) * x ^ n = x ^ n ∧
      x ^ n * y ^ n = x * y ∧ y ^ n * x ^ n = x * y := by
  let e := x * y
  have hxy : Commute x y := h.2.1
  have he : IsIdempotentElem e := by
    change (x * y) * (x * y) = x * y
    rw [mul_assoc, ← mul_assoc y, h.1]
  have hxe : Commute x e := (Commute.refl x).mul_right hxy
  have hnot : Commute x (1 - e) := (Commute.one_right x).sub_right hxe
  have hrem : x - (x * y) * x = x * (1 - e) := by
    change x - e * x = x * (1 - e)
    rw [mul_sub, mul_one, hxe.eq]
  have hzero : x ^ n * (1 - e) = 0 := by
    rw [hrem, hnot.mul_pow, he.one_sub.pow_eq hn] at hz
    exact hz
  have hright : x ^ n * e = x ^ n := by
    rw [mul_sub, mul_one] at hzero
    exact (sub_eq_zero.mp hzero).symm
  have hleft : e * x ^ n = x ^ n := (hxe.pow_left n).eq.symm.trans hright
  have hpos : x ^ n * y ^ n = e := (hxy.mul_pow n).symm.trans (he.pow_eq hn)
  exact ⟨hright, hleft, hpos, (hxy.pow_pow n n).eq.symm.trans hpos⟩

private theorem fd_unique {x y w : R} (hy : FD x y) (hw : FD x w) : y = w := by
  obtain ⟨i, hi⟩ := hy.2.2
  obtain ⟨j, hj⟩ := hw.2.2
  let n := max i j + 1
  have hn : n ≠ 0 := by simp [n]
  have hi' : i ≤ n := Nat.le_trans (le_max_left i j) (Nat.le_succ _)
  have hj' : j ≤ n := Nat.le_trans (le_max_right i j) (Nat.le_succ _)
  obtain ⟨_, hyl, _, hyp⟩ := fd_powers hy hn (pow_eq_zero_of_le hi' hi)
  obtain ⟨hwr, _, hwp, _⟩ := fd_powers hw hn (pow_eq_zero_of_le hj' hj)
  have heq : x * y = x * w := by
    calc
      x * y = (y ^ n * x ^ n) * (x * w) := by rw [mul_assoc, hwr, hyp]
      _ = (x * y) * (x ^ n * w ^ n) := by rw [hyp, hwp]
      _ = x * w := by rw [← mul_assoc, hyl, hwp]
  calc
    y = y * (x * y) := by rw [← mul_assoc, hy.1]
    _ = y * (x * w) := by rw [heq]
    _ = (x * y) * w := by rw [← mul_assoc, hy.2.1]
    _ = w := by rw [heq, fd_mul x w hw]

/-- The unique finite Drazin inverse, for an element with a finite Drazin witness. -/
noncomputable def drazin (x : R) (h : ∃ y, FD x y) : R := Classical.choose h

private theorem fd_iff_drazin_eq (x s : R) : FD x s ↔ ∃ h : ∃ y, FD x y, drazin x h = s := by
  constructor
  · intro hs
    let h : ∃ y, FD x y := ⟨s, hs⟩
    exact ⟨h, fd_unique (Classical.choose_spec h) hs⟩
  · rintro ⟨h, heq⟩
    rw [← heq]
    exact Classical.choose_spec h

private theorem inverse_notation_bridge (a c u v b : R) (ha : FD a u) (hc : FD c v) :
    let t := a - a * b * a
    FD t (u + v) ↔
      ∃ ht : ∃ y, FD t y, drazin t ht = drazin a ⟨u, ha⟩ + drazin c ⟨v, hc⟩ := by
  dsimp only
  have hua : drazin a ⟨u, ha⟩ = u := fd_unique (Classical.choose_spec ⟨u, ha⟩) ha
  have hvc : drazin c ⟨v, hc⟩ = v := fd_unique (Classical.choose_spec ⟨v, hc⟩) hc
  rw [hua, hvc, fd_iff_drazin_eq]

/-- Golovanov's Problem 10.1: three tests for the finite Drazin sum equality. -/
theorem result (a c u v b : R) (hab : (a + c) * b = 1)
    (hba : b * (a + c) = 1) (ha : FD a u) (hc : FD c v) :
    let p := a * u
    let r := c * v
    let z := r - p
    let nₐ := a - p * a
    let nc := c - r * c
    let t := a - a * b * a
    let P := c * b * nₐ * b * c + a * b * nc * b * a
    (∃ ht : ∃ y, FD t y, drazin t ht = drazin a ⟨u, ha⟩ + drazin c ⟨v, hc⟩) ↔
      a * b * z = z * b * a ∧ z * b * z = 0 ∧ IsNilpotent P :=
  (inverse_notation_bridge a c u v b ha hc).symm.trans (three_test_iff a c u v b hab hba ha hc)

end D5.S3.ArithUnits.GolovanovBareDrazinEqualities
