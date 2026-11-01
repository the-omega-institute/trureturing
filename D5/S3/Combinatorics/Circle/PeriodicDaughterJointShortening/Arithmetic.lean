/- GID: D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: Native integer rows for minus-one physical joint transport. -/
import D5.S3.Combinatorics.Circle.PeriodicShorteningArithmetic
import D5.S3.Combinatorics.Circle.RunFirstEarTransport

/-! Native digit charges, geometric sums and centered uniqueness for the
physical MINUS-one construction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening
open SourceWidth PeriodicShorteningArithmetic PeriodicShortening RunFirstEarTransport
open scoped BigOperators

def length (d r : ℕ) : ℕ := (d + 1) * r - 1

def seed (d w r : ℕ) : ℕ := w * geom (d + 1) r

def q (d : ℕ) : ℤ := 2 ^ (d + 1)
def n (d : ℕ) : ℤ := 2 ^ d - 1
def H (d r : ℕ) : ℤ := geom (d + 1) (r - 1)
def R (d r : ℕ) : ℤ := q d ^ (r - 1)
def G (d r : ℕ) : ℤ := geom (d + 1) r
def N (d r : ℕ) : ℤ := modulus (length d r)

/-- Scalar identities are tied to the actual modulus, not to an abstract row. -/
structure ScaleFacts (d w r : ℕ) : Prop where
  length_succ : length d r + 1 = (d + 1) * r
  q_eq : q d = 2 * (n d + 1)
  q_ge : 8 ≤ q d
  H_ge : 1 ≤ H d r
  R_ge : 1 ≤ R d r
  G_ge : q d + 1 ≤ G d r
  w_nonneg : 0 ≤ (w : ℤ)
  w_bound : 4 * (w : ℤ) ≤ q d - 4
  G_eq : G d r = 1 + q d * H d r
  modulus_eq : 2 * N d r + 1 = (q d - 1) * G d r
  top_power : 2 * N d r + 2 = q d * R d r
  top_modulus : N d r = R d r * n d + (q d - 1) * H d r
  old_half : 2 * (N d r / 2) = N d r - 1
  base_half : 2 * (modulus d / 2) = n d - 1
  daughter_half : modulus (d + 1) / 2 = n d
  new_modulus : modulus (length d r + 1) = (q d - 1) * G d r
  regular_margin : G d r * n d + 2 * (w : ℤ) * H d r ≤ N d r - 1
  top_margin : R d r * (n d - 1) +
    2 * H d r * (n d + w) ≤ N d r - 1
  daughter_margin : G d r * n d ≤ modulus (length d r + 1) / 2

set_option maxHeartbeats 4000000 in
-- Polynomial certificates combine native charges and three modulus identities.
theorem scale_facts (d w r : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hr : 2 ≤ r) : ScaleFacts d w r := by
  have hlen : length d r + 1 = (d + 1) * r := by
    have := Nat.mul_pos (show 0 < d + 1 by omega) (show 0 < r by omega)
    dsimp [length]; omega
  have hq : q d = 2 * (n d + 1) := by dsimp [q, n]; rw [pow_succ]; ring
  have hq8 : 8 ≤ q d := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      (show 3 ≤ d + 1 by omega)
    norm_num at this; exact this
  have h1 : geom (d + 1) 1 = 1 := by
    simp only [geom, pow_one]
    exact Nat.div_self (by have := Nat.one_lt_two_pow (show d + 1 ≠ 0 by omega); omega)
  have hH : 1 ≤ H d r := by
    have := geom_mono (d + 1) (by omega) (show 1 ≤ r - 1 by omega)
    simpa [H, h1] using this
  have hR : 1 ≤ R d r := one_le_pow₀ (by omega : (1 : ℤ) ≤ q d)
  have hsplit : G d r = H d r + R d r := by
    simpa [G, H, R, q, show r - 1 + 1 = r by omega] using
      geom_succ (d + 1) (r - 1) (by omega)
  have hReq : R d r = (q d - 1) * H d r + 1 := by
    have := geom_mul (d + 1) (r - 1) (by omega)
    dsimp [R, q, H] at *; omega
  have hGeq : G d r = 1 + q d * H d r := by rw [hsplit, hReq]; ring
  have hG : q d + 1 ≤ G d r := by
    rw [hGeq]; nlinarith [mul_nonneg (show 0 ≤ q d by omega) (show 0 ≤ H d r - 1 by omega)]
  have hwb : 4 * (w : ℤ) ≤ q d - 4 := by
    have hw' : (w : ℤ) + 1 ≤ (2 : ℤ) ^ (d - 1) := by
      exact_mod_cast (show w + 1 ≤ 2 ^ (d - 1) by
        have := Nat.one_le_two_pow (n := d - 1); omega)
    have he : q d = 4 * (2 : ℤ) ^ (d - 1) := by
      dsimp [q]
      rw [show d + 1 = (d - 1) + 2 by omega, pow_add]
      norm_num; ring
    nlinarith
  have hNm : 2 * N d r + 1 = (q d - 1) * G d r := by
    have hg := geom_mul (d + 1) r (by omega)
    have he : 2 * N d r + 2 = q d ^ r := by
      change 2 * ((2 : ℤ) ^ length d r - 1) + 2 = _
      rw [q, ← pow_mul, ← hlen, pow_succ]; ring
    dsimp [q, G] at *; nlinarith only [hg, he]
  have htp : 2 * N d r + 2 = q d * R d r := by
    have hg := hNm
    rw [hGeq] at hg
    linear_combination hg - q d * hReq
  have htop : N d r = R d r * n d + (q d - 1) * H d r := by
    have he : 2 * (N d r - R d r * n d - (q d - 1) * H d r) = 0 := by
      linear_combination htp + R d r * hq + 2 * hReq
    omega
  obtain ⟨hpos, hodd⟩ := TwoRunSource.modulus_positive_odd (length d r) (by
    have := Nat.mul_le_mul (show 3 ≤ d + 1 by omega) hr
    dsimp [length]; omega)
  have hhalf : 2 * (N d r / 2) = N d r - 1 := by
    have := Int.emod_add_mul_ediv (N d r) 2
    change N d r % 2 = 1 at hodd; omega
  have hbase : 2 * (modulus d / 2) = n d - 1 := by
    have := (TwoRunSource.modulus_positive_odd d (by omega)).2
    have := Int.emod_add_mul_ediv (modulus d) 2
    dsimp [n, modulus] at *; omega
  have hdaughter : modulus (d + 1) / 2 = n d := by
    dsimp [modulus, n]; rw [pow_succ]; omega
  have hnew : modulus (length d r + 1) = (q d - 1) * G d r := by
    rw [hlen]
    have := geom_mul (d + 1) r (by omega)
    simpa [modulus, q, G, pow_mul] using this.symm
  have hnewhalf : 2 * (modulus (length d r + 1) / 2) =
      modulus (length d r + 1) - 1 := by
    have := (TwoRunSource.modulus_positive_odd (length d r + 1) (by omega)).2
    have := Int.emod_add_mul_ediv (modulus (length d r + 1)) 2
    omega
  have hmargin : G d r * n d + 2 * (w : ℤ) * H d r ≤ N d r - 1 := by
    have he : 2 * (N d r - 1 - G d r * n d - 2 * (w : ℤ) * H d r) =
        (q d - 4 * w) * H d r - 2 := by
      linear_combination hNm + G d r * hq + hGeq
    have hb := mul_le_mul_of_nonneg_right hwb (show 0 ≤ H d r by omega)
    nlinarith only [he, hb, hH]
  have htm : R d r * (n d - 1) + 2 * H d r * (n d + w) ≤ N d r - 1 := by
    have hnw : 0 ≤ n d + 1 - w := by nlinarith only [hq, hwb]
    have he : N d r - 1 - (R d r * (n d - 1) +
        2 * H d r * (n d + w)) = 2 * H d r * (n d + 1 - w) := by
      linear_combination htop + hReq + 2 * H d r * hq
    nlinarith [mul_nonneg (show 0 ≤ H d r by omega) hnw]
  have hdm : G d r * n d ≤ modulus (length d r + 1) / 2 := by
    rw [hnew] at hnewhalf ⊢
    have he := congrArg (fun z : ℤ => z * G d r) hq
    nlinarith only [hnewhalf, he, hG, hq8]
  exact ⟨hlen, hq, hq8, hH, hR, hG, Int.natCast_nonneg _, hwb,
    hGeq, hNm, htp, htop, hhalf, hbase, hdaughter,
    hnew, hmargin, htm, hdm⟩

/-- Extend the native OLD phase by the distinct local ear phase. -/
def alpha (d w : ℕ) (i : Fin (d + 1)) : ℤ :=
  if hi : i.val < d then actualSource d w ⟨i.val, hi⟩ else w

def e (d w : ℕ) (i : Fin (d + 1)) : ℤ :=
  if hi : i.val < d then charge d w ⟨i.val, hi⟩ else w

def beta (d w : ℕ) : Fin (d + 1) → ℤ := actualSource (d + 1) (2 * w)

theorem phase_data (d w : ℕ) (hd : 2 ≤ d) (hw : w ≤ 2 ^ (d - 1) - 1)
    (i : Fin (d + 1)) :
    0 ≤ e d w i ∧
    alpha d w i = (2 : ℤ) ^ i.val * w - n d * e d w i ∧
    beta d w i = 2 * alpha d w i - e d w i ∧
    beta d w i = (2 : ℤ) ^ (i.val + 1) * w - (q d - 1) * e d w i ∧
    -n d ≤ beta d w i ∧ beta d w i ≤ n d := by
  have fs := scale_facts d w 2 hd hw (by omega)
  have hb := centered_bounds
    (TwoRunSource.modulus_positive_odd (d + 1) (by omega)).1
    (TwoRunSource.modulus_positive_odd (d + 1) (by omega)).2
    ((2 : ℤ) ^ i.val * (2 * w : ℕ))
  change -(modulus (d + 1) / 2) ≤ beta d w i ∧
    beta d w i ≤ modulus (d + 1) / 2 at hb
  rw [fs.daughter_half] at hb
  have hdata : 0 ≤ e d w i ∧
      alpha d w i = (2 : ℤ) ^ i.val * w - n d * e d w i ∧
      beta d w i = 2 * alpha d w i - e d w i := by
    by_cases hi : i.val < d
    · let j : Fin d := ⟨i.val, hi⟩
      have hshift : beta d w i = actualSource (d + 1) w
          ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
        unfold beta actualSource
        congr 1
        simp only [Nat.cast_mul, Nat.cast_ofNat, pow_succ]
        dsimp [j]; ring
      have hh := digit_data d w hd hw j
      simpa [alpha, e, hi, n, j, hshift] using hh
    · have hiv : i.val = d := by omega
      have hbet : beta d w i = (w : ℤ) := by
        obtain ⟨hN, ho⟩ := TwoRunSource.modulus_positive_odd (d + 1) (by omega)
        apply centered_unique hN ho (centered_bounds hN ho _) ?_ ?_
        · rw [fs.daughter_half]
          constructor <;> nlinarith [fs.w_bound, fs.q_eq, fs.w_nonneg]
        · rw [centered_mod]
          have he : (2 : ℤ) ^ i.val * (2 * w : ℕ) =
              (w : ℤ) + modulus (d + 1) * w := by
            rw [hiv, modulus, pow_succ, Nat.cast_mul, Nat.cast_ofNat]; ring
          rw [he, Int.add_mul_emod_self_left]
      simp only [alpha, e, dite_eq_right hi, hbet]
      refine ⟨Int.natCast_nonneg _, ?_, by ring⟩
      rw [hiv]; dsimp [n]; ring
  refine ⟨hdata.1, hdata.2.1, hdata.2.2, ?_, hb⟩
  rw [hdata.2.2, hdata.2.1, pow_succ, fs.q_eq]
  ring

theorem phase_fresh (d w : ℕ) (hd : 2 ≤ d) (hw : w ≤ 2 ^ (d - 1) - 1) :
    beta d w (Fin.last d) = w := by
  have hh := (phase_data d w hd hw (Fin.last d)).2.2.1
  simpa [alpha, e, two_mul] using hh

theorem phase_cast (d w : ℕ) (hd : 2 ≤ d) (hw : w ≤ 2 ^ (d - 1) - 1)
    (i : Fin d) : beta d w i.castSucc = 2 * actualSource d w i - charge d w i := by
  simpa [alpha, e, i.isLt] using (phase_data d w hd hw i.castSucc).2.2.1

theorem phase_charge_sum (d w : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) : (∑ i : Fin (d + 1), e d w i) = 2 * w := by
  rw [Fin.sum_univ_castSucc]
  have he : (fun i : Fin d => e d w i.castSucc) = charge d w := by
    funext i; simp [e, i.isLt]
  rw [he, charge_sum d w hd hw]
  simp [e]; ring

/-- The nonnegative cross-modulus defect, with no division or parity choice. -/
def defect (d w j : ℕ) (i : Fin (d + 1)) : ℤ :=
  (2 : ℤ) ^ (i.val + 1) * w * (geom (d + 1) j : ℤ) + e d w i

def regularValue (d w r j : ℕ) (i : Fin (d + 1)) : ℤ :=
  (2 : ℤ) ^ d * H d r * beta d w i + alpha d w i +
    (2 : ℤ) ^ i.val * w * (geom (d + 1) j : ℤ)

def topValue (d w r : ℕ) (i : Fin d) : ℤ :=
  R d r * actualSource d w i + H d r * beta d w i.castSucc

theorem defect_data (d w j : ℕ) (hd : 2 ≤ d) (hw : w ≤ 2 ^ (d - 1) - 1) :
    (∀ i, 0 ≤ defect d w j i) ∧
      (∑ i : Fin (d + 1), defect d w j i) = 2 * w * q d ^ j := by
  have he := phase_charge_sum d w hd hw
  have hp : (∑ i : Fin (d + 1), (2 : ℤ) ^ (i.val + 1)) = 2 * (q d - 1) := by
    simp_rw [pow_succ]
    rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range]
    have hh := geom_sum_mul (2 : ℤ) (d + 1)
    norm_num at hh
    dsimp [q]; nlinarith only [hh]
  constructor
  · intro i
    exact add_nonneg (by positivity) (phase_data d w hd hw i).1
  · dsimp [defect]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hp, he]
    have hh := geom_mul (d + 1) j (by omega)
    change (q d - 1) * (geom (d + 1) j : ℤ) = q d ^ j - 1 at hh
    linear_combination 2 * (w : ℤ) * hh

theorem regular_double (d w r j : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hr : 2 ≤ r) (i : Fin (d + 1)) :
    2 * regularValue d w r j i = G d r * beta d w i + defect d w j i := by
  have fs := scale_facts d w r hd hw hr
  have hg : G d r = 1 + 2 * (2 : ℤ) ^ d * H d r := by
    simpa [q, pow_succ, mul_assoc, mul_left_comm, mul_comm] using fs.G_eq
  dsimp [regularValue, defect]
  rw [hg, (phase_data d w hd hw i).2.2.1, pow_succ]
  ring

set_option maxHeartbeats 4000000 in
-- Polynomial certificates combine native charges and three modulus identities.
theorem regular_source (d w r j : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hr : 2 ≤ r) (hj : j < r - 1)
    (i : Fin (d + 1)) (hp : j * (d + 1) + i.val < length d r) :
    actualSource (length d r) (seed d w r) ⟨j * (d + 1) + i.val, hp⟩ =
      regularValue d w r j i := by
  have fs := scale_facts d w r hd hw hr
  have hrow := phase_data d w hd hw i
  have hdbl := regular_double d w r j hd hw hr i
  have hdef := defect_data d w j hd hw
  have hB : defect d w j i ≤ 2 * w * q d ^ j := by
    rw [← hdef.2]
    exact Finset.single_le_sum (fun z _ => hdef.1 z) (Finset.mem_univ i)
  have hJ : q d ^ j ≤ H d r := by
    have he := geom_succ (d + 1) j (by omega)
    have hm := geom_mono (d + 1) (by omega) (show j + 1 ≤ r - 1 by omega)
    have hz : 0 ≤ (geom (d + 1) j : ℤ) := Int.natCast_nonneg _
    change (geom (d + 1) (j + 1) : ℤ) = (geom (d + 1) j : ℤ) + q d ^ j at he
    change (geom (d + 1) (j + 1) : ℤ) ≤ H d r at hm
    omega
  have hg0 : 0 ≤ G d r := by linarith [fs.G_ge, fs.q_ge]
  have hcap : -(N d r / 2) ≤ regularValue d w r j i ∧
      regularValue d w r j i ≤ N d r / 2 := by
    have hb0 := hdef.1 i
    have hlow := mul_le_mul_of_nonneg_left hrow.2.2.2.2.1 hg0
    have hhi := mul_le_mul_of_nonneg_left hrow.2.2.2.2.2 hg0
    have hwH := mul_le_mul_of_nonneg_left hJ (show 0 ≤ 2 * (w : ℤ) by positivity)
    have hz := mul_nonneg (show 0 ≤ 2 * (w : ℤ) by positivity)
      (show 0 ≤ H d r by linarith [fs.H_ge])
    constructor <;>
      nlinarith only [hdbl, hb0, hB, hlow, hhi, hwH, hz, fs.regular_margin, fs.old_half]
  obtain ⟨hN, ho⟩ := TwoRunSource.modulus_positive_odd (length d r) (by
    have := fs.length_succ; have := Nat.mul_le_mul (show 3 ≤ d + 1 by omega) hr; omega)
  apply centered_unique hN ho (centered_bounds hN ho _) hcap
  rw [centered_mod]
  have hjg := geom_mul (d + 1) j (by omega)
  change (q d - 1) * (geom (d + 1) j : ℤ) = q d ^ j - 1 at hjg
  have hcharge : (geom (d + 1) j : ℤ) * beta d w i + q d ^ j * e d w i =
      defect d w j i := by
    have hb := hrow.2.2.2.1
    dsimp [defect]
    rw [pow_succ] at hb ⊢
    linear_combination (geom (d + 1) j : ℤ) * hb - e d w i * hjg
  have hp2 : (2 : ℤ) ^ (j * (d + 1) + i.val) = q d ^ j * 2 ^ i.val := by
    rw [pow_add, Nat.mul_comm j (d + 1), pow_mul]; rfl
  have heq : (2 : ℤ) ^ (j * (d + 1) + i.val) * (seed d w r : ℤ) -
      regularValue d w r j i = N d r *
        ((geom (d + 1) j : ℤ) * beta d w i + q d ^ j * e d w i) := by
    rw [hcharge, hp2, seed, Nat.cast_mul]
    change q d ^ j * 2 ^ i.val * ((w : ℤ) * G d r) - _ = _
    have he : 2 * (q d ^ j * 2 ^ i.val * ((w : ℤ) * G d r) -
        regularValue d w r j i - N d r * defect d w j i) = 0 := by
      dsimp [defect] at hdbl ⊢
      rw [pow_succ] at hdbl ⊢
      have hb := hrow.2.2.2.1
      rw [pow_succ] at hb
      linear_combination -hdbl - G d r * hb -
        2 * G d r * (2 : ℤ) ^ i.val * (w : ℤ) * hjg -
        (2 * (2 : ℤ) ^ i.val * (w : ℤ) * (geom (d + 1) j : ℤ) + e d w i) * fs.modulus_eq
    omega
  have heq' : regularValue d w r j i =
      (2 : ℤ) ^ (j * (d + 1) + i.val) * (seed d w r : ℤ) -
        modulus (length d r) * defect d w j i := by
    rw [hcharge] at heq
    change _ - _ = modulus (length d r) * _ at heq; linarith
  rw [heq', Int.sub_mul_emod_self_left]

set_option maxHeartbeats 4000000 in
-- Polynomial certificates combine native charges and three modulus identities.
theorem top_source (d w r : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hr : 2 ≤ r) (i : Fin d)
    (hp : (r - 1) * (d + 1) + i.val < length d r) :
    actualSource (length d r) (seed d w r) ⟨(r - 1) * (d + 1) + i.val, hp⟩ =
      topValue d w r i := by
  have fs := scale_facts d w r hd hw hr
  have ha := centered_bounds (TwoRunSource.modulus_positive_odd d (by omega)).1
    (TwoRunSource.modulus_positive_odd d (by omega)).2 ((2 : ℤ) ^ i.val * w)
  change -(modulus d / 2) ≤ actualSource d w i ∧ actualSource d w i ≤ modulus d / 2 at ha
  have hb := phase_data d w hd hw i.castSucc
  have hR0 : 0 ≤ R d r := by linarith [fs.R_ge]
  have hH0 : 0 ≤ H d r := by linarith [fs.H_ge]
  have hwH := mul_nonneg (show 0 ≤ (w : ℤ) by positivity) hH0
  have hbounds : -(N d r / 2) ≤ topValue d w r i ∧ topValue d w r i ≤ N d r / 2 := by
    have a1 := mul_le_mul_of_nonneg_left ha.1 hR0
    have a2 := mul_le_mul_of_nonneg_left ha.2 hR0
    have b1 := mul_le_mul_of_nonneg_left hb.2.2.2.2.1 hH0
    have b2 := mul_le_mul_of_nonneg_left hb.2.2.2.2.2 hH0
    have hbaseR := congrArg (fun z : ℤ => R d r * z) fs.base_half
    dsimp [topValue]
    constructor <;> nlinarith only [a1, a2, b1, b2, hbaseR, fs.old_half,
      fs.top_margin, hwH]
  obtain ⟨hN, ho⟩ := TwoRunSource.modulus_positive_odd (length d r) (by
    have := fs.length_succ; have := Nat.mul_le_mul (show 3 ≤ d + 1 by omega) hr; omega)
  apply centered_unique hN ho (centered_bounds hN ho _) hbounds
  rw [centered_mod]
  have hp2 : (2 : ℤ) ^ ((r - 1) * (d + 1) + i.val) = R d r * 2 ^ i.val := by
    rw [pow_add, Nat.mul_comm (r - 1) (d + 1), pow_mul]; rfl
  have heq : (2 : ℤ) ^ ((r - 1) * (d + 1) + i.val) * (seed d w r : ℤ) -
      topValue d w r i = N d r * ((2 : ℤ) ^ (i.val + 1) * w * H d r + charge d w i) := by
    rw [hp2, seed, Nat.cast_mul]
    change R d r * 2 ^ i.val * ((w : ℤ) * G d r) - _ = _
    have haeq : actualSource d w i = (2 : ℤ) ^ i.val * w - n d * charge d w i := by
      simpa only [n] using (digit_data d w hd hw i).2.1
    rw [topValue, phase_cast d w hd hw, haeq]
    have hg : G d r - 1 = q d * H d r := by linarith [fs.G_eq]
    rw [pow_succ]
    linear_combination (2 : ℤ) ^ i.val * (w : ℤ) * R d r * hg -
      (2 : ℤ) ^ i.val * (w : ℤ) * H d r * fs.top_power -
      charge d w i * fs.top_modulus -
      H d r * charge d w i * fs.q_eq
  have heq' : topValue d w r i =
      (2 : ℤ) ^ ((r - 1) * (d + 1) + i.val) * (seed d w r : ℤ) -
        modulus (length d r) * ((2 : ℤ) ^ (i.val + 1) * w * H d r + charge d w i) := by
    change _ - _ = modulus (length d r) * _ at heq; linarith
  rw [heq', Int.sub_mul_emod_self_left]

set_option maxHeartbeats 4000000 in
-- Polynomial certificates combine native charges and three modulus identities.
/-- Exact periodic daughter source, with distinct physical labels in every block. -/
theorem daughter_source (d w r j : ℕ) (hd : 2 ≤ d)
    (hw : w ≤ 2 ^ (d - 1) - 1) (hr : 2 ≤ r) (i : Fin (d + 1))
    (hp : j * (d + 1) + i.val < length d r + 1) :
    actualSource (length d r + 1) (2 * seed d w r) ⟨j * (d + 1) + i.val, hp⟩ =
      G d r * beta d w i := by
  have fs := scale_facts d w r hd hw hr
  have hb := phase_data d w hd hw i
  have hg0 : 0 ≤ G d r := by linarith [fs.G_ge, fs.q_ge]
  have hbounds : -(modulus (length d r + 1) / 2) ≤ G d r * beta d w i ∧
      G d r * beta d w i ≤ modulus (length d r + 1) / 2 := by
    constructor <;> nlinarith only [mul_le_mul_of_nonneg_left hb.2.2.2.2.1 hg0,
      mul_le_mul_of_nonneg_left hb.2.2.2.2.2 hg0, fs.daughter_margin]
  obtain ⟨hN, ho⟩ := TwoRunSource.modulus_positive_odd (length d r + 1) (by omega)
  apply centered_unique hN ho (centered_bounds hN ho _) hbounds
  rw [centered_mod]
  have hjg := geom_mul (d + 1) j (by omega)
  change (q d - 1) * (geom (d + 1) j : ℤ) = q d ^ j - 1 at hjg
  have hp2 : (2 : ℤ) ^ (j * (d + 1) + i.val) = q d ^ j * 2 ^ i.val := by
    rw [pow_add, Nat.mul_comm j (d + 1), pow_mul]; rfl
  have heq : G d r * beta d w i =
      (2 : ℤ) ^ (j * (d + 1) + i.val) * (2 * seed d w r : ℕ) -
        modulus (length d r + 1) *
          ((2 : ℤ) ^ (i.val + 1) * w * (geom (d + 1) j : ℤ) + e d w i) := by
    rw [hp2, Nat.cast_mul, Nat.cast_ofNat, seed, Nat.cast_mul, fs.new_modulus]
    change G d r * beta d w i =
      q d ^ j * 2 ^ i.val * (2 * ((w : ℤ) * G d r)) - _
    have hbraw := hb.2.2.2.1
    rw [pow_succ] at hbraw ⊢
    linear_combination G d r * hbraw +
      2 * (2 : ℤ) ^ i.val * (w : ℤ) * G d r * hjg
  rw [heq, Int.sub_mul_emod_self_left]

end D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening
