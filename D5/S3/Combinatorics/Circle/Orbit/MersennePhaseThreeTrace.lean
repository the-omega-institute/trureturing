/- GID: D5/S3/Combinatorics/Circle/Orbit/MersennePhaseThreeTrace
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/Orbit/MersennePhaseThreeTrace
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: []
   utility: none
   digest: Literal three-point integer phase traces on every original physical label. -/
module
public import D5.S3.Combinatorics.Circle.SourceWidth

/-! # Three-point Mersenne phase traces on physical labels -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace D5.S3.Combinatorics.Circle.MersennePhaseThreeTrace

open scoped BigOperators
open SourceWidth

/-- Identify a scaled representative by the existing centered uniqueness theorem.
The strict doubled inequalities imply the inclusive integer half-modulus bounds. -/
private theorem centered_scaled {g q z r ell : ℤ}
    (hg : 0 < g) (hq : 0 < q) (hodd : (g * q) % 2 = 1)
    (hz : z = r + q * ell) (hr : -q < 2 * r ∧ 2 * r < q) :
    centered (g * q) (g * z) = g * r := by
  have hN : 0 < g * q := mul_pos hg hq
  apply centered_unique hN hodd (centered_bounds hN hodd (g * z))
  · have hlo : -(g * q) < 2 * (g * r) := by
      have h := mul_lt_mul_of_pos_left hr.1 hg
      nlinarith only [h]
    have hhi : 2 * (g * r) < g * q := by
      have h := mul_lt_mul_of_pos_left hr.2 hg
      nlinarith only [h]
    have hdiv := Int.emod_add_mul_ediv (g * q) 2
    omega
  · rw [centered_mod]
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-ell, ?_⟩
    rw [hz]
    ring

/-- The full physical phase filter has exactly these three distinct labels. -/
private theorem phase_sum_three {d : ℕ} (hd : 0 < d) (j : Fin d)
    (f : Fin (3 * d) → ℤ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin (3 * d) => i.val % d = j.val), f i) =
      f ⟨j.val, by have := j.isLt; omega⟩ +
        f ⟨j.val + d, by have := j.isLt; omega⟩ +
        f ⟨j.val + 2 * d, by have := j.isLt; omega⟩ := by
  classical
  have hj : j.val < d := j.isLt
  let p0 : Fin (3 * d) := ⟨j.val, by omega⟩
  let p1 : Fin (3 * d) := ⟨j.val + d, by omega⟩
  let p2 : Fin (3 * d) := ⟨j.val + 2 * d, by omega⟩
  have hset :
      Finset.univ.filter (fun i : Fin (3 * d) => i.val % d = j.val) =
        {p0, p1, p2} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hi
      have hquot : i.val / d < 3 := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using i.isLt)
      have he := Nat.mod_add_div i.val d
      have hcases : i.val / d = 0 ∨ i.val / d = 1 ∨ i.val / d = 2 := by
        generalize i.val / d = n at hquot ⊢
        omega
      rcases hcases with h | h | h
      · left
        apply Fin.ext
        dsimp [p0]
        simp only [h, mul_zero, add_zero] at he
        omega
      · right; left
        apply Fin.ext
        dsimp [p1]
        simp only [h, mul_one] at he
        omega
      · right; right
        apply Fin.ext
        dsimp [p2]
        simp only [h, mul_two] at he
        omega
    · rintro (rfl | rfl | rfl)
      · exact Nat.mod_eq_of_lt j.isLt
      · simp [p1, Nat.mod_eq_of_lt j.isLt]
      · simp [p2, Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  have h01 : p0 ≠ p1 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p0, p1] at hv
    omega
  have h02 : p0 ≠ p2 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p0, p2] at hv
    omega
  have h12 : p1 ≠ p2 := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p1, p2] at hv
    omega
  rw [hset]
  calc
    _ = f p0 + f p1 + f p2 := by simp [h01, h02, h12, add_assoc]
    _ = _ := rfl

/-- The literal three-point phase trace of the seed
`(2^d - 1) * (2^(d+1) - 3)`, on every original physical label.
There is no coprimality, primality, period, or upper-bound premise. -/
theorem actual_phase_trace (d : ℕ) (hd : 3 ≤ d) (j : Fin d) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin (3 * d) => i.val % d = j.val),
      actualSource (3 * d) ((2 ^ d - 1) * (2 ^ (d + 1) - 3)) i) =
      modulus (3 * d) *
        ((if j.val = d - 3 then (1 : ℤ) else 0) -
          (if j.val = d - 1 then (1 : ℤ) else 0)) := by
  classical
  have hj : j.val < d := j.isLt
  let B : ℤ := 2 ^ d
  let g : ℤ := B - 1
  let q : ℤ := B ^ 2 + B + 1
  let x : ℤ := 2 ^ j.val
  let a : ℤ := (2 * B - 3) * x
  let b : ℤ := (5 * B + 2) * x
  let c : ℤ := (3 * B + 5) * x
  have hB : 8 ≤ B := by
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
         _ ≤ B := pow_le_pow_right₀ (by norm_num) hd
  have hx : 1 ≤ x := one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2)
  have hg : 0 < g := by dsimp [g]; omega
  have hq : 0 < q := by dsimp [q]; nlinarith [sq_nonneg B]
  have hfactor : modulus (3 * d) = g * q := by
    have hp : (2 : ℤ) ^ (3 * d) = B ^ 3 := by
      dsimp [B]
      rw [show 3 * d = d * 3 by omega, pow_mul]
    rw [modulus, hp]
    dsimp [g, q]
    ring
  have hodd : (g * q) % 2 = 1 := by
    rw [← hfactor, modulus,
      show 3 * d = (3 * d - 1) + 1 by omega, pow_succ]
    omega
  have hBn : 8 ≤ (2 : ℕ) ^ d := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
  have hnext : 3 ≤ (2 : ℕ) ^ (d + 1) := by rw [pow_succ]; omega
  have hseed :
      (((2 ^ d - 1) * (2 ^ (d + 1) - 3) : ℕ) : ℤ) = g * (2 * B - 3) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ (2 : ℕ) ^ d),
      Nat.cast_sub hnext]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [pow_succ]
    dsimp [g, B]
    ring
  have hp1 : (2 : ℤ) ^ (j.val + d) = x * B := by
    dsimp [x, B]
    rw [pow_add]
  have hp2 : (2 : ℤ) ^ (j.val + 2 * d) = x * B ^ 2 := by
    dsimp [x, B]
    rw [pow_add, show 2 * d = d * 2 by omega, pow_mul]
  rw [phase_sum_three (by omega : 0 < d) j]
  simp only [actualSource]
  rw [hfactor, hseed, hp1, hp2]
  change
    centered (g * q) (x * (g * (2 * B - 3))) +
      centered (g * q) ((x * B) * (g * (2 * B - 3))) +
      centered (g * q) ((x * B ^ 2) * (g * (2 * B - 3))) =
        g * q * ((if j.val = d - 3 then (1 : ℤ) else 0) -
          (if j.val = d - 1 then (1 : ℤ) else 0))
  have harg0 : x * (g * (2 * B - 3)) = g * a := by dsimp [a]; ring
  have harg1 : (x * B) * (g * (2 * B - 3)) = g * (B * a) := by
    dsimp [a]; ring
  have harg2 : (x * B ^ 2) * (g * (2 * B - 3)) = g * (B ^ 2 * a) := by
    dsimp [a]; ring
  rw [harg0, harg1, harg2]
  have heval (r0 r1 r2 ell0 ell1 ell2 : ℤ)
      (he0 : a = r0 + q * ell0)
      (he1 : B * a = r1 + q * ell1)
      (he2 : B ^ 2 * a = r2 + q * ell2)
      (hr0 : -q < 2 * r0 ∧ 2 * r0 < q)
      (hr1 : -q < 2 * r1 ∧ 2 * r1 < q)
      (hr2 : -q < 2 * r2 ∧ 2 * r2 < q) :
      centered (g * q) (g * a) + centered (g * q) (g * (B * a)) +
        centered (g * q) (g * (B ^ 2 * a)) = g * (r0 + r1 + r2) := by
    rw [centered_scaled hg hq hodd he0 hr0,
      centered_scaled hg hq hodd he1 hr1,
      centered_scaled hg hq hodd he2 hr2]
    ring
  have hshift (r : ℕ) (hr : j.val + r = d) : (2 : ℤ) ^ r * x = B := by
    dsimp [x, B]
    rw [← pow_add, show r + j.val = d by omega]
  by_cases hlow : j.val + 4 ≤ d
  · have h16 : 16 * x ≤ B := by
      calc 16 * x = (2 : ℤ) ^ (j.val + 4) := by
             dsimp [x]
             norm_num [pow_add, mul_comm]
           _ ≤ B := pow_le_pow_right₀ (by norm_num) hlow
    have ha0 : 0 ≤ a := mul_nonneg (by omega) (by omega)
    have hc0 : 0 ≤ c := mul_nonneg (by omega) (by omega)
    have hbalance : a - b + c = 0 := by dsimp [a, b, c]; ring
    have hbcap : 16 * b ≤ (5 * B + 2) * B := by
      have hh := mul_nonneg (show 0 ≤ 5 * B + 2 by omega)
        (show 0 ≤ B - 16 * x by omega)
      dsimp [b]
      nlinarith only [hh]
    have hb2 : 2 * b < q := by
      dsimp [q]
      nlinarith only [hB, hbcap, sq_nonneg B]
    have ha : -q < 2 * a ∧ 2 * a < q := by
      constructor <;> linarith only [ha0, hc0, hbalance, hb2, hq]
    have hb : -q < 2 * (-b) ∧ 2 * (-b) < q := by
      constructor <;> linarith only [ha0, hc0, hbalance, hb2, hq]
    have hc : -q < 2 * c ∧ 2 * c < q := by
      constructor <;> linarith only [ha0, hc0, hbalance, hb2, hq]
    have hs := heval a (-b) c 0 (2 * x) ((2 * B - 5) * x)
      (by ring) (by dsimp [a, b, q]; ring) (by dsimp [a, c, q]; ring) ha hb hc
    rw [hs]
    have hj3 : j.val ≠ d - 3 := by omega
    have hj1 : j.val ≠ d - 1 := by omega
    simp only [ite_eq_right hj3, ite_eq_right hj1]
    dsimp [a, b, c]
    ring
  · by_cases hj3 : j.val = d - 3
    · have h8 : 8 * x = B := by simpa using hshift 3 (by omega)
      have ha : -q < 2 * a ∧ 2 * a < q := by
        dsimp [a, q]
        rw [← h8]
        constructor <;> nlinarith only [hx, sq_nonneg (x - 1)]
      have hb : -q < 2 * (q - b) ∧ 2 * (q - b) < q := by
        dsimp [b, q]
        rw [← h8]
        constructor <;> nlinarith only [hx, sq_nonneg (x - 1)]
      have hc : -q < 2 * c ∧ 2 * c < q := by
        dsimp [c, q]
        rw [← h8]
        constructor <;> nlinarith only [hx, sq_nonneg (x - 1)]
      have hs := heval a (q - b) c 0 (2 * x - 1) ((2 * B - 5) * x)
        (by ring) (by dsimp [a, b, q]; ring) (by dsimp [a, c, q]; ring) ha hb hc
      rw [hs]
      have hj1 : j.val ≠ d - 1 := by omega
      simp only [ite_eq_left hj3, ite_eq_right hj1]
      dsimp [a, b, c]
      ring
    · by_cases hj2 : j.val = d - 2
      · have h4 : 4 * x = B := by simpa using hshift 2 (by omega)
        have ha : -q < 2 * a ∧ 2 * a < q := by
          dsimp [a, q]
          rw [← h4]
          constructor <;> nlinarith only [hx, sq_nonneg (x - 1)]
        have hb : -q < 2 * (q - b) ∧ 2 * (q - b) < q := by
          dsimp [b, q]
          rw [← h4]
          constructor <;> nlinarith only [hx, sq_nonneg (x - 1)]
        have hc : -q < 2 * (c - q) ∧ 2 * (c - q) < q := by
          dsimp [c, q]
          rw [← h4]
          constructor <;> nlinarith only [hx, sq_nonneg (x - 1)]
        have hs := heval a (q - b) (c - q) 0 (2 * x - 1) ((2 * B - 5) * x + 1)
          (by ring) (by dsimp [a, b, q]; ring) (by dsimp [a, c, q]; ring) ha hb hc
        rw [hs]
        have hj1 : j.val ≠ d - 1 := by omega
        simp only [ite_eq_right hj3, ite_eq_right hj1]
        dsimp [a, b, c]
        ring
      · have hj1 : j.val = d - 1 := by omega
        have h2 : 2 * x = B := by simpa using hshift 1 (by omega)
        have hx4 : 4 ≤ x := by omega
        have ha : -q < 2 * (a - q) ∧ 2 * (a - q) < q := by
          dsimp [a, q]
          rw [← h2]
          constructor <;> nlinarith only [hx4, sq_nonneg (x - 2)]
        have hb : -q < 2 * (2 * q - b) ∧ 2 * (2 * q - b) < q := by
          dsimp [b, q]
          rw [← h2]
          constructor <;> nlinarith only [hx4, sq_nonneg (x - 2)]
        have hc : -q < 2 * (c - 2 * q) ∧ 2 * (c - 2 * q) < q := by
          dsimp [c, q]
          rw [← h2]
          constructor <;> nlinarith only [hx4, sq_nonneg (x - 2)]
        have hs := heval (a - q) (2 * q - b) (c - 2 * q) 1
          (2 * x - 2) ((2 * B - 5) * x + 2)
          (by ring) (by dsimp [a, b, q]; ring) (by dsimp [a, c, q]; ring) ha hb hc
        rw [hs]
        simp only [ite_eq_right hj3, ite_eq_left hj1]
        dsimp [a, b, c]
        ring

end D5.S3.Combinatorics.Circle.MersennePhaseThreeTrace
