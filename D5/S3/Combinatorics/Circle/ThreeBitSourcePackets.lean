/- GID: D5/S3/Combinatorics/Circle/ThreeBitSourcePackets
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeBitSourcePackets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Colex]
   utility: none
   digest: Complementary exact coefficient constructions for three physical ladders. -/
module
import D5.S3.Combinatorics.Circle.DyadicPrefix
import Mathlib.Data.Nat.Bitwise
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import all D5.S3.Combinatorics.Circle.ThreeBitSourceResidual
import all D5.S3.Combinatorics.Circle.ThreeBitSourceQTwo
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.ThreeBitSource

/-- The direct branch takes the exact unused U support and a suffix coefficient of W. -/
theorem packet_direct (n : ℕ) (P Q H u v w C h δ T D : ℤ)
    (hH : 1 ≤ H) (hQ : 2 ≤ Q) (hQeven : Q % 2 = 0)
    (hP : P = H * Q) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (hT : 2 * T = u - 1) (hD : 2 * D = w - 1)
    (huw : u ≤ w) (hv : v = H * w + δ)
    (hC : C = P / 2 * w - (T + 1)) (hh : h = v - (n + 1) * u)
    (hδ : 0 ≤ δ ∧ δ ≤ T) :
    ∃ dW : ℕ, (dW : ℤ) < P / 2 ∧
      0 ≤ (n : ℤ) * u + dW * w ∧
      0 ≤ C - h - ((n : ℤ) * u + dW * w) ∧
      C - h - ((n : ℤ) * u + dW * w) ≤ D := by
  have hQhalf : Q = 2 * (Q / 2) := by omega
  have hPhalf : P / 2 = H * (Q / 2) := by
    have he : P = 2 * (H * (Q / 2)) := by
      calc P = H * Q := hP
           _ = H * (2 * (Q / 2)) := congrArg (fun t : ℤ => H * t) hQhalf
           _ = 2 * (H * (Q / 2)) := by ring
    omega
  have hd0 : 0 ≤ P / 2 - H := by rw [hPhalf]; nlinarith
  let d := (P / 2 - H).toNat
  have hd : (d : ℤ) = P / 2 - H := Int.toNat_of_nonneg hd0
  have he : C - h - ((n : ℤ) * u + d * w) = T - δ := by
    rw [hd, hC, hh, hv]
    nlinarith only [hT]
  refine ⟨d, by rw [hd]; omega, ?_, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg (by positivity) hu) (mul_nonneg (by positivity) hw)
  · rw [he]; omega
  · rw [he]; omega

/-- A complete untouched V ladder supplies the rounded second packet when its step fits. -/
theorem packet_ceiling (qV v C h Aw D : ℤ)
    (hq : 1 ≤ qV) (hv : 1 ≤ v) (hh : 0 ≤ h ∧ h ≤ C)
    (hAw : 0 ≤ Aw) (hD : D = C - Aw) (hstep : v ≤ D + 1)
    (hfull : Aw ≤ (qV - 1) * v) :
    ∃ dV : ℕ, (dV : ℤ) < qV ∧ 0 ≤ (dV : ℤ) * v ∧
      0 ≤ C - h - dV * v ∧ C - h - dV * v ≤ D := by
  by_cases hsmall : Aw ≤ h
  · exact ⟨0, by simpa only [Nat.cast_zero] using (show 0 < qV by omega), by simp, by simpa using hh.2, by simp; omega⟩
  · let L := Aw - h
    let d := (L + v - 1) / v
    have hL : 1 ≤ L := by dsimp [L]; omega
    have hd0 : 0 ≤ d := Int.ediv_nonneg (by omega) (by omega)
    have hr0 := Int.emod_nonneg (L + v - 1) (by omega : v ≠ 0)
    have hr1 := Int.emod_lt_of_pos (L + v - 1) (by omega : 0 < v)
    have he := Int.emod_add_mul_ediv (L + v - 1) v
    change (L + v - 1) % v + v * d = L + v - 1 at he
    have hmass : L ≤ d * v ∧ d * v ≤ L + v - 1 := by
      constructor <;> nlinarith only [hr0, hr1, he]
    have hdq : d < qV := by
      by_contra hn
      have hm := mul_le_mul_of_nonneg_right (show qV ≤ d by omega) (by omega : 0 ≤ v)
      dsimp [L] at hmass
      nlinarith
    refine ⟨d.toNat, by simpa only [Int.toNat_of_nonneg hd0] using hdq, ?_, ?_, ?_⟩
    · exact mul_nonneg (by positivity) (by omega)
    · rw [Int.toNat_of_nonneg hd0]
      dsimp [L] at hmass
      omega
    · rw [Int.toNat_of_nonneg hd0]
      dsimp [L] at hmass
      omega

/-- An actual present singleton supplies both ladder coefficients, including their endpoint bounds. -/
theorem packet_exit (n r : ℕ) (P Q H u v w C h δ T D : ℤ)
    (hH : 1 ≤ H) (hQ : 2 ≤ Q) (hQeven : Q % 2 = 0)
    (hP : P = H * Q) (hu : 1 ≤ u) (huw : u ≤ w)
    (hT : 2 * T = u - 1) (hD : 2 * D = w - 1)
    (hv : v = H * w + δ) (hrel : w - u = Q * δ)
    (hC : C = P / 2 * w - (T + 1)) (hh : h = v - (n + 1) * u)
    (hh0 : 0 ≤ h) (hδ : 0 < δ) (hrn : r ≤ n)
    (hs : δ - T ≤ ((r : ℤ) * u) % w ∧ ((r : ℤ) * u) % w ≤ w - u) :
    ∃ dV dW : ℕ, (dV : ℤ) < Q / 2 ∧ (dW : ℤ) < P / 2 ∧
      0 ≤ ((n - r : ℕ) : ℤ) * u + dV * v + dW * w ∧
      0 ≤ C - h - (((n - r : ℕ) : ℤ) * u + dV * v + dW * w) ∧
      C - h - (((n - r : ℕ) : ℤ) * u + dV * v + dW * w) ≤ D := by
  have hQhalf : Q = 2 * (Q / 2) := by omega
  have hPhalf : P / 2 = H * (Q / 2) := by
    have he : P = 2 * (H * (Q / 2)) := by
      calc P = H * Q := hP
           _ = H * (2 * (Q / 2)) := congrArg (fun t : ℤ => H * t) hQhalf
           _ = 2 * (H * (Q / 2)) := by ring
    omega
  have hw : 0 < w := by omega
  have hv0 : 0 ≤ v := by nlinarith
  have hT0 : 0 ≤ T := by omega
  have hDrel : D = Q / 2 * δ + T := by
    nlinarith only [hT, hD, hrel, congrArg (fun t : ℤ => t * δ) hQhalf]
  let s := ((r : ℤ) * u) % w
  obtain ⟨hi1, hiQ, hE0, hED⟩ :=
    coupled_transfer (Q / 2) δ s T D (by omega) hδ hT0 hDrel
      (by dsimp [s]; omega)
      (by dsimp [s]; nlinarith only [hs.2, hrel, congrArg (fun t : ℤ => t * δ) hQhalf])
  let i := min (Q / 2) ((s + T) / δ)
  let E := s + T - i * δ
  let B := (r : ℤ) * u + T - i * v
  let j := i * H - ((r : ℤ) * u) / w
  change 1 ≤ i at hi1
  change i ≤ Q / 2 at hiQ
  change 0 ≤ E at hE0
  change E ≤ D at hED
  have he : E = B + j * w := by
    have hd := Int.emod_add_mul_ediv ((r : ℤ) * u) w
    dsimp only [E, s, B, j]
    rw [hv]
    nlinarith only [hd]
  have hB : B < 0 := by
    have hru := mul_le_mul_of_nonneg_right (show (r : ℤ) ≤ n by exact_mod_cast hrn)
      (show 0 ≤ u by omega)
    have hiv := mul_le_mul_of_nonneg_right hi1 hv0
    dsimp only [B]
    nlinarith only [hru, hiv, hh, hh0, hT, hu]
  have hj1 : 1 ≤ j := by
    by_contra hn
    have hm := mul_nonpos_of_nonpos_of_nonneg (show j ≤ 0 by omega) (le_of_lt hw)
    omega
  have hjP : j ≤ P / 2 := by
    by_contra hn
    have hiv := mul_le_mul_of_nonneg_right hiQ hv0
    have hjw := mul_le_mul_of_nonneg_right (show P / 2 + 1 ≤ j by omega) (le_of_lt hw)
    have hru : 0 ≤ (r : ℤ) * u := mul_nonneg (by positivity) (by omega)
    have hid : (Q / 2 : ℤ) * v = P / 2 * w + (D - T) := by
      rw [hv, hPhalf, hDrel]; ring
    dsimp only [B] at he
    nlinarith only [he, hiv, hjw, hru, hid, hD, hT, hED, hu]
  let dV := (i - 1).toNat
  let dW := (P / 2 - j).toNat
  have hdV : (dV : ℤ) = i - 1 := Int.toNat_of_nonneg (by omega)
  have hdW : (dW : ℤ) = P / 2 - j := Int.toNat_of_nonneg (by omega)
  have hc : ((n - r : ℕ) : ℤ) = (n : ℤ) - r := Nat.cast_sub hrn
  have hE : C - h - (((n - r : ℕ) : ℤ) * u + dV * v + dW * w) = E := by
    rw [hdV, hdW, hc, hC, hh, he]
    dsimp only [B]
    nlinarith only [hT]
  refine ⟨dV, dW, by rw [hdV]; omega, by rw [hdW]; omega, ?_, ?_, ?_⟩
  · exact add_nonneg (add_nonneg (mul_nonneg (by positivity) (by omega))
      (mul_nonneg (by positivity) hv0)) (mul_nonneg (by positivity) (le_of_lt hw))
  · rw [hE]; exact hE0
  · rw [hE]; exact hED

/-- The source quotient contains the ratio-specific top bit of the untouched U mask. -/
theorem source_top_bit (x y z : ℕ) (hxy : y ≤ x) (hy : 2 ≤ y) (hz : y + 2 ≤ z) :
    let n := 2 ^ z * (2 ^ x + 1) / (2 * (1 + 2 ^ x + 2 ^ x * 2 ^ y))
    n.testBit (z - y - 2) = true := by
  let P := 2 ^ x
  let Q := 2 ^ y
  let e := z - y - 2
  let r := 2 ^ e
  let u := 1 + P + P * Q
  let n := 2 ^ z * (P + 1) / (2 * u)
  change n.testBit e = true
  have hPQ : Q ≤ P := Nat.pow_le_pow_right (by decide : 0 < 2) hxy
  have hQ : 4 ≤ Q := Nat.pow_le_pow_right (by decide : 0 < 2) hy
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : 2 ^ z = 4 * Q * r := by
    rw [show z = y + (e + 2) by dsimp [e]; omega]
    dsimp only [Q, r]
    simp only [pow_add]
    norm_num
    ring
  have hn : n = 4 * Q * r * (P + 1) / (2 * u) := by dsimp only [n]; rw [hR]
  have hu : 0 < 2 * u := by dsimp [u]; positivity
  have hlo : u ≤ 2 * Q * (P + 1) := by dsimp [u]; nlinarith
  have hhi : Q * (P + 1) < u := by dsimp [u]; nlinarith
  have hnlo : r ≤ n := by
    rw [hn, Nat.le_div_iff_mul_le hu]
    have hm := Nat.mul_le_mul_right r hlo
    nlinarith only [hm]
  have hnhi : n < 2 ^ (e + 1) := by
    rw [hn, Nat.div_lt_iff_lt_mul hu, pow_succ]
    change 4 * Q * r * (P + 1) < r * 2 * (2 * u)
    have hm := Nat.mul_lt_mul_of_pos_right hhi hr
    nlinarith only [hm]
  have hmem := DyadicPrefix.bit_subset_top_mem (u := e + 1) (x := n)
    (by omega) (by simpa using hnlo) hnhi
  have hb := (DyadicPrefix.bit_subset_mem hnhi).mp hmem
  simpa using hb

/-- The small source ratios have the stated zero-wrap or one-wrap exit. -/
theorem small_ratio_residue (P Q H r : ℤ) (hQ : 4 ≤ Q)
    (hH : H = 1 ∨ H = 2 ∨ H = 4) (hP : P = H * Q) (hr : 1 ≤ r)
    (hlarge : P * Q ≤ 4 * Q * r) :
    let R := 4 * Q * r
    let u := 1 + P + P * Q
    let w := 1 + Q + Q * R
    let T := (u - 1) / 2
    R - P - H + 1 - T ≤ (r * u) % w ∧ (r * u) % w ≤ w - u := by
  dsimp only
  let R := 4 * Q * r
  let u := 1 + P + P * Q
  let w := 1 + Q + Q * R
  let T := (u - 1) / 2
  change R - P - H + 1 - T ≤ (r * u) % w ∧ (r * u) % w ≤ w - u
  have hH0 : 1 ≤ H := by rcases hH with h | h | h <;> omega
  have hP0 : 4 ≤ P := by nlinarith
  have hu : 1 ≤ u := by dsimp [u]; nlinarith
  have hT : 0 ≤ T := Int.ediv_nonneg (by omega) (by decide)
  rcases hH with rfl | rfl | rfl
  · have hPQ : P = Q := by simpa using hP
    subst P
    have hcoef : 0 ≤ 3 * Q ^ 2 - Q - 1 := by nlinarith
    have hm := mul_nonneg (show 0 ≤ r - 1 by omega) hcoef
    have hbound : r * u ≤ w - u := by dsimp [u, w, R]; nlinarith
    have hs0 : 0 ≤ r * u := by positivity
    have hs1 : r * u < w := by omega
    have hbase : R ≤ r * u := by
      have hm := mul_nonneg (show 0 ≤ r by omega)
        (show 0 ≤ Q ^ 2 - 3 * Q + 1 by nlinarith)
      dsimp [R, u]; nlinarith only [hm]
    rw [Int.emod_eq_of_lt hs0 hs1]
    exact ⟨by omega, hbound⟩
  · have hPQ : P = 2 * Q := hP
    subst P
    have hr2 : 2 ≤ r := by
      by_contra hn
      have hm := mul_le_mul_of_nonneg_left (show r ≤ 1 by omega) (show 0 ≤ Q by omega)
      nlinarith
    have hcoef : 0 ≤ 2 * Q ^ 2 - 2 * Q - 1 := by nlinarith
    have hm := mul_nonneg (show 0 ≤ r - 2 by omega) hcoef
    have hbound : r * u ≤ w - u := by dsimp [u, w, R]; nlinarith
    have hs0 : 0 ≤ r * u := by positivity
    have hs1 : r * u < w := by omega
    have hbase : R ≤ r * u := by
      have hm := mul_nonneg (show 0 ≤ r by omega)
        (show 0 ≤ 2 * Q ^ 2 - 2 * Q + 1 by nlinarith)
      dsimp [R, u]; nlinarith only [hm]
    rw [Int.emod_eq_of_lt hs0 hs1]
    exact ⟨by omega, hbound⟩
  · have hPQ : P = 4 * Q := hP
    subst P
    have hr2 : 2 ≤ r := by
      by_contra hn
      have hm := mul_le_mul_of_nonneg_left (show r ≤ 1 by omega) (show 0 ≤ Q by omega)
      nlinarith
    let s := R + r - Q - 1
    have hcoef : 0 ≤ 4 * Q ^ 2 - 4 * Q - 1 := by nlinarith
    have hm := mul_nonneg (show 0 ≤ r - 2 by omega) hcoef
    have hbound : s ≤ w - u := by dsimp [s, u, w, R]; nlinarith
    have hs0 : 0 ≤ s := by
      have hm := mul_nonneg (show 0 ≤ Q by omega) (show 0 ≤ r - 2 by omega)
      dsimp [s, R]; nlinarith only [hm, hr2, hQ]
    have hs1 : s < w := by omega
    have he : r * u = s + w := by dsimp [s, u, w, R]; ring
    rw [he, Int.add_emod_right, Int.emod_eq_of_lt hs0 hs1]
    exact ⟨by dsimp [s]; omega, hbound⟩

private theorem twice_low (P R n : ℤ) (hP : 2 ≤ P) (hR : 2 * P ≤ R)
    (hPeven : P % 2 = 0) (hn : 0 ≤ n) (hsmall : 2 * R ≤ P ^ 2) :
    let u := 1 + P + 2 * P ^ 2
    let v := 1 + R + R * P
    let w := 1 + 2 * P + 2 * P * R
    let C := P / 2 * w - (u + 1) / 2
    let h := v - (n + 1) * u
    let q := n * u + v + (P / 2 - 1) * w
    0 ≤ q ∧ 0 ≤ C - h - q ∧ C - h - q ≤ (w - 1) / 2 := by
  dsimp only
  have hhalf : P = 2 * (P / 2) := by omega
  have hu : (1 + P + 2 * P ^ 2 + 1) / 2 = 1 + P / 2 + P ^ 2 := by omega
  have hw : (1 + 2 * P + 2 * P * R - 1) / 2 = P + P * R := by
    rw [show 1 + 2 * P + 2 * P * R - 1 = 2 * (P + P * R) by ring]
    omega
  rw [hu, hw]
  have hq : 0 ≤ n * (1 + P + 2 * P ^ 2) + (1 + R + R * P) +
      (P / 2 - 1) * (1 + 2 * P + 2 * P * R) := by
    have hR0 : 0 ≤ R := by omega
    exact add_nonneg (add_nonneg (by positivity) (by positivity))
      (mul_nonneg (by omega) (by positivity))
  have hpr := mul_nonneg (show 0 ≤ P by omega) (show 0 ≤ R - 2 * P by omega)
  refine ⟨hq, ?_, ?_⟩ <;> nlinarith only [hsmall, hP, hR, hhalf, hpr]

private theorem twice_high (P R n : ℤ) (hP : 2 ≤ P) (hR : 2 * P ^ 2 ≤ R)
    (hPeven : P % 2 = 0) (hn : 0 ≤ n) :
    let u := 1 + P + 2 * P ^ 2
    let v := 1 + R + R * P
    let w := 1 + 2 * P + 2 * P * R
    let C := P / 2 * w - (u + 1) / 2
    let h := v - (n + 1) * u
    let q := n * u + (P / 2 - 1) * w
    0 ≤ q ∧ 0 ≤ C - h - q ∧ C - h - q ≤ (w - 1) / 2 := by
  dsimp only
  have hhalf : P = 2 * (P / 2) := by omega
  have hu : (1 + P + 2 * P ^ 2 + 1) / 2 = 1 + P / 2 + P ^ 2 := by omega
  have hw : (1 + 2 * P + 2 * P * R - 1) / 2 = P + P * R := by
    rw [show 1 + 2 * P + 2 * P * R - 1 = 2 * (P + P * R) by ring]
    omega
  rw [hu, hw]
  have hR0 : 0 ≤ R := by nlinarith
  have hq : 0 ≤ n * (1 + P + 2 * P ^ 2) +
      (P / 2 - 1) * (1 + 2 * P + 2 * P * R) :=
    add_nonneg (by positivity) (mul_nonneg (by omega) (by positivity))
  have hpr := mul_nonneg hR0 (show 0 ≤ P - 1 by omega)
  have hpp := mul_nonneg (show 0 ≤ P - 2 by omega) (show 0 ≤ P by omega)
  refine ⟨hq, ?_, ?_⟩ <;> nlinarith only [hP, hR, hhalf, hpr, hpp]

private theorem middle_quotient (J : ℕ) (hJ : 0 < J) :
    (4 * J) ^ 2 * (4 * J + 1) / (2 * (1 + 4 * J + 2 * (4 * J) ^ 2)) = J := by
  let A := (4 * J) ^ 2 * (4 * J + 1)
  let d := 2 * (1 + 4 * J + 2 * (4 * J) ^ 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have he0 : d * J ≤ A := by
    have hm := Nat.mul_le_mul_left J (show 1 ≤ 4 * J by omega)
    dsimp [A, d]
    nlinarith only [hm]
  have he1 : d * (J + 1) = A + (56 * J ^ 2 + 10 * J + 2) := by dsimp [A, d]; ring
  have h0 : J ≤ A / d := (Nat.le_div_iff_mul_le hd).mpr (by nlinarith only [he0])
  have h1 : A / d < J + 1 := (Nat.div_lt_iff_lt_mul hd).mpr (by nlinarith only [he1])
  change A / d = J
  exact Nat.le_antisymm (by omega) h0

private theorem twice_middle (J : ℤ) (hJ : 1 ≤ J) :
    let u := 1 + 4 * J + 32 * J ^ 2
    let v := 1 + 16 * J ^ 2 + 64 * J ^ 3
    let w := 1 + 8 * J + 128 * J ^ 3
    let C := 2 * J * w - (u + 1) / 2
    let h := v - (J + 1) * u
    let q := (2 * J - 1) * v + J * w
    0 ≤ q ∧ 0 ≤ C - h - q ∧ C - h - q ≤ (w - 1) / 2 := by
  dsimp only
  have hu : (1 + 4 * J + 32 * J ^ 2 + 1) / 2 = 1 + 2 * J + 16 * J ^ 2 := by omega
  have hw : (1 + 8 * J + 128 * J ^ 3 - 1) / 2 = 4 * J + 64 * J ^ 3 := by omega
  rw [hu, hw]
  have hj0 : 0 ≤ J := by omega
  have hq : 0 ≤ (2 * J - 1) * (1 + 16 * J ^ 2 + 64 * J ^ 3) +
      J * (1 + 8 * J + 128 * J ^ 3) :=
    add_nonneg (mul_nonneg (by omega) (by positivity)) (by positivity)
  have hm := mul_nonneg (show 0 ≤ J - 1 by omega) (sq_nonneg J)
  refine ⟨hq, ?_, ?_⟩ <;> nlinarith only [hJ, hm, sq_nonneg J]

/-- Every minimum-oriented source has a legal second packet on its exact unused support. -/
theorem second_packet (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 2 ≤ z)
    (hxz : x ≤ z) (hyz : y ≤ z) :
    let P : ℤ := 2 ^ x
    let Q : ℤ := 2 ^ y
    let R : ℤ := 2 ^ z
    let u := 1 + P + P * Q
    let v := 1 + R + R * P
    let w := 1 + Q + Q * R
    let n : ℕ := 2 ^ z * (2 ^ x + 1) / (2 * (1 + 2 ^ x + 2 ^ x * 2 ^ y))
    let C := P / 2 * w - (u + 1) / 2
    let h := v - (n + 1) * u
    let D := (w - 1) / 2
    u ≤ w → 0 ≤ h ∧ h ≤ C →
      ∃ c dV dW : ℕ, c.bitIndices.toFinset ⊆ n.bitIndices.toFinset ∧
        (dV : ℤ) < Q / 2 ∧ (dW : ℤ) < P / 2 ∧
        0 ≤ (c : ℤ) * u + dV * v + dW * w ∧
        0 ≤ C - h - ((c : ℤ) * u + dV * v + dW * w) ∧
        C - h - ((c : ℤ) * u + dV * v + dW * w) ≤ D := by
  dsimp only
  let P : ℤ := 2 ^ x
  let Q : ℤ := 2 ^ y
  let R : ℤ := 2 ^ z
  let u := 1 + P + P * Q
  let v := 1 + R + R * P
  let w := 1 + Q + Q * R
  let n : ℕ := 2 ^ z * (2 ^ x + 1) / (2 * (1 + 2 ^ x + 2 ^ x * 2 ^ y))
  let C := P / 2 * w - (u + 1) / 2
  let h := v - ((n : ℤ) + 1) * u
  let T := (u - 1) / 2
  let D := (w - 1) / 2
  change u ≤ w → 0 ≤ h ∧ h ≤ C → _
  intro huw hh
  let Goal := ∃ c dV dW : ℕ, c.bitIndices.toFinset ⊆ n.bitIndices.toFinset ∧
    (dV : ℤ) < Q / 2 ∧ (dW : ℤ) < P / 2 ∧
    0 ≤ (c : ℤ) * u + dV * v + dW * w ∧
    0 ≤ C - h - ((c : ℤ) * u + dV * v + dW * w) ∧
    C - h - ((c : ℤ) * u + dV * v + dW * w) ≤ D
  change Goal
  have hP : 2 ≤ P := by
    simpa [P] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hx
  have hQ : 2 ≤ Q := by
    simpa [Q] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hy
  have hR : 4 ≤ R := by
    simpa [R] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hz
  have hp : P = 2 * (2 : ℤ) ^ (x - 1) := by
    dsimp [P]
    conv_lhs => rw [show x = (x - 1) + 1 by omega, pow_succ]
    ring
  have hq : Q = 2 * (2 : ℤ) ^ (y - 1) := by
    dsimp [Q]
    conv_lhs => rw [show y = (y - 1) + 1 by omega, pow_succ]
    ring
  have hPe : P % 2 = 0 := by omega
  have hQe : Q % 2 = 0 := by omega
  have hph : P = 2 * (P / 2) := by omega
  have hqh : Q = 2 * (Q / 2) := by omega
  have hPQe : (P * Q) % 2 = 0 := by simp [Int.mul_emod, hPe]
  have hQRe : (Q * R) % 2 = 0 := by simp [Int.mul_emod, hQe]
  have hu : 1 ≤ u := by
    have hm : 0 ≤ P * Q := by positivity
    dsimp [u]; omega
  have hv : 1 ≤ v := by
    have hm : 0 ≤ R * P := by positivity
    dsimp [v]; omega
  have hw : 1 ≤ w := by
    have hm : 0 ≤ Q * R := by positivity
    dsimp [w]; omega
  have hue : u % 2 = 1 := by dsimp [u]; omega
  have hwe : w % 2 = 1 := by dsimp [w]; omega
  have hT : 2 * T = u - 1 := by dsimp [T]; omega
  have hD : 2 * D = w - 1 := by dsimp [D]; omega
  have hT0 : 0 ≤ T := by omega
  have hUhalf : (u + 1) / 2 = T + 1 := by omega
  have hC : 2 * C = P * w - u - 1 := by
    dsimp only [C]
    rw [hUhalf]
    nlinarith only [hT, congrArg (fun t : ℤ => t * w) hph]
  have hQv : Q * v = (P + 1) * w - u := by dsimp [u, v, w]; ring
  by_cases hxy : x < y
  · by_cases hwide : x + 2 ≤ y
    · have hPQ : 4 * P ≤ Q := by
        have ht := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hwide
        simpa [P, Q, pow_add, mul_comm] using ht
      have hstep : 2 * v ≤ w + 1 := by
        have hm := mul_nonneg (show 0 ≤ R by omega) (show 0 ≤ Q - 2 * P - 2 by omega)
        dsimp only [v, w]
        nlinarith only [hm, hQ]
      have hvw : v ≤ w := by omega
      have hAw0 : 0 ≤ C - D := by
        have hm := mul_nonneg (show 0 ≤ P - 2 by omega) (show 0 ≤ w by omega)
        nlinarith only [hm, hC, hD, huw]
      have hfull : C - D ≤ (Q / 2 - 1) * v := by
        nlinarith only [hQv, hC, hD, hvw, congrArg (fun t : ℤ => t * v) hqh]
      obtain ⟨dV, hdV, hm, he0, heD⟩ :=
        packet_ceiling (Q / 2) v C h (C - D) D (by omega) hv hh
          hAw0 (by ring) (by omega) hfull
      refine ⟨0, dV, 0, by simp, hdV, by simp; omega, ?_, ?_, ?_⟩
      · simpa using hm
      · simpa using he0
      · simpa using heD
    · have hyE : y = x + 1 := by omega
      have hQP : Q = 2 * P := by
        dsimp [P, Q]
        rw [hyE, pow_succ]
        ring
      have hRP : 2 * P ≤ R := by
        have ht := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hyz
        change Q ≤ R at ht
        omega
      have huE : u = 1 + P + 2 * P ^ 2 := by dsimp [u]; rw [hQP]; ring
      have hwE : w = 1 + 2 * P + 2 * P * R := by dsimp [w]; rw [hQP] <;> ring
      let dW := (P / 2 - 1).toNat
      have hdW : (dW : ℤ) = P / 2 - 1 := Int.toNat_of_nonneg (by omega)
      by_cases hzlo : z < 2 * x
      · have hsmall : 2 * R ≤ P ^ 2 := by
          have ht := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
            (show z + 1 ≤ x + x by omega)
          simpa [P, R, pow_succ, pow_add, pow_two, mul_comm] using ht
        have hs := twice_low P R n hP hRP hPe (by positivity) hsmall
        refine ⟨n, 1, dW, Finset.Subset.rfl, by simp; omega, by rw [hdW]; omega,
          ?_, ?_, ?_⟩
        · simpa only [Nat.cast_one, one_mul, hdW, huE, hwE, C, h, v] using hs.1
        · simpa only [Nat.cast_one, one_mul, hdW, huE, hwE, C, h, v] using hs.2.1
        · simpa only [Nat.cast_one, one_mul, hdW, huE, hwE, C, h, D, v] using hs.2.2
      · by_cases hzhi : 2 * x < z
        · have hlarge : 2 * P ^ 2 ≤ R := by
            have ht := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
              (show x + x + 1 ≤ z by omega)
            simpa [P, R, pow_succ, pow_add, pow_two, mul_comm] using ht
          have hs := twice_high P R n hP hlarge hPe (by positivity)
          refine ⟨n, 0, dW, Finset.Subset.rfl, by simp; omega, by rw [hdW]; omega,
            ?_, ?_, ?_⟩
          · simpa only [Nat.cast_zero, zero_mul, add_zero, hdW, huE, hwE, C, h, v] using hs.1
          · simpa only [Nat.cast_zero, zero_mul, add_zero, hdW, huE, hwE, C, h, v] using hs.2.1
          · simpa only [Nat.cast_zero, zero_mul, add_zero, hdW, huE, hwE, C, h, D, v] using hs.2.2
        · have hzE : z = x + x := by omega
          by_cases hxE : x = 1
          · have hy2 : y = 2 := by omega
            have hz2 : z = 2 := by omega
            subst x; subst y; subst z
            refine ⟨0, 1, 0, by simp, ?_, ?_, ?_, ?_, ?_⟩ <;>
              norm_num [P, Q, R, u, v, w, n, C, h, D]
          · have hx2 : 2 ≤ x := by omega
            let J : ℕ := 2 ^ (x - 2)
            have hJ : 0 < J := by dsimp [J]; positivity
            have hPJ : P = 4 * (J : ℤ) := by
              dsimp [P, J]
              conv_lhs => rw [show x = (x - 2) + 2 by omega, pow_add]
              norm_num
              ring
            have hRJ : R = P ^ 2 := by dsimp [R, P]; rw [hzE, pow_add, pow_two]
            have hPJN : 2 ^ x = 4 * J := by
              have ht := hPJ
              dsimp only [P] at ht
              exact_mod_cast ht
            have hQJN : 2 ^ y = 8 * J := by
              have ht : Q = 8 * (J : ℤ) := by omega
              dsimp only [Q] at ht
              exact_mod_cast ht
            have hRJN : 2 ^ z = (4 * J) ^ 2 := by
              have ht : R = (4 * (J : ℤ)) ^ 2 := by rw [hRJ, hPJ]
              dsimp only [R] at ht
              exact_mod_cast ht
            have hnJ : n = J := by
              dsimp only [n]
              rw [hPJN, hQJN, hRJN]
              convert middle_quotient J hJ using 1 <;> congr 1 <;> ring
            let dV : ℕ := 2 * J - 1
            have hdV : (dV : ℤ) = 2 * (J : ℤ) - 1 := by
              dsimp [dV]
              rw [Nat.cast_sub (by omega)]
              norm_cast
            have hpJ : P / 2 = 2 * (J : ℤ) := by omega
            have hqJ : Q / 2 = 4 * (J : ℤ) := by omega
            have huJ : u = 1 + 4 * (J : ℤ) + 32 * (J : ℤ) ^ 2 := by rw [huE, hPJ]; ring
            have hvJ : v = 1 + 16 * (J : ℤ) ^ 2 + 64 * (J : ℤ) ^ 3 := by
              dsimp [v]; rw [hRJ, hPJ]; ring
            have hwJ : w = 1 + 8 * (J : ℤ) + 128 * (J : ℤ) ^ 3 := by
              rw [hwE, hRJ, hPJ]; ring
            have hs := twice_middle (J : ℤ) (by exact_mod_cast hJ)
            refine ⟨0, dV, J, by simp, by rw [hdV, hqJ]; omega,
              by rw [hpJ]; omega, ?_, ?_, ?_⟩
            · simpa only [Nat.cast_zero, zero_mul, zero_add, hdV, huJ, hvJ, hwJ] using hs.1
            · simpa only [Nat.cast_zero, zero_mul, zero_add, hdV, C, h, D, hnJ,
                hpJ, huJ, hvJ, hwJ] using hs.2.1
            · simpa only [Nat.cast_zero, zero_mul, zero_add, hdV, C, h, D, hnJ,
                hpJ, huJ, hvJ, hwJ] using hs.2.2

  · have hyx : y ≤ x := by omega
    let H : ℤ := 2 ^ (x - y)
    let δ := R - P - H + 1
    have hH : 1 ≤ H := by dsimp [H]; exact one_le_pow₀ (by norm_num)
    have hPH : P = H * Q := by
      dsimp [P, H, Q]
      rw [← pow_add, Nat.sub_add_cancel hyx]
    have hrel : w - u = Q * δ := by dsimp [w, u, δ]; rw [hPH]; ring
    have hvrel : v = H * w + δ := by dsimp [v, w, δ]; rw [hPH]; ring
    have hδ0 : 0 ≤ δ := by
      by_contra hn
      have hm := mul_neg_of_pos_of_neg (show 0 < Q by omega) (show δ < 0 by omega)
      omega
    by_cases hdir : δ ≤ T
    · obtain ⟨dW, hdW, hm, he0, heD⟩ := packet_direct n P Q H u v w C h δ T D
        hH hQ hQe hPH (by omega) (by omega) hT hD huw hvrel
        (by dsimp only [C]; rw [hUhalf]) rfl ⟨hδ0, hdir⟩
      refine ⟨n, 0, dW, Finset.Subset.rfl, by simp; omega, hdW, ?_, ?_, ?_⟩
      · simpa using hm
      · simpa using he0
      · simpa using heD
    · have hδT : T < δ := by omega
      have hδ : 0 < δ := by omega
      have hzlarge : x + y ≤ z := by
        by_contra hn
        have ht := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
          (show z + 1 ≤ x + y by omega)
        have hs : 2 * R ≤ P * Q := by simpa [P, Q, R, pow_succ, pow_add, mul_comm] using ht
        have huE : u = 1 + P + P * Q := rfl
        have hdE : δ = R - P - H + 1 := rfl
        nlinarith only [hs, hδT, hT, hP, hH, huE, hdE]
      have hRlarge : P * Q ≤ R := by
        have ht := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hzlarge
        simpa [P, Q, R, pow_add] using ht
      have from_bit (e : ℕ) (hb : n.testBit e = true)
          (hs : δ - T ≤ ((2 : ℤ) ^ e * u) % w ∧
            ((2 : ℤ) ^ e * u) % w ≤ w - u) : Goal := by
        have hrn : 2 ^ e ≤ n := Nat.two_pow_le_of_mem_bitIndices (Nat.mem_bitIndices.mpr hb)
        obtain ⟨dV, dW, hdV, hdW, hm, he0, heD⟩ :=
          packet_exit n (2 ^ e) P Q H u v w C h δ T D hH hQ hQe hPH hu huw
            hT hD hvrel hrel (by dsimp only [C]; rw [hUhalf]) rfl hh.1 hδ hrn
            (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hs)
        refine ⟨n - 2 ^ e, dV, dW, ?_, hdV, hdW, hm, he0, heD⟩
        rw [erase_bit n e hb]
        exact Finset.erase_subset _ _
      by_cases hy1 : y = 1
      · have hQ2 : Q = 2 := by norm_num [Q, hy1]
        have hHhalf : H = P / 2 := by
          have ht := hPH
          rw [hQ2] at ht
          omega
        have huE : u = 1 + 3 * P := by dsimp [u]; rw [hQ2]; ring
        have hwE : w = 3 + 2 * R := by dsimp [w]; rw [hQ2]; ring
        by_cases hx1 : x = 1
        · have hP2 : P = 2 := by norm_num [P, hx1]
          have hz3 : 3 ≤ z := by
            by_contra hn
            have hz2 : z = 2 := by omega
            norm_num [δ, T, u, P, Q, R, H, hx1, hy1, hz2] at hδT
          have hR8 : 8 ≤ R := by
            simpa [R] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hz3
          have hnE : n = 2 ^ z * 3 / 14 := by norm_num [n, hx1, hy1]
          have hnB : 14 * (n : ℤ) ≤ 3 * R := by
            have hb := Nat.mul_div_le (2 ^ z * 3) 14
            rw [← hnE] at hb
            have ht : 14 * n ≤ 3 * 2 ^ z := by nlinarith only [hb]
            dsimp only [R]
            exact_mod_cast ht
          have hu7 : u = 7 := by rw [huE, hP2]; norm_num
          have hvE : v = 1 + 3 * R := by dsimp [v]; rw [hP2]; ring
          have hDE : D = R + 1 := by dsimp only [D]; rw [hwE]; omega
          have hE : C - h = 7 * (n : ℤ) - R + 5 := by
            dsimp only [C, h]
            rw [hP2, hu7, hvE, hwE]
            norm_num
            ring
          refine ⟨0, 0, 0, by simp, by simp; omega, by simp; omega,
            by simp, by simp; omega, ?_⟩
          simp only [Nat.cast_zero, zero_mul, zero_add, add_zero]
          rw [hE, hDE]
          nlinarith only [hnB, hR8]
        · have hx2 : 2 ≤ x := by omega
          have hl2 : 2 ≤ z - x := by
            by_contra hn
            have hz1 : z ≤ x + 1 := by omega
            have ht := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hz1
            have hs : R ≤ 2 * P := by simpa [R, P, pow_succ, mul_comm] using ht
            have hTE : 2 * T = 3 * P := by rw [huE] at hT; linarith only [hT]
            have hdE : δ = R - P - H + 1 := rfl
            nlinarith only [hδT, hs, hHhalf, hph, hTE, hdE, hP]
          let l := z - x
          let K : ℤ := 2 ^ l
          have hRn : 2 ^ z = 2 ^ l * 2 ^ x := by
            rw [show z = l + x by dsimp only [l]; omega, pow_add]
          have hRK : R = K * P := by dsimp [R, K, P]; exact_mod_cast hRn
          have hnE : n = 2 ^ l * 2 ^ x * (2 ^ x + 1) / (2 * (1 + 3 * 2 ^ x)) := by
            dsimp only [n]
            rw [hRn, hy1]
            norm_num only [pow_one]
            congr 1 <;> ring
          obtain ⟨e, hel, hb, hs0, hs1⟩ := q_two_selected_bit x l hx2 hl2
          rw [← hnE] at hb
          have hα : δ - T = K * P - 3 * P + 1 := by
            have hTE : 2 * T = 3 * P := by rw [huE] at hT; linarith only [hT]
            dsimp only [δ]
            rw [hRK, hHhalf]
            nlinarith only [hTE, hph]
          apply from_bit e hb
          rw [hα, huE, hwE, hRK]
          simpa only [P, K, mul_assoc] using And.intro hs0 hs1
      · have hy2 : 2 ≤ y := by omega
        have hQ4 : 4 ≤ Q := by
          simpa [Q] using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hy2
        by_cases hnear : x ≤ y + 2
        · have hHcases : H = 1 ∨ H = 2 ∨ H = 4 := by
            have he : x - y = 0 ∨ x - y = 1 ∨ x - y = 2 := by omega
            rcases he with he | he | he <;> norm_num [H, he]
          let e := z - y - 2
          have hze : y + 2 ≤ z := by omega
          have hb := source_top_bit x y z hyx hy2 hze
          change n.testBit e = true at hb
          have hRe : R = 4 * Q * (2 : ℤ) ^ e := by
            dsimp only [R, Q]
            conv_lhs => rw [show z = y + (e + 2) by dsimp only [e]; omega,
              pow_add, pow_add]
            norm_num
            ring
          have hr : 1 ≤ (2 : ℤ) ^ e := one_le_pow₀ (by norm_num)
          have hs := small_ratio_residue P Q H ((2 : ℤ) ^ e)
            hQ4 hHcases hPH hr (by rw [← hRe]; exact hRlarge)
          apply from_bit e hb
          simpa only [δ, T, u, w, hRe] using hs
        · have hfar : y + 3 ≤ x := by omega
          let l := z - x - y
          have hRn : 2 ^ z = 2 ^ l * 2 ^ x * 2 ^ y := by
            rw [show z = l + x + y by dsimp only [l]; omega, pow_add, pow_add]
          have hRi : (2 : ℤ) ^ l * (2 : ℤ) ^ x * (2 : ℤ) ^ y = R := by
            dsimp only [R]
            exact_mod_cast hRn.symm
          have hnE : n = 2 ^ l * 2 ^ x * 2 ^ y * (2 ^ x + 1) /
              (2 * (1 + 2 ^ x + 2 ^ x * 2 ^ y)) := by dsimp only [n]; rw [hRn]
          have hs := packet_residual x y l hfar hy2
          dsimp only at hs
          rw [hRi, ← hnE] at hs
          change ∃ c dV dW : ℕ, c.bitIndices.toFinset ⊆ n.bitIndices.toFinset ∧
            dV < 2 ^ (y - 1) ∧ dW < 2 ^ (x - 1) ∧
            0 ≤ (c : ℤ) * u + dV * v + dW * w ∧
            0 ≤ C - h - ((c : ℤ) * u + dV * v + dW * w) ∧
            C - h - ((c : ℤ) * u + dV * v + dW * w) ≤ D at hs
          obtain ⟨c, dV, dW, hc, hdV, hdW, hm, he0, heD⟩ := hs
          have hqdiv : Q / 2 = (2 : ℤ) ^ (y - 1) := by omega
          have hpdiv : P / 2 = (2 : ℤ) ^ (x - 1) := by omega
          refine ⟨c, dV, dW, hc, ?_, ?_, hm, he0, heD⟩
          · rw [hqdiv]; exact_mod_cast hdV
          · rw [hpdiv]; exact_mod_cast hdW

end D5.S3.Combinatorics.Circle.ThreeBitSource
