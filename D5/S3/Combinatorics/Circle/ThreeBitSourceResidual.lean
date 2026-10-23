/- GID: D5/S3/Combinatorics/Circle/ThreeBitSourceResidual
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeBitSourceResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Colex]
   utility: none
   digest: Source-forced unused-bit windows and coupled three-ladder transfers. -/
module
import Mathlib.Data.Nat.Bitwise
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.ThreeBitSource

/-- The quotient digit stays strictly between the two endpoint digits. -/
private theorem quotient_digit (P Q B d s F : ℤ)
    (hP : 2 ≤ P) (hQ : 4 ≤ Q) (hPB : P = 2 * B)
    (hBs : B = d * (Q + 1) + s) (hs : 1 ≤ s ∧ s ≤ Q)
    (hF : 2 * (1 + P + P * Q) * F ≤ P * Q * (P + 1))
    (hF' : P * Q * (P + 1) < 2 * (1 + P + P * Q) * (F + 1)) :
    ∃ c : ℤ, (c = 0 ∨ c = 1) ∧ F = d * Q + s - c ∧ 1 ≤ s - c ∧ s - c < Q := by
  let u := 1 + P + P * Q
  let K := d * Q + s
  let E := P * Q * (P + 1) - 2 * u * K
  have hu : 0 < u := by dsimp [u]; nlinarith
  have hq : 0 < Q + 1 := by omega
  have hid : (Q + 1) * E = P * Q ^ 2 - 2 * u * s := by
    dsimp [E, K, u]
    rw [hPB, hBs]
    ring
  have ha : 2 * u < P * Q ^ 2 := by
    have hq2 : 0 < Q ^ 2 - 2 * Q - 2 := by nlinarith
    have hp := mul_nonneg (show 0 ≤ P - 2 by omega) (le_of_lt hq2)
    dsimp [u]; nlinarith
  have hb : P * Q ^ 2 < u * (Q + 1) := by dsimp [u]; nlinarith
  have helo : -2 * u < E := by
    have hm := mul_le_mul_of_nonneg_left hs.2 (show 0 ≤ 2 * u by omega)
    have hp : 0 ≤ P * Q ^ 2 := by positivity
    nlinarith
  have hehi : E < 2 * u := by
    have hm := mul_nonneg (show 0 ≤ 2 * u by omega) (show 0 ≤ s by omega)
    nlinarith
  have hbounds : K - 1 ≤ F ∧ F ≤ K := by
    change 2 * u * F ≤ P * Q * (P + 1) at hF
    change P * Q * (P + 1) < 2 * u * (F + 1) at hF'
    constructor
    · by_contra h
      have hm := mul_le_mul_of_nonneg_left (show F + 1 ≤ K - 1 by omega) (le_of_lt hu)
      dsimp [E] at helo
      nlinarith
    · by_contra h
      have hm := mul_le_mul_of_nonneg_left (show K + 1 ≤ F by omega) (le_of_lt hu)
      dsimp [E] at hehi
      nlinarith
  have hsone : s = 1 → F = K := by
    intro hs1
    have he : 0 < E := by rw [hs1] at hid; nlinarith
    change P * Q * (P + 1) < 2 * u * (F + 1) at hF'
    dsimp [E] at he
    by_contra h
    have hm := mul_le_mul_of_nonneg_left (show F + 1 ≤ K by omega) (le_of_lt hu)
    nlinarith
  have hstop : s = Q → F = K - 1 := by
    intro hsq
    have he : E < 0 := by
      rw [hsq] at hid
      have hm := mul_le_mul_of_nonneg_left (show Q + 1 ≤ 2 * Q by omega) (le_of_lt hu)
      nlinarith
    change 2 * u * F ≤ P * Q * (P + 1) at hF
    by_contra h
    have hFK : F = K := by omega
    dsimp [E] at he
    rw [hFK] at hF
    nlinarith
  by_cases hFK : F = K
  · refine ⟨0, Or.inl rfl, ?_, ?_, ?_⟩ <;> dsimp [K] at * <;> omega
  · refine ⟨1, Or.inr rfl, ?_, ?_, ?_⟩ <;> dsimp [K] at * <;> omega

/-- The nonzero digit is forced by the source quotient, including its endpoint digits. -/
private theorem residual_digit (x y : ℕ) (hx : 0 < x) (hy : 2 ≤ y) :
    let P := 2 ^ x
    let Q := 2 ^ y
    let u := 1 + P + P * Q
    0 < (P * Q * (P + 1) / (2 * u)) % Q := by
  dsimp only
  let P := 2 ^ x
  let Q := 2 ^ y
  let B := 2 ^ (x - 1)
  let d := B / (Q + 1)
  let s := B % (Q + 1)
  let u := 1 + P + P * Q
  let F := P * Q * (P + 1) / (2 * u)
  change 0 < F % Q
  have hP : 2 ≤ P := by dsimp [P]; exact Nat.one_lt_two_pow_iff.mpr (by omega)
  have hQ : 4 ≤ Q := by
    change 2 ^ 2 ≤ 2 ^ y
    exact Nat.pow_le_pow_right (by decide) hy
  have hPB : P = 2 * B := by dsimp [P, B]; rw [← pow_succ', Nat.sub_add_cancel hx]
  have hQhalf : Q = 2 * 2 ^ (y - 1) := by dsimp [Q]; rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  have hc : Nat.Coprime (Q + 1) B := by
    apply Nat.Coprime.pow_right
    apply Nat.coprime_two_right.mpr
    exact ⟨2 ^ (y - 1), by omega⟩
  have hs0 : 0 < s := by
    by_contra h
    have hz : B % (Q + 1) = 0 := by change s = 0; omega
    have he := hc.eq_one_of_dvd (Nat.dvd_of_mod_eq_zero hz)
    omega
  have hsQ : s ≤ Q := by have := Nat.mod_lt B (show 0 < Q + 1 by omega); omega
  have hBs : B = d * (Q + 1) + s := by
    simpa only [d, s, Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div B (Q + 1)).symm
  have hF := Nat.mul_div_le (P * Q * (P + 1)) (2 * u)
  have hF' := Nat.lt_mul_div_succ (P * Q * (P + 1)) (show 0 < 2 * u by dsimp [u]; positivity)
  obtain ⟨c, hc01, he, hlo, hhi⟩ := quotient_digit P Q B d s F
    (by exact_mod_cast hP) (by exact_mod_cast hQ) (by exact_mod_cast hPB)
    (by exact_mod_cast hBs) ⟨by exact_mod_cast hs0, by exact_mod_cast hsQ⟩
    (by exact_mod_cast hF) (by exact_mod_cast hF')
  have hmod : (F : ℤ) % (Q : ℤ) = (s : ℤ) - c := by
    rw [show (F : ℤ) = ((s : ℤ) - c) + (d : ℤ) * Q by linarith,
      Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) hhi]
  by_contra hn
  have hz : F % Q = 0 := by omega
  have hz' : (F : ℤ) % (Q : ℤ) = 0 := by exact_mod_cast hz
  omega

/-- A least set bit occurs in the exact quotient window of the unused mask. -/
private theorem residual_window (x y l : ℕ) (hx : 0 < x) (hy : 2 ≤ y) :
    let P := 2 ^ x
    let Q := 2 ^ y
    let L := 2 ^ l
    let n := L * P * Q * (P + 1) / (2 * (1 + P + P * Q))
    ∃ e : ℕ, e < y ∧ n.testBit (l + e) = true ∧
      (∀ j : ℕ, j < e → ((n / L) % Q).testBit j = false) := by
  dsimp only
  let P := 2 ^ x
  let Q := 2 ^ y
  let L := 2 ^ l
  let u := 1 + P + P * Q
  let n := L * P * Q * (P + 1) / (2 * u)
  change ∃ e, e < y ∧ n.testBit (l + e) = true ∧
    ∀ j, j < e → ((n / L) % Q).testBit j = false
  have hL : 0 < L := by dsimp [L]; positivity
  have hnL : n / L = P * Q * (P + 1) / (2 * u) := by
    dsimp only [n]
    rw [show L * P * Q * (P + 1) = L * (P * Q * (P + 1)) by ring,
      Nat.div_div_eq_div_mul, Nat.mul_comm (2 * u) L]
    exact Nat.mul_div_mul_left _ _ hL
  have hb : 0 < (n / L) % Q := by rw [hnL]; exact residual_digit x y hx hy
  let b := (n / L) % Q
  have he : ∃ e : ℕ, b.testBit e = true := by
    by_contra h
    have hz : b = 0 := Nat.zero_of_testBit_eq_false (fun i => by
      cases hi : b.testBit i <;> simp_all)
    omega
  let e := Nat.find he
  have heb : b.testBit e = true := Nat.find_spec he
  have hey : e < y := by
    by_contra h
    have hp : Q ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) (by omega)
    have hbQ : b < Q := Nat.mod_lt _ (by dsimp [Q]; positivity)
    have hf := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hbQ hp)
    rw [hf] at heb
    contradiction
  have hnb : (n / L).testBit e = true := by
    simpa only [b, Q, Nat.testBit_mod_two_pow, decide_eq_true hey, Bool.true_and] using heb
  refine ⟨e, hey, ?_, ?_⟩
  · rw [Nat.add_comm l e, Nat.testBit_add]
    exact hnb
  · intro j hj
    have hj' := Nat.find_min he hj
    cases hb : b.testBit j <;> simp_all

/-- Deleting a present bit gives exactly the remaining support, with no borrow. -/
theorem erase_bit (n j : ℕ) (hj : n.testBit j = true) :
    (n - 2 ^ j).bitIndices.toFinset = n.bitIndices.toFinset.erase j := by
  classical
  have hmem : j ∈ n.bitIndices.toFinset := by simpa using Nat.mem_bitIndices.mpr hj
  have hsum := Finset.sum_erase_add (n.bitIndices.toFinset) (fun i => 2 ^ i) hmem
  rw [Finset.sum_toFinset_bitIndices_two_pow] at hsum
  apply Finset.geomSum_injective (by decide : 2 ≤ (2 : ℕ))
  dsimp only
  rw [Finset.sum_toFinset_bitIndices_two_pow]
  omega

/-- Capping the quotient transfers mass between the two complete untouched ladders. -/
theorem coupled_transfer (q δ S T D : ℤ) (hq : 1 ≤ q) (hd : 0 < δ)
    (hT : 0 ≤ T) (hD : D = q * δ + T) (hlo : δ ≤ S + T)
    (hhi : S ≤ 2 * q * δ) :
    let i := min q ((S + T) / δ)
    1 ≤ i ∧ i ≤ q ∧ 0 ≤ S + T - i * δ ∧ S + T - i * δ ≤ D := by
  dsimp only
  let f := (S + T) / δ
  have hr0 := Int.emod_nonneg (S + T) (ne_of_gt hd)
  have hr1 := Int.emod_lt_of_pos (S + T) hd
  have he := Int.emod_add_mul_ediv (S + T) δ
  change (S + T) % δ + δ * f = S + T at he
  have hf : 1 ≤ f := by
    by_contra h
    have hm := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd) (show f ≤ 0 by omega)
    omega
  have hdD : δ ≤ D := by nlinarith
  by_cases hfq : f ≤ q
  · rw [min_eq_right hfq]
    exact ⟨hf, hfq, by nlinarith, by nlinarith⟩
  · rw [min_eq_left (by omega : q ≤ f)]
    have hm := mul_le_mul_of_nonneg_right (show q ≤ f by omega) (le_of_lt hd)
    exact ⟨hq, le_rfl, by nlinarith, by nlinarith⟩

/-- Every bit in the forced source window has a strict unwrapped exit. -/
private theorem residual_bounds (P Q H L r : ℤ)
    (hP : 2 ≤ P) (hQ : 4 ≤ Q) (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hPH : P = H * Q) (hr : L ≤ r) (hrQ : 2 * r ≤ L * Q) :
    let R := L * P * Q
    let u := 1 + P + P * Q
    let w := 1 + Q + Q * R
    let δ := R - P - H + 1
    let T := (u - 1) / 2
    δ - T < r * u ∧ r * u < w - u := by
  dsimp only
  let R := L * P * Q
  let u := 1 + P + P * Q
  let T := (u - 1) / 2
  change (R - P - H + 1) - T < r * u ∧ r * u < (1 + Q + Q * R) - u
  have hPQ : 0 ≤ P * Q := by positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hT : 0 ≤ T := by dsimp [T]; exact Int.ediv_nonneg (by omega) (by decide)
  have hlow : R < r * u := by
    have hm := mul_le_mul_of_nonneg_right hr (le_of_lt hu)
    dsimp [R, u] at *
    nlinarith
  refine ⟨by omega, ?_⟩
  have hcoef : 0 ≤ P * Q - P - 1 := by nlinarith
  have hqpoly : 0 ≤ Q ^ 2 - 3 * Q - 2 := by nlinarith
  have hmargin : 0 < P * (Q ^ 2 - 3 * Q - 2) + Q := by positivity
  have hscale := mul_le_mul_of_nonneg_right hL (mul_nonneg (show 0 ≤ Q by omega) hcoef)
  have hrscale := mul_le_mul_of_nonneg_right hrQ (le_of_lt hu)
  dsimp only [u, R] at *
  nlinarith only [hscale, hrscale, hmargin]

/-- A present reserved bit and the capped transfer produce legal coefficients. -/
private theorem residual_coefficients (n r : ℕ) (P Q H L : ℤ)
    (hP : 2 ≤ P) (hQ : 4 ≤ Q) (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hPH : P = H * Q) (hQeven : Q % 2 = 0)
    (hr : L ≤ r) (hrQ : 2 * (r : ℤ) ≤ L * Q) :
    let R := L * P * Q
    let u := 1 + P + P * Q
    let v := 1 + R + R * P
    let w := 1 + Q + Q * R
    let δ := R - P - H + 1
    let T := (u - 1) / 2
    let D := (w - 1) / 2
    ∃ i : ℤ, 1 ≤ i ∧ i ≤ Q / 2 ∧
      0 ≤ P / 2 - i * H ∧ P / 2 - i * H < P / 2 ∧
      0 ≤ i - 1 ∧ i - 1 < Q / 2 ∧
      0 ≤ (n - r : ℕ) * u + (i - 1) * v + (P / 2 - i * H) * w ∧
      0 ≤ (r : ℤ) * u + T - i * δ ∧ (r : ℤ) * u + T - i * δ ≤ D := by
  dsimp only
  let R := L * P * Q
  let u := 1 + P + P * Q
  let v := 1 + R + R * P
  let w := 1 + Q + Q * R
  let δ := R - P - H + 1
  let T := (u - 1) / 2
  let D := (w - 1) / 2
  have hQhalf : Q = 2 * (Q / 2) := by omega
  have hPhalf : P / 2 = H * (Q / 2) := by
    have hp : P = 2 * (H * (Q / 2)) := by
      calc P = H * Q := hPH
           _ = H * (2 * (Q / 2)) := congrArg (fun z : ℤ => H * z) hQhalf
           _ = 2 * (H * (Q / 2)) := by ring
    omega
  have hrel : w - u = Q * δ := by dsimp [w, u, δ]; rw [hPH]; ring
  have hPeven : P % 2 = 0 := by
    have hp : P = 2 * (H * (Q / 2)) := by calc P = H * Q := hPH
           _ = H * (2 * (Q / 2)) := congrArg (fun z : ℤ => H * z) hQhalf
           _ = 2 * (H * (Q / 2)) := by ring
    omega
  have hPQeven : (P * Q) % 2 = 0 := by simp [Int.mul_emod, hQeven]
  have hQReven : (Q * R) % 2 = 0 := by simp [Int.mul_emod, hQeven]
  have huodd : u % 2 = 1 := by dsimp [u]; omega
  have hwodd : w % 2 = 1 := by dsimp [w]; omega
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hv0 : 0 ≤ v := by dsimp [v, R]; positivity
  have hw0 : 0 ≤ w := by dsimp [w, R]; positivity
  have hT : 0 ≤ T := by dsimp [T]; exact Int.ediv_nonneg (by dsimp [u]; nlinarith) (by decide)
  have hD : D = Q / 2 * δ + T := by
    have ht : 2 * T = u - 1 := by dsimp [T]; omega
    have hd : 2 * D = w - 1 := by dsimp [D]; omega
    nlinarith only [ht, hd, hrel, congrArg (fun z : ℤ => z * δ) hQhalf]
  have hb := residual_bounds P Q H L r hP hQ hH hL hPH hr hrQ
  change δ - T < (r : ℤ) * u ∧ (r : ℤ) * u < w - u at hb
  have hwu : 0 < w - u := by
    have hu : 0 < u := by dsimp [u]; positivity
    have hr0 : 0 < (r : ℤ) := by omega
    nlinarith only [hb.2, mul_pos hr0 hu]
  have hd : 0 < δ := by
    have hp : 0 < Q * δ := by omega
    exact (mul_pos_iff_of_pos_left (by omega : 0 < Q)).mp hp
  obtain ⟨hi1, hiQ, he0, heD⟩ := coupled_transfer (Q / 2) δ ((r : ℤ) * u) T D
    (by omega) hd hT hD (by omega) (by nlinarith only [hb.2, hrel, congrArg (fun z : ℤ => z * δ) hQhalf])
  let i := min (Q / 2) (((r : ℤ) * u + T) / δ)
  change 1 ≤ i at hi1
  change i ≤ Q / 2 at hiQ
  change 0 ≤ (r : ℤ) * u + T - i * δ at he0
  change (r : ℤ) * u + T - i * δ ≤ D at heD
  have hdW0 : 0 ≤ P / 2 - i * H := by nlinarith [hPhalf]
  have hdW1 : P / 2 - i * H < P / 2 := by nlinarith
  refine ⟨i, hi1, hiQ, hdW0, hdW1, by omega, by omega, ?_, he0, heD⟩
  exact add_nonneg (add_nonneg (mul_nonneg (by positivity) hu0)
    (mul_nonneg (by omega) hv0)) (mul_nonneg hdW0 hw0)

/-- The source-forced window supplies an actual submask and both compatible ladder coefficients. -/
theorem packet_residual (x y l : ℕ) (hx : y + 3 ≤ x) (hy : 2 ≤ y) :
    let P : ℤ := 2 ^ x
    let Q : ℤ := 2 ^ y
    let R : ℤ := 2 ^ l * P * Q
    let u : ℤ := 1 + P + P * Q
    let v : ℤ := 1 + R + R * P
    let w : ℤ := 1 + Q + Q * R
    let n : ℕ := 2 ^ l * 2 ^ x * 2 ^ y * (2 ^ x + 1) /
      (2 * (1 + 2 ^ x + 2 ^ x * 2 ^ y))
    let C := P / 2 * w - (u + 1) / 2
    let h := v - (n + 1) * u
    let D := (w - 1) / 2
    ∃ c dV dW : ℕ, c.bitIndices.toFinset ⊆ n.bitIndices.toFinset ∧
      dV < 2 ^ (y - 1) ∧ dW < 2 ^ (x - 1) ∧
      0 ≤ (c : ℤ) * u + (dV : ℤ) * v + (dW : ℤ) * w ∧
      0 ≤ C - h - ((c : ℤ) * u + (dV : ℤ) * v + (dW : ℤ) * w) ∧
      C - h - ((c : ℤ) * u + (dV : ℤ) * v + (dW : ℤ) * w) ≤ D := by
  dsimp only
  let P : ℤ := 2 ^ x
  let Q : ℤ := 2 ^ y
  let H : ℤ := 2 ^ (x - y)
  let L : ℤ := 2 ^ l
  let R := L * P * Q
  let u := 1 + P + P * Q
  let v := 1 + R + R * P
  let w := 1 + Q + Q * R
  let n : ℕ := 2 ^ l * 2 ^ x * 2 ^ y * (2 ^ x + 1) /
    (2 * (1 + 2 ^ x + 2 ^ x * 2 ^ y))
  let C := P / 2 * w - (u + 1) / 2
  let h := v - ((n : ℤ) + 1) * u
  let D := (w - 1) / 2
  change ∃ c dV dW : ℕ, c.bitIndices.toFinset ⊆ n.bitIndices.toFinset ∧
    dV < 2 ^ (y - 1) ∧ dW < 2 ^ (x - 1) ∧
    0 ≤ (c : ℤ) * u + (dV : ℤ) * v + (dW : ℤ) * w ∧
    0 ≤ C - h - ((c : ℤ) * u + (dV : ℤ) * v + (dW : ℤ) * w) ∧
    C - h - ((c : ℤ) * u + (dV : ℤ) * v + (dW : ℤ) * w) ≤ D
  obtain ⟨e, hey, hbit, _⟩ := residual_window x y l (by omega) hy
  change n.testBit (l + e) = true at hbit
  let r := 2 ^ (l + e)
  have hrn : r ≤ n := Nat.two_pow_le_of_mem_bitIndices (Nat.mem_bitIndices.mpr hbit)
  have hP : 2 ≤ P := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 1 ≤ x by omega)
    simpa [P] using hp
  have hQ : 4 ≤ Q := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hy
    simpa [Q] using hp
  have hH : 1 ≤ H := by dsimp [H]; exact one_le_pow₀ (by norm_num)
  have hL : 1 ≤ L := by dsimp [L]; exact one_le_pow₀ (by norm_num)
  have hPH : P = H * Q := by
    dsimp [P, H, Q]
    rw [← pow_add, Nat.sub_add_cancel (by omega : y ≤ x)]
  have hpHalf : P = 2 * (2 : ℤ) ^ (x - 1) := by
    dsimp [P]; conv_lhs => rw [show x = (x - 1) + 1 by omega, pow_succ]
    ring
  have hqHalf : Q = 2 * (2 : ℤ) ^ (y - 1) := by
    dsimp [Q]; conv_lhs => rw [show y = (y - 1) + 1 by omega, pow_succ]
    ring
  have hPdiv : P / 2 = (2 : ℤ) ^ (x - 1) := by omega
  have hQdiv : Q / 2 = (2 : ℤ) ^ (y - 1) := by omega
  have hr : L ≤ (r : ℤ) := by
    dsimp only [L, r]
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2) (show l ≤ l + e by omega))
  have hrQ : 2 * (r : ℤ) ≤ L * Q := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show e + 1 ≤ y by omega)
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ L by omega)
    simpa only [r, L, Q, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, pow_add, pow_succ,
      mul_comm, mul_left_comm, mul_assoc] using hm
  obtain ⟨i, hi1, hiQ, hdW0, hdW1, hdV0, hdV1, hmass0, hE0, hED⟩ :=
    residual_coefficients n r P Q H L hP hQ hH hL hPH (by omega) hr hrQ
  let dV := (i - 1).toNat
  let dW := (P / 2 - i * H).toNat
  have hdV : (dV : ℤ) = i - 1 := Int.toNat_of_nonneg hdV0
  have hdW : (dW : ℤ) = P / 2 - i * H := Int.toNat_of_nonneg hdW0
  have hc : ((n - r : ℕ) : ℤ) = (n : ℤ) - r := Nat.cast_sub hrn
  have hPeven : P % 2 = 0 := by omega
  have hQeven : Q % 2 = 0 := by omega
  have hPQeven : (P * Q) % 2 = 0 := by simp [Int.mul_emod, hQeven]
  have huodd : u % 2 = 1 := by dsimp [u]; omega
  let T := (u - 1) / 2
  let δ := R - P - H + 1
  have ht : 2 * T = u - 1 := by dsimp [T]; omega
  have ht' : (u + 1) / 2 = T + 1 := by omega
  have hv : v = H * w + δ := by dsimp [v, w, δ]; rw [hPH]; ring
  have heq : C - h - (((n - r : ℕ) : ℤ) * u + (dV : ℤ) * v + (dW : ℤ) * w) =
      (r : ℤ) * u + T - i * δ := by
    dsimp only [C, h]
    rw [hc, hdV, hdW, hv, ht']
    ring_nf
    nlinarith only [ht]
  refine ⟨n - r, dV, dW, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [erase_bit n (l + e) hbit]
    exact Finset.erase_subset _ _
  · have hh : (dV : ℤ) < (2 : ℤ) ^ (y - 1) := by rw [hdV, ← hQdiv]; exact hdV1
    exact_mod_cast hh
  · have hh : (dW : ℤ) < (2 : ℤ) ^ (x - 1) := by rw [hdW, ← hPdiv]; exact hdW1
    exact_mod_cast hh
  · simpa only [hdV, hdW] using hmass0
  · rw [heq]; exact hE0
  · rw [heq]; exact hED


end D5.S3.Combinatorics.Circle.ThreeBitSource
