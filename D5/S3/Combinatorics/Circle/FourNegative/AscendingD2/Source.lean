/- GID: D5/S3/Combinatorics/Circle/FourNegative/AscendingD2/Source
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-source-table)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact four-chain centered sources for strict ascending gaps and a first ear. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.ThreeBitSource
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

/-! Four exact physical ladders, with no period or coprimality assumption. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.AscendingD2
open SourceWidth PeriodicShortening RunFirstEarTransport
open private centered_ladder from D5.S3.Combinatorics.Circle.ThreeBitSource

private theorem pow_ge_four (n : ℕ) (hn : 2 ≤ n) : (4 : ℤ) ≤ 2 ^ n := by
  simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hn

private theorem seed_bounds (p q r s : ℤ) (hp : 4 ≤ p) (hq : 4 ≤ q)
    (hr : 4 ≤ r) (hs : 4 ≤ s) :
    1 ≤ 1 + p + p * q + p * q * r ∧ 1 + p + p * q + p * q * r < p * q * r * s - 1 := by
  have hpq : 0 < p * q := by positivity
  have hpqr : 0 < p * q * r := by positivity
  have h1 : 1 + p + p * q < 2 * (p * q) := by nlinarith
  have h2 : 4 * (p * q) ≤ p * q * r := by nlinarith
  have h3 : 4 * (p * q * r) ≤ p * q * r * s := by nlinarith
  constructor <;> nlinarith

private theorem shifted (N X Y : ℤ) (e i : ℕ)
    (hrel : (2 : ℤ) ^ e * X = N + Y) :
    centered N ((2 : ℤ) ^ (e + i) * X) = centered N ((2 : ℤ) ^ i * Y) := by
  apply centered_congr
  rw [pow_add]
  rw [show (2 : ℤ) ^ e * 2 ^ i * X = 2 ^ i * (2 ^ e * X) by ring, hrel]
  rw [mul_add, add_comm, Int.add_mul_emod_self_right]

/-- The four consecutive physical ladders, with their terminal negative representatives. -/
private theorem chains (a b c d : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hc : 2 ≤ c) (hd : 2 ≤ d) :
    let R : ℤ := 2 ^ a
    let T : ℤ := 2 ^ b
    let Z : ℤ := 2 ^ c
    let H : ℤ := 2 ^ d
    let N := modulus (a + b + c + d)
    let A := 1 + R + R * T + R * T * Z
    let B := 1 + H + H * R + H * R * T
    let W := 1 + Z + Z * H + Z * H * R
    let X := 1 + T + T * Z + T * Z * H
    let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * A)
    (1 ≤ A ∧ A < N) ∧
    (∀ i < d, f i = if i + 1 < d then (2 : ℤ) ^ i * A else - (N - B)/2) ∧
    (∀ i < c, f (d + i) = if i + 1 < c then (2 : ℤ) ^ i * B else - (N - W)/2) ∧
    (∀ i < b, f (d + c + i) = if i + 1 < b then (2 : ℤ) ^ i * W else - (N - X)/2) ∧
    (∀ i < a, f (d + c + b + i) = if i + 1 < a then (2 : ℤ) ^ i * X else - (N - A)/2) := by
  dsimp only
  let R : ℤ := 2 ^ a
  let T : ℤ := 2 ^ b
  let Z : ℤ := 2 ^ c
  let H : ℤ := 2 ^ d
  let N := modulus (a + b + c + d)
  let A := 1 + R + R * T + R * T * Z
  let B := 1 + H + H * R + H * R * T
  let W := 1 + Z + Z * H + Z * H * R
  let X := 1 + T + T * Z + T * Z * H
  have hN : N = R * T * Z * H - 1 := by dsimp [N, modulus, R, T, Z, H]; simp only [pow_add] <;> ring
  have hR := pow_ge_four a ha
  have hT := pow_ge_four b hb
  have hZ := pow_ge_four c hc
  have hH := pow_ge_four d hd
  change 4 ≤ R at hR
  change 4 ≤ T at hT
  change 4 ≤ Z at hZ
  change 4 ≤ H at hH
  have hA : 1 ≤ A ∧ A < N := by simpa only [A, hN] using seed_bounds R T Z H hR hT hZ hH
  have hB : 1 ≤ B ∧ B < N := by
    have h := seed_bounds H R T Z hH hR hT hZ
    simpa only [B, hN, mul_comm, mul_left_comm, mul_assoc] using h
  have hW : 1 ≤ W ∧ W < N := by
    have h := seed_bounds Z H R T hZ hH hR hT
    simpa only [W, hN, mul_comm, mul_left_comm, mul_assoc] using h
  have hX : 1 ≤ X ∧ X < N := by
    have h := seed_bounds T Z H R hT hZ hH hR
    simpa only [X, hN, mul_comm, mul_left_comm, mul_assoc] using h
  have hpos : 0 < N := by omega
  have hodd : N % 2 = 1 := by
    have hh : H = 2 * (2 : ℤ) ^ (d - 1) := by
      dsimp [H]
      conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
      ring
    have he : N = 2 * (R * T * Z * (2 : ℤ) ^ (d - 1) - 1) + 1 := by rw [hN, hh]; ring
    rw [he]
    omega
  have hAB : (2 : ℤ) ^ d * A = N + B := by change H * A = N + B; rw [hN]; dsimp [A, B]; ring
  have hBW : (2 : ℤ) ^ c * B = N + W := by change Z * B = N + W; rw [hN]; dsimp [B, W]; ring
  have hWX : (2 : ℤ) ^ b * W = N + X := by change T * W = N + X; rw [hN]; dsimp [W, X]; ring
  have hXA : (2 : ℤ) ^ a * X = N + A := by change R * X = N + A; rw [hN]; dsimp [X, A]; ring
  refine ⟨hA, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact centered_ladder N A B d i hpos hodd (by omega) ⟨hB.1, hB.2.le⟩ hi hAB
  · intro i hi
    rw [shifted N A B d i hAB]
    exact centered_ladder N B W c i hpos hodd (by omega) ⟨hW.1, hW.2.le⟩ hi hBW
  · intro i hi
    rw [show d + c + i = d + (c + i) by omega, shifted N A B d (c + i) hAB,
      shifted N B W c i hBW]
    exact centered_ladder N W X b i hpos hodd (by omega) ⟨hX.1, hX.2.le⟩ hi hWX
  · intro i hi
    rw [show d + c + b + i = d + (c + (b + i)) by omega, shifted N A B d (c + (b + i)) hAB,
      shifted N B W c (b + i) hBW, shifted N W X b i hWX]
    exact centered_ladder N X A a i hpos hodd (by omega) ⟨hA.1, hA.2.le⟩ hi hXA

open SourceWidth PeriodicShortening RunFirstEarTransport

private structure Table (a b c : ℕ) (R T Z : ℤ) (f g : ℕ → ℤ) : Prop where
  u : f 0 = 1 + R + R * T + R * T * Z
  un : g 0 = 2 * (1 + R + R * T + R * T * Z)
  v : ∀ i < c - 1, f (2 + i) = (2 : ℤ) ^ i * (4 * R * T + 4 * R + 5)
  vn : ∀ i < c - 1, g (2 + i) = (2 : ℤ) ^ i * (8 * R * T + 8 * R + 9)
  w : ∀ i < b - 1, f (c + 2 + i) = (2 : ℤ) ^ i * ((4 * R + 5) * Z + 1)
  wn : ∀ i < b - 1, g (c + 2 + i) = (2 : ℤ) ^ i * ((8 * R + 9) * Z + 1)
  x : ∀ i < a - 1, f (c + b + 2 + i) = (2 : ℤ) ^ i * (5 * T * Z + T + 1)
  xn : ∀ i < a - 1, g (c + b + 2 + i) = (2 : ℤ) ^ i * (9 * T * Z + T + 1)
  nu : 2 * f 1 = -4 * R * T * Z + 4 * R * T + 4 * R + 6
  nun : 2 * g 1 = -8 * R * T * Z + 8 * R * T + 8 * R + 10
  nv : 2 * f (c + 1) = -4 * R * T * Z + (4 * R + 5) * Z + 2
  nvn : 2 * g (c + 1) = -8 * R * T * Z + (8 * R + 9) * Z + 2
  nw : 2 * f (c + b + 1) = -4 * R * T * Z + 5 * T * Z + T + 2
  nwn : 2 * g (c + b + 1) = -8 * R * T * Z + 9 * T * Z + T + 2
  nx : 2 * f (a + b + c + 1) = -3 * R * T * Z + R * (T + 1) + 2
  nxn : 2 * g (a + b + c + 1) = -7 * R * T * Z + R * (T + 1) + 2

private theorem last_double (N u v : ℤ) (len : ℕ) (hlen : 0 < len)
    (hrel : (2 : ℤ) ^ len * u = N + v) : 2 * (-(N - v)/2) = v - N := by
  have hp : 2 * ((2 : ℤ) ^ (len - 1) * u) = N + v := by
    rw [show len = (len - 1) + 1 by omega, pow_succ] at hrel
    nlinarith only [hrel]
  omega

set_option maxHeartbeats 1200000 in
private theorem paired_table (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    let k := a + b + c + 2
    let A : ℤ := 1 + 2 ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)
    let f := fun i : ℕ => centered (modulus k) ((2 : ℤ) ^ i * A)
    let g := fun i : ℕ => centered (modulus (k + 1)) ((2 : ℤ) ^ i * (2 * A))
    Table a b c (2 ^ a) (2 ^ b) (2 ^ c) f g := by
  dsimp only
  let R : ℤ := 2 ^ a
  let T : ℤ := 2 ^ b
  let Z : ℤ := 2 ^ c
  let k := a + b + c + 2
  let N := modulus k
  let M := modulus (k + 1)
  let A := 1 + R + R * T + R * T * Z
  let B := 1 + 4 + 4 * R + 4 * R * T
  let W := 1 + Z + Z * 4 + Z * 4 * R
  let X := 1 + T + T * Z + T * Z * 4
  let Bn := 1 + 8 + 8 * R + 8 * R * T
  let Wn := 1 + Z + Z * 8 + Z * 8 * R
  let Xn := 1 + T + T * Z + T * Z * 8
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * A)
  let F := fun i : ℕ => centered M ((2 : ℤ) ^ i * A)
  let g := fun i : ℕ => centered M ((2 : ℤ) ^ i * (2 * A))
  have hA : (1 + (2 : ℤ) ^ a + 2 ^ (a + b) + 2 ^ (a + b + c)) = A := by
    dsimp [A, R, T, Z]; simp only [pow_add]
  rw [hA]
  change Table a b c R T Z f g
  have hN : N = 4 * R * T * Z - 1 := by dsimp [N, k, modulus, R, T, Z]; simp only [pow_add] <;> ring
  have hM : M = 2 * N + 1 := by dsimp [M, N, modulus]; rw [pow_succ]; ring
  have h2 := chains a b c 2 ha hb hc (by decide)
  have h3 := chains a b c 3 ha hb hc (by decide)
  norm_num only [show (2 : ℤ) ^ 2 = 4 by norm_num] at h2
  norm_num only [show (2 : ℤ) ^ 3 = 8 by norm_num] at h3
  obtain ⟨_, hU, hV, hW, hX⟩ := h2
  obtain ⟨_, hUn, hVn, hWn, hXn⟩ := h3
  change ∀ i < 2, f i = if i + 1 < 2 then 2 ^ i * A else - (N - B)/2 at hU
  change ∀ i < c, f (2 + i) = if i + 1 < c then 2 ^ i * B else - (N - W)/2 at hV
  change ∀ i < b, f (2 + c + i) = if i + 1 < b then 2 ^ i * W else - (N - X)/2 at hW
  change ∀ i < a, f (2 + c + b + i) = if i + 1 < a then 2 ^ i * X else - (N - A)/2 at hX
  change ∀ i < 3, F i = if i + 1 < 3 then 2 ^ i * A else - (M - Bn)/2 at hUn
  change ∀ i < c, F (3 + i) = if i + 1 < c then 2 ^ i * Bn else - (M - Wn)/2 at hVn
  change ∀ i < b, F (3 + c + i) = if i + 1 < b then 2 ^ i * Wn else - (M - Xn)/2 at hWn
  change ∀ i < a, F (3 + c + b + i) = if i + 1 < a then 2 ^ i * Xn else - (M - A)/2 at hXn
  have hshift (i : ℕ) : g i = F (i + 1) := by dsimp [g, F]; rw [pow_succ]; congr 1; ring
  have rU : (2 : ℤ) ^ 2 * A = N + B := by norm_num; rw [hN]; dsimp [A, B]; ring
  have rV : (2 : ℤ) ^ c * B = N + W := by change Z * B = N + W; rw [hN]; dsimp [B, W]; ring
  have rW : (2 : ℤ) ^ b * W = N + X := by change T * W = N + X; rw [hN]; dsimp [W, X]; ring
  have rX : (2 : ℤ) ^ a * X = N + A := by change R * X = N + A; rw [hN]; dsimp [X, A]; ring
  have rUn : (2 : ℤ) ^ 3 * A = M + Bn := by norm_num; rw [hM, hN]; dsimp [A, Bn]; ring
  have rVn : (2 : ℤ) ^ c * Bn = M + Wn := by change Z * Bn = M + Wn; rw [hM, hN]; dsimp [Bn, Wn]; ring
  have rWn : (2 : ℤ) ^ b * Wn = M + Xn := by change T * Wn = M + Xn; rw [hM, hN]; dsimp [Wn, Xn]; ring
  have rXn : (2 : ℤ) ^ a * Xn = M + A := by change R * Xn = M + A; rw [hM, hN]; dsimp [Xn, A]; ring
  constructor
  · simpa [A] using hU 0 (by decide)
  · rw [hshift]; simpa [A] using hUn 1 (by decide)
  · intro i hi; simpa [B, show i + 1 < c by omega, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hV i (by omega)
  · intro i hi; rw [hshift, show 2 + i + 1 = 3 + i by omega]
    simpa [Bn, show i + 1 < c by omega, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hVn i (by omega)
  · intro i hi
    rw [show c + 2 + i = 2 + c + i by omega, hW i (by omega), ite_eq_left (by omega)]
    dsimp [W]; ring
  · intro i hi; rw [hshift, show c + 2 + i + 1 = 3 + c + i by omega]
    rw [hWn i (by omega), ite_eq_left (by omega)]
    dsimp [Wn]; ring
  · intro i hi
    rw [show c + b + 2 + i = 2 + c + b + i by omega, hX i (by omega), ite_eq_left (by omega)]
    dsimp [X]; ring
  · intro i hi; rw [hshift, show c + b + 2 + i + 1 = 3 + c + b + i by omega]
    rw [hXn i (by omega), ite_eq_left (by omega)]
    dsimp [Xn]; ring
  · have h := hU 1 (by decide)
    rw [ite_eq_right (by decide)] at h
    rw [h, last_double N A B 2 (by decide) rU, hN]
    dsimp [B]; ring
  · rw [hshift]
    have h := hUn 2 (by decide)
    rw [ite_eq_right (by decide)] at h
    rw [h, last_double M A Bn 3 (by decide) rUn, hM, hN]
    dsimp [Bn]; ring
  · have h := hV (c - 1) (by omega)
    rw [ite_eq_right (by omega)] at h
    rw [show c + 1 = 2 + (c - 1) by omega, h, last_double N B W c (by omega) rV, hN]
    dsimp [W]; ring
  · rw [hshift]
    have h := hVn (c - 1) (by omega)
    rw [ite_eq_right (by omega)] at h
    rw [show c + 1 + 1 = 3 + (c - 1) by omega, h, last_double M Bn Wn c (by omega) rVn, hM, hN]
    dsimp [Wn]; ring
  · have h := hW (b - 1) (by omega)
    rw [ite_eq_right (by omega)] at h
    rw [show c + b + 1 = 2 + c + (b - 1) by omega, h, last_double N W X b (by omega) rW, hN]
    dsimp [X]; ring
  · rw [hshift]
    have h := hWn (b - 1) (by omega)
    rw [ite_eq_right (by omega)] at h
    rw [show c + b + 1 + 1 = 3 + c + (b - 1) by omega, h, last_double M Wn Xn b (by omega) rWn, hM, hN]
    dsimp [Xn]; ring
  · have h := hX (a - 1) (by omega)
    rw [ite_eq_right (by omega)] at h
    rw [show a + b + c + 1 = 2 + c + b + (a - 1) by omega, h, last_double N X A a (by omega) rX, hN]
    dsimp [A]; ring
  · rw [hshift]
    have h := hXn (a - 1) (by omega)
    rw [ite_eq_right (by omega)] at h
    rw [show a + b + c + 1 + 1 = 3 + c + b + (a - 1) by omega, h, last_double M Xn A a (by omega) rXn, hM, hN]
    dsimp [A]; ring

end D5.S3.Combinatorics.Circle.FourNegative.AscendingD2
