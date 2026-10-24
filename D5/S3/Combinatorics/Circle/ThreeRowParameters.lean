/- GID: D5/S3/Combinatorics/Circle/ThreeRowParameters
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeRowParameters
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Parameter arithmetic and the attained-mask gate for the explicit three-row family. -/
module
import D5.S3.Combinatorics.Circle.SourceWidth
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
namespace D5.S3.Combinatorics.Circle.ThreeRowSource
open SourceWidth
open scoped BigOperators

open SourceWidth
open scoped BigOperators

/- Parameter definitions keep natural powers separate from signed arithmetic. -/
public def rowLength (J m : ℕ) : ℕ := J + m * (J + 1)
public def baseLength (J m : ℕ) : ℕ := 3 * rowLength J m + J + 4
public def r (J : ℕ) : ℤ := 2 ^ J
public def q (J m : ℕ) : ℤ := 2 ^ rowLength J m
public def H (r : ℤ) : ℤ := 2 * r - 1
public def Q (r q : ℤ) : ℤ := 4 * r * q ^ 3
public def C (r q : ℤ) : ℤ := 8 * r * q ^ 3 - 1
public def N (r q : ℤ) : ℤ := 16 * r * q ^ 3 - 1
public def M (r q : ℤ) : ℤ := 8 * r * q ^ 3 - 2 * H r * q ^ 2 - q - 1
public def a (r q : ℤ) : ℤ := 4 * H r * q ^ 2 + 2 * q + 1
public def b (_r q : ℤ) : ℤ := 8 * q ^ 3 - 4 * q ^ 2 - 2 * q - 1
public def delta (r q : ℤ) : ℤ := (q + r - 1) * (2 * q + 1)
public def e2 (r q : ℤ) : ℤ := 2 * q * (q + r - 1)
public def z1 (r q : ℤ) : ℤ := a r q + 2 * delta r q
public def z2 (r q : ℤ) : ℤ := a r q + 2 * e2 r q
public def D (r q : ℤ) : ℤ := q * a r q
public def V1 (r q : ℤ) : ℤ := r * b r q
public def V2 (r q : ℤ) : ℤ := M r q - e2 r q
public def W1 (r q : ℤ) : ℤ := (q / 2) * z1 r q
public def W2 (r q : ℤ) : ℤ := (q / 2) * z2 r q

/- The geometric sum is integral by definition, not by an assumed divisibility. -/
def firstCoefficient (J m : ℕ) : ℕ :=
  2 ^ J * ∑ h ∈ Finset.range m, (2 ^ (J + 1)) ^ h

private theorem coefficient_identity (J m : ℕ) :
    H (r J) * (firstCoefficient J m : ℤ) = q J m - r J := by
  induction m with
  | zero => simp [firstCoefficient, q, rowLength, H, r]
  | succ m ih =>
    have hr : (2 : ℤ) ^ (J + 1) = 2 * r J := by
      simp [r, pow_succ]; ring
    have hq : q J (m + 1) = q J m * (2 : ℤ) ^ (J + 1) := by
      unfold q rowLength
      rw [show J + (m + 1) * (J + 1) = J + m * (J + 1) + (J + 1) by ring, pow_add]
    have hc : (firstCoefficient J (m + 1) : ℤ) =
        firstCoefficient J m + r J * ((2 : ℤ) ^ (J + 1)) ^ m := by
      simp [firstCoefficient, Finset.sum_range_succ, mul_add, Nat.cast_sum,
        Nat.cast_mul, Nat.cast_pow, r]
    have hp : q J m = r J * ((2 : ℤ) ^ (J + 1)) ^ m := by
      simp [q, rowLength, r, pow_add, pow_mul, mul_pow]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hc]
    calc
      H (r J) * ((firstCoefficient J m : ℕ) + r J * ((2 : ℤ) ^ (J + 1)) ^ m) =
          H (r J) * (firstCoefficient J m : ℤ) + H (r J) * r J * ((2 : ℤ) ^ (J + 1)) ^ m := by ring
      _ = (q J m - r J) + H (r J) * q J m := by rw [ih, hp, hr]; ring
      _ = q J (m + 1) - r J := by rw [hq, hr]; unfold H; ring

private theorem parameter_bounds (J m : ℕ) (hJ : 2 ≤ J) (hm : 1 ≤ m) :
    4 ≤ r J ∧ 2 * (r J) ^ 2 ≤ q J m ∧
    2 * (r J / 2) = r J ∧ 2 * (q J m / 2) = q J m ∧
    1 ≤ rowLength J m ∧ r J ≤ (firstCoefficient J m : ℤ) ∧
    (firstCoefficient J m : ℤ) < q J m := by
  have hr : (4 : ℤ) ≤ 2 ^ J := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hJ
    norm_num at this
    exact this
  have hL : 2 * J + 1 ≤ rowLength J m := by
    unfold rowLength
    nlinarith
  have hq : 2 * (r J) ^ 2 ≤ q J m := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hL
    have he : (2 : ℤ) ^ (2 * J + 1) = 2 * (r J) ^ 2 := by
      unfold r
      have hpow : (2 : ℤ) ^ (2 * J) = ((2 : ℤ) ^ J) ^ 2 := by
        calc
          (2 : ℤ) ^ (2 * J) = ((2 : ℤ) ^ 2) ^ J := by rw [pow_mul]
          _ = ((2 : ℤ) ^ J) ^ 2 := by
            rw [← pow_mul]
            rw [show 2 * J = J * 2 by omega]
            rw [pow_mul]
      calc
        (2 : ℤ) ^ (2 * J + 1) = (2 : ℤ) ^ (2 * J) * 2 := by rw [pow_add]; ring
        _ = ((2 : ℤ) ^ J) ^ 2 * 2 := by rw [hpow]
        _ = 2 * ((2 : ℤ) ^ J) ^ 2 := by ring
    simpa [q, he] using this
  have heven (n : ℕ) (hn : 1 ≤ n) : 2 * ((2 : ℤ) ^ n / 2) = 2 ^ n := by
    obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ]
    omega
  have hrR : (4 : ℤ) ≤ r J := by simpa [r] using hr
  have hc := coefficient_identity J m
  have hc0 : 0 ≤ (firstCoefficient J m : ℤ) := Int.natCast_nonneg _
  have hcr : r J ≤ (firstCoefficient J m : ℤ) := by
    have hq' : r J * H (r J) ≤ q J m - r J := by
      unfold H
      nlinarith [hq, hrR]
    have hposH : 0 < H (r J) := by unfold H; nlinarith [hrR]
    by_contra hn
    have hn' : (firstCoefficient J m : ℤ) < r J := lt_of_not_ge hn
    have hmul := mul_lt_mul_of_pos_left hn' hposH
    rw [← hc] at hq'
    nlinarith
  have hclt : (firstCoefficient J m : ℤ) < q J m := by
    have hH : 1 ≤ H (r J) := by unfold H; nlinarith [hrR]
    by_contra hnlt
    have hqle : q J m ≤ (firstCoefficient J m : ℤ) := le_of_not_gt hnlt
    have hmul := mul_le_mul_of_nonneg_left hqle (by unfold H; nlinarith [hrR] : 0 ≤ H (r J))
    have hq0 : 0 ≤ q J m := by nlinarith [hq]
    have hmul2 := mul_le_mul_of_nonneg_right hH hq0
    have hqbound : q J m ≤ H (r J) * (firstCoefficient J m : ℤ) := by
      simpa only [one_mul] using hmul2.trans hmul
    rw [hc] at hqbound
    have hr0 : 0 < r J := by nlinarith [hrR]
    nlinarith [hqbound]
  exact ⟨hr, hq, heven J (by omega), heven _ (by omega), by omega, hcr, hclt⟩

private theorem modulus_identity (J m : ℕ) :
    modulus (baseLength J m) = N (r J) (q J m) := by
  unfold modulus baseLength N r q
  rw [pow_add, pow_add, pow_mul]
  norm_num [mul_pow]
  have h8 : (8 : ℤ) ^ rowLength J m = 2 ^ (rowLength J m * 3) := by
    rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_mul]
    rw [Nat.mul_comm]
  rw [h8]
  ring

/- All gate inequalities are polynomial, with the true lower bound q>=2r^2. -/
private theorem polynomial_gates (r q : ℤ) (hr : 4 ≤ r) (hq : 2 * r ^ 2 ≤ q) :
    0 < a r q - 1 - 4 * delta r q ∧
    0 < a r q - 2 * r * delta r q ∧
    0 < 2 * H r * delta r q - a r q - 1 ∧
    0 < M r q - D r q ∧
    0 < V1 r q - (q / 2) * z1 r q ∧
    0 < V2 r q - (q / 2) * z2 r q := by
  obtain ⟨x, hx, hrx⟩ : ∃ x : ℤ, 0 ≤ x ∧ r = x + 4 :=
    ⟨r - 4, by omega, by ring⟩
  obtain ⟨y, hy, hqy⟩ : ∃ y : ℤ, 0 ≤ y ∧ q = y + 2 * (x + 4) ^ 2 := by
    refine ⟨q - 2 * r ^ 2, by omega, ?_⟩
    rw [← hrx]; ring
  have hq0 : 0 ≤ q := by nlinarith
  have hhalf : q / 2 ≤ q / 2 + 1 := by omega
  have hhalf' : 2 * (q / 2) ≤ q := by omega
  have hz1 : 0 < z1 r q := by
    rw [hrx, hqy]; unfold z1 a delta H; ring_nf; positivity
  have hz2 : 0 < z2 r q := by
    rw [hrx, hqy]; unfold z2 a e2 H; ring_nf; positivity
  have pos (p : ℤ → ℤ → ℤ)
      (hp : 0 < p (x + 4) (y + 2 * (x + 4) ^ 2)) :
      0 < p r q := by simpa only [hrx, hqy] using hp
  constructor
  · apply pos (fun r q => a r q - 1 - 4 * delta r q)
    dsimp [a, delta, H]
    ring_nf
    positivity
  constructor
  · apply pos (fun r q => a r q - 2 * r * delta r q)
    dsimp [a, delta, H]
    ring_nf
    positivity
  constructor
  · apply pos (fun r q => 2 * H r * delta r q - a r q - 1)
    dsimp [a, delta, H]
    ring_nf
    positivity
  constructor
  · apply pos (fun r q => M r q - D r q)
    dsimp [M, D, a, H]
    ring_nf
    positivity
  have hV1 : 0 < 2 * V1 r q - q * z1 r q := by
    apply pos (fun r q => 2 * V1 r q - q * z1 r q)
    dsimp [V1, b, z1, a, delta, H]
    ring_nf
    positivity
  have hV2 : 0 < 2 * V2 r q - q * z2 r q := by
    apply pos (fun r q => 2 * V2 r q - q * z2 r q)
    dsimp [V2, M, e2, z2, a, H]
    ring_nf
    positivity
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hhalf' hz1.le,
    mul_le_mul_of_nonneg_right hhalf' hz2.le]

private theorem gate_polynomial (r q : ℤ) (hr : 4 ≤ r) (hq : 2 * r ^ 2 ≤ q) :
    0 < 8 * (r - 1) * q ^ 2 + (-16 * r ^ 3 + 32 * r ^ 2 - 26 * r + 7) * q
      - 8 * r ^ 3 + 14 * r ^ 2 - 7 * r + 2 ∧
    8 * (r - 1) * q ^ 2 + (-16 * r ^ 3 + 32 * r ^ 2 - 26 * r + 7) * q
      - 8 * r ^ 3 + 14 * r ^ 2 - 7 * r + 2 < 4 * H r * q ^ 2 := by
  obtain ⟨x, hx, hr'⟩ : ∃ x : ℤ, 0 ≤ x ∧ r = x + 4 :=
    ⟨r - 4, by omega, by ring⟩
  obtain ⟨y, hy, hq'⟩ : ∃ y : ℤ, 0 ≤ y ∧ q = y + 2 * (x + 4) ^ 2 := by
    refine ⟨q - 2 * r ^ 2, by omega, ?_⟩
    rw [← hr']; ring
  constructor
  · rw [hr', hq']
    ring_nf
    positivity
  · have hpos : 0 < 4 * H r * q ^ 2 -
        (8 * (r - 1) * q ^ 2 + (-16 * r ^ 3 + 32 * r ^ 2 - 26 * r + 7) * q
          - 8 * r ^ 3 + 14 * r ^ 2 - 7 * r + 2) := by
      rw [hr', hq']
      unfold H
      ring_nf
      positivity
    omega

/- The bridge uses an exact attained INTEGER endpoint; n is the geometric
coefficient, not an extra physical label or a conclusion supplied as a premise. -/
private theorem bridge_arithmetic (r q n : ℤ)
    (hr : 4 ≤ r) (hq : 2 * r ^ 2 ≤ q)
    (hr2 : 2 * (r / 2) = r) (hq2 : 2 * (q / 2) = q)
    (hn : H r * n = q - r) :
    let c := (n + 1) * (2 * q + 1)
    let R := a r q - c - 2 * (r - 1) * delta r q
    let F := R + V1 r q - W1 r q
    let f := F - W2 r q + (r / 2) * b r q - (q / 2 - 1) * z2 r q
    0 < R ∧ R ≤ C r q - V1 r q ∧
    0 < F ∧ F ≤ C r q ∧
    2 * H r * f =
      8 * (r - 1) * q ^ 2 + (-16 * r ^ 3 + 32 * r ^ 2 - 26 * r + 7) * q
        - 8 * r ^ 3 + 14 * r ^ 2 - 7 * r + 2 ∧
    0 < f ∧ f < C r q - V2 r q ∧ W2 r q + f < C r q := by
  dsimp only
  let c := (n + 1) * (2 * q + 1)
  let R := a r q - c - 2 * (r - 1) * delta r q
  let F := R + V1 r q - W1 r q
  let f := F - W2 r q + (r / 2) * b r q - (q / 2 - 1) * z2 r q
  have hH : 0 < H r := by unfold H; omega
  have hq0 : 0 < q := by nlinarith
  have hd : 0 < delta r q := by
    have h1 : 0 < q + r - 1 := by omega
    have h2 : 0 < 2 * q + 1 := by omega
    exact mul_pos h1 h2
  have hc : H r * c = delta r q := by
    dsimp [c, delta, H] at *
    linear_combination (2 * q + 1) * hn
  have hc0 : 0 < c := by nlinarith
  have hc_le : c < 2 * delta r q := by unfold H at hc hH; nlinarith
  obtain ⟨h4, h2r, h2H, hh, hV1W1, hV2W2⟩ := polynomial_gates r q hr hq
  have hR : 0 < R := by dsimp [R]; nlinarith
  have hcap1 : 2 * (C r q - V1 r q) = a r q - 1 + 2 * delta r q := by
    unfold C V1 b a delta H
    ring
  have hRcap : R ≤ C r q - V1 r q := by
    have hR2 : 2 * R ≤ 2 * (C r q - V1 r q) := by
      rw [hcap1]
      dsimp [R]
      unfold H at h2H
      nlinarith [h2H, hc0]
    nlinarith
  have hW1 : 0 ≤ W1 r q := by
    rw [W1]
    have h1 : 0 ≤ q / 2 := Int.ediv_nonneg hq0.le (by norm_num)
    have h2 : 0 ≤ z1 r q := by
      unfold z1 a delta H
      nlinarith [sq_nonneg q]
    exact mul_nonneg h1 h2
  have hV2W : W2 r q < V2 r q := by simpa [W2] using hV2W2
  have hF : 0 < F ∧ F ≤ C r q := by
    dsimp [F, W1] at *
    constructor <;> omega
  have heqStep : 2 * H r * f =
      2 * H r * (a r q - 2 * (r - 1) * delta r q + V1 r q + z2 r q)
        - 2 * delta r q + H r * r * b r q - H r * q * (z1 r q + 2 * z2 r q) := by
    dsimp [f, F, R, W1, W2]
    linear_combination (H r * b r q) * hr2 -
      (H r * (z1 r q + 2 * z2 r q)) * hq2 - 2 * hc
  have heq : 2 * H r * f =
      8 * (r - 1) * q ^ 2 + (-16 * r ^ 3 + 32 * r ^ 2 - 26 * r + 7) * q
        - 8 * r ^ 3 + 14 * r ^ 2 - 7 * r + 2 := by
    rw [heqStep]
    simp only [V1, b, a, z1, z2, delta, e2, H]
    ring_nf
  obtain ⟨hp0, hp1⟩ := gate_polynomial r q hr hq
  have hf0 : 0 < f := by nlinarith
  have hf2 : f < 2 * q ^ 2 := by nlinarith
  have hgap : C r q - V2 r q = 4 * r * q ^ 2 + H r * q := by
    unfold C V2 M e2 H
    ring
  have hfG : f < C r q - V2 r q := by
    rw [hgap]
    unfold H
    nlinarith
  have hclip : W2 r q + f < C r q := by omega
  exact ⟨hR, hRcap, hF.1, hF.2, heq, hf0, hfG, hclip⟩


end D5.S3.Combinatorics.Circle.ThreeRowSource
