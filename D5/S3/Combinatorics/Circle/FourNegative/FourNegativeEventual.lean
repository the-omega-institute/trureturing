/- GID: D5/S3/Combinatorics/Circle/FourNegative/FourNegativeEventual
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/FourNegativeEventual
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Eventual physical four-chain joint lift with a literal ear. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.ThreeBitSource
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

/-! Eventual physical four-chain source table and joint lift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventual

open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators

open private mask_labels mask_labels_bound mask_labels_mem mask_complement
  mask_labels_disjoint mask_labels_sum
  from D5.S3.Combinatorics.Circle.ThreeBitSource

private theorem centered_shift (N X Y : ℤ) (e i : ℕ)
    (hN : 0 < N) (hodd : N % 2 = 1)
    (hrel : (2 : ℤ) ^ e * X = N + Y) :
    centered N ((2 : ℤ) ^ (e + i) * X) =
      centered N ((2 : ℤ) ^ i * Y) := by
  apply centered_unique hN hodd (centered_bounds hN hodd _)
    (centered_bounds hN hodd _)
  rw [centered_mod, centered_mod, pow_add]
  have hmul : (2 : ℤ) ^ i * ((2 : ℤ) ^ e * X) =
      (2 : ℤ) ^ i * (N + Y) := by rw [hrel]
  rw [show (2 : ℤ) ^ e * (2 : ℤ) ^ i * X =
      (2 : ℤ) ^ i * ((2 : ℤ) ^ e * X) by ring, hrel, mul_add]
  rw [show (2 : ℤ) ^ i * N + (2 : ℤ) ^ i * Y =
      (2 : ℤ) ^ i * Y + (2 : ℤ) ^ i * N by ring,
    Int.add_mul_emod_self_right]

private theorem centered_ladder (N u v : ℤ) (z e : ℕ)
    (hN : 0 < N) (hodd : N % 2 = 1) (hu : 0 < u)
    (hv : 1 ≤ v ∧ v ≤ N) (he : e < z)
    (hrel : (2 : ℤ) ^ z * u = N + v) :
    centered N ((2 : ℤ) ^ e * u) =
      if e + 1 < z then (2 : ℤ) ^ e * u else -(N - v) / 2 := by
  by_cases hez : e + 1 < z
  · rw [ite_eq_left hez]
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show e + 2 ≤ z by omega)
    rw [pow_add] at hp
    norm_num at hp
    have hm := mul_le_mul_of_nonneg_right hp (le_of_lt hu)
    apply centered_unique hN hodd (centered_bounds hN hodd _) ?_ (centered_mod N _)
    have hx0 : 0 ≤ (2 : ℤ) ^ e * u := by positivity
    have hn0 : 0 ≤ N / 2 := Int.ediv_nonneg (le_of_lt hN) (by decide)
    have hbound : 2 * ((2 : ℤ) ^ e * u) ≤ N := by
      nlinarith [hm, hrel, hv.2]
    exact ⟨by omega, by omega⟩
  · rw [ite_eq_right hez]
    have hexp : z = e + 1 := by omega
    have hp : 2 * ((2 : ℤ) ^ e * u) = N + v := by
      rw [hexp, pow_succ] at hrel
      nlinarith
    have hval : -(N - v) / 2 = (2 : ℤ) ^ e * u - N := by omega
    rw [hval]
    apply centered_unique hN hodd (centered_bounds hN hodd _) ?_ ?_
    · constructor <;> omega
    · rw [centered_mod, Int.sub_emod_right]

set_option maxHeartbeats 1000000 in
-- The paired ladders carry eight centered reductions and their arithmetic bounds.
private theorem four_chain_table (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : a + b + c + 3 ≤ d) :
    let x : ℤ := 2 ^ a
    let y : ℤ := 2 ^ b
    let z : ℤ := 2 ^ c
    let t : ℤ := 2 ^ d
    let P : ℤ := x * y * z
    let DB : ℤ := 1 + x + x * y
    let DL : ℤ := z * (1 + x)
    let DM : ℤ := y * z
    let A : ℤ := P + DB
    let B : ℤ := t * DB + 1
    let L : ℤ := t * DL + 1 + z
    let M : ℤ := t * DM + 1 + y + y * z
    let N : ℤ := P * t - 1
    let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * A)
    let g := fun i : ℕ => centered (2 * N + 1) ((2 : ℤ) ^ i * (2 * A))
    (1 ≤ A ∧ A < N) ∧ (1 ≤ B ∧ B < N) ∧ (1 ≤ L ∧ L < N) ∧
    (1 ≤ M ∧ M < N) ∧
    (∀ i < d, f i = if i + 1 < d then (2 : ℤ) ^ i * A else -(N - B) / 2) ∧
    (∀ i < c, f (d + i) =
      if i + 1 < c then (2 : ℤ) ^ i * B else -(N - L) / 2) ∧
    (∀ i < b, f (d + c + i) =
      if i + 1 < b then (2 : ℤ) ^ i * L else -(N - M) / 2) ∧
    (∀ i < a, f (d + c + b + i) =
      if i + 1 < a then (2 : ℤ) ^ i * M else -(N - A) / 2) ∧
    (∀ i < d, g i = if i + 1 < d then (2 : ℤ) ^ i * (2 * A)
      else -((2 * N + 1) - (2 * B - 1)) / 2) ∧
    (∀ i < c, g (d + i) = if i + 1 < c then (2 : ℤ) ^ i * (2 * B - 1)
      else -((2 * N + 1) - (2 * L - 1 - z)) / 2) ∧
    (∀ i < b, g (d + c + i) = if i + 1 < b then (2 : ℤ) ^ i * (2 * L - 1 - z)
      else -((2 * N + 1) - (2 * M - 1 - y - y * z)) / 2) ∧
    (∀ i < a, g (d + c + b + i) = if i + 1 < a then
      (2 : ℤ) ^ i * (2 * M - 1 - y - y * z)
      else -((2 * N + 1) - A) / 2) ∧
    g (d + c + b + a) = A := by
  dsimp only
  let x : ℤ := 2 ^ a
  let y : ℤ := 2 ^ b
  let z : ℤ := 2 ^ c
  let t : ℤ := 2 ^ d
  let P : ℤ := x * y * z
  let DB : ℤ := 1 + x + x * y
  let DL : ℤ := z * (1 + x)
  let DM : ℤ := y * z
  let A : ℤ := P + DB
  let B : ℤ := t * DB + 1
  let L : ℤ := t * DL + 1 + z
  let M : ℤ := t * DM + 1 + y + y * z
  let N : ℤ := P * t - 1
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * A)
  let g := fun i : ℕ => centered (2 * N + 1) ((2 : ℤ) ^ i * (2 * A))
  have hx : 4 ≤ x := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ha
    norm_num at h
    simpa [x] using h
  have hy : 4 ≤ y := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hb
    norm_num at h
    simpa [y] using h
  have hz : 4 ≤ z := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hc
    norm_num at h
    simpa [z] using h
  have ht : 0 < t := by dsimp [t]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hN : 0 < N := by
    have hk : 8 ≤ a + b + c + d := by omega
    have hp : (2 : ℤ) ^ 8 ≤ 2 ^ (a + b + c + d) := by
      exact pow_le_pow_right₀ (by norm_num) hk
    have he : (2 : ℤ) ^ (a + b + c + d) = P * t := by
      dsimp [P, t, x, y, z]
      ring
    rw [he] at hp
    dsimp [N]
    norm_num at hp ⊢
    omega
  have ht_even : t = 2 * (2 : ℤ) ^ (d - 1) := by
    dsimp [t]
    calc
      (2 : ℤ) ^ d = (2 : ℤ) ^ ((d - 1) + 1) := by congr 1 <;> omega
      _ = (2 : ℤ) ^ (d - 1) * 2 := by rw [pow_succ]
      _ = 2 * (2 : ℤ) ^ (d - 1) := by ring
  have hodd : N % 2 = 1 := by
    have hNform : N = 2 * (P * (2 : ℤ) ^ (d - 1) - 1) + 1 := by
      dsimp [N]
      rw [ht_even]
      ring
    rw [hNform]
    omega
  have hDBP : DB < P := by
    dsimp [DB, P]
    have hxy : 0 < x * y := mul_pos (by omega) (by omega)
    have hdb : 1 + x + x * y < 2 * (x * y) := by nlinarith
    have hp : 4 * (x * y) ≤ x * y * z := by nlinarith
    nlinarith
  have ht8 : 8 ≤ t := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show 3 ≤ d by omega)
    norm_num at h
    simpa [t] using h
  have hA : 1 ≤ A ∧ A < N := by
    constructor
    · dsimp [A, P, DB]
      nlinarith [hP]
    · dsimp [A, N]
      have hPt : 8 * P ≤ P * t := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left ht8 hP.le
      nlinarith [hP, hDBP, hPt]
  have hrelA : t * A = N + B := by dsimp [A, B, N, P, DB]; ring
  have hrelB : z * B = N + L := by dsimp [B, L, N, P, DB, DL]; ring
  have hrelL : y * L = N + M := by dsimp [L, M, N, P, DL, DM]; ring
  have hrelM : x * M = N + A := by dsimp [M, A, N, P, DB, DM]; ring
  have hB : 1 ≤ B ∧ B < N := by
    constructor
    · dsimp [B]
      have hDB0 : 0 < DB := by dsimp [DB]; positivity
      nlinarith
    · nlinarith [hrelA, hA.1, hA.2, hx]
  have hM : 1 ≤ M ∧ M < N := by
    constructor
    · dsimp [M]
      have hDM0 : 0 < DM := by dsimp [DM]; positivity
      nlinarith
    · nlinarith [hrelM, hA.1, hA.2, hx]
  have hL : 1 ≤ L ∧ L < N := by
    constructor
    · dsimp [L]
      have hDL0 : 0 < DL := by dsimp [DL]; positivity
      nlinarith
    · nlinarith [hrelL, hM.1, hM.2, hy]
  have hN' : 0 < 2 * N + 1 := by omega
  have hodd' : (2 * N + 1) % 2 = 1 := by omega
  have hB' : 1 ≤ 2 * B - 1 ∧ 2 * B - 1 < 2 * N + 1 := by omega
  have hL' : 1 ≤ 2 * L - 1 - z ∧ 2 * L - 1 - z < 2 * N + 1 := by
    constructor
    · dsimp [L]
      have hDL0 : 0 < DL := by dsimp [DL]; positivity
      nlinarith
    · nlinarith [hL.2, hz]
  have hM' : 1 ≤ 2 * M - 1 - y - y * z ∧ 2 * M - 1 - y - y * z < 2 * N + 1 := by
    constructor
    · dsimp [M]
      have hDM0 : 0 < DM := by dsimp [DM]; positivity
      nlinarith
    · nlinarith [hM.2, hy, hz]
  have hrelA' : t * (2 * A) = (2 * N + 1) + (2 * B - 1) := by nlinarith
  have hrelB' : z * (2 * B - 1) = (2 * N + 1) + (2 * L - 1 - z) := by nlinarith [hrelB]
  have hrelL' : y * (2 * L - 1 - z) = (2 * N + 1) + (2 * M - 1 - y - y * z) := by nlinarith [hrelL]
  have hrelM' : x * (2 * M - 1 - y - y * z) = (2 * N + 1) + A := by nlinarith [hrelM]
  have hshiftA (i : ℕ) : f (d + i) = centered N ((2 : ℤ) ^ i * B) := by
    simpa [f] using centered_shift N A B d i hN hodd hrelA
  have hshiftB (i : ℕ) : f (d + c + i) = centered N ((2 : ℤ) ^ i * L) := by
    calc
      f (d + c + i) = centered N ((2 : ℤ) ^ (c + i) * B) := by
        simpa [Nat.add_assoc] using hshiftA (c + i)
      _ = centered N ((2 : ℤ) ^ i * L) := centered_shift N B L c i hN hodd hrelB
  have hshiftL (i : ℕ) : f (d + c + b + i) = centered N ((2 : ℤ) ^ i * M) := by
    calc
      f (d + c + b + i) = centered N ((2 : ℤ) ^ (b + i) * L) := by
        simpa [Nat.add_assoc] using hshiftB (b + i)
      _ = centered N ((2 : ℤ) ^ i * M) := centered_shift N L M b i hN hodd hrelL
  have hshiftG (i : ℕ) : f (d + c + b + a + i) = centered N ((2 : ℤ) ^ i * A) := by
    calc
      f (d + c + b + a + i) = centered N ((2 : ℤ) ^ (a + i) * M) := by
        simpa [Nat.add_assoc] using hshiftL (a + i)
      _ = centered N ((2 : ℤ) ^ i * A) := centered_shift N M A a i hN hodd hrelM
  have hu (i : ℕ) (hi : i < d) :
      f i = if i + 1 < d then (2 : ℤ) ^ i * A else -(N - B) / 2 :=
    centered_ladder N A B d i hN hodd (by omega) ⟨hB.1, hB.2.le⟩ hi hrelA
  have hv (i : ℕ) (hi : i < c) :
      f (d + i) = if i + 1 < c then (2 : ℤ) ^ i * B else -(N - L) / 2 := by
    calc
      f (d + i) = centered N ((2 : ℤ) ^ i * B) := hshiftA i
      _ = if i + 1 < c then (2 : ℤ) ^ i * B else -(N - L) / 2 :=
        centered_ladder N B L c i hN hodd (by omega) ⟨hL.1, hL.2.le⟩ hi hrelB
  have hw (i : ℕ) (hi : i < b) :
      f (d + c + i) = if i + 1 < b then (2 : ℤ) ^ i * L else -(N - M) / 2 := by
    calc
      f (d + c + i) = centered N ((2 : ℤ) ^ i * L) := hshiftB i
      _ = if i + 1 < b then (2 : ℤ) ^ i * L else -(N - M) / 2 :=
        centered_ladder N L M b i hN hodd (by omega) ⟨hM.1, hM.2.le⟩ hi hrelL
  have hu4 (i : ℕ) (hi : i < a) :
      f (d + c + b + i) = if i + 1 < a then (2 : ℤ) ^ i * M else -(N - A) / 2 := by
    calc
      f (d + c + b + i) = centered N ((2 : ℤ) ^ i * M) := hshiftL i
      _ = if i + 1 < a then (2 : ℤ) ^ i * M else -(N - A) / 2 :=
        centered_ladder N M A a i hN hodd (by omega) ⟨hA.1, hA.2.le⟩ hi hrelM
  have hgu (i : ℕ) (hi : i < d) :
      g i = if i + 1 < d then (2 : ℤ) ^ i * (2 * A)
        else -((2 * N + 1) - (2 * B - 1)) / 2 :=
    centered_ladder (2 * N + 1) (2 * A) (2 * B - 1) d i hN' hodd' (by omega) ⟨hB'.1, hB'.2.le⟩ hi hrelA'
  have hgv (i : ℕ) (hi : i < c) :
      g (d + i) = if i + 1 < c then (2 : ℤ) ^ i * (2 * B - 1)
        else -((2 * N + 1) - (2 * L - 1 - z)) / 2 := by
    calc
      g (d + i) = centered (2 * N + 1) ((2 : ℤ) ^ i * (2 * B - 1)) := by
        simpa [g] using centered_shift (2 * N + 1) (2 * A) (2 * B - 1) d i hN' hodd' hrelA'
      _ = if i + 1 < c then (2 : ℤ) ^ i * (2 * B - 1)
          else -((2 * N + 1) - (2 * L - 1 - z)) / 2 :=
        centered_ladder (2 * N + 1) (2 * B - 1) (2 * L - 1 - z) c i hN' hodd' (by omega) ⟨hL'.1, hL'.2.le⟩ hi hrelB'
  have hgw (i : ℕ) (hi : i < b) :
      g (d + c + i) = if i + 1 < b then (2 : ℤ) ^ i * (2 * L - 1 - z)
        else -((2 * N + 1) - (2 * M - 1 - y - y * z)) / 2 := by
    calc
      g (d + c + i) = centered (2 * N + 1) ((2 : ℤ) ^ (c + i) * (2 * B - 1)) := by
        simpa [Nat.add_assoc, g] using
          (show g (d + (c + i)) = centered (2 * N + 1) ((2 : ℤ) ^ (c + i) * (2 * B - 1)) by
            simpa [g] using centered_shift (2 * N + 1) (2 * A) (2 * B - 1) d (c + i) hN' hodd' hrelA')
      _ = centered (2 * N + 1) ((2 : ℤ) ^ i * (2 * L - 1 - z)) :=
        centered_shift (2 * N + 1) (2 * B - 1) (2 * L - 1 - z) c i hN' hodd' hrelB'
      _ = if i + 1 < b then (2 : ℤ) ^ i * (2 * L - 1 - z)
          else -((2 * N + 1) - (2 * M - 1 - y - y * z)) / 2 :=
        centered_ladder (2 * N + 1) (2 * L - 1 - z) (2 * M - 1 - y - y * z)
          b i hN' hodd' (by omega) ⟨hM'.1, hM'.2.le⟩ hi hrelL'
  have hgu4 (i : ℕ) (hi : i < a) :
      g (d + c + b + i) = if i + 1 < a then
        (2 : ℤ) ^ i * (2 * M - 1 - y - y * z)
        else -((2 * N + 1) - A) / 2 := by
    calc
      g (d + c + b + i) = centered (2 * N + 1) ((2 : ℤ) ^ (c + b + i) * (2 * B - 1)) := by
        simpa [Nat.add_assoc, g] using
          centered_shift (2 * N + 1) (2 * A) (2 * B - 1) d (c + (b + i)) hN' hodd' hrelA'
      _ = centered (2 * N + 1) ((2 : ℤ) ^ (b + i) * (2 * L - 1 - z)) :=
        (by simpa [Nat.add_assoc] using
          centered_shift (2 * N + 1) (2 * B - 1) (2 * L - 1 - z) c (b + i) hN' hodd' hrelB')
      _ = centered (2 * N + 1) ((2 : ℤ) ^ i * (2 * M - 1 - y - y * z)) := by
        exact centered_shift (2 * N + 1) (2 * L - 1 - z) (2 * M - 1 - y - y * z)
          b i hN' hodd' hrelL'
      _ = if i + 1 < a then (2 : ℤ) ^ i * (2 * M - 1 - y - y * z)
          else -((2 * N + 1) - A) / 2 :=
        centered_ladder (2 * N + 1) (2 * M - 1 - y - y * z) A a i hN' hodd' (by omega)
          ⟨hA.1, by omega⟩ hi hrelM'
  refine ⟨hA, hB, hL, hM, hu, hv, hw, hu4, hgu, hgv, hgw, hgu4, ?_⟩
  have hfull : (2 : ℤ) ^ (d + c + b + a) * (2 * A) =
      (2 : ℤ) ^ (d + c + b + a) * (2 * A) := rfl
  rw [show d + c + b + a = a + b + c + d by omega]
  rw [show (2 : ℤ) ^ (a + b + c + d) * (2 * A) =
    (2 : ℤ) ^ (a + b + c + d + 1) * A by
      rw [pow_succ]; ring]
  have hA0 := hA.1
  have hAN := hA.2
  have hhalf' : (2 * N + 1) / 2 = N := by omega
  have hAbound : -((2 * N + 1) / 2) ≤ A ∧ A ≤ (2 * N + 1) / 2 := by
    rw [hhalf']
    omega
  symm
  apply centered_unique (x := A)
    (y := centered (2 * N + 1) ((2 : ℤ) ^ (a + b + c + d + 1) * A))
    hN' hodd' hAbound (centered_bounds hN' hodd' _)
  rw [centered_mod]
  have hpow : (2 : ℤ) ^ (a + b + c + d) = N + 1 := by
    dsimp [N, modulus]
    ring
  rw [show (2 : ℤ) ^ (a + b + c + d + 1) =
      (2 : ℤ) ^ (a + b + c + d) * 2 by rw [pow_succ]]
  rw [hpow]
  rw [show (N + 1) * 2 * A = (2 * N + 1) * A + A by ring]
  rw [show (2 * N + 1) * A + A = A + (2 * N + 1) * A by ring]
  simp [Int.add_emod, Int.mul_emod]

/-- The phase coordinate is four times the actual phase. -/
private def HalfPhase (D R : ℤ) : Prop :=
  ∃ n : ℤ, 1 ≤ n ∧ (4 * n - 2) * D < R ∧ R < 4 * n * D

/-- An interval longer than one closed half-period gap meets an open upper half.
The interval endpoints are twice their actual coordinates. -/
private theorem interval_half_phase (p a b : ℤ) (hp : 0 < p)
    (ha : 0 ≤ a) (hab : p < b - a) :
    ∃ R : ℤ, 2 * a < R ∧ R < 2 * b ∧ HalfPhase p R := by
  let n := a / (2 * p) + 1
  have hmod := Int.emod_nonneg a (show 2 * p ≠ 0 by omega)
  have hmod' := Int.emod_lt_of_pos a (show 0 < 2 * p by omega)
  have hdiv := Int.emod_add_mul_ediv a (2 * p)
  have hn : 1 ≤ n := by
    dsimp [n]
    have := Int.ediv_nonneg ha (show 0 ≤ 2 * p by omega)
    omega
  have hfloor : 2 * (n - 1) * p ≤ a ∧ a < 2 * n * p := by
    dsimp [n]
    constructor <;> nlinarith
  let l := max a ((2 * n - 1) * p)
  let u := min b (2 * n * p)
  have hlow : l < u := by
    dsimp [l, u]
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    constructor
    · constructor <;> nlinarith [hfloor.2]
    · constructor <;> nlinarith [hfloor.1]
  refine ⟨l + u, ?_, ?_, n, hn, ?_, ?_⟩
  · have := le_max_left a ((2 * n - 1) * p)
    change a ≤ l at this
    omega
  · have := min_le_left b (2 * n * p)
    change u ≤ b at this
    omega
  · have := le_max_right a ((2 * n - 1) * p)
    change (2 * n - 1) * p ≤ l at this
    nlinarith
  · have := min_le_right b (2 * n * p)
    change u ≤ 2 * n * p at this
    nlinarith

private theorem phase_meet (p q r e v E : ℤ)
    (he : 1 ≤ e) (hv : 1 ≤ v)
    (hp : (2 * e - 1) * p < E) (hq : (2 * v - 1) * q < E)
    (hr : r < E) (hP : E ≤ 2 * e * p) (hQ : E ≤ 2 * v * q)
    (hR : E ≤ 2 * r) :
    ∃ R : ℤ, 2 * r < R ∧ R < 4 * r ∧ HalfPhase p R ∧ HalfPhase q R := by
  let l := max ((2 * e - 1) * p) (max ((2 * v - 1) * q) r)
  have hl : l < E := by simp only [l, max_lt_iff]; exact ⟨hp, hq, hr⟩
  have hlp : (2 * e - 1) * p ≤ l := le_max_left _ _
  have hlq : (2 * v - 1) * q ≤ l := le_trans (le_max_left _ _) (le_max_right _ _)
  have hlr : r ≤ l := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨l + E, by omega, by omega, ⟨e, he, ?_, ?_⟩, ⟨v, hv, ?_, ?_⟩⟩ <;>
    nlinarith

/-- A direct clipped-interval proof replaces connected-complement reasoning. -/
private theorem wide_half_phase (p q r : ℤ) (hp : 0 < p) (hpq : p ≤ q)
    (hwide : 2 * p + q < r) :
    ∃ R : ℤ, 2 * r < R ∧ R < 4 * r ∧ HalfPhase p R ∧ HalfPhase q R := by
  have hq : 0 < q := by omega
  have hr : 0 < r := by omega
  by_cases heq : p = q
  · obtain ⟨R, hR, hR', hphase⟩ := interval_half_phase p r (2 * r) hp hr.le (by omega)
    exact ⟨R, hR, by omega, hphase, by simpa [← heq] using hphase⟩
  have hpq' : p < q := by omega
  let n := r / (2 * q) + 1
  have hn : 1 ≤ n := by
    dsimp [n]
    have := Int.ediv_nonneg hr.le (show 0 ≤ 2 * q by omega)
    omega
  have hmod := Int.emod_nonneg r (show 2 * q ≠ 0 by omega)
  have hmod' := Int.emod_lt_of_pos r (show 0 < 2 * q by omega)
  have hdiv := Int.emod_add_mul_ediv r (2 * q)
  have hfloor : 2 * (n - 1) * q ≤ r ∧ r < 2 * n * q := by
    dsimp [n]
    constructor <;> nlinarith
  let a := max r ((2 * n - 1) * q)
  have har : r ≤ a := le_max_left _ _
  have haq : (2 * n - 1) * q ≤ a := le_max_right _ _
  have ha_bound : a ≤ r + q := by
    dsimp [a]
    rw [max_le_iff]
    constructor <;> nlinarith [hfloor.1]
  by_cases htail : p < 2 * n * q - a
  · let b := min (2 * r) (2 * n * q)
    have hab : p < b - a := by
      dsimp [b]
      rcases le_total (2 * r) (2 * n * q) with h | h
      · rw [min_eq_left h]; omega
      · rw [min_eq_right h]; exact htail
    obtain ⟨R, hR, hR', hphase⟩ := interval_half_phase p a b hp (by omega) hab
    have hb : b ≤ 2 * r := min_le_left _ _
    have hb' : b ≤ 2 * n * q := min_le_right _ _
    exact ⟨R, by omega, by omega, hphase, ⟨n, hn, by nlinarith, by nlinarith⟩⟩
  · have hend : 2 * n * q ≤ r + p := by
      by_cases h : r ≤ (2 * n - 1) * q
      · have ha' : a = (2 * n - 1) * q := max_eq_right h
        rw [ha'] at htail
        nlinarith
      · have ha' : a = r := max_eq_left (by omega)
        rw [ha'] at htail
        omega
    let a' := (2 * n + 1) * q
    let b' := min (2 * r) (2 * (n + 1) * q)
    have ha' : r ≤ a' := by dsimp [a']; nlinarith [hfloor.2]
    have ha'_bound : a' ≤ r + p + q := by dsimp [a']; nlinarith
    have hab : p < b' - a' := by
      dsimp [b', a']
      rcases le_total (2 * r) (2 * (n + 1) * q) with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    obtain ⟨R, hR, hR', hphase⟩ := interval_half_phase p a' b' hp (by omega) hab
    have hb : b' ≤ 2 * r := min_le_left _ _
    have hb' : b' ≤ 2 * (n + 1) * q := min_le_right _ _
    exact ⟨R, by omega, by omega, hphase, ⟨n + 1, by omega, by dsimp [a'] at hR; nlinarith,
      by nlinarith⟩⟩

private theorem sorted_half_phase (p q r : ℤ) (i j k : ℕ)
    (hij : i ≤ j) (hjk : j ≤ k) (hpq : p ≤ q) (hqr : q ≤ r)
    (hp : (2 : ℤ) ^ i ≤ p) (hp' : 3 * p < 4 * (2 : ℤ) ^ i)
    (hq : (2 : ℤ) ^ j ≤ q) (hq' : 3 * q < 4 * (2 : ℤ) ^ j)
    (hr : (2 : ℤ) ^ k ≤ r) (hr' : 3 * r < 4 * (2 : ℤ) ^ k) :
    ∃ R : ℤ, 2 * r < R ∧ R < 4 * r ∧ HalfPhase p R ∧ HalfPhase q R := by
  have hI : 0 < (2 : ℤ) ^ i := by positivity
  have hJ : 0 < (2 : ℤ) ^ j := by positivity
  have hp0 : 0 < p := by omega
  by_cases hjk' : j = k
  · subst k
    by_cases hij' : i = j
    · subst j
      have hlt : r < 2 * p := by omega
      exact phase_meet p q r 1 1 (2 * p) (by norm_num) (by norm_num)
        (by nlinarith) (by nlinarith) hlt (by nlinarith) (by nlinarith) (by nlinarith)
    · have hpow : 2 * (2 : ℤ) ^ i ≤ (2 : ℤ) ^ j := by
        have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show i + 1 ≤ j by omega)
        simpa [pow_succ, mul_comm] using this
      obtain ⟨R, hR, hR', hphase⟩ := interval_half_phase p r (2 * q) hp0 (by omega) (by omega)
      exact ⟨R, hR, by omega, hphase, ⟨1, by norm_num, by nlinarith, by nlinarith⟩⟩
  have hjk1 : j + 1 ≤ k := by omega
  by_cases hstep : k = j + 1
  · have hK : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ j := by rw [hstep, pow_succ]; ring
    by_cases hij' : i = j
    · subst j
      exact phase_meet p q r 2 2 (min (2 * r) (4 * p)) (by norm_num) (by norm_num)
        (by rw [lt_min_iff]; constructor <;> nlinarith)
        (by rw [lt_min_iff]; constructor <;> nlinarith)
        (by rw [lt_min_iff]; constructor <;> nlinarith)
        (min_le_right _ _) (le_trans (min_le_right _ _) (by omega)) (min_le_left _ _)
    · by_cases hstep' : j = i + 1
      · have hJ' : (2 : ℤ) ^ j = 2 * (2 : ℤ) ^ i := by rw [hstep', pow_succ]; ring
        by_cases hqp : q < 2 * p
        · exact phase_meet p q r 3 2 (6 * p) (by norm_num) (by norm_num)
            (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
            (by nlinarith) (by nlinarith)
        · by_cases hrp : r < 4 * p
          · exact phase_meet p q r 2 1 (4 * p) (by norm_num) (by norm_num)
              (by nlinarith) (by nlinarith) hrp (by nlinarith)
              (by nlinarith) (by nlinarith)
          · exact phase_meet p q r 4 2 (8 * p) (by norm_num) (by norm_num)
              (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
              (by nlinarith) (by nlinarith)
      · have hpow : 4 * (2 : ℤ) ^ i ≤ (2 : ℤ) ^ j := by
          have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show i + 2 ≤ j by omega)
          simpa [pow_add, mul_comm] using this
        exact wide_half_phase p q r hp0 hpq (by nlinarith)
  · have hpow : 4 * (2 : ℤ) ^ j ≤ (2 : ℤ) ^ k := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show j + 2 ≤ k by omega)
      simpa [pow_add, mul_comm] using this
    exact wide_half_phase p q r hp0 hpq (by nlinarith)

private theorem dyadic_index_mono (p q : ℤ) (i j : ℕ) (hpq : p ≤ q)
    (hp : (2 : ℤ) ^ i ≤ p) (hq' : 3 * q < 4 * (2 : ℤ) ^ j) : i ≤ j := by
  by_contra h
  have hpow : 2 * (2 : ℤ) ^ j ≤ (2 : ℤ) ^ i := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show j + 1 ≤ i by omega)
    simpa [pow_succ, mul_comm] using this
  have : 0 < (2 : ℤ) ^ j := by positivity
  nlinarith

private theorem simultaneous_half_phase (p q r : ℤ) (i j k : ℕ)
    (hp : (2 : ℤ) ^ i ≤ p) (hp' : 3 * p < 4 * (2 : ℤ) ^ i)
    (hq : (2 : ℤ) ^ j ≤ q) (hq' : 3 * q < 4 * (2 : ℤ) ^ j)
    (hr : (2 : ℤ) ^ k ≤ r) (hr' : 3 * r < 4 * (2 : ℤ) ^ k) :
    ∃ R : ℤ, 0 < R ∧ R < 4 * max p (max q r) ∧
      HalfPhase p R ∧ HalfPhase q R ∧ HalfPhase r R := by
  have hsorted (p q r : ℤ) (i j k : ℕ) (hpq : p ≤ q) (hqr : q ≤ r)
      (hp : (2 : ℤ) ^ i ≤ p) (hp' : 3 * p < 4 * (2 : ℤ) ^ i)
      (hq : (2 : ℤ) ^ j ≤ q) (hq' : 3 * q < 4 * (2 : ℤ) ^ j)
      (hr : (2 : ℤ) ^ k ≤ r) (hr' : 3 * r < 4 * (2 : ℤ) ^ k) :
      ∃ R : ℤ, 0 < R ∧ R < 4 * r ∧ HalfPhase p R ∧ HalfPhase q R ∧ HalfPhase r R := by
    obtain ⟨R, hR, hR', hP, hQ⟩ := sorted_half_phase p q r i j k
      (dyadic_index_mono p q i j hpq hp hq') (dyadic_index_mono q r j k hqr hq hr')
      hpq hqr hp hp' hq hq' hr hr'
    have : 0 < r := lt_of_lt_of_le (by positivity : 0 < (2 : ℤ) ^ k) hr
    exact ⟨R, by omega, hR', hP, hQ, ⟨1, by norm_num, by nlinarith, by nlinarith⟩⟩
  rcases le_total p q with hpq | hqp
  · rcases le_total q r with hqr | hrq
    · obtain ⟨R, hR, hR', hP, hQ, hT⟩ := hsorted p q r i j k hpq hqr hp hp' hq hq' hr hr'
      exact ⟨R, hR, by simpa [max_eq_right hpq, max_eq_right hqr, max_eq_right (le_trans hpq hqr)] using hR', hP, hQ, hT⟩
    · rcases le_total p r with hpr | hrp
      · obtain ⟨R, hR, hR', hP, hT, hQ⟩ := hsorted p r q i k j hpr hrq hp hp' hr hr' hq hq'
        exact ⟨R, hR, by simpa [max_eq_left hrq, max_eq_right hpq] using hR', hP, hQ, hT⟩
      · obtain ⟨R, hR, hR', hT, hP, hQ⟩ := hsorted r p q k i j hrp hpq hr hr' hp hp' hq hq'
        exact ⟨R, hR, by simpa [max_eq_left hrq, max_eq_right hpq] using hR', hP, hQ, hT⟩
  · rcases le_total p r with hpr | hrp
    · obtain ⟨R, hR, hR', hQ, hP, hT⟩ := hsorted q p r j i k hqp hpr hq hq' hp hp' hr hr'
      exact ⟨R, hR, by simpa [max_eq_right (le_trans hqp hpr), max_eq_right hpr] using hR', hP, hQ, hT⟩
    · rcases le_total q r with hqr | hrq
      · obtain ⟨R, hR, hR', hQ, hT, hP⟩ := hsorted q r p j k i hqr hrp hq hq' hr hr' hp hp'
        exact ⟨R, hR, by simpa [max_eq_right hqr, max_eq_left hrp] using hR', hP, hQ, hT⟩
      · obtain ⟨R, hR, hR', hT, hQ, hP⟩ := hsorted r q p k j i hrq hqp hr hr' hq hq' hp hp'
        exact ⟨R, hR, by simpa [max_eq_left hrq, max_eq_left hqp] using hR', hP, hQ, hT⟩

private theorem four_phase_selector (a b c : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    let x : ℤ := 2 ^ a
    let y : ℤ := 2 ^ b
    let z : ℤ := 2 ^ c
    let P := x * y * z
    let DB := 1 + x + x * y
    let DL := z * (1 + x)
    let DM := y * z
    ∃ R nB nL nM : ℤ, 0 < R ∧ 3 * R < 4 * P ∧
      (1 ≤ nB ∧ 2 * nB < z ∧ 1 ≤ 4 * nB * DB - R ∧
        1 ≤ R - (4 * nB - 2) * DB) ∧
      (1 ≤ nL ∧ 2 * nL < y ∧ 1 ≤ 4 * nL * DL - R ∧
        1 ≤ R - (4 * nL - 2) * DL) ∧
      (1 ≤ nM ∧ 2 * nM < x ∧ 1 ≤ 4 * nM * DM - R ∧
        1 ≤ R - (4 * nM - 2) * DM) := by
  dsimp only
  let x : ℤ := 2 ^ a
  let y : ℤ := 2 ^ b
  let z : ℤ := 2 ^ c
  let P := x * y * z
  let DB := 1 + x + x * y
  let DL := z * (1 + x)
  let DM := y * z
  have hx : 4 ≤ x := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ha
    simpa [x] using this
  have hy : 4 ≤ y := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hb
    simpa [y] using this
  have hz : 4 ≤ z := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hc
    simpa [z] using this
  have hxy : 0 < x * y := mul_pos (by omega) (by omega)
  have hxz : 0 < x * z := mul_pos (by omega) (by omega)
  have hyz : 0 < y * z := mul_pos (by omega) (by omega)
  have hDB : x * y ≤ DB ∧ 3 * DB < 4 * (x * y) := by dsimp [DB]; constructor <;> nlinarith only [hx, hy]
  have hDL : x * z ≤ DL ∧ 3 * DL < 4 * (x * z) := by dsimp [DL]; constructor <;> nlinarith only [hx, hz]
  have hDM : y * z ≤ DM ∧ 3 * DM < 4 * (y * z) := by dsimp [DM]; constructor <;> nlinarith only [hyz]
  obtain ⟨R, hR0, hR, ⟨nB, hnB, hB0, hB1⟩,
      ⟨nL, hnL, hL0, hL1⟩, ⟨nM, hnM, hM0, hM1⟩⟩ :=
    simultaneous_half_phase DB DL DM (a + b) (a + c) (b + c)
      (by simpa [pow_add, x, y] using hDB.1) (by simpa [pow_add, x, y] using hDB.2)
      (by simpa [pow_add, x, z] using hDL.1) (by simpa [pow_add, x, z] using hDL.2)
      (by simpa [pow_add, y, z] using hDM.1) (by simpa [pow_add, y, z] using hDM.2)
  let r := max DB (max DL DM)
  have hBr : DB ≤ r := le_max_left _ _
  have hLr : DL ≤ r := le_trans (le_max_left _ _) (le_max_right _ _)
  have hMr : DM ≤ r := le_trans (le_max_right _ _) (le_max_right _ _)
  have hsmall : 3 * r < P := by
    have hB : 3 * DB < P := by dsimp [P]; nlinarith only [hDB.2, mul_le_mul_of_nonneg_left hz hxy.le]
    have hL : 3 * DL < P := by
      have := mul_le_mul_of_nonneg_left hy hxz.le
      dsimp [P]; nlinarith only [hDL.2, this]
    have hM : 3 * DM < P := by dsimp [P]; nlinarith only [hDM.2, mul_le_mul_of_nonneg_left hx hyz.le]
    dsimp [r]
    rcases le_total DL DM with h | h
    · rw [max_eq_right h]
      rcases le_total DB DM with h' | h'
      · rw [max_eq_right h']; exact hM
      · rw [max_eq_left h']; exact hB
    · rw [max_eq_left h]
      rcases le_total DB DL with h' | h'
      · rw [max_eq_right h']; exact hL
      · rw [max_eq_left h']; exact hB
  have hcapB : 2 * nB < z := by
    have hnp : 2 * nB * DB < P := by
      change R < 4 * r at hR
      nlinarith only [hB0, hR, hBr, hsmall]
    have hrel : z * DB = P + DL := by dsimp [DB, DL, P]; ring
    have hpos : 0 < DB := by omega
    have hposL : 0 < DL := by omega
    by_contra h
    have := mul_le_mul_of_nonneg_right (show z ≤ 2 * nB by omega) hpos.le
    nlinarith only [hnp, hrel, hposL, this]
  have hcapL : 2 * nL < y := by
    have hnp : 2 * nL * DL < P := by
      change R < 4 * r at hR
      nlinarith only [hL0, hR, hLr, hsmall]
    have hrel : y * DL = P + DM := by dsimp [DL, DM, P]; ring
    have hpos : 0 < DL := by omega
    have hposM : 0 < DM := by omega
    by_contra h
    have := mul_le_mul_of_nonneg_right (show y ≤ 2 * nL by omega) hpos.le
    nlinarith only [hnp, hrel, hposM, this]
  have hcapM : 2 * nM < x := by
    have hnp : 2 * nM * DM < P := by
      change R < 4 * r at hR
      nlinarith only [hM0, hR, hMr, hsmall]
    have hrel : x * DM = P := by dsimp [DM, P]; ring
    have hpos : 0 < DM := by omega
    by_contra h
    have := mul_le_mul_of_nonneg_right (show x ≤ 2 * nM by omega) hpos.le
    nlinarith only [hnp, hrel, this]
  refine ⟨R, nB, nL, nM, hR0, ?_, ⟨hnB, hcapB, by nlinarith only [hB1], by nlinarith only [hB0]⟩,
    ⟨hnL, hcapL, by nlinarith only [hL1], by nlinarith only [hL0]⟩, ⟨hnM, hcapM, by nlinarith only [hM1], by nlinarith only [hM0]⟩⟩
  change R < 4 * r at hR
  nlinarith only [hR, hsmall]

/-- Ceiling in the quarter-grid coordinate, with its exact rounding loss. -/
private theorem quarter_ceiling (A t R : ℤ) (hA : 0 < A) (ht : 0 < t)
    (hR : 0 < R) (hRA : R < 2 * A) (hte : t % 2 = 0) :
    ∃ q : ℤ, 1 ≤ q ∧ 2 * q ≤ t ∧ 0 ≤ 4 * A * q - t * R ∧
      4 * A * q - t * R < 4 * A := by
  let q := (t * R - 1) / (4 * A) + 1
  have hprod : 0 < t * R := mul_pos ht hR
  have hmod := Int.emod_nonneg (t * R - 1) (show 4 * A ≠ 0 by omega)
  have hmod' := Int.emod_lt_of_pos (t * R - 1) (show 0 < 4 * A by omega)
  have hdiv := Int.emod_add_mul_ediv (t * R - 1) (4 * A)
  have hq : 1 ≤ q := by
    dsimp [q]
    have := Int.ediv_nonneg (show 0 ≤ t * R - 1 by omega) (show 0 ≤ 4 * A by omega)
    omega
  have heps : 0 ≤ 4 * A * q - t * R ∧ 4 * A * q - t * R < 4 * A := by
    dsimp [q]; constructor <;> nlinarith
  have hhalf : 2 * (t / 2) = t := by omega
  have hqt : q ≤ t / 2 := by
    by_contra h
    have hq' : t / 2 + 1 ≤ q := by omega
    have := mul_le_mul_of_nonneg_left hq' (show 0 ≤ 4 * A by omega)
    have hmul := mul_lt_mul_of_pos_left hRA ht
    nlinarith
  exact ⟨q, hq, by omega, heps⟩

/-- A quarter-grid margin absorbs the entire ceiling loss at t >= 8P. -/
private theorem rounded_phase_seam (P A D rho t R n q : ℤ)
    (hP : 0 < P) (hA : 0 < A) (hAP : A < 2 * P)
    (ht : 8 * P ≤ t) (hrho : 1 ≤ rho) (hnrho : n * rho < A)
    (hlo : 1 ≤ 4 * n * D - R) (hhi : 1 ≤ R - (4 * n - 2) * D)
    (heps : 0 ≤ 4 * A * q - t * R) (heps' : 4 * A * q - t * R < 4 * A) :
    let Y := t * D + rho
    let tau := n * Y - A * q
    n * rho < tau ∧ 2 * tau < Y - 1 := by
  dsimp only
  have ht0 : 0 < t := by omega
  have hmul := mul_le_mul_of_nonneg_left hlo ht0.le
  have hmul' := mul_le_mul_of_nonneg_left hhi ht0.le
  constructor <;> nlinarith

private theorem four_mask_parameters (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : a + b + c + 3 ≤ d) :
    let x : ℤ := 2 ^ a
    let y : ℤ := 2 ^ b
    let z : ℤ := 2 ^ c
    let t : ℤ := 2 ^ d
    let P := x * y * z
    let A := P + (1 + x + x * y)
    let B := t * (1 + x + x * y) + 1
    let L := t * (z * (1 + x)) + 1 + z
    let M := t * (y * z) + 1 + y + y * z
    ∃ nB nL nM q : ℤ,
      (1 ≤ q ∧ 2 * q ≤ t) ∧
      (1 ≤ nB ∧ 2 * nB < z) ∧ (1 ≤ nL ∧ 2 * nL < y) ∧ (1 ≤ nM ∧ 2 * nM < x) ∧
      (nB < nB * B - A * q ∧ 2 * (nB * B - A * q) < B - 1) ∧
      (nL * (1 + z) < nL * L - A * q ∧ 2 * (nL * L - A * q) < L - 1) ∧
      (nM * (1 + y + y * z) < nM * M - A * q ∧ 2 * (nM * M - A * q) < M - 1) := by
  dsimp only
  let x : ℤ := 2 ^ a
  let y : ℤ := 2 ^ b
  let z : ℤ := 2 ^ c
  let t : ℤ := 2 ^ d
  let P := x * y * z
  let DB := 1 + x + x * y
  let DL := z * (1 + x)
  let DM := y * z
  let A := P + DB
  have hx : 4 ≤ x := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ha
    simpa [x] using this
  have hy : 4 ≤ y := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hb
    simpa [y] using this
  have hz : 4 ≤ z := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hc
    simpa [z] using this
  have hxy : 0 < x * y := mul_pos (by omega) (by omega)
  have hyz : 0 < y * z := mul_pos (by omega) (by omega)
  have hP : 0 < P := mul_pos hxy (by omega)
  have hDB : 0 < DB := by dsimp [DB]; nlinarith
  have hDBP : DB < P := by
    have hxy' : 4 * x ≤ x * y := by nlinarith
    have hP' : 4 * (x * y) ≤ P := by dsimp [P]; nlinarith
    dsimp [DB]; nlinarith
  have hA : 0 < A := by dsimp [A]; omega
  have hAP : A < 2 * P := by dsimp [A]; omega
  have ht : 8 * P ≤ t := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hd
    have he : (2 : ℤ) ^ (a + b + c + 3) = 8 * P := by
      dsimp [P, x, y, z]; ring
    simpa only [he] using this
  have ht0 : 0 < t := by omega
  have hte : t % 2 = 0 := by
    have he : t = 2 * (2 : ℤ) ^ (d - 1) := by
      dsimp [t]
      calc
        (2 : ℤ) ^ d = 2 ^ ((d - 1) + 1) := by congr 1 <;> omega
        _ = 2 * (2 : ℤ) ^ (d - 1) := by rw [pow_succ]; ring
    rw [he]; omega
  obtain ⟨R, nB, nL, nM, hR, hRP, hB, hL, hM⟩ := four_phase_selector a b c ha hb hc
  change 3 * R < 4 * P at hRP
  change 1 ≤ nB ∧ 2 * nB < z ∧ 1 ≤ 4 * nB * DB - R ∧
    1 ≤ R - (4 * nB - 2) * DB at hB
  change 1 ≤ nL ∧ 2 * nL < y ∧ 1 ≤ 4 * nL * DL - R ∧
    1 ≤ R - (4 * nL - 2) * DL at hL
  change 1 ≤ nM ∧ 2 * nM < x ∧ 1 ≤ 4 * nM * DM - R ∧
    1 ≤ R - (4 * nM - 2) * DM at hM
  obtain ⟨q, hq, hqt, heps, heps'⟩ := quarter_ceiling A t R hA ht0 hR
    (by dsimp [A]; omega) hte
  have hchargeB : nB * 1 < A := by
    have hxy' : 1 ≤ x * y := by omega
    have hzP : z ≤ P := by dsimp [P]; nlinarith
    dsimp [A]; nlinarith only [hB.1, hB.2.1, hzP, hDB]
  have hchargeL : nL * (1 + z) < A := by
    have hmul := mul_lt_mul_of_pos_right hL.2.1 (show 0 < 1 + z by omega)
    have hP' : 4 * (y * z) ≤ P := by dsimp [P]; nlinarith
    have hy' : y ≤ y * z := by nlinarith
    dsimp [A]; nlinarith only [hmul, hP', hy', hDB, hP]
  have hchargeM : nM * (1 + y + y * z) < A := by
    have hmul := mul_lt_mul_of_pos_right hM.2.1 (show 0 < 1 + y + y * z by nlinarith only [hy, hyz])
    have he : x * (1 + y + y * z) = A - 1 := by dsimp [A, P, DB]; ring
    have hpos : 0 < nM * (1 + y + y * z) := mul_pos (by omega) (by nlinarith only [hy, hyz])
    nlinarith only [hmul, he, hpos]
  have hseamB := rounded_phase_seam P A DB 1 t R nB q hP hA hAP ht
    (by norm_num) hchargeB hB.2.2.1 hB.2.2.2 heps heps'
  have hseamL := rounded_phase_seam P A DL (1 + z) t R nL q hP hA hAP ht
    (by omega) hchargeL hL.2.2.1 hL.2.2.2 heps heps'
  have hseamM := rounded_phase_seam P A DM (1 + y + y * z) t R nM q hP hA hAP ht
    (by nlinarith only [hy, hyz]) hchargeM hM.2.2.1 hM.2.2.2 heps heps'
  refine ⟨nB, nL, nM, q, ⟨hq, hqt⟩, ⟨hB.1, hB.2.1⟩, ⟨hL.1, hL.2.1⟩,
    ⟨hM.1, hM.2.1⟩, ?_, ?_, ?_⟩
  · simpa [A, P, DB] using hseamB
  · simpa [A, P, DB, DL, mul_add, add_assoc] using hseamL
  · simpa [A, P, DB, DM, add_assoc] using hseamM

private noncomputable def chainMask (len off m : ℕ) : List ℕ :=
  if h : m < 2 ^ len then (mask_labels len off m h).toList else []

private theorem chainMask_partition (len off m n : ℕ) (hs : m + n = 2 ^ len - 1) :
    (chainMask len off m ++ chainMask len off n).Perm (List.range' off len) := by
  classical
  have hp : 0 < 2 ^ len := by positivity
  have hm : m < 2 ^ len := by omega
  have hn : n < 2 ^ len := by omega
  have hc := mask_complement len m n hs
  have hd := mask_labels_disjoint (len := len) (off := off) (hx := hm) (hy := hn) hc.1
  simp only [chainMask, dite_eq_left hm, dite_eq_left hn]
  apply (List.perm_ext_iff_of_nodup ?_ (List.nodup_range' (s := off) (n := len))).mpr
  · intro i
    simp only [List.mem_append, Finset.mem_toList, mask_labels_mem, List.mem_range'_1]
    constructor
    · rintro (⟨e, he, _, hei⟩ | ⟨e, he, _, hei⟩) <;> omega
    · intro hi
      have he : i - off < len := by omega
      have hmem : i - off ∈ m.bitIndices.toFinset ∪ n.bitIndices.toFinset := by
        rw [hc.2]; exact Finset.mem_range.mpr he
      rcases Finset.mem_union.mp hmem with h | h
      · left
        exact ⟨i - off, he, Nat.mem_bitIndices.mp (List.mem_toFinset.mp h), by omega⟩
      · right
        exact ⟨i - off, he, Nat.mem_bitIndices.mp (List.mem_toFinset.mp h), by omega⟩
  · apply List.nodup_append.mpr
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
    intro i hi j hj hij
    subst j
    exact Finset.disjoint_left.mp hd (Finset.mem_toList.mp hi) (Finset.mem_toList.mp hj)

private theorem chainMask_sum (len off m : ℕ) (hm : m < 2 ^ len)
    (f : ℕ → ℤ) (A : ℤ) (hf : ∀ e < len, f (off + e) = (2 : ℤ) ^ e * A) :
    ((chainMask len off m).map f).sum = (m : ℤ) * A := by
  classical
  simp only [chainMask, dite_eq_left hm]
  change (((mask_labels len off m hm).toList : Multiset ℕ).map f).sum = _
  rw [Finset.coe_toList]
  exact mask_labels_sum len off m hm f A hf

private theorem four_mask_inventory (a b c d q nB nL nM : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hq : 1 ≤ q ∧ q ≤ 2 ^ (d - 1))
    (hB : 1 ≤ nB ∧ nB ≤ 2 ^ (c - 1))
    (hL : 1 ≤ nL ∧ nL ≤ 2 ^ (b - 1))
    (hM : 1 ≤ nM ∧ nM ≤ 2 ^ (a - 1)) :
    let U0 := chainMask (d - 1) 0 (2 ^ (d - 1) - q)
    let U1 := chainMask (d - 1) 0 (q - 1)
    let V0 := chainMask (c - 1) d (nB - 1)
    let V1 := chainMask (c - 1) d (2 ^ (c - 1) - nB)
    let W0 := chainMask (b - 1) (d + c) (nL - 1)
    let W1 := chainMask (b - 1) (d + c) (2 ^ (b - 1) - nL)
    let X0 := chainMask (a - 1) (d + c + b) (nM - 1)
    let X1 := chainMask (a - 1) (d + c + b) (2 ^ (a - 1) - nM)
    (U0 ++ V0 ++ [d - 1] ++ V1 ++ W0 ++ [d + c - 1] ++
      W1 ++ X0 ++ [d + c + b - 1] ++ U1 ++ X1 ++ [d + c + b + a - 1]).Perm
      (List.range (a + b + c + d)) := by
  dsimp only
  let U0 := chainMask (d - 1) 0 (2 ^ (d - 1) - q)
  let U1 := chainMask (d - 1) 0 (q - 1)
  let V0 := chainMask (c - 1) d (nB - 1)
  let V1 := chainMask (c - 1) d (2 ^ (c - 1) - nB)
  let W0 := chainMask (b - 1) (d + c) (nL - 1)
  let W1 := chainMask (b - 1) (d + c) (2 ^ (b - 1) - nL)
  let X0 := chainMask (a - 1) (d + c + b) (nM - 1)
  let X1 := chainMask (a - 1) (d + c + b) (2 ^ (a - 1) - nM)
  have hU := chainMask_partition (d - 1) 0 (2 ^ (d - 1) - q) (q - 1) (by omega)
  have hV := chainMask_partition (c - 1) d (nB - 1) (2 ^ (c - 1) - nB) (by omega)
  have hW := chainMask_partition (b - 1) (d + c) (nL - 1) (2 ^ (b - 1) - nL) (by omega)
  have hX := chainMask_partition (a - 1) (d + c + b) (nM - 1) (2 ^ (a - 1) - nM) (by omega)
  have hblock (off len : ℕ) (hlen : 1 ≤ len) (A B : List ℕ)
      (h : (A ++ B).Perm (List.range' off (len - 1))) :
      (A ++ B ++ [off + len - 1]).Perm (List.range' off len) := by
    have he : List.range' off (len - 1) ++ [off + len - 1] = List.range' off len := by
      simpa [show len - 1 + 1 = len by omega, show off + (len - 1) = off + len - 1 by omega]
        using (List.range'_1_concat (s := off) (n := len - 1)).symm
    simpa only [List.append_assoc, he] using h.append (List.Perm.refl [off + len - 1])
  have hu : (U0 ++ U1 ++ [d - 1]).Perm (List.range' 0 d) := by
    simpa only [Nat.zero_add] using hblock 0 d (by omega) U0 U1 hU
  have hv := hblock d c (by omega) V0 V1 hV
  have hw := hblock (d + c) b (by omega) W0 W1 hW
  have hx := hblock (d + c + b) a (by omega) X0 X1 hX
  have hreorder :
      (U0 ++ V0 ++ [d - 1] ++ V1 ++ W0 ++ [d + c - 1] ++
        W1 ++ X0 ++ [d + c + b - 1] ++ U1 ++ X1 ++ [d + c + b + a - 1]).Perm
      ((U0 ++ U1 ++ [d - 1]) ++ (V0 ++ V1 ++ [d + c - 1]) ++
        (W0 ++ W1 ++ [d + c + b - 1]) ++ (X0 ++ X1 ++ [d + c + b + a - 1])) := by
    apply Multiset.coe_eq_coe.mp
    simp only [← Multiset.coe_add]
    ac_rfl
  have hrange : List.range' 0 d ++ List.range' d c ++ List.range' (d + c) b ++
      List.range' (d + c + b) a = List.range (a + b + c + d) := by
    have hdc : List.range' 0 d ++ List.range' d c = List.range' 0 (d + c) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s := 0) (m := d) (n := c))
    have hdcb : List.range' 0 (d + c) ++ List.range' (d + c) b =
        List.range' 0 (d + c + b) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s := 0) (m := d + c) (n := b))
    have hdcba : List.range' 0 (d + c + b) ++ List.range' (d + c + b) a =
        List.range' 0 (d + c + b + a) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s := 0) (m := d + c + b) (n := a))
    rw [hdc, hdcb, hdcba]
    simp [← List.range_eq_range', show d + c + b + a = a + b + c + d by omega]
  exact hreorder.trans (by simpa only [← List.append_assoc, hrange] using hu.append (hv.append (hw.append hx)))

private noncomputable def maskWord (a b c d q nB nL nM : ℕ) : List ℕ :=
  chainMask (d - 1) 0 (2 ^ (d - 1) - q) ++
  chainMask (c - 1) d (nB - 1) ++ [d - 1] ++
  chainMask (c - 1) d (2 ^ (c - 1) - nB) ++
  chainMask (b - 1) (d + c) (nL - 1) ++ [d + c - 1] ++
  chainMask (b - 1) (d + c) (2 ^ (b - 1) - nL) ++
  chainMask (a - 1) (d + c + b) (nM - 1) ++ [d + c + b - 1] ++
  chainMask (d - 1) 0 (q - 1) ++
  chainMask (a - 1) (d + c + b) (2 ^ (a - 1) - nM) ++ [d + c + b + a - 1]

/-- Simultaneous phases produce actual complementary physical masks and strict seams. -/
private theorem eventual_mask_certificate (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : a + b + c + 3 ≤ d) :
    let x : ℤ := 2 ^ a
    let y : ℤ := 2 ^ b
    let z : ℤ := 2 ^ c
    let t : ℤ := 2 ^ d
    let A := x * y * z + (1 + x + x * y)
    let B := t * (1 + x + x * y) + 1
    let L := t * (z * (1 + x)) + 1 + z
    let M := t * (y * z) + 1 + y + y * z
    ∃ q nB nL nM : ℕ,
      (1 ≤ q ∧ q ≤ 2 ^ (d - 1)) ∧
      (1 ≤ nB ∧ nB ≤ 2 ^ (c - 1)) ∧
      (1 ≤ nL ∧ nL ≤ 2 ^ (b - 1)) ∧
      (1 ≤ nM ∧ nM ≤ 2 ^ (a - 1)) ∧
      (maskWord a b c d q nB nL nM).Perm (List.range (a + b + c + d)) ∧
      ((nB : ℤ) < nB * B - A * q ∧ 2 * (nB * B - A * q) < B - 1) ∧
      ((nL : ℤ) * (1 + z) < nL * L - A * q ∧ 2 * (nL * L - A * q) < L - 1) ∧
      ((nM : ℤ) * (1 + y + y * z) < nM * M - A * q ∧
        2 * (nM * M - A * q) < M - 1) := by
  dsimp only
  obtain ⟨nB, nL, nM, q, hq, hB, hL, hM, hsB, hsL, hsM⟩ :=
    four_mask_parameters a b c d ha hb hc hd
  have half_pow (e : ℕ) (he : 1 ≤ e) : (2 : ℤ) ^ e = 2 * (2 : ℤ) ^ (e - 1) := by
    calc
      (2 : ℤ) ^ e = 2 ^ ((e - 1) + 1) := by congr 1 <;> omega
      _ = 2 * (2 : ℤ) ^ (e - 1) := by rw [pow_succ]; ring
  have hqcast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
  have hBcast : (nB.toNat : ℤ) = nB := Int.toNat_of_nonneg (by omega)
  have hLcast : (nL.toNat : ℤ) = nL := Int.toNat_of_nonneg (by omega)
  have hMcast : (nM.toNat : ℤ) = nM := Int.toNat_of_nonneg (by omega)
  have hqn : 1 ≤ q.toNat ∧ q.toNat ≤ 2 ^ (d - 1) := by
    have hp := half_pow d (by omega)
    constructor
    · exact_mod_cast (show (1 : ℤ) ≤ (q.toNat : ℤ) by omega)
    · exact_mod_cast (show (q.toNat : ℤ) ≤ (2 : ℤ) ^ (d - 1) by omega)
  have hBn : 1 ≤ nB.toNat ∧ nB.toNat ≤ 2 ^ (c - 1) := by
    have hp := half_pow c (by omega)
    constructor
    · exact_mod_cast (show (1 : ℤ) ≤ (nB.toNat : ℤ) by omega)
    · exact_mod_cast (show (nB.toNat : ℤ) ≤ (2 : ℤ) ^ (c - 1) by omega)
  have hLn : 1 ≤ nL.toNat ∧ nL.toNat ≤ 2 ^ (b - 1) := by
    have hp := half_pow b (by omega)
    constructor
    · exact_mod_cast (show (1 : ℤ) ≤ (nL.toNat : ℤ) by omega)
    · exact_mod_cast (show (nL.toNat : ℤ) ≤ (2 : ℤ) ^ (b - 1) by omega)
  have hMn : 1 ≤ nM.toNat ∧ nM.toNat ≤ 2 ^ (a - 1) := by
    have hp := half_pow a (by omega)
    constructor
    · exact_mod_cast (show (1 : ℤ) ≤ (nM.toNat : ℤ) by omega)
    · exact_mod_cast (show (nM.toNat : ℤ) ≤ (2 : ℤ) ^ (a - 1) by omega)
  refine ⟨q.toNat, nB.toNat, nL.toNat, nM.toNat, hqn, hBn, hLn, hMn, ?_, ?_, ?_, ?_⟩
  · exact four_mask_inventory a b c d q.toNat nB.toNat nL.toNat nM.toNat
      ha hb hc (by omega) hqn hBn hLn hMn
  · simpa only [hqcast, hBcast] using hsB
  · simpa only [hqcast, hLcast] using hsL
  · simpa only [hqcast, hMcast] using hsM

end D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventual
