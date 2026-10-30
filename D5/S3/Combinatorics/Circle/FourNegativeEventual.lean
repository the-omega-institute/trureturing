/- GID: D5/S3/Combinatorics/Circle/FourNegativeEventual
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegativeEventual
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Eventual physical four-chain joint lift with a literal ear. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Circle.ThreeBitSource
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegativeEventual

open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators

open private ThreeBitSource.centered_ladder ThreeBitSource.mask_labels
  ThreeBitSource.mask_labels_bound ThreeBitSource.mask_labels_disjoint
  ThreeBitSource.mask_labels_sum ThreeBitSource.labelled_permutation
  from D5.S3.Combinatorics.Circle.ThreeBitSource
open private ThreeNegativeEqualOuterJointLift.label
  ThreeNegativeEqualOuterJointLift.lift_order
  ThreeNegativeEqualOuterJointLift.marked_word
  ThreeNegativeEqualOuterJointLift.schedule_from_tail
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

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
  rw [← hmul, mul_add, Int.add_mul_emod_self_left]

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
  have hx : 4 ≤ x := by dsimp [x]; norm_num; exact_mod_cast ha
  have hy : 4 ≤ y := by dsimp [y]; norm_num; exact_mod_cast hb
  have hz : 4 ≤ z := by dsimp [z]; norm_num; exact_mod_cast hc
  have ht : 0 < t := by dsimp [t]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hN : 0 < N := by
    dsimp [N, P, t]
    have hk : 8 ≤ a + b + c + d := by omega
    have hp : (2 : ℤ) ^ 8 ≤ 2 ^ (a + b + c + d) := by
      exact pow_le_pow_right₀ (by norm_num) hk
    rw [show (2 : ℤ) ^ (a + b + c + d) =
      (2 : ℤ) ^ a * 2 ^ b * 2 ^ c * 2 ^ d by ring] at hp
    omega
  have hodd : N % 2 = 1 := by dsimp [N]; omega
  have hA : 1 ≤ A ∧ A < N := by
    dsimp [A, N, P, DB]
    have hxa : 0 < (2 : ℤ) ^ a := by positivity
    have hxb : 0 < (2 : ℤ) ^ b := by positivity
    have hxc : 0 < (2 : ℤ) ^ c := by positivity
    have hxd : 8 * (2 : ℤ) ^ (a + b + c) ≤ 2 ^ d := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show a + b + c + 3 ≤ d by omega)
      rw [show (2 : ℤ) ^ (a + b + c + 3) =
        8 * 2 ^ (a + b + c) by ring] at this
      exact this
    rw [show (2 : ℤ) ^ (a + b + c) =
      (2 : ℤ) ^ a * 2 ^ b * 2 ^ c by ring] at hxd
    constructor <;> nlinarith
  have hB : 1 ≤ B ∧ B < N := by
    dsimp [B, N, P, DB]
    have hxa : 0 < (2 : ℤ) ^ a := by positivity
    have hxb : 0 < (2 : ℤ) ^ b := by positivity
    have hxc : 0 < (2 : ℤ) ^ c := by positivity
    have hxd : 8 * (2 : ℤ) ^ (a + b + c) ≤ 2 ^ d := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show a + b + c + 3 ≤ d by omega)
      rw [show (2 : ℤ) ^ (a + b + c + 3) = 8 * 2 ^ (a + b + c) by ring] at this
      exact this
    rw [show (2 : ℤ) ^ (a + b + c) = (2 : ℤ) ^ a * 2 ^ b * 2 ^ c by ring] at hxd
    constructor <;> nlinarith
  have hL : 1 ≤ L ∧ L < N := by
    dsimp [L, N, P, DL]
    have hxd : 8 * (2 : ℤ) ^ (a + b + c) ≤ 2 ^ d := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show a + b + c + 3 ≤ d by omega)
      rw [show (2 : ℤ) ^ (a + b + c + 3) = 8 * 2 ^ (a + b + c) by ring] at this
      exact this
    rw [show (2 : ℤ) ^ (a + b + c) = (2 : ℤ) ^ a * 2 ^ b * 2 ^ c by ring] at hxd
    constructor <;> nlinarith
  have hM : 1 ≤ M ∧ M < N := by
    dsimp [M, N, P, DM]
    have hxd : 8 * (2 : ℤ) ^ (a + b + c) ≤ 2 ^ d := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (show a + b + c + 3 ≤ d by omega)
      rw [show (2 : ℤ) ^ (a + b + c + 3) = 8 * 2 ^ (a + b + c) by ring] at this
      exact this
    rw [show (2 : ℤ) ^ (a + b + c) = (2 : ℤ) ^ a * 2 ^ b * 2 ^ c by ring] at hxd
    constructor <;> nlinarith
  have hrelA : t * A = N + B := by dsimp [A, B, N, P, DB]; ring
  have hrelB : z * B = N + L := by dsimp [B, L, N, P, DB, DL]; ring
  have hrelL : y * L = N + M := by dsimp [L, M, N, P, DL, DM]; ring
  have hrelM : x * M = N + A := by dsimp [M, A, N, P, DB, DM]; ring
  have hN' : 0 < 2 * N + 1 := by omega
  have hodd' : (2 * N + 1) % 2 = 1 := by omega
  have hB' : 1 ≤ 2 * B - 1 ∧ 2 * B - 1 < 2 * N + 1 := by omega
  have hL' : 1 ≤ 2 * L - 1 - z ∧ 2 * L - 1 - z < 2 * N + 1 := by
    constructor <;> dsimp [L]; nlinarith
  have hM' : 1 ≤ 2 * M - 1 - y - y * z ∧ 2 * M - 1 - y - y * z < 2 * N + 1 := by
    constructor <;> dsimp [M]; nlinarith
  have hrelA' : t * (2 * A) = (2 * N + 1) + (2 * B - 1) := by nlinarith
  have hrelB' : z * (2 * B - 1) = (2 * N + 1) + (2 * L - 1 - z) := by nlinarith [hrelB]
  have hrelL' : y * (2 * L - 1 - z) = (2 * N + 1) + (2 * M - 1 - y - y * z) := by nlinarith [hrelL]
  have hrelM' : x * (2 * M - 1 - y - y * z) = (2 * N + 1) + A := by nlinarith [hrelM]
  have hshiftA (i : ℕ) : f (d + i) = centered N ((2 : ℤ) ^ i * B) := by
    dsimp [f]; rw [show d + i = d + i by rfl, pow_add]
    exact centered_shift N A B d i hN hodd hrelA
  have hshiftB (i : ℕ) : f (d + c + i) = centered N ((2 : ℤ) ^ i * L) := by
    rw [hshiftA, show d + i = d + i by rfl]
    exact centered_shift N B L c i hN hodd hrelB
  have hshiftL (i : ℕ) : f (d + c + b + i) = centered N ((2 : ℤ) ^ i * M) := by
    rw [hshiftB]
    exact centered_shift N L M b i hN hodd hrelL
  have hshiftG (i : ℕ) : f (d + c + b + a + i) = centered N ((2 : ℤ) ^ i * A) := by
    rw [hshiftL]
    exact centered_shift N M A a i hN hodd hrelM
  have hu (i : ℕ) (hi : i < d) :
      f i = if i + 1 < d then (2 : ℤ) ^ i * A else -(N - B) / 2 :=
    centered_ladder N A B d i hN hodd (by omega) hB hi hrelA
  have hv (i : ℕ) (hi : i < c) :
      f (d + i) = if i + 1 < c then (2 : ℤ) ^ i * B else -(N - L) / 2 := by
    rw [hshiftA]
    exact centered_ladder N B L c i hN hodd (by omega) hL hi hrelB
  have hw (i : ℕ) (hi : i < b) :
      f (d + c + i) = if i + 1 < b then (2 : ℤ) ^ i * L else -(N - M) / 2 := by
    rw [hshiftB]
    exact centered_ladder N L M b i hN hodd (by omega) hM hi hrelL
  have hu4 (i : ℕ) (hi : i < a) :
      f (d + c + b + i) = if i + 1 < a then (2 : ℤ) ^ i * M else -(N - A) / 2 := by
    rw [hshiftL]
    exact centered_ladder N M A a i hN hodd (by omega) hA hi hrelM
  have hgu (i : ℕ) (hi : i < d) :
      g i = if i + 1 < d then (2 : ℤ) ^ i * (2 * A)
        else -((2 * N + 1) - (2 * B - 1)) / 2 :=
    centered_ladder (2 * N + 1) (2 * A) (2 * B - 1) d i hN' hodd' (by omega) hB' hi hrelA'
  have hgv (i : ℕ) (hi : i < c) :
      g (d + i) = if i + 1 < c then (2 : ℤ) ^ i * (2 * B - 1)
        else -((2 * N + 1) - (2 * L - 1 - z)) / 2 := by
    have hs : g (d + i) = centered (2 * N + 1) ((2 : ℤ) ^ i * (2 * B - 1)) := by
      dsimp [g]; rw [pow_add]
      exact centered_shift (2 * N + 1) (2 * A) (2 * B - 1) d i hN' hodd' hrelA'
    rw [hs]
    exact centered_ladder (2 * N + 1) (2 * B - 1) (2 * L - 1 - z) c i hN' hodd' (by omega) hL' hi hrelB'
  have hgw (i : ℕ) (hi : i < b) :
      g (d + c + i) = if i + 1 < b then (2 : ℤ) ^ i * (2 * L - 1 - z)
        else -((2 * N + 1) - (2 * M - 1 - y - y * z)) / 2 := by
    have hs : g (d + c + i) = centered (2 * N + 1) ((2 : ℤ) ^ i * (2 * L - 1 - z)) := by
      dsimp [g]; rw [pow_add]
      rw [show (2 : ℤ) ^ (d + c) * (2 * A) =
        (2 : ℤ) ^ c * (2 * B - 1) by
          rw [pow_add]; nlinarith [hrelA']]
      exact centered_shift (2 * N + 1) (2 * B - 1) (2 * L - 1 - z) c i hN' hodd' hrelB'
    rw [hs]
    exact centered_ladder (2 * N + 1) (2 * L - 1 - z) (2 * M - 1 - y - y * z)
      b i hN' hodd' (by omega) hM' hi hrelL'
  have hgu4 (i : ℕ) (hi : i < a) :
      g (d + c + b + i) = if i + 1 < a then
        (2 : ℤ) ^ i * (2 * M - 1 - y - y * z)
        else -((2 * N + 1) - A) / 2 := by
    have hs : g (d + c + b + i) = centered (2 * N + 1) ((2 : ℤ) ^ i * (2 * M - 1 - y - y * z)) := by
      dsimp [g]; rw [pow_add]
      rw [show (2 : ℤ) ^ (d + c + b) * (2 * A) =
        (2 : ℤ) ^ b * (2 * L - 1 - z) by
          rw [pow_add]; nlinarith [hrelA', hrelB']]
      rw [show (2 : ℤ) ^ b * (2 * L - 1 - z) =
        (2 : ℤ) ^ b * (2 * L - 1 - z) by rfl]
      exact centered_shift (2 * N + 1) (2 * M - 1 - y - y * z) A a i hN' hodd' hrelM'
    rw [hs]
    exact centered_ladder (2 * N + 1) (2 * M - 1 - y - y * z) A a i hN' hodd' (by omega) hA hi hrelM'
  refine ⟨hA, hB, hL, hM, hu, hv, hw, hu4, hgu, hgv, hgw, hgu4, ?_⟩
  dsimp [g]
  have hfull : (2 : ℤ) ^ (d + c + b + a) * (2 * A) =
      (2 : ℤ) ^ (d + c + b + a) * (2 * A) := rfl
  have hp := centered_full_period (a + b + c + d + 1) A
  rw [show d + c + b + a = a + b + c + d by omega]
  rw [show (2 : ℤ) ^ (a + b + c + d) * (2 * A) =
    (2 : ℤ) ^ (a + b + c + d + 1) * A by
      rw [pow_succ]; ring]
  have hcenter : centered (2 * N + 1) ((2 : ℤ) ^ (a + b + c + d + 1) * A) =
      centered (2 * N + 1) A := by
    simpa [show 2 * N + 1 = modulus (a + b + c + d + 1) by
      dsimp [N, modulus]; rw [pow_succ]; ring] using hp
  rw [hcenter]
  dsimp [centered]
  have hApos := hA.1
  have hAlt := hA.2
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

end D5.S3.Combinatorics.Circle.FourNegativeEventual
