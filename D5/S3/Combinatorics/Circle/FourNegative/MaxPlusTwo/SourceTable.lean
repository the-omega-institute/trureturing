/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/SourceTable
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/SourceTable
   mirror-E: none(waiver:consumed-source-table)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Actual four-chain centered source reductions with an independent fourth gap. -/
import D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventual

/-! Centered reductions needed by physical max-plus-two schedules. The fourth
chain length is independent of the sum of the first three lengths. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable
open SourceWidth PeriodicShortening RunFirstEarTransport
open private centered_shift centered_ladder
  from D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventual

set_option maxHeartbeats 1000000 in
-- The paired ladders carry eight centered reductions and their arithmetic bounds.
private theorem source_table (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hd : 2 ≤ d) :
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
  have ht4 : 4 ≤ t := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hd
    norm_num at h
    simpa [t] using h
  have hA : 1 ≤ A ∧ A < N := by
    constructor
    · dsimp [A, P, DB]
      nlinarith [hP]
    · dsimp [A, N]
      have hPt : 4 * P ≤ P * t := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left ht4 hP.le
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

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable
