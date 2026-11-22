/- GID: D5/S3/Arith/Additive/BenfieldLippard/PositiveFixedLength
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/BenfieldLippard/PositiveFixedLength
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A fixed number of positive powers represents every sufficiently large integer. -/

import D5.S3.Arith.Additive.Waring.WaringTheorem2

open scoped BigOperators

namespace BenfieldLippard

/-- A representation by exactly j positive kth powers. -/
def PosRep (k j n : ℕ) : Prop :=
  ∃ f : Fin j → ℕ, (∀ i, 0 < f i) ∧ n = ∑ i, (f i) ^ k

private def powerSum (k : ℕ) (xs : List ℕ) : ℕ :=
  (xs.map (· ^ k)).sum

private theorem powerSum_filter_pos {k : ℕ} (hk : 0 < k) (xs : List ℕ) :
    powerSum k (xs.filter (fun a => decide (0 < a))) = powerSum k xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases ha : 0 < a
    · simpa [powerSum, ha] using congrArg ((a ^ k) + ·) ih
    · have he : a = 0 := Nat.eq_zero_of_not_pos ha
      simpa [powerSum, ha, he, zero_pow (Nat.ne_of_gt hk)] using ih

private theorem repeated_block (k t : ℕ) (xs : List ℕ)
    (hpos : ∀ a ∈ xs, 0 < a) :
    ∃ ys : List ℕ,
      ys.length = t * xs.length ∧ powerSum k ys = t * powerSum k xs ∧
        ∀ a ∈ ys, 0 < a := by
  induction t with
  | zero => exact ⟨[], by simp, by simp [powerSum], by simp⟩
  | succ t ih =>
    obtain ⟨ys, hlen, hsum, hy⟩ := ih
    refine ⟨ys ++ xs, ?_, ?_, ?_⟩
    · simp [hlen, Nat.succ_mul]
    · simp only [powerSum, List.map_append, List.sum_append]
      change powerSum k ys + powerSum k xs = (t + 1) * powerSum k xs
      rw [hsum, Nat.add_mul, one_mul]
    · intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact hy a h
      · exact hpos a h

/-- The two blocks have the same power sum and lengths that differ by one.
With a = 2^k - 1 and m = a^(k-1), the identity is m * 2^k = a^k + m. -/
private theorem reserve_blocks (k : ℕ) (hk : 2 ≤ k) :
    ∃ m R : ℕ, ∃ low high : List ℕ,
      low.length = m ∧ high.length = m + 1 ∧
      powerSum k low = R ∧ powerSum k high = R ∧
      (∀ a ∈ low, 0 < a) ∧ (∀ a ∈ high, 0 < a) := by
  let a : ℕ := 2 ^ k - 1
  let m : ℕ := a ^ (k - 1)
  have h2 : 2 ≤ (2 : ℕ) ^ k := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 1 ≤ k by omega)
  have ha : 0 < a := by dsimp [a]; omega
  have htwo : 2 ^ k = a + 1 := by dsimp [a]; omega
  have hpow : a ^ k = m * a := by
    calc
      a ^ k = a ^ (k - 1 + 1) := congrArg (a ^ ·) (by omega)
      _ = m * a := pow_succ a (k - 1)
  refine ⟨m, m * 2 ^ k, List.replicate m 2, a :: List.replicate m 1,
    by simp, by simp, ?_, ?_, ?_, ?_⟩
  · simp [powerSum, List.sum_replicate]
  · simp [powerSum, List.sum_replicate, hpow]
    rw [htwo, Nat.mul_add, Nat.mul_one]
  · intro x hx
    simp [List.eq_of_mem_replicate hx]
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · simp [List.eq_of_mem_replicate hx]

/-- For each k ≥ 2 there is a fixed positive number of summands covering a tail. -/
theorem eventual_fixed_length :
    ∀ k : ℕ, 2 ≤ k → ∃ j : ℕ, 1 ≤ j ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → PosRep k j n := by
  intro k hk
  have hkpos : 0 < k := by omega
  obtain ⟨g, hg⟩ := Waring.waringTheorem k hkpos
  obtain ⟨m, R, low, high, hlow, hhigh, hlowSum, hhighSum, hlowPos, hhighPos⟩ :=
    reserve_blocks k hk
  refine ⟨g * (m + 1) + 1, by omega, g * R + 1, ?_⟩
  intro n hn
  obtain ⟨s, hs, f, hf⟩ := hg (n - (g * R + 1))
  let raw := List.ofFn f
  let positive := raw.filter (fun a => decide (0 < a))
  let i := positive.length
  have hi : i ≤ g := by
    calc
      i ≤ raw.length := List.length_filter_le _ _
      _ = s := List.length_ofFn
      _ ≤ g := hs
  have hpos : ∀ a ∈ positive, 0 < a := by
    intro a ha
    simpa using (List.mem_filter.mp ha).2
  have hsum : powerSum k positive = n - (g * R + 1) := by
    rw [powerSum_filter_pos hkpos raw, hf]
    change ((List.ofFn f).map (· ^ k)).sum = _
    rw [← List.ofFn_comp' f (· ^ k), List.sum_ofFn]
  obtain ⟨q, hq⟩ : ∃ q : ℕ, g = i + q := ⟨g - i, by omega⟩
  obtain ⟨ls, hls, hlsSum, hlsPos⟩ := repeated_block k i low hlowPos
  obtain ⟨rs, hrs, hrsSum, hrsPos⟩ := repeated_block k q high hhighPos
  let xs := 1 :: (positive ++ ls ++ rs)
  have hlen : xs.length = g * (m + 1) + 1 := by
    simp only [xs, List.length_cons, List.length_append, hls, hrs, hlow, hhigh]
    rw [hq, Nat.add_mul, Nat.mul_add i m 1, Nat.mul_one]
    change i + i * m + q * (m + 1) + 1 = i * m + i + q * (m + 1) + 1
    ac_rfl
  have htotal : powerSum k xs = n := by
    have hres : i * R + q * R = g * R := by rw [hq, Nat.add_mul]
    simp only [xs, powerSum, List.map_cons, List.sum_cons, List.map_append, List.sum_append]
    change 1 ^ k + (powerSum k positive + powerSum k ls + powerSum k rs) = n
    rw [one_pow, hsum, hlsSum, hrsSum, hlowSum, hhighSum, add_assoc _ (i * R) (q * R), hres]
    omega
  have hall : ∀ a ∈ xs, 0 < a := by
    intro a ha
    simp only [xs, List.mem_cons, List.mem_append] at ha
    rcases ha with rfl | (h | h) | h
    · decide
    · exact hpos a h
    · exact hlsPos a h
    · exact hrsPos a h
  change PosRep k (g * (m + 1) + 1) n
  rw [← hlen]
  refine ⟨xs.get, fun t => hall _ (List.get_mem _ _), ?_⟩
  rw [← htotal]
  rw [← List.sum_ofFn, List.ofFn_comp' xs.get (· ^ k), List.ofFn_get]
  rfl

end BenfieldLippard
