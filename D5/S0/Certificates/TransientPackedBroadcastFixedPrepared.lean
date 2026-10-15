/-
Prepared source only, 2026-10-15. NOT compiled or kernel accepted.
This companion does not edit PackedBroadcastPrepared.lean or any WT.
The sibling import below should become the verified broadcast module's import
when the parent integrates both files into its own compilation directory.
-/
import D5.S0.Certificates.TransientPackedBroadcastPrepared
import D5.S0.Certificates.FinitePackedLaneGuard

namespace EJMPackedBroadcastFixedPrepared

open EJMPackedBroadcastPrepared

/-- Exactly `count` low-first radix digits, including terminal zeros. -/
def fixedDigits (base count value : Nat) : List Nat :=
  List.ofFn (fun i : Fin count => digit base i.val value)

theorem fixedDigits_length (base count value : Nat) :
    (fixedDigits base count value).length = count := by
  simp [fixedDigits]

theorem fixedDigits_lt (base : Nat) (hbase : 0 < base) (count value : Nat) :
    ∀ x ∈ fixedDigits base count value, x < base := by
  intro x hx
  change x ∈ List.ofFn (fun i : Fin count => digit base i.val value) at hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact Nat.mod_lt _ hbase

theorem digit_zero (base value : Nat) : digit base 0 value = value % base := by
  simp [digit]

theorem digit_succ (base index value : Nat) :
    digit base (index + 1) value = digit base index (value / base) := by
  unfold digit
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']

theorem fixedDigits_succ (base count value : Nat) :
    fixedDigits base (count + 1) value =
      value % base :: fixedDigits base count (value / base) := by
  simp only [fixedDigits, List.ofFn_succ, Fin.val_zero, Fin.val_succ,
    digit_zero, digit_succ]

/-- Reconstruct a bounded packed natural from a complete fixed-length digit list.
No positivity assumption is required; this also handles zero-width packing. -/
theorem ofDigits_fixedDigits (base count value : Nat) (hvalue : value < base ^ count) :
    Nat.ofDigits base (fixedDigits base count value) = value := by
  induction count generalizing value with
  | zero =>
      have hzero : value = 0 := by simpa using hvalue
      subst value
      simp [fixedDigits]
  | succ count ih =>
      have hquot : value / base < base ^ count :=
        Nat.div_lt_of_lt_mul (by simpa only [Nat.pow_succ'] using hvalue)
      rw [fixedDigits_succ, Nat.ofDigits_cons, ih (value / base) hquot]
      exact Nat.mod_add_div value base

/-- Definitional match for `pack width = Nat.ofDigits (2^width)`. -/
theorem pack_fixed_reconstruction (width count value : Nat)
    (hvalue : value < (2 ^ width) ^ count) :
    Nat.ofDigits (2 ^ width)
      (List.ofFn (fun i : Fin count => digit (2 ^ width) i.val value)) = value :=
  ofDigits_fixedDigits (2 ^ width) count value hvalue

/-- Direct consumer wrapper matching the guard module's `pack`.
`Nat.ofDigits` and `FinitePackedLaneGuard.pack` agree definitionally. -/
theorem pack_ofFn_digit (width count value : Nat)
    (hvalue : value < (2 ^ width) ^ count) :
    D5.S0.Certificates.FinitePackedLaneGuard.pack width
      (List.ofFn (fun i : Fin count => digit (2 ^ width) i.val value)) = value :=
  ofDigits_fixedDigits (2 ^ width) count value hvalue

theorem length_repeatEach4 (xs : List Nat) :
    (repeatEach4 xs).length = 4 * xs.length := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      simp only [repeatEach4, List.length_cons]
      rw [ih]
      omega

theorem broadcastBlocks_zero (base count : Nat) : broadcastBlocks base count 0 = 0 := by
  induction count with
  | zero => rfl
  | succ count ih => simp [broadcastBlocks, ih]

/-- List-free API: bounded source naturals inherit the exact lane projection. -/
theorem broadcastBlocks_lane_nat (base size count value : Nat)
    (hsize : 0 < size) (hbase : 0 < base ^ size)
    (hvalue : value < (base ^ size) ^ count) (index : Nat) :
    digit base index (broadcastBlocks (base ^ size) count value) =
      digit base ((index / (4 * size)) * size + index % size) value := by
  let xs := fixedDigits (base ^ size) count value
  have hxs : ∀ x ∈ xs, x < base ^ size :=
    fixedDigits_lt (base ^ size) hbase count value
  have hlength : xs.length = count := fixedDigits_length _ _ _
  have hpack : Nat.ofDigits (base ^ size) xs = value :=
    ofDigits_fixedDigits (base ^ size) count value hvalue
  have h := broadcastBlocks_lane base size hsize hbase xs hxs index
  rw [hlength, hpack] at h
  exact h

/-- Every repeated source block is bounded, so the entire broadcast fits exactly
four times as many blocks. `base=1` is handled rather than silently excluded. -/
theorem broadcastBlocks_bound_nat (base : Nat) (hbase : 0 < base)
    (count value : Nat) (hvalue : value < base ^ count) :
    broadcastBlocks base count value < base ^ (4 * count) := by
  by_cases hone : base = 1
  · subst base
    have hzero : value = 0 := by simpa using hvalue
    subst value
    simp [broadcastBlocks_zero]
  · have hbase' : 1 < base := by omega
    let xs := fixedDigits base count value
    have hxs : ∀ x ∈ xs, x < base := fixedDigits_lt base hbase count value
    have hlength : xs.length = count := fixedDigits_length _ _ _
    have hpack : Nat.ofDigits base xs = value :=
      ofDigits_fixedDigits base count value hvalue
    have hrepeat : ∀ x ∈ repeatEach4 xs, x < base :=
      fun x hx => hxs x ((mem_repeatEach4 x xs).mp hx)
    have heq := broadcastBlocks_ofDigits base hbase xs hxs
    rw [hlength, hpack] at heq
    rw [heq]
    have hbound := Nat.ofDigits_lt_base_pow_length hbase' hrepeat
    simpa only [length_repeatEach4, hlength] using hbound

/-- Consumer API for one missing original scope axis.
No expanded source literals or explicit chunks occur in the statement.
The equality holds for all `index`, preserving complete-domain semantics. -/
theorem broadcastBits_lane_nat (width prefix suffix value : Nat)
    (hvalue : value < (2 ^ width) ^ (4 ^ prefix * 4 ^ suffix)) (index : Nat) :
    digit (2 ^ width) index
        (broadcastBits (width * 4 ^ suffix) (4 ^ prefix) value) =
      digit (2 ^ width) (eraseDigit 4 suffix index) value := by
  have hsize : 0 < 4 ^ suffix := Nat.pow_pos (by decide)
  have hbase : 0 < (2 ^ width) ^ (4 ^ suffix) :=
    Nat.pow_pos (Nat.two_pow_pos width)
  have hsource : value < ((2 ^ width) ^ (4 ^ suffix)) ^ (4 ^ prefix) := by
    rw [← Nat.pow_mul, Nat.mul_comm (4 ^ suffix) (4 ^ prefix)]
    exact hvalue
  rw [broadcastBits_eq, Nat.pow_mul]
  exact broadcastBlocks_lane_nat (2 ^ width) (4 ^ suffix) (4 ^ prefix)
    value hsize hbase hsource index

/-- Consumer range API: one missing axis multiplies the lane count by four.
This includes width zero, whose source and broadcast are both zero. -/
theorem broadcastBits_lt_nat (width prefix suffix value : Nat)
    (hvalue : value < (2 ^ width) ^ (4 ^ prefix * 4 ^ suffix)) :
    broadcastBits (width * 4 ^ suffix) (4 ^ prefix) value <
      (2 ^ width) ^ (4 ^ (prefix + suffix + 1)) := by
  have hbase : 0 < (2 ^ width) ^ (4 ^ suffix) :=
    Nat.pow_pos (Nat.two_pow_pos width)
  have hsource : value < ((2 ^ width) ^ (4 ^ suffix)) ^ (4 ^ prefix) := by
    rw [← Nat.pow_mul, Nat.mul_comm (4 ^ suffix) (4 ^ prefix)]
    exact hvalue
  have hexponent : (4 ^ suffix) * (4 * (4 ^ prefix)) =
      4 ^ (prefix + suffix + 1) := by
    rw [Nat.pow_succ, Nat.pow_add]
    ring
  have hboundPower : ((2 ^ width) ^ (4 ^ suffix)) ^ (4 * (4 ^ prefix)) =
      (2 ^ width) ^ (4 ^ (prefix + suffix + 1)) := by
    calc
      _ = (2 ^ width) ^ ((4 ^ suffix) * (4 * (4 ^ prefix))) :=
        (Nat.pow_mul (2 ^ width) (4 ^ suffix) (4 * (4 ^ prefix))).symm
      _ = _ := by rw [hexponent]
  have h := broadcastBlocks_bound_nat ((2 ^ width) ^ (4 ^ suffix)) hbase
    (4 ^ prefix) value hsource
  rw [hboundPower] at h
  simpa only [broadcastBits_eq, Nat.pow_mul] using h

end EJMPackedBroadcastFixedPrepared
