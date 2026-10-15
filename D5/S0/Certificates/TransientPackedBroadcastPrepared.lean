/-
Prepared source only, 2026-10-15. This file has NOT been compiled.
No kernel-acceptance or performance claim is attached to these proof drafts.
It does not change the active WT or replace original F1/F2 source bindings.

Scope codes use C order: the last scope axis varies fastest. Low packed lane
number equals scope code. Native expanded vectors are never source bindings.
-/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Bitwise
import Lean.Elab.Tactic.Omega

namespace EJMPackedBroadcastPrepared

def digit (base index value : Nat) : Nat := value / base ^ index % base

def repeatEach4 : List Nat → List Nat
  | [] => []
  | a :: as => a :: a :: a :: a :: repeatEach4 as

def repeatWeight (base : Nat) : Nat := 1 + base + base ^ 2 + base ^ 3

/-- Extract source blocks, repeat each four times, concatenate in low-first order. -/
def broadcastBlocks (base : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, value =>
      (value % base) * repeatWeight base +
        base ^ 4 * broadcastBlocks base count (value / base)

/-- Same algorithm using kernel bigint bitwise and shift primitives. -/
def broadcastBits (blockBits : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, value =>
      (value &&& (2 ^ blockBits - 1)) * repeatWeight (2 ^ blockBits) +
        (broadcastBits blockBits count (value >>> blockBits) <<< (4 * blockBits))

theorem mem_repeatEach4 (x : Nat) (xs : List Nat) :
    x ∈ repeatEach4 xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [repeatEach4]
  | cons a as ih => simp [repeatEach4, ih, or_assoc]

/-- Algebraic identity: no digit bounds are needed for this step. -/
theorem ofDigits_repeatEach4 (base : Nat) (xs : List Nat) :
    Nat.ofDigits base (repeatEach4 xs) =
      repeatWeight base * Nat.ofDigits (base ^ 4) xs := by
  induction xs with
  | nil => simp [repeatEach4, Nat.ofDigits]
  | cons a as ih =>
      simp only [repeatEach4, Nat.ofDigits_cons]
      rw [ih]
      dsimp [repeatWeight]
      ring

/-- Fixed-width packing keeps terminal zeros; it does not use `Nat.digits`. -/
theorem digit_ofDigits (base : Nat) (hbase : 0 < base) :
    ∀ xs : List Nat, (∀ x ∈ xs, x < base) → ∀ index,
      digit base index (Nat.ofDigits base xs) = xs.getD index 0 := by
  intro xs
  induction xs with
  | nil => intro _ index; simp [digit, Nat.ofDigits]
  | cons a as ih =>
      intro hxs index
      have ha : a < base := hxs a (by simp)
      have has : ∀ x ∈ as, x < base :=
        fun x hx => hxs x (List.mem_cons_of_mem a hx)
      cases index with
      | zero =>
          simp [digit, Nat.ofDigits_cons, Nat.mod_eq_of_lt ha]
      | succ index =>
          change ((a + base * Nat.ofDigits base as) / base ^ (index + 1)) % base =
            as.getD index 0
          rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul,
            Nat.add_mul_div_left _ _ hbase, Nat.div_eq_of_lt ha, Nat.zero_add]
          exact ih has index

theorem getD_repeatEach4 (xs : List Nat) :
    ∀ index, (repeatEach4 xs).getD index 0 = xs.getD (index / 4) 0 := by
  induction xs with
  | nil => intro index; simp [repeatEach4]
  | cons a as ih =>
      intro index
      match index with
      | 0 => simp [repeatEach4]
      | 1 => simp [repeatEach4]
      | 2 => simp [repeatEach4]
      | 3 => simp [repeatEach4]
      | index + 4 =>
          change (repeatEach4 as).getD index 0 =
            (a :: as).getD ((index + 4) / 4) 0
          rw [Nat.add_div_right index (by decide), List.getD_cons_succ]
          exact ih index

/-- The recursive computation is bound to the original packed source blocks. -/
theorem broadcastBlocks_ofDigits (base : Nat) (hbase : 0 < base) :
    ∀ xs : List Nat, (∀ x ∈ xs, x < base) →
      broadcastBlocks base xs.length (Nat.ofDigits base xs) =
        Nat.ofDigits base (repeatEach4 xs) := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons a as ih =>
      intro hxs
      have ha : a < base := hxs a (by simp)
      have has : ∀ x ∈ as, x < base :=
        fun x hx => hxs x (List.mem_cons_of_mem a hx)
      simp only [List.length_cons, Nat.ofDigits_cons, broadcastBlocks]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
        Nat.add_mul_div_left _ _ hbase, Nat.div_eq_of_lt ha, Nat.zero_add, ih has]
      simp only [repeatEach4, Nat.ofDigits_cons]
      dsimp [repeatWeight]
      ring

theorem broadcastBits_eq (blockBits count value : Nat) :
    broadcastBits blockBits count value =
      broadcastBlocks (2 ^ blockBits) count value := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih =>
      simp only [broadcastBits, broadcastBlocks, Nat.and_two_pow_sub_one_eq_mod,
        Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, ih]
      have hpow : (2 ^ blockBits) ^ 4 = 2 ^ (4 * blockBits) := by
        rw [← Nat.pow_mul, Nat.mul_comm blockBits 4]
      rw [hpow]
      ring

theorem broadcastBlocks_digit (base : Nat) (hbase : 0 < base)
    (xs : List Nat) (hxs : ∀ x ∈ xs, x < base) (index : Nat) :
    digit base index (broadcastBlocks base xs.length (Nat.ofDigits base xs)) =
      digit base (index / 4) (Nat.ofDigits base xs) := by
  have hrepeat : ∀ x ∈ repeatEach4 xs, x < base :=
    fun x hx => hxs x ((mem_repeatEach4 x xs).mp hx)
  calc
    _ = (repeatEach4 xs).getD index 0 := by
      rw [broadcastBlocks_ofDigits base hbase xs hxs]
      exact digit_ofDigits base hbase _ hrepeat index
    _ = xs.getD (index / 4) 0 := getD_repeatEach4 xs index
    _ = _ := (digit_ofDigits base hbase xs hxs (index / 4)).symm

/-- Extracting a lane inside a packed block equals extracting the original lane. -/
theorem nested_digit (base size blockIndex laneIndex value : Nat)
    (hlane : laneIndex < size) :
    digit base laneIndex (digit (base ^ size) blockIndex value) =
      digit base (size * blockIndex + laneIndex) value := by
  have hpow : base ^ size = base ^ laneIndex * base ^ (size - laneIndex) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hlane)]
  have hdiv : base ∣ base ^ (size - laneIndex) := by
    simpa using Nat.pow_dvd_pow base (Nat.sub_pos_of_lt hlane)
  have hmod (a : Nat) : (a % base ^ size / base ^ laneIndex) % base =
      (a / base ^ laneIndex) % base := by
    rw [hpow, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdiv]
  unfold digit
  rw [hmod, Nat.div_div_eq_div_mul, ← Nat.pow_mul, ← Nat.pow_add]

/-- Exact missing-axis projection; it holds even beyond the declared domain (zero padding). -/
theorem broadcastBlocks_lane (base size : Nat) (hsize : 0 < size)
    (hbase : 0 < base ^ size) (xs : List Nat)
    (hxs : ∀ x ∈ xs, x < base ^ size) (index : Nat) :
    digit base index (broadcastBlocks (base ^ size) xs.length
      (Nat.ofDigits (base ^ size) xs)) =
      digit base ((index / (4 * size)) * size + index % size)
        (Nat.ofDigits (base ^ size) xs) := by
  let blockIndex := index / size
  let laneIndex := index % size
  have hlane : laneIndex < size := Nat.mod_lt index hsize
  have hindex : size * blockIndex + laneIndex = index := Nat.div_add_mod index size
  have hproject : size * (blockIndex / 4) + laneIndex =
      (index / (4 * size)) * size + index % size := by
    dsimp [blockIndex, laneIndex]
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm size 4,
      Nat.mul_comm size (index / (4 * size))]
  calc
    _ = digit base laneIndex (digit (base ^ size) blockIndex
        (broadcastBlocks (base ^ size) xs.length (Nat.ofDigits (base ^ size) xs))) := by
      rw [nested_digit _ _ _ _ _ hlane, hindex]
    _ = digit base laneIndex (digit (base ^ size) (blockIndex / 4)
        (Nat.ofDigits (base ^ size) xs)) := by
      rw [broadcastBlocks_digit (base ^ size) hbase xs hxs blockIndex]
    _ = digit base (size * (blockIndex / 4) + laneIndex)
        (Nat.ofDigits (base ^ size) xs) := nested_digit _ _ _ _ _ hlane
    _ = _ := by rw [hproject]

/-- Group the actual source lane table into equal-width chunks without changing packing. -/
theorem ofDigits_flatten_equal_lengths (base size : Nat) :
    ∀ chunks : List (List Nat), (∀ chunk ∈ chunks, chunk.length = size) →
      Nat.ofDigits base chunks.flatten =
        Nat.ofDigits (base ^ size) (chunks.map (Nat.ofDigits base)) := by
  intro chunks
  induction chunks with
  | nil => intro _; rfl
  | cons chunk chunks ih =>
      intro hchunks
      have hlength : chunk.length = size := hchunks chunk (by simp)
      have hrest : ∀ c ∈ chunks, c.length = size :=
        fun c hc => hchunks c (List.mem_cons_of_mem chunk hc)
      simp only [List.flatten_cons, List.map_cons, Nat.ofDigits_cons]
      rw [Nat.ofDigits_append, hlength, ih hrest]

/-- Delete one radix digit with `suffix` digits to its right. -/
def eraseDigit (base suffix code : Nat) : Nat :=
  (code / (base * base ^ suffix)) * base ^ suffix + code % base ^ suffix

theorem eraseDigit_mod (base suffix code : Nat) :
    eraseDigit base suffix code % base ^ suffix = code % base ^ suffix := by
  unfold eraseDigit
  rw [Nat.mul_add_mod_self_right, Nat.mod_mod]

theorem eraseDigit_div (base : Nat) (hbase : 0 < base) (suffix code : Nat) :
    eraseDigit base suffix code / base ^ suffix = code / (base * base ^ suffix) := by
  have hpow : 0 < base ^ suffix := Nat.pow_pos hbase
  unfold eraseDigit
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpow,
    Nat.div_eq_of_lt (Nat.mod_lt code hpow), Nat.zero_add]

theorem digit_eq_mod_div (base index value : Nat) :
    digit base index value = value % base ^ (index + 1) / base ^ index := by
  unfold digit
  rw [Nat.pow_succ, Nat.mod_mul_right_div_self]

/-- All less significant retained coordinates preserve their original values. -/
theorem eraseDigit_low (base suffix code index : Nat) (hindex : index < suffix) :
    digit base index (eraseDigit base suffix code) = digit base index code := by
  have hdiv : base ^ (index + 1) ∣ base ^ suffix := Nat.pow_dvd_pow base hindex
  have hmod : eraseDigit base suffix code % base ^ (index + 1) =
      code % base ^ (index + 1) := by
    calc
      _ = (eraseDigit base suffix code % base ^ suffix) % base ^ (index + 1) :=
        (Nat.mod_mod_of_dvd _ hdiv).symm
      _ = (code % base ^ suffix) % base ^ (index + 1) := by rw [eraseDigit_mod]
      _ = _ := Nat.mod_mod_of_dvd _ hdiv
  rw [digit_eq_mod_div, digit_eq_mod_div, hmod]

/-- More significant retained coordinates shift by one original radix digit. -/
theorem eraseDigit_high (base : Nat) (hbase : 0 < base)
    (suffix code index : Nat) (hindex : suffix ≤ index) :
    digit base index (eraseDigit base suffix code) = digit base (index + 1) code := by
  have hshift (value : Nat) : digit base index value =
      digit base (index - suffix) (value / base ^ suffix) := by
    unfold digit
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_of_le hindex]
  have hden : (base * base ^ suffix) * base ^ (index - suffix) = base ^ (index + 1) := by
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_of_le hindex, ← Nat.pow_succ']
  calc
    _ = digit base (index - suffix) (eraseDigit base suffix code / base ^ suffix) :=
      hshift _
    _ = digit base (index - suffix) (code / (base * base ^ suffix)) := by
      rw [eraseDigit_div base hbase]
    _ = _ := by unfold digit; rw [Nat.div_div_eq_div_mul, hden]

def cDigit (arity code position : Nat) : Nat := digit 4 (arity - 1 - position) code

/-- Actual C-order source coordinates agree after deleting a missing axis.
The arbitrary `code` is never truncated to a smaller domain by this theorem. -/
theorem cDigit_erase (prefixAxes suffix code position : Nat)
    (hposition : position < prefixAxes + suffix) :
    cDigit (prefixAxes + suffix) (eraseDigit 4 suffix code) position =
      cDigit (prefixAxes + suffix + 1) code
        (if position < prefixAxes then position else position + 1) := by
  by_cases hpositionPrefix : position < prefixAxes
  · simp only [cDigit, if_pos hpositionPrefix]
    have hhigh : suffix ≤ prefixAxes + suffix - 1 - position := by omega
    rw [eraseDigit_high 4 (by decide) suffix code _ hhigh]
    congr 1
    omega
  · simp only [cDigit, if_neg hpositionPrefix]
    have hlow : prefixAxes + suffix - 1 - position < suffix := by omega
    rw [eraseDigit_low 4 suffix code _ hlow]
    congr 1
    omega

/- Actual EJM integration obligations (not assertions or proof receipts):

1. Bind ORIGINAL source packed lanes to original factor / prior verified bucket
   values, including the exact signed offset and scale K=6987435 bridge.
2. For each missing axis, set size=4^suffixAxes and count=4^prefixAxes;
   derive equal-size source chunks and their < (2^w)^size range from original
   lanes, using Nat.ofDigits_lt_base_pow_length, then apply the theorem above.
3. Bind the original scope decoder to `cDigit`, then use `cDigit_erase` for
   retained coordinate equality. The omitted-axis projection is exactly
       code ↦ (code / (4*size))*size + code%size.
   C-order is confirmed in prepare-anchor-bucket-ve-lean.py `lookup`.
4. Compose these single-axis projections to the actual union scope (sorted
   original coordinates), preserving all 20 coordinates and all four values.
5. Close full-sum range and guard bridge separately. These lemmas by themselves
   do not prove any EJM bucket inequality or adaptive/global acceptance.

Future SWAR optimization should prove equality with broadcastBits; its native
expanded literals must never replace obligations 1–4.
-/

end EJMPackedBroadcastPrepared
