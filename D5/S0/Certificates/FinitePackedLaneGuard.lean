/- GID: D5/S0/Certificates/FinitePackedLaneGuard
   generality: G
   mirror-B: D5/B/S0/Certificates/FinitePackedLaneGuard
   mirror-E: none(waiver:finite-packed-comparison-guard)
   anchors: []
   utility: none
   digest: A proved finite lane encoding and full half-base range bounds make the packed high-bit guard imply every original pointwise comparison. -/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Forall2

/-!
Prepared source, uncompiled. Library search found Nat.ofDigits digitwise
addition, Nat.testBit_two_pow_mul_add, Nat.testBit_and, and
Nat.ge_two_pow_of_testBit. No packed-lane guard-to-pointwise comparison theorem
was found in the finite-certificate, EJM or Mathlib Nat modules. These existing
arithmetic and bitwise bridges are reused rather than trusted native packing.

The comparison is one-direction soundness only. With B = 2^width and
H = 2^(width-1), the lists encode X and Y in little-endian lanes; the mask has
exactly one H digit for every list entry. Both complete compared values in
each lane, including all relevant sums and offsets, must be below H. Bounds
on individual summands do not discharge this obligation.

The proof builds z_i = H + y_i - x_i, proves X + Z = M + Y using digitwise
addition, and hence identifies M + Y - X exactly with Z. Every z_i is below B.
The guard then forces the high bit in each actual z_i and yields x_i ≤ y_i.
No lane count, native packing result, broadcast alignment or coordinate
projection is accepted as a substitute for the defined pack and range proofs.
Concrete EJM receipt applications must separately connect every original
four-valued assignment and full bucket sum to these exact list entries.

admission_basis: escape-witness
testBit_pack_lane: proof_shape: content; escape_witness: structural digit
induction extracts the selected actual high bit without cross-lane carries.
Consumer: guard_le applies this at every lane of the normalized difference.
guard_le: proof_shape: content; escape_witness: exact no-borrow arithmetic
and per-lane high-bit extraction recover every comparison from one guard.
The intended consumer is the original EJM finite bucket inequality pilot;
its packing/broadcast equalities, complete lane bounds and actual guard are
still required. No actual kernel guard, min-plus step, prefix bound, raw replay
acceptance or full frontier coverage is asserted here. Compiled source-owned
Reg evidence and current binding remain unfinished under
https://github.com/the-omega-institute/trureturing/issues/16309
No audit success or declared_validated status is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FinitePackedLaneGuard

/-- Exact little-endian base-two-power encoding, including terminal zeros. -/
def pack (width : ℕ) (digits : List ℕ) : ℕ := Nat.ofDigits (2 ^ width) digits

/-- One highest-lane-bit marker for each actual list entry. -/
def mask (width count : ℕ) : ℕ :=
  pack width (List.replicate count (2 ^ (width - 1)))

/-- Extract the actual high bit of a bounded digit at its original list index.
The bound is on each complete digit; no canonical Nat.digits length is used. -/
theorem testBit_pack_lane (width : ℕ) (positive : 0 < width) :
    ∀ (digits : List ℕ), (∀ d ∈ digits, d < 2 ^ width) →
      ∀ (i : ℕ) (inside : i < digits.length),
        (pack width digits).testBit (width * i + (width - 1)) =
          digits[i].testBit (width - 1) := by
  intro digits
  induction digits with
  | nil =>
    intro bounded i inside
    simp only [List.length_nil] at inside
    omega
  | cons d digits ih =>
    intro bounded i inside
    have headBound : d < 2 ^ width := bounded d (by simp)
    have tailBound : ∀ a ∈ digits, a < 2 ^ width := by
      intro a member
      exact bounded a (List.mem_cons_of_mem d member)
    cases i with
    | zero =>
      rw [pack, Nat.ofDigits_cons, Nat.add_comm,
        Nat.testBit_two_pow_mul_add _ headBound]
      have low : width - 1 < width := by omega
      simp only [Nat.mul_zero, Nat.zero_add, if_pos low, List.getElem_cons_zero]
    | succ i =>
      rw [pack, Nat.ofDigits_cons, Nat.add_comm,
        Nat.testBit_two_pow_mul_add _ headBound]
      have high : ¬ width * (i + 1) + (width - 1) < width := by
        rw [Nat.mul_succ]
        omega
      have shifted : width * (i + 1) + (width - 1) - width =
          width * i + (width - 1) := by
        rw [Nat.mul_succ]
        omega
      rw [if_neg high, shifted]
      simpa only [pack, List.getElem_cons_succ] using ih tailBound i (by
        simpa only [List.length_cons, Nat.succ_lt_succ_iff] using inside)

private theorem add_difference_lists (half : ℕ) (xs : List ℕ) :
    ∀ (ys : List ℕ), xs.length = ys.length → (∀ x ∈ xs, x < half) →
      xs.zipWith (· + ·) (xs.zipWith (fun x y => half + y - x) ys) =
        (List.replicate xs.length half).zipWith (· + ·) ys := by
  induction xs with
  | nil =>
    intro ys lengths bounded
    have empty : ys = [] := List.length_eq_zero_iff.mp lengths.symm
    subst ys
    rfl
  | cons x xs ih =>
    intro ys lengths bounded
    cases ys with
    | nil =>
      simp only [List.length_cons, List.length_nil] at lengths
      omega
    | cons y ys =>
      have tailLength : xs.length = ys.length := Nat.succ.inj lengths
      have row : x + (half + y - x) = half + y := by
        have below := bounded x (by simp)
        omega
      have tailBound : ∀ a ∈ xs, a < half := by
        intro a member
        exact bounded a (List.mem_cons_of_mem x member)
      simp only [List.zipWith_cons_cons, List.length_cons, List.replicate_succ]
      rw [row, ih ys tailLength tailBound]

private theorem no_borrow (width : ℕ) (xs ys : List ℕ)
    (lengths : xs.length = ys.length)
    (bounded : ∀ x ∈ xs, x < 2 ^ (width - 1)) :
    mask width xs.length + pack width ys - pack width xs =
      pack width (xs.zipWith (fun x y => 2 ^ (width - 1) + y - x) ys) := by
  let zs := xs.zipWith (fun x y => 2 ^ (width - 1) + y - x) ys
  have differenceLength : xs.length = zs.length := by
    simp only [zs, List.length_zipWith, lengths, Nat.min_self]
  have maskLength : (List.replicate xs.length (2 ^ (width - 1))).length = ys.length := by
    simpa only [List.length_replicate] using lengths
  have added : pack width xs + pack width zs = mask width xs.length + pack width ys := by
    calc
      pack width xs + pack width zs = pack width (xs.zipWith (· + ·) zs) :=
        Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq differenceLength
      _ = pack width ((List.replicate xs.length (2 ^ (width - 1))).zipWith (· + ·) ys) :=
        congrArg (pack width) (add_difference_lists (2 ^ (width - 1)) xs ys lengths bounded)
      _ = mask width xs.length + pack width ys :=
        (Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq maskLength).symm
  change mask width xs.length + pack width ys - pack width xs = pack width zs
  omega

/-- The packed guard implies every pointwise comparison, provided the actual
full lane operands have equal length and both stay strictly below half-base.
The output relation includes every list occurrence; no outcome is omitted. -/
theorem guard_le (width : ℕ) (positive : 0 < width) (xs ys : List ℕ)
    (lengths : xs.length = ys.length)
    (xBound : ∀ x ∈ xs, x < 2 ^ (width - 1))
    (yBound : ∀ y ∈ ys, y < 2 ^ (width - 1))
    (guard : Nat.land (mask width xs.length + pack width ys - pack width xs)
      (mask width xs.length) = mask width xs.length) :
    List.Forall₂ (· ≤ ·) xs ys := by
  let zs := xs.zipWith (fun x y => 2 ^ (width - 1) + y - x) ys
  have zsLength : zs.length = xs.length := by
    simp only [zs, List.length_zipWith, lengths, Nat.min_self]
  have zsBound : ∀ z ∈ zs, z < 2 ^ width := by
    intro z member
    obtain ⟨i, inside, rfl⟩ := List.mem_iff_getElem.mp member
    have yi : i < ys.length := List.lt_length_right_of_zipWith inside
    have below := yBound ys[i] (List.getElem_mem yi)
    have double := Nat.two_pow_pred_add_two_pow_pred positive
    change (xs.zipWith (fun x y => 2 ^ (width - 1) + y - x) ys)[i] < 2 ^ width
    rw [List.getElem_zipWith]
    omega
  have normalized : mask width xs.length + pack width ys - pack width xs =
      pack width zs := no_borrow width xs ys lengths xBound
  rw [normalized] at guard
  apply List.forall₂_of_length_eq_of_get lengths
  intro i xi yi
  have zi : i < zs.length := by simpa only [zsLength] using xi
  have markerBound : ∀ d ∈ List.replicate xs.length (2 ^ (width - 1)), d < 2 ^ width := by
    intro d member
    have same : d = 2 ^ (width - 1) := List.eq_of_mem_replicate member
    rw [same]
    exact Nat.two_pow_pred_lt_two_pow positive
  have markerBit : (mask width xs.length).testBit (width * i + (width - 1)) = true := by
    change (pack width (List.replicate xs.length (2 ^ (width - 1)))).testBit
      (width * i + (width - 1)) = true
    rw [testBit_pack_lane width positive _ markerBound i
      (by simpa only [List.length_replicate] using xi)]
    simp only [List.getElem_replicate, Nat.testBit_two_pow_self]
  have packedBit : (pack width zs).testBit (width * i + (width - 1)) = true := by
    have bits := congrArg (fun n : ℕ => n.testBit (width * i + (width - 1))) guard
    change ((pack width zs) &&& (mask width xs.length)).testBit
      (width * i + (width - 1)) =
        (mask width xs.length).testBit (width * i + (width - 1)) at bits
    simpa only [Nat.testBit_and, markerBit, Bool.and_true] using bits
  have digitBit : zs[i].testBit (width - 1) = true :=
    (testBit_pack_lane width positive zs zsBound i zi).symm.trans packedBit
  have large : 2 ^ (width - 1) ≤ zs[i] := Nat.ge_two_pow_of_testBit digitBit
  have digitEq : zs[i] = 2 ^ (width - 1) + ys[i] - xs[i] := by
    simp only [zs, List.getElem_zipWith]
  have compared : xs[i] ≤ ys[i] := by
    rw [digitEq] at large
    have below := xBound xs[i] (List.getElem_mem xi)
    omega
  simpa only [List.get_eq_getElem] using compared

#print axioms testBit_pack_lane
#print axioms guard_le
end D5.S0.Certificates.FinitePackedLaneGuard
