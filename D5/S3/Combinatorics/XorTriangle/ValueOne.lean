/- GID: D5/S3/Combinatorics/XorTriangle/ValueOne
   generality: G
   mirror-B: D5/B/S3/Combinatorics/XorTriangle/ValueOne
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bits, mathlib/module/Mathlib.Data.Nat.Digits.Lemmas]
   utility: none
   digest: A positive input has XOR-triangle right-edge value one exactly at powers of two. -/

import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.XorTriangle.ValueOne

/-- Adjacent XOR, with the order of the row preserved. -/
def differences : List Bool → List Bool
  | [] => []
  | [_] => []
  | b :: c :: xs => (b ^^ c) :: differences (c :: xs)

/-- The left edge of a row, read from its first element down to the apex.
The width is retained even when some edge entries are zero. -/
def leftEdge : Nat → List Bool → List Bool
  | 0, _ => []
  | k + 1, xs => xs.headD false :: leftEdge k (differences xs)

/-- The source's unpadded, most-significant-first binary row. -/
def sourceRow (n : Nat) : List Bool := n.bits.reverse

/-- Right edge from the top-right corner to the apex. Reversing the row
turns adjacent XOR's right edge into the left edge. -/
def rightEdge (row : List Bool) : List Bool := leftEdge row.length row.reverse

/-- A fixed-length most-significant-first binary word interpreted as a natural. -/
def decode (row : List Bool) : Nat := Nat.ofDigits 2 (row.reverse.map Bool.toNat)

/-- OEIS A334595, retaining all right-edge bits before decoding. -/
def a (n : Nat) : Nat := decode (rightEdge (sourceRow n))

/-- Peter Kagey's value-one conjecture, OEIS A334595, revision 18,
fourth comment. Source: https://oeis.org/A334595 (CC BY-SA 4.0).
The finite-XOR reconstruction follows the reversible-triangle relation
also used by Ilya Bogdanov, https://mathoverflow.net/a/359278 (CC BY-SA 4.0). -/
theorem result (n : Nat) (hn : 1 ≤ n) : a n = 1 ↔ ∃ k : Nat, n = 2 ^ k := by
  have dlen : ∀ xs : List Bool, (differences xs).length = xs.length - 1 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons b xs ih =>
      cases xs with
      | nil => rfl
      | cons c xs => simpa [differences] using ih
  have reconstruct : ∀ xs ys : List Bool, xs.length = ys.length →
      xs.headD false = ys.headD false → differences xs = differences ys → xs = ys := by
    intro xs
    induction xs with
    | nil =>
      intro ys hlen _ _
      exact (List.length_eq_zero_iff.mp hlen.symm).symm
    | cons b xs ih =>
      intro ys hlen hhead hdiff
      cases ys with
      | nil => simp at hlen
      | cons c ys =>
        have bc : b = c := by simpa using hhead
        subst c
        apply congrArg (List.cons b)
        cases xs with
        | nil => exact (List.length_eq_zero_iff.mp (by simpa using hlen)).symm
        | cons d xs =>
          cases ys with
          | nil => simp at hlen
          | cons e ys =>
            have hp : (b ^^ d) = (b ^^ e) ∧ differences (d :: xs) = differences (e :: ys) := by
              simpa [differences] using hdiff
            have de : d = e := by cases b <;> simpa using hp.1
            exact ih (e :: ys) (by simpa using hlen) (by simp [de]) hp.2
  have elen : ∀ k (xs : List Bool), xs.length = k → (leftEdge k xs).length = k := by
    intro k
    induction k with
    | zero => intro xs _; rfl
    | succ k ih =>
      intro xs hlen
      simp only [leftEdge, List.length_cons]
      rw [ih (differences xs) (by rw [dlen, hlen]; omega)]
  have einj : ∀ k (xs ys : List Bool), xs.length = k → ys.length = k →
      leftEdge k xs = leftEdge k ys → xs = ys := by
    intro k
    induction k with
    | zero =>
      intro xs ys hx hy _
      rw [List.length_eq_zero_iff.mp hx, List.length_eq_zero_iff.mp hy]
    | succ k ih =>
      intro xs ys hx hy he
      have hp : xs.headD false = ys.headD false ∧
          leftEdge k (differences xs) = leftEdge k (differences ys) := by
        simpa only [leftEdge, List.cons.injEq] using he
      apply reconstruct xs ys (hx.trans hy.symm) hp.1
      exact ih (differences xs) (differences ys)
        (by rw [dlen, hx]; omega) (by rw [dlen, hy]; omega) hp.2
  have unitDiff : ∀ k : Nat, differences (List.replicate (k + 1) false ++ [true]) =
      List.replicate k false ++ [true] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simpa [List.replicate_succ, differences] using congrArg (List.cons false) ih
  have unitEdge : ∀ k : Nat, leftEdge (k + 1) (List.replicate k false ++ [true]) =
      List.replicate k false ++ [true] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ, List.cons_append]
      change false :: leftEdge (k + 1) (differences (false :: (List.replicate k false ++ [true]))) =
        false :: (List.replicate k false ++ [true])
      rw [show differences (false :: (List.replicate k false ++ [true])) =
        List.replicate k false ++ [true] by simpa [List.replicate_succ] using unitDiff k]
      rw [ih]
  have unitDecode : ∀ k : Nat, decode (List.replicate k false ++ [true]) = 1 := by
    intro k
    simp [decode, List.reverse_append,
      Nat.ofDigits_cons, Nat.ofDigits_replicate_zero]
  have decInj : ∀ xs ys : List Bool, xs.length = ys.length → decode xs = decode ys → xs = ys := by
    intro xs ys hlen he
    have hm : xs.reverse.map Bool.toNat = ys.reverse.map Bool.toNat :=
      Nat.ofDigits_inj_of_len_eq (by decide) (by simpa using hlen)
        (by intro x hx; rcases List.mem_map.mp hx with ⟨b, _, rfl⟩; cases b <;> decide)
        (by intro x hx; rcases List.mem_map.mp hx with ⟨b, _, rfl⟩; cases b <;> decide) he
    have hi : Function.Injective Bool.toNat := by intro b c; cases b <;> cases c <;> simp
    exact List.reverse_injective (List.map_injective_iff.mpr hi hm)
  have bitsDigits : ∀ m : Nat, m.bits.map Bool.toNat = Nat.digits 2 m := by
    intro m
    rw [Nat.digits_two_eq_bits]
    apply List.map_congr_left
    intro b _
    cases b <;> rfl
  have bitsDecode : ∀ m : Nat, Nat.ofDigits 2 (m.bits.map Bool.toNat) = m := by
    intro m
    rw [bitsDigits, Nat.ofDigits_digits]
  have powerBits : ∀ k : Nat, (2 ^ k).bits = List.replicate k false ++ [true] := by
    intro k
    have hi : Function.Injective Bool.toNat := by intro b c; cases b <;> cases c <;> simp
    apply List.map_injective_iff.mpr hi
    rw [bitsDigits]
    have h := @Nat.digits_base_pow_mul 2 k 1 (by decide) (by decide)
    simpa using h
  have nonempty : n.bits ≠ [] := by
    intro he
    have hz := bitsDecode n
    simp [he] at hz
    omega
  let k := n.bits.length - 1
  have hlen : n.bits.length = k + 1 := by
    have : 0 < n.bits.length := List.length_pos_iff.mpr nonempty
    dsimp [k]
    omega
  simp only [a, rightEdge, sourceRow, List.length_reverse, List.reverse_reverse]
  constructor
  · intro he
    have hed : leftEdge n.bits.length n.bits = List.replicate k false ++ [true] :=
      decInj _ _ (by rw [elen _ _ rfl]; simp [hlen]) (he.trans (unitDecode k).symm)
    have heq : n.bits = List.replicate k false ++ [true] :=
      einj (k + 1) _ _ hlen (by simp) (by rw [← hlen, hed, hlen]; exact (unitEdge k).symm)
    refine ⟨k, ?_⟩
    rw [← bitsDecode n, heq]
    simp [Nat.ofDigits_append, Nat.ofDigits_replicate_zero]
  · rintro ⟨j, rfl⟩
    rw [powerBits j]
    simp only [List.length_append, List.length_replicate, List.length_singleton]
    rw [unitEdge, unitDecode]

end D5.S3.Combinatorics.XorTriangle.ValueOne
