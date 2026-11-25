/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Kernel
   generality: G
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificates)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Checker.checkPrime_sound; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Blocks05/Block0426.checked0426
   digest: Lightweight finite certificate trees and complete odd-slot checking. -/

import Init.Data.List.Lemmas

set_option autoImplicit false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

/-- Fuel bounds recursion only; the residual branch preserves exact semantics. -/
def powLoop : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, b, e, m, r => (r * b ^ e) % m
  | k + 1, b, e, m, r =>
    if e == 0 then r % m
    else powLoop k ((b * b) % m) (e / 2) m
      (if e % 2 == 1 then (r * b) % m else r)

/-- Repeated squaring with enough fuel for the finite certificate interval. -/
def powMod (a e m : Nat) : Nat := powLoop 24 (a % m) e m 1

/-- Remove at most the supplied fuel's number of copies; exhaustion returns zero. -/
def stripOne : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, n, l =>
    if n % l == 0 then stripOne k (n / l) l else n

/-- Remove the full powers of all supplied natural factors. -/
def stripAllNat (n : Nat) (ls : List Nat) : Nat :=
  ls.foldl (fun m l => stripOne 24 m l) n

/-- Returning power, complete factor support, and prime-divisor power tests. -/
def checkPrimeNat (p q : Nat) (ls : List Nat) : Bool :=
  3 ≤ p && q < p && stripAllNat (p - 1) ls == 1 &&
  powMod q (p - 1) p == 1 &&
  ls.all (fun l => powMod q ((p - 1) / l) p != 1)

/-- A finite proof tree of checked Lucas certificates. -/
inductive PrimeCertificate : Nat → Prop where
  | two : PrimeCertificate 2
  | step {p q : Nat} {ls : List Nat}
      (root : PrimeCertificate q)
      (factors : ∀ l ∈ ls, PrimeCertificate l)
      (checked : checkPrimeNat p q ls = true) : PrimeCertificate p

/-- A shared literal with its finite primality certificate. -/
structure PrimeValue where
  val : Nat
  certificate : PrimeCertificate val

/-- Remove full powers of certified factors. -/
def stripAll (n : Nat) (ls : List PrimeValue) : Nat :=
  stripAllNat n (ls.map PrimeValue.val)

/-- Check the natural data of the supplied certified values. -/
def checkPrime (p : Nat) (q : PrimeValue) (ls : List PrimeValue) : Bool :=
  checkPrimeNat p q.val (ls.map PrimeValue.val)

/-- Build a proof-tree node from a checked root and checked factor subtrees. -/
def certifyPrime {p : Nat} (q : PrimeValue) (ls : List PrimeValue)
    (h : checkPrime p q ls = true) : PrimeCertificate p :=
  .step q.certificate (by
    intro l hl
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
    exact v.certificate) h

/-- Each odd slot has either a nontrivial divisor or a prime-root certificate. -/
inductive Row where
  | c (d : Nat)
  | p (q : PrimeValue) (ls : List PrimeValue)

/-- Check every consecutive odd slot, without trusting a prime enumeration. -/
def checkRows : Nat → List Row → Bool
  | _, [] => true
  | n, .c d :: rows =>
    1 < d && d < n && n % d == 0 && checkRows (n + 2) rows
  | n, .p q ls :: rows => checkPrime n q ls && checkRows (n + 2) rows

/-- Explicit length checking prevents an omitted suffix or an empty-block shortcut. -/
def checkBlock (start count : Nat) (rows : List Row) : Bool :=
  rows.length == count && checkRows start rows

private theorem checkRows_append (start : Nat) (xs ys : List Row) :
    checkRows start (xs ++ ys) =
      (checkRows start xs && checkRows (start + 2 * xs.length) ys) := by
  induction xs generalizing start with
  | nil => simp [checkRows]
  | cons row xs ih =>
    cases row <;>
      simp [checkRows, ih, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Bool.and_assoc]

/-- Adjacent successful blocks compose without rechecking their literal rows. -/
theorem checkBlock_append {start n m : Nat} {xs ys : List Row}
    (hxs : checkBlock start n xs = true)
    (hys : checkBlock (start + 2 * n) m ys = true) :
    checkBlock start (n + m) (xs ++ ys) = true := by
  simp only [checkBlock, Bool.and_eq_true, beq_iff_eq] at hxs hys ⊢
  refine ⟨by simp [List.length_append, hxs.1, hys.1], ?_⟩
  rw [checkRows_append, hxs.1, hxs.2, hys.2]
  rfl

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
