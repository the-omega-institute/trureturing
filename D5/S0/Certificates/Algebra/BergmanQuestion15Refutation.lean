/- GID: D5/S0/Certificates/Algebra/BergmanQuestion15Refutation
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/BergmanQuestion15Refutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Finsupp.LSum, mathlib/module/Mathlib.Algebra.Group.PNatPowAssoc, mathlib/module/Mathlib.RingTheory.RootsOfUnity.Complex]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.claim; result=D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.result; claim=D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.claim
   digest: Bergman's Question 15 fails in a contracted commutative semigroup algebra. -/

/- proof_shape: result: bind-only
   admission_basis: open-problem-resolution (issue #15095)
   escape_witness: none
   Direct frozen dependencies: none. -/
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.Span
import Mathlib.Algebra.Group.PNatPowAssoc
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

namespace D5.S0.Certificates.Algebra.BergmanQuestion15Refutation

universe u v

open scoped IsMulCommutative

/-- The contracted vector space has exactly the nonzero semigroup elements as basis. -/
abbrev Contracted (F : Type v) (S : Type u) [Zero S] [Zero F] := {s : S // s ≠ 0} →₀ F

/-- The zero semigroup element is the zero vector, rather than a basis vector. -/
noncomputable def delta (F : Type v) (S : Type u) [Zero S] [Field F]
    (s : S) : Contracted F S :=
  by
    classical
    exact if h : s = 0 then 0 else Finsupp.single ⟨s, h⟩ 1

/-- Bilinear extension of the contracted basis multiplication. -/
noncomputable def product (F : Type v) (S : Type u) [Zero S] [Mul S] [Field F] :
    Contracted F S →ₗ[F] Contracted F S →ₗ[F] Contracted F S :=
  Finsupp.llift (S := F) (M := Contracted F S →ₗ[F] Contracted F S)
    (R := F) (X := {s : S // s ≠ 0}) (fun s =>
      Finsupp.llift (S := F) (M := Contracted F S) (R := F)
        (X := {s : S // s ≠ 0}) (fun t => delta F S (s.val * t.val)))

noncomputable instance contractedMul (F : Type v) (S : Type u)
    [Zero S] [Mul S] [Field F] : Mul (Contracted F S) := ⟨fun f g => product F S f g⟩

noncomputable instance contractedDistrib (F : Type v) (S : Type u)
    [Zero S] [Mul S] [Field F] : Distrib (Contracted F S) where
  left_distrib f g h := (product F S f).map_add g h
  right_distrib f g h := by
    change (product F S (f + g)) h = _
    exact congrArg (fun k : Contracted F S →ₗ[F] Contracted F S => k h)
      ((product F S).map_add f g)

noncomputable instance contractedZeroMul (F : Type v) (S : Type u)
    [Zero S] [Mul S] [Field F] : MulZeroClass (Contracted F S) where
  zero_mul f := by change product F S 0 f = 0; simp
  mul_zero f := (product F S f).map_zero

noncomputable instance contractedCommRing (F : Type v) (S : Type u)
    [SemigroupWithZero S] [IsMulCommutative S] [Field F] :
    NonUnitalCommRing (Contracted F S) where
  mul_assoc f g h := by
    classical
    have singleProduct (a b : {s : S // s ≠ 0}) (r t : F) :
        (Finsupp.single a r : Contracted F S) * Finsupp.single b t =
          (r * t) • delta F S (a.val * b.val) := by
      simp [HMul.hMul, Mul.mul, product, Finsupp.llift, Finsupp.lift_apply, smul_smul]
    have deltaProduct (a b : S) :
        delta F S a * delta F S b = delta F S (a * b) := by
      by_cases ha : a = 0
      · simp [ha, delta]
      by_cases hb : b = 0
      · simp [hb, delta]
      simp only [delta, dif_neg ha, dif_neg hb, singleProduct, one_mul, one_smul]
    have smul_left (r : F) (a b : Contracted F S) : (r • a) * b = r • (a * b) := by
      change product F S (r • a) b = _
      rw [map_smul, LinearMap.smul_apply]
      rfl
    have smul_right (r : F) (a b : Contracted F S) : a * (r • b) = r • (a * b) :=
      (product F S a).map_smul r b
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [add_mul, hf, hg]
    | single a r =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [mul_add, add_mul, hf, hg]
      | single b t =>
        induction h using Finsupp.induction_linear with
        | zero => simp
        | add f g hf hg => simp only [mul_add, hf, hg]
        | single c q =>
          rw [singleProduct, singleProduct]
          have da : (Finsupp.single a r : Contracted F S) = r • delta F S a.val := by
            simp [delta, a.property, Finsupp.smul_single]
          have dc : (Finsupp.single c q : Contracted F S) = q • delta F S c.val := by
            simp [delta, c.property, Finsupp.smul_single]
          rw [da, dc, smul_left, smul_right, smul_right, smul_left,
            deltaProduct, deltaProduct, smul_smul, smul_smul]
          simp only [mul_assoc, mul_left_comm, mul_comm]
  mul_comm f g := by
    classical
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [add_mul, mul_add, hf, hg]
    | single a r =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp only [mul_add, add_mul, hf, hg]
      | single b t =>
        simp [HMul.hMul, Mul.mul, product, Finsupp.llift, Finsupp.lift_apply,
          smul_smul]
        change (r * t) • delta F S (a.val * b.val) =
          (t * r) • delta F S (b.val * a.val)
        rw [mul_comm r t, mul_comm a.val b.val]

/-- A positive power uses a nonempty product, with no multiplicative identity. -/
def positivePower {A : Type*} [Mul A] (a : A) : ℕ → A
  | 0 => a
  | n + 1 => positivePower a n * a

/-- The literal universal assertion in Question 15. The natural index is n−1. -/
def claim : Prop :=
  ∀ (S : Type) [SemigroupWithZero S] [IsMulCommutative S]
    (F : Type) [Field F] [CharZero F] (X : Set S), X.Finite →
    ∀ n : ℕ,
      Set.InjOn (fun s => positivePower s n) X →
      (∀ s ∈ X, s ≠ 0 → positivePower s n ≠ 0) →
      ∀ w ∈ Submodule.span F (delta F S '' X),
        w ≠ 0 → positivePower w n ≠ 0

/-- The 59 class labels: zero, 55 monomials of degrees 1–5, and A,B,C. -/
structure Model where
  val : Fin 59
  deriving DecidableEq, Fintype

instance modelOfNat (n : ℕ) : OfNat Model n :=
  ⟨⟨⟨n % 59, Nat.mod_lt _ (by decide)⟩⟩⟩

instance modelZero : Zero Model := ⟨⟨0⟩⟩

/-- Positive exponent representatives for the singleton classes. -/
def exponents : Model → ℕ × ℕ × ℕ
  | ⟨⟨0, _⟩⟩ => (0, 0, 0)
  | ⟨⟨1, _⟩⟩ => (1, 0, 0)
  | ⟨⟨2, _⟩⟩ => (0, 1, 0)
  | ⟨⟨3, _⟩⟩ => (0, 0, 1)
  | ⟨⟨4, _⟩⟩ => (2, 0, 0)
  | ⟨⟨5, _⟩⟩ => (1, 1, 0)
  | ⟨⟨6, _⟩⟩ => (1, 0, 1)
  | ⟨⟨7, _⟩⟩ => (0, 2, 0)
  | ⟨⟨8, _⟩⟩ => (0, 1, 1)
  | ⟨⟨9, _⟩⟩ => (0, 0, 2)
  | ⟨⟨10, _⟩⟩ => (3, 0, 0)
  | ⟨⟨11, _⟩⟩ => (2, 1, 0)
  | ⟨⟨12, _⟩⟩ => (2, 0, 1)
  | ⟨⟨13, _⟩⟩ => (1, 2, 0)
  | ⟨⟨14, _⟩⟩ => (1, 1, 1)
  | ⟨⟨15, _⟩⟩ => (1, 0, 2)
  | ⟨⟨16, _⟩⟩ => (0, 3, 0)
  | ⟨⟨17, _⟩⟩ => (0, 2, 1)
  | ⟨⟨18, _⟩⟩ => (0, 1, 2)
  | ⟨⟨19, _⟩⟩ => (0, 0, 3)
  | ⟨⟨20, _⟩⟩ => (4, 0, 0)
  | ⟨⟨21, _⟩⟩ => (3, 1, 0)
  | ⟨⟨22, _⟩⟩ => (3, 0, 1)
  | ⟨⟨23, _⟩⟩ => (2, 2, 0)
  | ⟨⟨24, _⟩⟩ => (2, 1, 1)
  | ⟨⟨25, _⟩⟩ => (2, 0, 2)
  | ⟨⟨26, _⟩⟩ => (1, 3, 0)
  | ⟨⟨27, _⟩⟩ => (1, 2, 1)
  | ⟨⟨28, _⟩⟩ => (1, 1, 2)
  | ⟨⟨29, _⟩⟩ => (1, 0, 3)
  | ⟨⟨30, _⟩⟩ => (0, 4, 0)
  | ⟨⟨31, _⟩⟩ => (0, 3, 1)
  | ⟨⟨32, _⟩⟩ => (0, 2, 2)
  | ⟨⟨33, _⟩⟩ => (0, 1, 3)
  | ⟨⟨34, _⟩⟩ => (0, 0, 4)
  | ⟨⟨35, _⟩⟩ => (5, 0, 0)
  | ⟨⟨36, _⟩⟩ => (4, 1, 0)
  | ⟨⟨37, _⟩⟩ => (4, 0, 1)
  | ⟨⟨38, _⟩⟩ => (3, 2, 0)
  | ⟨⟨39, _⟩⟩ => (3, 1, 1)
  | ⟨⟨40, _⟩⟩ => (3, 0, 2)
  | ⟨⟨41, _⟩⟩ => (2, 3, 0)
  | ⟨⟨42, _⟩⟩ => (2, 2, 1)
  | ⟨⟨43, _⟩⟩ => (2, 1, 2)
  | ⟨⟨44, _⟩⟩ => (2, 0, 3)
  | ⟨⟨45, _⟩⟩ => (1, 4, 0)
  | ⟨⟨46, _⟩⟩ => (1, 3, 1)
  | ⟨⟨47, _⟩⟩ => (1, 2, 2)
  | ⟨⟨48, _⟩⟩ => (1, 1, 3)
  | ⟨⟨49, _⟩⟩ => (1, 0, 4)
  | ⟨⟨50, _⟩⟩ => (0, 5, 0)
  | ⟨⟨51, _⟩⟩ => (0, 4, 1)
  | ⟨⟨52, _⟩⟩ => (0, 3, 2)
  | ⟨⟨53, _⟩⟩ => (0, 2, 3)
  | ⟨⟨54, _⟩⟩ => (0, 1, 4)
  | ⟨⟨55, _⟩⟩ => (0, 0, 5)
  | ⟨⟨56, _⟩⟩ => (6, 0, 0)
  | ⟨⟨57, _⟩⟩ => (0, 6, 0)
  | ⟨⟨58, _⟩⟩ => (0, 0, 6)
  | _ => (0, 0, 0)

/-- The three exact retained terminal classes; all other monomials are zero. -/
def label : ℕ × ℕ × ℕ → Model
  | (1, 0, 0) => 1
  | (0, 1, 0) => 2
  | (0, 0, 1) => 3
  | (2, 0, 0) => 4
  | (1, 1, 0) => 5
  | (1, 0, 1) => 6
  | (0, 2, 0) => 7
  | (0, 1, 1) => 8
  | (0, 0, 2) => 9
  | (3, 0, 0) => 10
  | (2, 1, 0) => 11
  | (2, 0, 1) => 12
  | (1, 2, 0) => 13
  | (1, 1, 1) => 14
  | (1, 0, 2) => 15
  | (0, 3, 0) => 16
  | (0, 2, 1) => 17
  | (0, 1, 2) => 18
  | (0, 0, 3) => 19
  | (4, 0, 0) => 20
  | (3, 1, 0) => 21
  | (3, 0, 1) => 22
  | (2, 2, 0) => 23
  | (2, 1, 1) => 24
  | (2, 0, 2) => 25
  | (1, 3, 0) => 26
  | (1, 2, 1) => 27
  | (1, 1, 2) => 28
  | (1, 0, 3) => 29
  | (0, 4, 0) => 30
  | (0, 3, 1) => 31
  | (0, 2, 2) => 32
  | (0, 1, 3) => 33
  | (0, 0, 4) => 34
  | (5, 0, 0) => 35
  | (4, 1, 0) => 36
  | (4, 0, 1) => 37
  | (3, 2, 0) => 38
  | (3, 1, 1) => 39
  | (3, 0, 2) => 40
  | (2, 3, 0) => 41
  | (2, 2, 1) => 42
  | (2, 1, 2) => 43
  | (2, 0, 3) => 44
  | (1, 4, 0) => 45
  | (1, 3, 1) => 46
  | (1, 2, 2) => 47
  | (1, 1, 3) => 48
  | (1, 0, 4) => 49
  | (0, 5, 0) => 50
  | (0, 4, 1) => 51
  | (0, 3, 2) => 52
  | (0, 2, 3) => 53
  | (0, 1, 4) => 54
  | (0, 0, 5) => 55
  | (6, 0, 0) => 56
  | (3, 3, 0) => 56
  | (5, 1, 0) => 56
  | (5, 0, 1) => 56
  | (2, 4, 0) => 56
  | (4, 2, 0) => 56
  | (0, 6, 0) => 57
  | (0, 3, 3) => 57
  | (0, 5, 1) => 57
  | (1, 5, 0) => 57
  | (0, 2, 4) => 57
  | (0, 4, 2) => 57
  | (0, 0, 6) => 58
  | (3, 0, 3) => 58
  | (1, 0, 5) => 58
  | (0, 1, 5) => 58
  | (4, 0, 2) => 58
  | (2, 0, 4) => 58
  | _ => 0

/-- Addition of exponent triples, with terminal elements absorbing into zero. -/
def modelMul (a b : Model) : Model :=
  if a.val.val = 0 ∨ b.val.val = 0 ∨ 56 ≤ a.val.val ∨ 56 ≤ b.val.val then 0 else
    label ( (exponents a).1 + (exponents b).1,
      (exponents a).2.1 + (exponents b).2.1,
      (exponents a).2.2 + (exponents b).2.2 )

/-- Six-bit row-major encoding of the exact 59-element multiplication table. -/
private def multiplicationTable : ℕ :=
  0x3aeba000000000000000000000000000000000000000000000000000000000000000000000000000000000000eb9000000000000000000000000000000000000000000000000000000000000000000000000000000000000039e40000000000000000000000000000000000000000000000000000000000000000000000000000000000000e79000000000000000000000000000000000000000000000000000000000000000000000000000000000000039e40000000000000000000000000000000000000000000000000000000000000000000000000000000000000e79e4000000000000000000000000000000000000000000000000000000000000000000000000000000000003a03a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e78000000000000000000000000000000000000000000000000000000000000000000000000000000000000e80e80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e38000000000000000000000000000000000000000000000000000000000000000000000000000000000000e80e80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000038e0000000000000000000000000000000000000000000000000000000000000000000000000000000000003a038000000000000000000000000000000000000000000000000000000000000000000000000000000000000038e00000000000000000000000000000000000000000000000000000000000000000000000000000000000038e38000000000000000000000000000000000000000000000000000000000000000000000000000ebae7a03adf6c4000000000000000000000000000000000000000000000000000000000000000000000000003ae79000036d70000000000000000000000000000000000000000000000000000000000000000000000000000e79e40000d74bc0000000000000000000000000000000000000000000000000000000000000000000000000039e79000034cee000000000000000000000000000000000000000000000000000000000000000000000000000e79e40e78cf2b4000000000000000000000000000000000000000000000000000000000000000000000000003a000e80eb1c2c000000000000000000000000000000000000000000000000000000000000000000000000000000000000c2fac000000000000000000000000000000000000000000000000000000000000000000000000000000000002fbaa000000000000000000000000000000000000000000000000000000000000000000000000000000e40e38bada4000000000000000000000000000000000000000000000000000000000000000000000000003a000e80eacae8000000000000000000000000000000000000000000000000000000000000000000000000000000000000aea9c0000000000000000000000000000000000000000000000000000000000000000000000000000038038e2aa66000000000000000000000000000000000000000000000000000000000000000000000000000e8003a038a27940000000000000000000000000000000000000000000000000000000000000000000000000000038038e279a4000000000000000000000000000000000000000000000000000000000000000000000000000e80e38e389648c000000000000000000000000000000000000000000000000000000000003aeb9e7a000e80eb7db5c70b2285d000000000000000000000000000000000000000000000000000000000000eb9e79000000000db5d30beb860700000000000000000000000000000000000000000000000000000000000039e79e40000000035d33beeaa07db000000000000000000000000000000000000000000000000000000000000e79e79000e40e38d33caeb697de68000000000000000000000000000000000000000000000000000000000003a00003a000e80eb1c2fb2ba1d719000000000000000000000000000000000000000000000000000000000000000000000000000c2fbabaa771b600000000000000000000000000000000000000000000000000000000000000000e40038038e2fbadaa999b697000000000000000000000000000000000000000000000000000000000000e80000e8003a038b2baa89e5658580000000000000000000000000000000000000000000000000000000000000000e00038038e2baa99e69185d5000000000000000000000000000000000000000000000000000000000000e80038e80e38e38a279a5923595500000000000000000000000000000000000000ebae79e7a00003a000e80eb7db5d31c2fb2ba2286075c65348f00000000000000000000000000000000000003ae79e79000000000000000db5d33c2fbabaa78607dc6d8491380000000000000000000000000000000000000e79e79e40000e40038038e35d33cafbadaa99a07de6da5d140d00000000000000000000000000000000000003a000000e80000e8003a038c70beeb2baa89e575c6d96163ce300000000000000000000000000000000000000000000e40000e00038038e30beeb6baa99e691c6da61754e34b00000000000000000000000000000000000003a000038e80038e80e38e38b2baa9a279a59236585d655430b28000003aeb9e79e7a000000e80000e8003a038df6d74cf1c2fbacaeaa279628607dd71b6585934913ce309206000000eb9e79e79000000e40000e00038038e36d74cf2c2fbadaeaa679a48607de71b6985d549140e34b20714000003a000000e7a000038e80038e80e38e38c70beeb6caeaa689e69648dd71b69961759550f38d30b286144000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

/-- Extract the exact table entry by its row and column labels. -/
def tableMul (a b : Model) : Model :=
  ⟨⟨((multiplicationTable >>> (6 * (a.val.val * 59 + b.val.val))) % 64) % 59,
    Nat.mod_lt _ (by decide)⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
instance modelSemigroup : SemigroupWithZero Model where
  mul := tableMul
  zero := 0
  mul_assoc := by
    intro a b c
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases c with ⟨c⟩
    apply (show Function.Injective Model.val from by
      rintro ⟨x⟩ ⟨y⟩ h
      cases h
      rfl)
    apply Fin.ext
    fin_cases a <;> revert b c <;> decide +kernel
  zero_mul := by decide +kernel
  mul_zero := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
instance modelCommutative : IsMulCommutative Model where
  is_comm := ⟨by
    intro a b
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    apply (show Function.Injective Model.val from by
      rintro ⟨x⟩ ⟨y⟩ h
      cases h
      rfl)
    apply Fin.ext
    fin_cases a <;> revert b <;> decide +kernel⟩


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option maxRecDepth 100000 in
/-- A literal negative answer to Bergman's Question 15. -/
theorem result : ¬ claim := by
  classical
  intro H
  let : NonUnitalCommRing (Contracted ℂ Model) := contractedCommRing ℂ Model
  let : Mul (Contracted ℂ Model) := contractedMul ℂ Model
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hζ : IsPrimitiveRoot ζ 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  have hζsum : 1 + ζ + ζ ^ 2 = 0 := by
    have h := hζ.geom_sum_eq_zero (by decide : 1 < 3)
    simpa [Finset.sum_range_succ] using h
  have hζ2 : ζ ^ 2 = -1 - ζ := by linear_combination hζsum
  let e : Model → Contracted ℂ Model := delta ℂ Model
  let w := e 1 + ζ • e 2 + ζ ^ 2 • e 3
  have e0 : e 0 = 0 := by simp [e, delta]
  have sl (r : ℂ) (a b : Contracted ℂ Model) : (r • a) * b = r • (a * b) := by
    change product ℂ Model (r • a) b = _
    rw [map_smul, LinearMap.smul_apply]
    rfl
  have sr (r : ℂ) (a b : Contracted ℂ Model) : a * (r • b) = r • (a * b) :=
    (product ℂ Model a).map_smul r b
  have sp (a b : {s : Model // s ≠ 0}) (r t : ℂ) :
      (Finsupp.single a r : Contracted ℂ Model) * Finsupp.single b t =
        (r * t) • e (a.val * b.val) := by
    change product ℂ Model (Finsupp.single a r) (Finsupp.single b t) = _
    simp [product, Finsupp.llift, Finsupp.lift_apply, smul_smul, e]
  have dm (a b : Model) : e a * e b = e (a * b) := by
    by_cases ha : a = 0
    · simp [ha, e0]
    by_cases hb : b = 0
    · simp [hb, e0]
    simp only [e, delta, dif_neg ha, dif_neg hb, sp, one_mul, one_smul]
  have tab : ∀ a b : Model, a * b = modelMul a b := by
    intro a b
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    apply (show Function.Injective Model.val from by
      rintro ⟨x⟩ ⟨y⟩ h
      cases h
      rfl)
    apply Fin.ext
    fin_cases a <;> revert b <;> decide +kernel
  have numericTab (a b : Model) : a * b = tableMul a b := rfl
  let v2 : Contracted ℂ Model :=
    (1 : ℂ) • e 4 +
    ((2 * ζ) : ℂ) • e 5 +
    ((-2 + -2 * ζ) : ℂ) • e 6 +
    ((-1 + -1 * ζ) : ℂ) • e 7 +
    (2 : ℂ) • e 8 +
    (ζ : ℂ) • e 9
  let v3 : Contracted ℂ Model :=
    (1 : ℂ) • e 10 +
    ((3 * ζ) : ℂ) • e 11 +
    ((-3 + -3 * ζ) : ℂ) • e 12 +
    ((-3 + -3 * ζ) : ℂ) • e 13 +
    (6 : ℂ) • e 14 +
    ((3 * ζ) : ℂ) • e 15 +
    (1 : ℂ) • e 16 +
    ((3 * ζ) : ℂ) • e 17 +
    ((-3 + -3 * ζ) : ℂ) • e 18 +
    (1 : ℂ) • e 19
  let v4 : Contracted ℂ Model :=
    (1 : ℂ) • e 20 +
    ((4 * ζ) : ℂ) • e 21 +
    ((-4 + -4 * ζ) : ℂ) • e 22 +
    ((-6 + -6 * ζ) : ℂ) • e 23 +
    (12 : ℂ) • e 24 +
    ((6 * ζ) : ℂ) • e 25 +
    (4 : ℂ) • e 26 +
    ((12 * ζ) : ℂ) • e 27 +
    ((-12 + -12 * ζ) : ℂ) • e 28 +
    (4 : ℂ) • e 29 +
    (ζ : ℂ) • e 30 +
    ((-4 + -4 * ζ) : ℂ) • e 31 +
    (6 : ℂ) • e 32 +
    ((4 * ζ) : ℂ) • e 33 +
    ((-1 + -1 * ζ) : ℂ) • e 34
  let v5 : Contracted ℂ Model :=
    (1 : ℂ) • e 35 +
    ((5 * ζ) : ℂ) • e 36 +
    ((-5 + -5 * ζ) : ℂ) • e 37 +
    ((-10 + -10 * ζ) : ℂ) • e 38 +
    (20 : ℂ) • e 39 +
    ((10 * ζ) : ℂ) • e 40 +
    (10 : ℂ) • e 41 +
    ((30 * ζ) : ℂ) • e 42 +
    ((-30 + -30 * ζ) : ℂ) • e 43 +
    (10 : ℂ) • e 44 +
    ((5 * ζ) : ℂ) • e 45 +
    ((-20 + -20 * ζ) : ℂ) • e 46 +
    (30 : ℂ) • e 47 +
    ((20 * ζ) : ℂ) • e 48 +
    ((-5 + -5 * ζ) : ℂ) • e 49 +
    ((-1 + -1 * ζ) : ℂ) • e 50 +
    (5 : ℂ) • e 51 +
    ((10 * ζ) : ℂ) • e 52 +
    ((-10 + -10 * ζ) : ℂ) • e 53 +
    (5 : ℂ) • e 54 +
    (ζ : ℂ) • e 55
  have h2 : w * w = v2 := by
    as_aux_lemma =>
      set_option maxHeartbeats 2000000 in
      (
        dsimp only [w, v2]
        rw [hζ2]
        simp only [mul_add, add_mul, sl, sr, dm, smul_smul, numericTab]
        simp only [tableMul, multiplicationTable, modelOfNat, modelZero,
          Nat.reduceShiftRight, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, e0, smul_zero]
        match_scalars <;> ring_nf <;> (try simp only [hζ2]) <;> ring
      )
  have h3 : v2 * w = v3 := by
    as_aux_lemma =>
      set_option maxHeartbeats 2000000 in
      (
        dsimp only [w, v2, v3]
        rw [hζ2]
        simp only [mul_add, add_mul, sl, sr, dm, smul_smul, numericTab]
        simp only [tableMul, multiplicationTable, modelOfNat, modelZero,
          Nat.reduceShiftRight, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, e0, smul_zero]
        match_scalars <;> ring_nf <;> (try simp only [hζ2]) <;> ring
      )
  have h4 : v3 * w = v4 := by
    as_aux_lemma =>
      set_option maxHeartbeats 2000000 in
      (
        dsimp only [w, v3, v4]
        rw [hζ2]
        simp only [mul_add, add_mul, sl, sr, dm, smul_smul, numericTab]
        simp only [tableMul, multiplicationTable, modelOfNat, modelZero,
          Nat.reduceShiftRight, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, e0, smul_zero]
        match_scalars <;> ring_nf <;> (try simp only [hζ2]) <;> ring
      )
  have h5 : v4 * w = v5 := by
    as_aux_lemma =>
      set_option maxHeartbeats 2000000 in
      (
        dsimp only [w, v4, v5]
        rw [hζ2]
        simp only [mul_add, add_mul, sl, sr, dm, smul_smul, numericTab]
        simp only [tableMul, multiplicationTable, modelOfNat, modelZero,
          Nat.reduceShiftRight, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, e0, smul_zero]
        match_scalars <;> ring_nf <;> (try simp only [hζ2]) <;> ring
      )
  have h6 : v5 * w = 0 := by
    as_aux_lemma =>
      set_option maxHeartbeats 2000000 in
      (
        dsimp only [w, v5]
        rw [hζ2]
        simp only [mul_add, add_mul, sl, sr, dm, smul_smul, numericTab]
        simp only [tableMul, multiplicationTable, modelOfNat, modelZero,
          Nat.reduceShiftRight, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, e0, smul_zero]
        match_scalars <;> ring_nf <;> (try simp only [hζ2]) <;> ring
      )
  have hw6 : positivePower w 5 = 0 := by
    simp only [positivePower, h2, h3, h4, h5, h6]
  let X : Set Model := {1, 2, 3}
  have hf : X.Finite := by simp [X]
  have hi : Set.InjOn (fun s : Model => positivePower s 5) X := by
    unfold Set.InjOn
    dsimp only [X]
    decide_cbv
  have hn : ∀ s ∈ X, s ≠ 0 → positivePower s 5 ≠ 0 := by
    decide_cbv
  have hwspan : w ∈ Submodule.span ℂ (delta ℂ Model '' X) := by
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.subset_span ⟨1, by simp [X], rfl⟩
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, by simp [X], rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, by simp [X], rfl⟩)
  have hw : w ≠ 0 := by
    intro he
    have hc := congrArg (fun f : Contracted ℂ Model => f ⟨1, by decide⟩) he
    have h10 : (1 : Model) ≠ 0 := by decide_cbv
    have h20 : (2 : Model) ≠ 0 := by decide_cbv
    have h30 : (3 : Model) ≠ 0 := by decide_cbv
    have h21 : (2 : Model) ≠ 1 := by decide_cbv
    have h31 : (3 : Model) ≠ 1 := by decide_cbv
    simp [w, e, delta, h10, h20, h30, Finsupp.single_apply,
      Subtype.ext_iff, h21, h31, Ne.symm h21, Ne.symm h31] at hc
  exact (H Model ℂ X hf 5 hi hn w hwspan hw) hw6

#print axioms result
#check claim
#check result

end D5.S0.Certificates.Algebra.BergmanQuestion15Refutation
