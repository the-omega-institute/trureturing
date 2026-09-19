/- GID: D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation
   generality: I
   mirror-B: D5/B/S3/ArithUnits/SharmaPrimitivePolynomialRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.fullClaim; result=D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.result; claim=D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.fullClaim
   digest: The p=41 dense root certificate refutes the full multiplicative primitive-polynomial conjecture. -/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import LeanInformationAudit.RegistrationWitnesses
import LeanInformationAudit.Syntax
import LeanInformationAudit.SealCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithUnits.SharmaPrimitivePolynomialRefutation

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
open LeanInformationAudit

universe u

/- The source notion is the minimal polynomial of a multiplicative generator in
   a degree-p extension.  It is deliberately separate from
   `Polynomial.IsPrimitive`, whose meaning is coefficient content. -/
def SourcePrimitivePolynomial (p : ℕ) {K : Type} [Field K] [Fintype K]
    (f : Polynomial K) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : Fintype L) (_ : Algebra K L), ∃ α : L,
    Module.finrank K L = p ∧
      minpoly K α = f ∧
      orderOf α = Fintype.card L - 1

def PrimitiveLambda {K : Type} [Monoid K] [Fintype K] (lam : K) : Prop :=
  orderOf lam = Fintype.card K - 1

def SourceLeadingCoefficient : Fin 2 := 1

noncomputable def sourcePolynomial {p : ℕ} {K : Type} [Semiring K]
    (c : Fin 2) (lam : K) : Polynomial K :=
  Polynomial.C (c.val : K) * Polynomial.X ^ p + Polynomial.X + Polynomial.C lam

def claimFor (c : Fin 2) : Prop :=
  ∀ (p : ℕ), p.Prime → Odd p →
    ∀ (K : Type) [Field K] [Fintype K] [CharP K p],
      Fintype.card K = p ^ 2 →
      ∀ lam : K, PrimitiveLambda lam →
        SourcePrimitivePolynomial p (sourcePolynomial (p := p) c lam)

def fullClaim : Prop := claimFor SourceLeadingCoefficient

def publicResult : Prop := ¬ claimFor SourceLeadingCoefficient

abbrev QuadraticField41 := QuadraticAlgebra (ZMod 41) 3 0

instance quadraticField41_prime : Fact (Nat.Prime 41) := ⟨by norm_num⟩

instance quadraticField41_nonsquare :
    Fact (∀ r : ZMod 41, r ^ 2 ≠ (3 : ZMod 41) + 0 * r) :=
  ⟨by decide⟩

local instance quadraticField41_fintype : Fintype QuadraticField41 :=
  Fintype.ofEquiv (ZMod 41 × ZMod 41)
    (QuadraticAlgebra.equivProd 3 0).symm

def lambda41 : QuadraticField41 := ⟨5, 1⟩

def certificateCoefficients : List QuadraticField41 :=
  [⟨-18, -5⟩, ⟨10, 3⟩, ⟨-1, -11⟩, ⟨-3, 12⟩, ⟨-13, -3⟩,
    ⟨-10, 3⟩, ⟨8, -12⟩, ⟨19, 10⟩, ⟨-12, 15⟩, ⟨6, 7⟩,
    ⟨13, 17⟩, ⟨-18, -4⟩, ⟨-13, -1⟩, ⟨2, -19⟩, ⟨-7, 13⟩,
    ⟨-11, -3⟩, ⟨-5, 16⟩, ⟨-18, -10⟩, ⟨7, 9⟩, ⟨-13, 9⟩,
    ⟨-15, 7⟩, ⟨-10, 18⟩, ⟨8, -9⟩, ⟨6, -18⟩, ⟨18, 13⟩,
    ⟨-10, 15⟩, ⟨14, -14⟩, ⟨9, 1⟩, ⟨15, 16⟩, ⟨9, 6⟩,
    ⟨4, -3⟩, ⟨-15, -6⟩, ⟨-16, -2⟩, ⟨-3, -20⟩, ⟨13, 9⟩,
    ⟨-10, -18⟩, ⟨6, 13⟩, ⟨-20, -20⟩, ⟨-2, 1⟩, ⟨4, 16⟩,
    ⟨19, -12⟩]


def certificateN : ℕ := 1681 ^ 41 - 1

noncomputable def certificatePolynomial : Polynomial QuadraticField41 :=
  certificateCoefficients.foldr (fun a p => Polynomial.C a + Polynomial.X * p) 0

/- Coefficient lists are in ascending degree order.  The executable product
   below is checked in the kernel; its interpretation is ordinary Horner
   evaluation through the given coefficient homomorphism. -/
private def coeffAdd : List QuadraticField41 → List QuadraticField41 → List QuadraticField41
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a + b) :: coeffAdd as bs

private def coeffMul : List QuadraticField41 → List QuadraticField41 → List QuadraticField41
  | [], _ => []
  | a :: as, b => coeffAdd (b.map (a * ·)) (0 :: coeffMul as b)

private def coeffEval {L : Type} [CommRing L] (f : QuadraticField41 →+* L)
    (x : L) : List QuadraticField41 → L
  | [] => 0
  | a :: as => f a + x * coeffEval f x as

private theorem coeffEval_add {L : Type} [CommRing L]
    (f : QuadraticField41 →+* L) (x : L) (a b : List QuadraticField41) :
    coeffEval f x (coeffAdd a b) = coeffEval f x a + coeffEval f x b := by
  induction a generalizing b with
  | nil => simp [coeffAdd, coeffEval]
  | cons a as ih =>
    cases b with
    | nil => simp [coeffAdd, coeffEval]
    | cons b bs => simp only [coeffAdd, coeffEval, map_add, ih]; ring

private theorem coeffEval_scale {L : Type} [CommRing L]
    (f : QuadraticField41 →+* L) (x : L) (c : QuadraticField41)
    (a : List QuadraticField41) :
    coeffEval f x (a.map (c * ·)) = f c * coeffEval f x a := by
  induction a with
  | nil => simp [coeffEval]
  | cons a as ih => simp only [List.map_cons, coeffEval, map_mul, ih]; ring

private theorem coeffEval_mul {L : Type} [CommRing L]
    (f : QuadraticField41 →+* L) (x : L) (a b : List QuadraticField41) :
    coeffEval f x (coeffMul a b) = coeffEval f x a * coeffEval f x b := by
  induction a with
  | nil => simp [coeffMul, coeffEval]
  | cons a as ih =>
    simp only [coeffMul, coeffEval_add, coeffEval_scale, coeffEval, map_zero, ih]
    ring

private theorem coeffEval_append {L : Type} [CommRing L]
    (f : QuadraticField41 →+* L) (x : L) (a b : List QuadraticField41) :
    coeffEval f x (a ++ b) = coeffEval f x a + x ^ a.length * coeffEval f x b := by
  induction a with
  | nil => simp [coeffEval]
  | cons a as ih => simp only [List.cons_append, coeffEval, List.length_cons, ih, pow_succ]; ring

private theorem coeffEval_zeros {L : Type} [CommRing L]
    (f : QuadraticField41 →+* L) (x : L) (n : ℕ) :
    coeffEval f x (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, coeffEval, ih]

private def coeffModulus (a : List QuadraticField41) : List QuadraticField41 :=
  coeffAdd (a.map (lambda41 * ·))
    (coeffAdd (0 :: a) (List.replicate 41 0 ++ a))

private def chain2 : List QuadraticField41 :=
  [⟨-16, -7⟩, ⟨8, 5⟩, ⟨-7, -19⟩, ⟨19, 1⟩, ⟨20, -15⟩,
    ⟨-12, 16⟩, ⟨-9, -18⟩, ⟨9, -15⟩, ⟨15, 15⟩, ⟨6, -11⟩,
    ⟨11, 8⟩, ⟨-19, 0⟩, ⟨10, -17⟩, ⟨-10, -9⟩, ⟨-20, -16⟩,
    ⟨-14, -7⟩, ⟨-4, -12⟩, ⟨-20, 17⟩, ⟨0, 14⟩, ⟨-3, -3⟩,
    ⟨-20, 1⟩, ⟨10, -11⟩, ⟨20, -3⟩, ⟨18, 16⟩, ⟨19, 19⟩,
    ⟨18, 17⟩, ⟨0, -11⟩, ⟨-18, -3⟩, ⟨19, 19⟩, ⟨-5, 13⟩,
    ⟨-2, 16⟩, ⟨-5, 17⟩, ⟨-12, 3⟩, ⟨12, -5⟩, ⟨14, 1⟩,
    ⟨17, 10⟩, ⟨17, 1⟩, ⟨-5, 8⟩, ⟨7, -10⟩, ⟨-6, -17⟩,
    ⟨-19, -2⟩]

private def quotient2 : List QuadraticField41 :=
  [⟨-2, 5⟩, ⟨-18, 1⟩, ⟨7, -3⟩, ⟨-5, 7⟩, ⟨-6, 9⟩,
    ⟨-16, 2⟩, ⟨-11, 5⟩, ⟨8, 0⟩, ⟨-10, 18⟩, ⟨5, 8⟩,
    ⟨11, -1⟩, ⟨-12, -12⟩, ⟨-10, -20⟩, ⟨15, -4⟩, ⟨-14, -7⟩,
    ⟨-2, 12⟩, ⟨0, -19⟩, ⟨-8, 2⟩, ⟨15, 14⟩, ⟨4, 17⟩,
    ⟨15, 20⟩, ⟨11, -13⟩, ⟨-2, -4⟩, ⟨17, 9⟩, ⟨-3, -1⟩,
    ⟨20, -1⟩, ⟨-5, 5⟩, ⟨-13, -17⟩, ⟨-15, -13⟩, ⟨-8, -20⟩,
    ⟨0, 3⟩, ⟨0, 6⟩, ⟨16, -6⟩, ⟨20, -2⟩, ⟨-1, 15⟩,
    ⟨7, -3⟩, ⟨-19, -8⟩, ⟨-20, 9⟩, ⟨-16, 20⟩, ⟨14, -5⟩]

private def chain3 : List QuadraticField41 :=
  [⟨-15, 8⟩, ⟨-1, 10⟩, ⟨20, -13⟩, ⟨19, -6⟩, ⟨2, 11⟩,
    ⟨9, -13⟩, ⟨1, -10⟩, ⟨4, 1⟩, ⟨19, -14⟩, ⟨-17, -18⟩,
    ⟨9, 5⟩, ⟨-19, -7⟩, ⟨3, 6⟩, ⟨-17, -2⟩, ⟨-17, 0⟩,
    ⟨-12, -5⟩, ⟨-12, -12⟩, ⟨16, -16⟩, ⟨5, 4⟩, ⟨-14, 0⟩,
    ⟨20, -3⟩, ⟨4, 16⟩, ⟨-20, 17⟩, ⟨5, 14⟩, ⟨-9, 19⟩,
    ⟨-3, 19⟩, ⟨-10, -19⟩, ⟨3, 7⟩, ⟨-19, -6⟩, ⟨-11, 20⟩,
    ⟨-13, -10⟩, ⟨-5, -4⟩, ⟨3, -3⟩, ⟨19, 4⟩, ⟨4, 0⟩,
    ⟨-19, 19⟩, ⟨-8, 20⟩, ⟨-15, 0⟩, ⟨15, -18⟩, ⟨-17, 20⟩,
    ⟨-19, 18⟩]

private def quotient3 : List QuadraticField41 :=
  [⟨-20, 19⟩, ⟨-2, -14⟩, ⟨-2, -15⟩, ⟨14, 15⟩, ⟨5, 6⟩,
    ⟨7, 15⟩, ⟨13, -14⟩, ⟨-11, 14⟩, ⟨12, 14⟩, ⟨-15, 14⟩,
    ⟨2, -1⟩, ⟨10, 13⟩, ⟨-20, -15⟩, ⟨-13, -6⟩, ⟨4, -19⟩,
    ⟨-8, 6⟩, ⟨14, -11⟩, ⟨-9, -5⟩, ⟨8, -14⟩, ⟨-10, 19⟩,
    ⟨17, 0⟩, ⟨-17, -14⟩, ⟨-3, 13⟩, ⟨-5, 20⟩, ⟨-19, 2⟩,
    ⟨5, 19⟩, ⟨13, 3⟩, ⟨0, 7⟩, ⟨0, 10⟩, ⟨3, 12⟩,
    ⟨-6, -20⟩, ⟨15, 10⟩, ⟨8, -19⟩, ⟨-1, -16⟩, ⟨8, -9⟩,
    ⟨-3, -5⟩, ⟨-5, -6⟩, ⟨13, -2⟩, ⟨-2, 11⟩, ⟨-2, -15⟩]

private def chain5 : List QuadraticField41 :=
  [⟨18, 20⟩, ⟨-2, 6⟩, ⟨-19, -7⟩, ⟨-11, -10⟩, ⟨3, -1⟩,
    ⟨-18, -20⟩, ⟨0, -9⟩, ⟨7, -4⟩, ⟨-13, 1⟩, ⟨15, 4⟩,
    ⟨18, -9⟩, ⟨-18, 0⟩, ⟨-11, -15⟩, ⟨13, -10⟩, ⟨11, -8⟩,
    ⟨-8, 3⟩, ⟨-3, 17⟩, ⟨-20, 16⟩, ⟨-5, 6⟩, ⟨11, -16⟩,
    ⟨2, 11⟩, ⟨14, 0⟩, ⟨-14, 6⟩, ⟨3, 3⟩, ⟨-14, -10⟩,
    ⟨13, -8⟩, ⟨9, 12⟩, ⟨-9, -2⟩, ⟨12, -19⟩, ⟨20, 14⟩,
    ⟨-19, -14⟩, ⟨10, 11⟩, ⟨9, 15⟩, ⟨5, 8⟩, ⟨0, -5⟩,
    ⟨-19, 3⟩, ⟨19, 20⟩, ⟨-4, 8⟩, ⟨9, 6⟩, ⟨7, 18⟩,
    ⟨19, 12⟩]

private def quotient5 : List QuadraticField41 :=
  [⟨20, 12⟩, ⟨-1, 13⟩, ⟨12, -3⟩, ⟨-9, -3⟩, ⟨5, 20⟩,
    ⟨-15, -8⟩, ⟨20, 16⟩, ⟨-14, -20⟩, ⟨-7, 7⟩, ⟨3, -2⟩,
    ⟨-15, 6⟩, ⟨-8, 10⟩, ⟨-8, 15⟩, ⟨6, 15⟩, ⟨5, 17⟩,
    ⟨-11, -18⟩, ⟨17, 5⟩, ⟨4, -1⟩, ⟨16, -5⟩, ⟨-6, 7⟩,
    ⟨9, -2⟩, ⟨5, -12⟩, ⟨16, -18⟩, ⟨-7, 0⟩, ⟨18, -11⟩,
    ⟨7, 1⟩, ⟨15, 19⟩, ⟨-19, 8⟩, ⟨16, 2⟩, ⟨-18, 12⟩,
    ⟨-9, 10⟩, ⟨15, -12⟩, ⟨-4, 11⟩, ⟨18, 3⟩, ⟨4, 0⟩,
    ⟨-3, -6⟩, ⟨19, -8⟩, ⟨-5, 18⟩, ⟨14, -8⟩, ⟨7, -17⟩]

private def chain10 : List QuadraticField41 :=
  [⟨-6, 12⟩, ⟨-4, -16⟩, ⟨0, 4⟩, ⟨9, -11⟩, ⟨-17, 0⟩,
    ⟨3, -13⟩, ⟨-20, -18⟩, ⟨-4, 1⟩, ⟨-5, -3⟩, ⟨-16, -16⟩,
    ⟨-18, -2⟩, ⟨-6, -12⟩, ⟨10, -17⟩, ⟨16, 13⟩, ⟨-5, 20⟩,
    ⟨-14, 10⟩, ⟨-1, -8⟩, ⟨11, 2⟩, ⟨-6, -1⟩, ⟨11, -1⟩,
    ⟨4, 19⟩, ⟨-13, 0⟩, ⟨5, -1⟩, ⟨17, 9⟩, ⟨-14, 10⟩,
    ⟨-17, 11⟩, ⟨18, -16⟩, ⟨-12, -13⟩, ⟨12, 11⟩, ⟨8, 7⟩,
    ⟨-15, -11⟩, ⟨-3, -17⟩, ⟨-11, -9⟩, ⟨-3, 9⟩, ⟨13, 2⟩,
    ⟨0, -11⟩, ⟨3, 18⟩, ⟨-8, 1⟩, ⟨-12, -18⟩, ⟨18, -14⟩,
    ⟨18, -2⟩]

private def quotient10 : List QuadraticField41 :=
  [⟨-6, -13⟩, ⟨-9, 2⟩, ⟨4, 4⟩, ⟨13, 12⟩, ⟨12, 14⟩,
    ⟨-7, -8⟩, ⟨2, -3⟩, ⟨15, -3⟩, ⟨-11, -2⟩, ⟨12, 4⟩,
    ⟨15, 6⟩, ⟨-4, -10⟩, ⟨-12, 8⟩, ⟨-5, -12⟩, ⟨-8, -17⟩,
    ⟨0, -2⟩, ⟨11, 15⟩, ⟨6, -3⟩, ⟨-16, -6⟩, ⟨-5, -2⟩,
    ⟨16, 4⟩, ⟨-1, 9⟩, ⟨-20, 19⟩, ⟨-6, -6⟩, ⟨3, 20⟩,
    ⟨18, -18⟩, ⟨18, 16⟩, ⟨-12, -8⟩, ⟨19, 20⟩, ⟨-19, -15⟩,
    ⟨-12, 11⟩, ⟨15, -15⟩, ⟨-20, -4⟩, ⟨-16, 20⟩, ⟨4, -20⟩,
    ⟨2, -20⟩, ⟨9, 1⟩, ⟨-9, -1⟩, ⟨4, -9⟩, ⟨14, 5⟩]

private def chain20 : List QuadraticField41 :=
  [⟨-2, -12⟩, ⟨-4, 16⟩, ⟨18, -10⟩, ⟨-20, -12⟩, ⟨-18, -13⟩,
    ⟨3, -19⟩, ⟨-18, 9⟩, ⟨-14, 16⟩, ⟨-14, -20⟩, ⟨-1, -4⟩,
    ⟨-14, -8⟩, ⟨-16, -2⟩, ⟨9, -3⟩, ⟨19, -8⟩, ⟨-9, 4⟩,
    ⟨6, 7⟩, ⟨-10, -4⟩, ⟨4, -1⟩, ⟨-17, -3⟩, ⟨4, -19⟩,
    ⟨8, 9⟩, ⟨-9, 11⟩, ⟨14, -13⟩, ⟨-10, -2⟩, ⟨16, -14⟩,
    ⟨-6, 1⟩, ⟨-8, -18⟩, ⟨9, -3⟩, ⟨-10, -17⟩, ⟨7, -6⟩,
    ⟨7, -19⟩, ⟨13, -2⟩, ⟨-5, 10⟩, ⟨-18, 17⟩, ⟨15, 10⟩,
    ⟨18, -5⟩, ⟨12, 16⟩, ⟨15, -11⟩, ⟨7, 13⟩, ⟨-13, -2⟩,
    ⟨-13, 5⟩]

private def quotient20 : List QuadraticField41 :=
  [⟨13, 12⟩, ⟨8, 12⟩, ⟨-4, 0⟩, ⟨-18, 20⟩, ⟨17, 13⟩,
    ⟨6, 13⟩, ⟨-17, 4⟩, ⟨-9, -17⟩, ⟨2, -4⟩, ⟨-6, 8⟩,
    ⟨14, 16⟩, ⟨-1, 13⟩, ⟨-8, 13⟩, ⟨-3, -15⟩, ⟨20, 12⟩,
    ⟨1, -2⟩, ⟨3, -17⟩, ⟨9, -6⟩, ⟨8, -15⟩, ⟨-12, 18⟩,
    ⟨-4, 10⟩, ⟨19, -10⟩, ⟨10, 0⟩, ⟨15, -5⟩, ⟨-7, -3⟩,
    ⟨9, 16⟩, ⟨16, -6⟩, ⟨2, 7⟩, ⟨-4, 9⟩, ⟨-4, -4⟩,
    ⟨17, -17⟩, ⟨14, 19⟩, ⟨20, -15⟩, ⟨-7, 11⟩, ⟨1, -19⟩,
    ⟨-20, 16⟩, ⟨1, 2⟩, ⟨-1, 3⟩, ⟨-4, -2⟩, ⟨8, 10⟩]

private def chain40 : List QuadraticField41 :=
  [⟨16, 20⟩, ⟨5, 11⟩, ⟨6, 16⟩, ⟨14, 0⟩, ⟨-13, 1⟩,
    ⟨17, -17⟩, ⟨-13, 20⟩, ⟨2, 17⟩, ⟨18, -3⟩, ⟨-19, -12⟩,
    ⟨-11, 11⟩, ⟨-10, 16⟩, ⟨-17, 11⟩, ⟨-5, -7⟩, ⟨-6, -3⟩,
    ⟨2, 13⟩, ⟨9, -17⟩, ⟨10, 17⟩, ⟨14, -12⟩, ⟨-14, -17⟩,
    ⟨17, -2⟩, ⟨5, -11⟩, ⟨19, 8⟩, ⟨20, -20⟩, ⟨-7, -20⟩,
    ⟨-5, 2⟩, ⟨-8, -3⟩, ⟨13, 0⟩, ⟨-7, 4⟩, ⟨-5, -5⟩,
    ⟨12, 3⟩, ⟨-13, -13⟩, ⟨6, 18⟩, ⟨6, 16⟩, ⟨19, 15⟩,
    ⟨-19, 11⟩, ⟨7, -20⟩, ⟨6, -8⟩, ⟨2, 6⟩, ⟨-19, -18⟩,
    ⟨18, 10⟩]

private def quotient40 : List QuadraticField41 :=
  [⟨-9, -9⟩, ⟨7, -20⟩, ⟨-19, -1⟩, ⟨-3, 8⟩, ⟨-3, 5⟩,
    ⟨20, 5⟩, ⟨16, -10⟩, ⟨-13, -16⟩, ⟨4, 11⟩, ⟨16, 0⟩,
    ⟨0, -14⟩, ⟨10, -13⟩, ⟨-17, -12⟩, ⟨-16, -15⟩, ⟨-3, -18⟩,
    ⟨5, -1⟩, ⟨8, 11⟩, ⟨19, 11⟩, ⟨3, 6⟩, ⟨14, 18⟩,
    ⟨-5, -5⟩, ⟨11, 6⟩, ⟨-19, -3⟩, ⟨12, 15⟩, ⟨10, 9⟩,
    ⟨-16, -18⟩, ⟨1, 9⟩, ⟨10, -18⟩, ⟨12, 19⟩, ⟨-12, 11⟩,
    ⟨18, 15⟩, ⟨-19, 16⟩, ⟨3, 0⟩, ⟨-11, -10⟩, ⟨-7, 0⟩,
    ⟨15, -11⟩, ⟨8, -12⟩, ⟨20, -11⟩, ⟨-9, 4⟩, ⟨-2, -7⟩]

private def chain80 : List QuadraticField41 :=
  [⟨0, 6⟩, ⟨2, -6⟩, ⟨-13, 14⟩, ⟨7, -4⟩, ⟨-2, 16⟩,
    ⟨10, -6⟩, ⟨11, -14⟩, ⟨12, -7⟩, ⟨-3, -12⟩, ⟨17, -8⟩,
    ⟨10, 4⟩, ⟨15, -17⟩, ⟨18, 19⟩, ⟨2, 6⟩, ⟨-12, 16⟩,
    ⟨-10, -2⟩, ⟨-17, 11⟩, ⟨-9, -13⟩, ⟨-1, -11⟩, ⟨17, -18⟩,
    ⟨7, 19⟩, ⟨20, -11⟩, ⟨14, 20⟩, ⟨-3, -7⟩, ⟨-18, -10⟩,
    ⟨-15, 8⟩, ⟨9, 19⟩, ⟨-4, 7⟩, ⟨4, 20⟩, ⟨-13, -14⟩,
    ⟨-19, 18⟩, ⟨-13, -17⟩, ⟨-10, 15⟩, ⟨-17, 3⟩, ⟨-9, 15⟩,
    ⟨-5, -11⟩, ⟨0, -15⟩, ⟨20, 4⟩, ⟨-17, 5⟩, ⟨-11, 16⟩,
    ⟨12, -11⟩]

private def quotient80 : List QuadraticField41 :=
  [⟨-9, -19⟩, ⟨17, -11⟩, ⟨1, -17⟩, ⟨-17, 14⟩, ⟨18, 1⟩,
    ⟨-2, -19⟩, ⟨-6, 0⟩, ⟨-10, -4⟩, ⟨-1, 19⟩, ⟨-10, -18⟩,
    ⟨-4, -12⟩, ⟨-15, -1⟩, ⟨-15, 20⟩, ⟨-9, -3⟩, ⟨15, -8⟩,
    ⟨-2, 19⟩, ⟨9, 16⟩, ⟨-20, -7⟩, ⟨-3, -14⟩, ⟨-15, 5⟩,
    ⟨-8, 15⟩, ⟨-20, 18⟩, ⟨6, 18⟩, ⟨-5, -5⟩, ⟨14, 2⟩,
    ⟨-5, 1⟩, ⟨8, 1⟩, ⟨-18, -9⟩, ⟨1, -16⟩, ⟨-5, 8⟩,
    ⟨-19, -5⟩, ⟨-2, 19⟩, ⟨-7, 13⟩, ⟨-2, -13⟩, ⟨7, -10⟩,
    ⟨5, -17⟩, ⟨-4, -17⟩, ⟨2, -3⟩, ⟨-1, -3⟩, ⟨9, -9⟩]

private def chain83 : List QuadraticField41 :=
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩,
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩,
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩,
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩,
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩,
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩,
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩,
    ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩,
    ⟨0, 0⟩]

private def quotient83 : List QuadraticField41 :=
  [⟨4, 14⟩, ⟨9, -1⟩, ⟨4, 15⟩, ⟨1, -7⟩, ⟨9, -19⟩,
    ⟨-18, 16⟩, ⟨18, 8⟩, ⟨3, 9⟩, ⟨-1, -16⟩, ⟨-4, -18⟩,
    ⟨15, -14⟩, ⟨5, 11⟩, ⟨9, -19⟩, ⟨-1, 3⟩, ⟨4, -16⟩,
    ⟨-17, -18⟩, ⟨-14, -14⟩, ⟨18, -15⟩, ⟨20, 10⟩, ⟨9, -8⟩,
    ⟨0, 4⟩, ⟨-3, -2⟩, ⟨4, 11⟩, ⟨-11, -10⟩, ⟨-7, 11⟩,
    ⟨-5, -6⟩, ⟨16, 19⟩, ⟨3, -16⟩, ⟨-16, 13⟩, ⟨-18, -4⟩,
    ⟨-6, 0⟩, ⟨7, 3⟩, ⟨9, -16⟩, ⟨20, 17⟩, ⟨-6, 6⟩,
    ⟨-17, 20⟩, ⟨-5, 11⟩, ⟨13, -3⟩, ⟨4, 7⟩, ⟨-2, 15⟩]

/- The certificate is evaluated at roots of the coefficient-dependent
   source polynomial; no coefficient equality is inserted into this law. -/
def denseCertificateIdentityFor (c : Fin 2) : Prop :=
  ∀ (L : Type) (_ : Field L) (_ : Algebra QuadraticField41 L) (α : L),
    Polynomial.aeval α (sourcePolynomial (p := 41) c lambda41) = 0 →
      (Polynomial.aeval α certificatePolynomial) ^ 83 = α

def fullCounterexampleLaw (c : Fin 2) : Prop :=
  (sourcePolynomial (p := 41) c lambda41).natDegree = 41 ∧
    denseCertificateIdentityFor c ∧ ¬ claimFor c

private theorem certificate_evaluation (L : Type) [Field L]
    [Algebra QuadraticField41 L] (α : L)
    (hroot : Polynomial.aeval α
      (sourcePolynomial (p := 41) SourceLeadingCoefficient lambda41) = 0) :
    (Polynomial.aeval α certificatePolynomial) ^ 83 = α := by
  have chain2_checked :
      coeffMul certificateCoefficients certificateCoefficients =
        coeffAdd chain2 (coeffModulus quotient2) := by
    decide +kernel
  have chain3_checked :
      coeffMul chain2 certificateCoefficients = coeffAdd chain3 (coeffModulus quotient3) := by
    decide +kernel
  have chain5_checked :
      coeffMul chain3 chain2 = coeffAdd chain5 (coeffModulus quotient5) := by
    decide +kernel
  have chain10_checked :
      coeffMul chain5 chain5 = coeffAdd chain10 (coeffModulus quotient10) := by
    decide +kernel
  have chain20_checked :
      coeffMul chain10 chain10 = coeffAdd chain20 (coeffModulus quotient20) := by
    decide +kernel
  have chain40_checked :
      coeffMul chain20 chain20 = coeffAdd chain40 (coeffModulus quotient40) := by
    decide +kernel
  have chain80_checked :
      coeffMul chain40 chain40 = coeffAdd chain80 (coeffModulus quotient80) := by
    decide +kernel
  have chain83_checked :
      coeffMul chain80 chain3 = coeffAdd chain83 (coeffModulus quotient83) := by
    decide +kernel
  let f := algebraMap QuadraticField41 L
  have hrel : α ^ 41 + α + f lambda41 = 0 := by
    simpa [sourcePolynomial, SourceLeadingCoefficient, f] using hroot
  have step (a b c q : List QuadraticField41)
      (h : coeffMul a b = coeffAdd c (coeffModulus q)) :
      coeffEval f α a * coeffEval f α b = coeffEval f α c := by
    have hm : coeffEval f α (coeffModulus q) =
        (α ^ 41 + α + f lambda41) * coeffEval f α q := by
      simp only [coeffModulus, coeffEval_add, coeffEval_scale, coeffEval_append,
        coeffEval_zeros, List.length_replicate, coeffEval, map_zero]
      ring
    rw [← coeffEval_mul, h, coeffEval_add, hm, hrel, zero_mul, add_zero]
  let z := coeffEval f α certificateCoefficients
  have h2 : coeffEval f α chain2 = z ^ 2 := by
    simpa only [pow_two] using (step _ _ _ _ chain2_checked).symm
  have h3 : coeffEval f α chain3 = z ^ 3 := by
    rw [← step _ _ _ _ chain3_checked, h2]
    exact (pow_succ z 2).symm
  have h5 : coeffEval f α chain5 = z ^ 5 := by
    rw [← step _ _ _ _ chain5_checked, h3, h2, ← pow_add]
  have h10 : coeffEval f α chain10 = z ^ 10 := by
    rw [← step _ _ _ _ chain10_checked, h5, ← pow_add]
  have h20 : coeffEval f α chain20 = z ^ 20 := by
    rw [← step _ _ _ _ chain20_checked, h10, ← pow_add]
  have h40 : coeffEval f α chain40 = z ^ 40 := by
    rw [← step _ _ _ _ chain40_checked, h20, ← pow_add]
  have h80 : coeffEval f α chain80 = z ^ 80 := by
    rw [← step _ _ _ _ chain80_checked, h40, ← pow_add]
  have h83 : coeffEval f α chain83 = z ^ 83 := by
    rw [← step _ _ _ _ chain83_checked, h80, h3, ← pow_add]
  have hend : coeffEval f α chain83 = α := by
    have hzero : (⟨0, 0⟩ : QuadraticField41) = 0 := rfl
    have hone : (⟨1, 0⟩ : QuadraticField41) = 1 := rfl
    simp [chain83, coeffEval, hzero, hone]
  have heval (a : List QuadraticField41) :
      Polynomial.aeval α
        (a.foldr (fun c p => Polynomial.C c + Polynomial.X * p) 0) =
      coeffEval f α a := by
    induction a with
    | nil => simp [coeffEval]
    | cons a as ih => simp [coeffEval, ih, f]
  rw [certificatePolynomial, heval]
  exact h83.symm.trans hend

theorem result : ¬ claimFor SourceLeadingCoefficient := by
  have quadraticField41_card : Fintype.card QuadraticField41 = 1681 := by
    rw [Fintype.card_congr (QuadraticAlgebra.equivProd 3 0)]
    simp
  have lambda41_pow_1680 : lambda41 ^ 1680 = 1 := by
    have h2 : lambda41 ^ 2 = ⟨-13, 10⟩ := by decide
    have h4 : lambda41 ^ 4 = ⟨18, -14⟩ := by
      calc
        lambda41 ^ 4 = (lambda41 ^ 2) ^ 2 := by rw [← pow_mul]
        _ = ⟨18, -14⟩ := by rw [h2]; decide
    have h8 : lambda41 ^ 8 = ⟨10, -12⟩ := by
      calc
        lambda41 ^ 8 = (lambda41 ^ 4) ^ 2 := by rw [← pow_mul]
        _ = ⟨10, -12⟩ := by rw [h4]; decide
    have h16 : lambda41 ^ 16 = ⟨-1, 6⟩ := by
      calc
        lambda41 ^ 16 = (lambda41 ^ 8) ^ 2 := by rw [← pow_mul]
        _ = ⟨-1, 6⟩ := by rw [h8]; decide
    have h32 : lambda41 ^ 32 = ⟨-14, -12⟩ := by
      calc
        lambda41 ^ 32 = (lambda41 ^ 16) ^ 2 := by rw [← pow_mul]
        _ = ⟨-14, -12⟩ := by rw [h16]; decide
    have h64 : lambda41 ^ 64 = ⟨13, 8⟩ := by
      calc
        lambda41 ^ 64 = (lambda41 ^ 32) ^ 2 := by rw [← pow_mul]
        _ = ⟨13, 8⟩ := by rw [h32]; decide
    have h128 : lambda41 ^ 128 = ⟨-8, 3⟩ := by
      calc
        lambda41 ^ 128 = (lambda41 ^ 64) ^ 2 := by rw [← pow_mul]
        _ = ⟨-8, 3⟩ := by rw [h64]; decide
    have h256 : lambda41 ^ 256 = ⟨9, -7⟩ := by
      calc
        lambda41 ^ 256 = (lambda41 ^ 128) ^ 2 := by rw [← pow_mul]
        _ = ⟨9, -7⟩ := by rw [h128]; decide
    have h512 : lambda41 ^ 512 = ⟨-18, -3⟩ := by
      calc
        lambda41 ^ 512 = (lambda41 ^ 256) ^ 2 := by rw [← pow_mul]
        _ = ⟨-18, -3⟩ := by rw [h256]; decide
    have h1024 : lambda41 ^ 1024 = ⟨-18, -15⟩ := by
      calc
        lambda41 ^ 1024 = (lambda41 ^ 512) ^ 2 := by rw [← pow_mul]
        _ = ⟨-18, -15⟩ := by rw [h512]; decide
    calc
      lambda41 ^ 1680 = lambda41 ^ (1024 + 512 + 128 + 16) := by norm_num
      _ = lambda41 ^ 1024 * lambda41 ^ 512 * lambda41 ^ 128 * lambda41 ^ 16 := by
        rw [pow_add, pow_add, pow_add]
      _ = 1 := by rw [h1024, h512, h128, h16]; decide
  have lambda41_pow_840 : lambda41 ^ 840 = -1 := by
    rw [show 840 = 512 + 256 + 64 + 8 by norm_num, pow_add, pow_add, pow_add]
    have h2 : lambda41 ^ 2 = ⟨-13, 10⟩ := by decide
    have h4 : lambda41 ^ 4 = ⟨18, -14⟩ := by
      calc lambda41 ^ 4 = (lambda41 ^ 2) ^ 2 := by rw [← pow_mul]
        _ = ⟨18, -14⟩ := by rw [h2]; decide
    have h8 : lambda41 ^ 8 = ⟨10, -12⟩ := by
      calc lambda41 ^ 8 = (lambda41 ^ 4) ^ 2 := by rw [← pow_mul]
        _ = ⟨10, -12⟩ := by rw [h4]; decide
    have h16 : lambda41 ^ 16 = ⟨-1, 6⟩ := by
      calc lambda41 ^ 16 = (lambda41 ^ 8) ^ 2 := by rw [← pow_mul]
        _ = ⟨-1, 6⟩ := by rw [h8]; decide
    have h32 : lambda41 ^ 32 = ⟨-14, -12⟩ := by
      calc lambda41 ^ 32 = (lambda41 ^ 16) ^ 2 := by rw [← pow_mul]
        _ = ⟨-14, -12⟩ := by rw [h16]; decide
    have h64 : lambda41 ^ 64 = ⟨13, 8⟩ := by
      calc lambda41 ^ 64 = (lambda41 ^ 32) ^ 2 := by rw [← pow_mul]
        _ = ⟨13, 8⟩ := by rw [h32]; decide
    have h128 : lambda41 ^ 128 = ⟨-8, 3⟩ := by
      calc lambda41 ^ 128 = (lambda41 ^ 64) ^ 2 := by rw [← pow_mul]
        _ = ⟨-8, 3⟩ := by rw [h64]; decide
    have h256 : lambda41 ^ 256 = ⟨9, -7⟩ := by
      calc lambda41 ^ 256 = (lambda41 ^ 128) ^ 2 := by rw [← pow_mul]
        _ = ⟨9, -7⟩ := by rw [h128]; decide
    have h512 : lambda41 ^ 512 = ⟨-18, -3⟩ := by
      calc lambda41 ^ 512 = (lambda41 ^ 256) ^ 2 := by rw [← pow_mul]
        _ = ⟨-18, -3⟩ := by rw [h256]; decide
    rw [h512, h256, h64, h8]
    decide
  have lambda41_pow_560 : lambda41 ^ 560 = ⟨20, 16⟩ := by
    rw [show 560 = 512 + 32 + 16 by norm_num, pow_add, pow_add]
    have h2 : lambda41 ^ 2 = ⟨-13, 10⟩ := by decide
    have h4 : lambda41 ^ 4 = ⟨18, -14⟩ := by
      calc lambda41 ^ 4 = (lambda41 ^ 2) ^ 2 := by rw [← pow_mul]
        _ = ⟨18, -14⟩ := by rw [h2]; decide
    have h8 : lambda41 ^ 8 = ⟨10, -12⟩ := by
      calc lambda41 ^ 8 = (lambda41 ^ 4) ^ 2 := by rw [← pow_mul]
        _ = ⟨10, -12⟩ := by rw [h4]; decide
    have h16 : lambda41 ^ 16 = ⟨-1, 6⟩ := by
      calc lambda41 ^ 16 = (lambda41 ^ 8) ^ 2 := by rw [← pow_mul]
        _ = ⟨-1, 6⟩ := by rw [h8]; decide
    have h32 : lambda41 ^ 32 = ⟨-14, -12⟩ := by
      calc lambda41 ^ 32 = (lambda41 ^ 16) ^ 2 := by rw [← pow_mul]
        _ = ⟨-14, -12⟩ := by rw [h16]; decide
    have h256 : lambda41 ^ 256 = ⟨9, -7⟩ := by
      have h64 : lambda41 ^ 64 = ⟨13, 8⟩ := by
        calc lambda41 ^ 64 = (lambda41 ^ 32) ^ 2 := by rw [← pow_mul]
          _ = ⟨13, 8⟩ := by rw [h32]; decide
      have h128 : lambda41 ^ 128 = ⟨-8, 3⟩ := by
        calc lambda41 ^ 128 = (lambda41 ^ 64) ^ 2 := by rw [← pow_mul]
          _ = ⟨-8, 3⟩ := by rw [h64]; decide
      calc lambda41 ^ 256 = (lambda41 ^ 128) ^ 2 := by rw [← pow_mul]
        _ = ⟨9, -7⟩ := by rw [h128]; decide
    rw [show 512 = 256 + 256 by norm_num, pow_add, h256, h32]
    decide
  have lambda41_pow_336 : lambda41 ^ 336 = ⟨37, 0⟩ := by
    rw [show 336 = 256 + 64 + 16 by norm_num, pow_add, pow_add]
    have h2 : lambda41 ^ 2 = ⟨-13, 10⟩ := by decide
    have h4 : lambda41 ^ 4 = ⟨18, -14⟩ := by
      calc lambda41 ^ 4 = (lambda41 ^ 2) ^ 2 := by rw [← pow_mul]
        _ = ⟨18, -14⟩ := by rw [h2]; decide
    have h8 : lambda41 ^ 8 = ⟨10, -12⟩ := by
      calc lambda41 ^ 8 = (lambda41 ^ 4) ^ 2 := by rw [← pow_mul]
        _ = ⟨10, -12⟩ := by rw [h4]; decide
    have h16 : lambda41 ^ 16 = ⟨-1, 6⟩ := by
      calc lambda41 ^ 16 = (lambda41 ^ 8) ^ 2 := by rw [← pow_mul]
        _ = ⟨-1, 6⟩ := by rw [h8]; decide
    have h32 : lambda41 ^ 32 = ⟨-14, -12⟩ := by
      calc lambda41 ^ 32 = (lambda41 ^ 16) ^ 2 := by rw [← pow_mul]
        _ = ⟨-14, -12⟩ := by rw [h16]; decide
    have h64 : lambda41 ^ 64 = ⟨13, 8⟩ := by
      calc lambda41 ^ 64 = (lambda41 ^ 32) ^ 2 := by rw [← pow_mul]
        _ = ⟨13, 8⟩ := by rw [h32]; decide
    rw [show 256 = 128 + 128 by norm_num, pow_add]
    have h128 : lambda41 ^ 128 = ⟨-8, 3⟩ := by
      calc lambda41 ^ 128 = (lambda41 ^ 64) ^ 2 := by rw [← pow_mul]
        _ = ⟨-8, 3⟩ := by rw [h64]; decide
    rw [h128, h64, h16]
    decide
  have lambda41_pow_240 : lambda41 ^ 240 = ⟨15, 15⟩ := by
    rw [show 240 = 128 + 64 + 32 + 16 by norm_num, pow_add, pow_add, pow_add]
    have h2 : lambda41 ^ 2 = ⟨-13, 10⟩ := by decide
    have h4 : lambda41 ^ 4 = ⟨18, -14⟩ := by
      calc lambda41 ^ 4 = (lambda41 ^ 2) ^ 2 := by rw [← pow_mul]
        _ = ⟨18, -14⟩ := by rw [h2]; decide
    have h8 : lambda41 ^ 8 = ⟨10, -12⟩ := by
      calc lambda41 ^ 8 = (lambda41 ^ 4) ^ 2 := by rw [← pow_mul]
        _ = ⟨10, -12⟩ := by rw [h4]; decide
    have h16 : lambda41 ^ 16 = ⟨-1, 6⟩ := by
      calc lambda41 ^ 16 = (lambda41 ^ 8) ^ 2 := by rw [← pow_mul]
        _ = ⟨-1, 6⟩ := by rw [h8]; decide
    have h32 : lambda41 ^ 32 = ⟨-14, -12⟩ := by
      calc lambda41 ^ 32 = (lambda41 ^ 16) ^ 2 := by rw [← pow_mul]
        _ = ⟨-14, -12⟩ := by rw [h16]; decide
    have h64 : lambda41 ^ 64 = ⟨13, 8⟩ := by
      calc lambda41 ^ 64 = (lambda41 ^ 32) ^ 2 := by rw [← pow_mul]
        _ = ⟨13, 8⟩ := by rw [h32]; decide
    have h128 : lambda41 ^ 128 = ⟨-8, 3⟩ := by
      calc lambda41 ^ 128 = (lambda41 ^ 64) ^ 2 := by rw [← pow_mul]
        _ = ⟨-8, 3⟩ := by rw [h64]; decide
    rw [h128, h64, h32, h16]
    decide
  have lambda41_is_primitive : PrimitiveLambda lambda41 := by
    have h2 : lambda41 ^ (1680 / 2) ≠ 1 := by
      rw [show 1680 / 2 = 840 by norm_num, lambda41_pow_840]
      decide
    have h3 : lambda41 ^ (1680 / 3) ≠ 1 := by
      rw [show 1680 / 3 = 560 by norm_num, lambda41_pow_560]
      decide
    have h5 : lambda41 ^ (1680 / 5) ≠ 1 := by
      rw [show 1680 / 5 = 336 by norm_num, lambda41_pow_336]
      decide
    have h7 : lambda41 ^ (1680 / 7) ≠ 1 := by
      rw [show 1680 / 7 = 240 by norm_num, lambda41_pow_240]
      decide
    have ho : orderOf lambda41 = 1680 := by
      apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) lambda41_pow_1680
      intro q hq hqd
      rw [show (1680 : ℕ) = ((16 * 3) * 5) * 7 by norm_num] at hqd
      rcases hq.dvd_mul.mp hqd with hqA | hq7
      · rcases hq.dvd_mul.mp hqA with hqB | hq5
        · rcases hq.dvd_mul.mp hqB with hq16 | hq3
          · have hqpow : q ∣ 2 ^ 4 := by simpa using hq16
            have hq2 : q ∣ 2 := hq.dvd_of_dvd_pow hqpow
            have hqeq : q = 2 := by
              rcases (Nat.dvd_prime Nat.prime_two).mp hq2 with rfl | rfl
              · exact (hq.ne_one rfl).elim
              · rfl
            simpa [hqeq] using h2
          · have hqeq : q = 3 := by
              rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hq3 with rfl | rfl
              · exact (hq.ne_one rfl).elim
              · rfl
            simpa [hqeq] using h3
        · have hqeq : q = 5 := by
            rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hq5 with rfl | rfl
            · exact (hq.ne_one rfl).elim
            · rfl
          simpa [hqeq] using h5
      · have hqeq : q = 7 := by
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hq7 with rfl | rfl
          · exact (hq.ne_one rfl).elim
          · rfl
        simpa [hqeq] using h7
    calc
      orderOf lambda41 = 1680 := ho
      _ = Fintype.card QuadraticField41 - 1 := by rw [quadraticField41_card]
  letI : CharP QuadraticField41 41 :=
    charP_of_injective_algebraMap' (ZMod 41) 41
  intro hclaim
  have hs : SourcePrimitivePolynomial 41
      (sourcePolynomial (p := 41) SourceLeadingCoefficient lambda41) := by
    apply hclaim 41 (by norm_num) (by decide) QuadraticField41
    · rw [quadraticField41_card]
      norm_num
    · exact lambda41_is_primitive
  rcases hs with ⟨L, hField, hFintype, hAlg, α, hdegree, hminpoly, horder⟩
  letI : Field L := hField
  letI : Fintype L := hFintype
  letI : Algebra QuadraticField41 L := hAlg
  letI : Module.Finite QuadraticField41 L := Module.Finite.of_finite
  have hcard : Fintype.card L = 1681 ^ 41 := by
    have h := Module.natCard_eq_pow_finrank (K := QuadraticField41) (V := L)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      quadraticField41_card, hdegree] at h
    exact h
  have hroot : Polynomial.aeval α
      (sourcePolynomial (p := 41) SourceLeadingCoefficient lambda41) = 0 := by
    rw [← hminpoly]
    exact minpoly.aeval QuadraticField41 α
  have hα : α ≠ 0 := by
    intro hzero
    subst α
    have hz : (0 : ℕ) = Fintype.card L - 1 := by simpa using horder
    rw [hcard] at hz
    norm_num [certificateN] at hz
  let z := Polynomial.aeval α certificatePolynomial
  have hz : z ^ 83 = α := certificate_evaluation L α hroot
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hα
    rw [← hz, hz0, zero_pow]
    norm_num
  have hcardpos : 0 < Fintype.card L := Fintype.card_pos
  have hzcard : z ^ (Fintype.card L - 1) = 1 := by
    rw [pow_sub₀ z hz0 (by omega : 1 ≤ Fintype.card L), FiniteField.pow_card]
    simpa only [pow_one] using mul_inv_cancel₀ hz0
  have certificateN_divisible_by_83 : 83 ∣ certificateN := by
    norm_num [certificateN]

  have certificateN_division_strict :
      0 < certificateN / 83 ∧ certificateN / 83 < certificateN := by
    norm_num [certificateN]
  have hobs : α ^ (certificateN / 83) = 1 := by
    calc
      α ^ (certificateN / 83) = (z ^ 83) ^ (certificateN / 83) := by rw [hz]
      _ = z ^ (83 * (certificateN / 83)) := by rw [pow_mul]
      _ = z ^ certificateN := by rw [Nat.mul_div_cancel' certificateN_divisible_by_83]
      _ = z ^ (Fintype.card L - 1) := by rw [hcard]; rfl
      _ = 1 := hzcard
  have hdvd : orderOf α ∣ certificateN / 83 := orderOf_dvd_iff_pow_eq_one.mpr hobs
  rw [horder, hcard] at hdvd
  have hle : certificateN ≤ certificateN / 83 := by
    apply Nat.le_of_dvd
    · exact certificateN_division_strict.1
    · simpa [certificateN] using hdvd
  exact (Nat.not_lt_of_ge hle) certificateN_division_strict.2

private def sourceCoefficientRealization (f : Fin 2 → Fin 2) :
    PrimitiveRealization (cutSignature (Fin 2) (Fin 2)) :=
  ⟨fun _ => f, Fin.elim0⟩

register_information_template sourceCoefficientRealization

def actualSourceCoefficientRealization :
    PrimitiveRealization (cutSignature (Fin 2) (Fin 2)) :=
  sourceCoefficientRealization (fun c => c)

def alternateSourceCoefficientRealization :
    PrimitiveRealization (cutSignature (Fin 2) (Fin 2)) :=
  sourceCoefficientRealization (fun _ => 0)

def sourceCounterexampleArena : PrimitiveLawArena where
  toArena := Arena.ofFintype (Fin 2)
  signature := cutSignature (Fin 2) (Fin 2)
  Law r :=
    fullCounterexampleLaw (r.readout () SourceLeadingCoefficient)

private theorem sourceCoefficient_variation :
    FiniteLawVariation sourceCounterexampleArena := by
  refine ⟨actualSourceCoefficientRealization, alternateSourceCoefficientRealization, ?_, ?_⟩
  · change fullCounterexampleLaw SourceLeadingCoefficient
    refine ⟨?_, ?_, result⟩
    · norm_num [sourcePolynomial, SourceLeadingCoefficient]
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow 41
      · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
        norm_num
    · intro L _ _ α hroot
      exact certificate_evaluation L α hroot
  · intro h
    change fullCounterexampleLaw (0 : Fin 2) at h
    have hd := h.1
    norm_num [sourcePolynomial] at hd

private theorem sourceCoefficient_sensitivity :
    FiniteSlotSensitivity sourceCounterexampleArena := by
  constructor
  · intro i
    cases i
    obtain ⟨r, r', hr, hr'⟩ := sourceCoefficient_variation
    refine ⟨r, r', ?_, ?_, ?_⟩
    · intro j hne
      exact (hne rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => hr', fun _ => hr⟩
  · intro i
    exact Fin.elim0 i

register_information_theorem result in sourceCounterexampleArena
  readout via (sourceCoefficientRealization (fun c : Fin 2 => c))
  primitives actualSourceCoefficientRealization.toPrimitiveBundle
  realization inline actualSourceCoefficientRealization := (by
    constructor
    change (¬ claimFor SourceLeadingCoefficient) ↔ fullCounterexampleLaw SourceLeadingCoefficient
    constructor
    · intro hresult
      refine ⟨?_, ?_, hresult⟩
      · norm_num [sourcePolynomial, SourceLeadingCoefficient]
        rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
        · exact Polynomial.natDegree_X_pow 41
        · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
          norm_num
      · intro L _ _ α hroot
        exact certificate_evaluation L α hroot
    · exact fun h => h.2.2)
  variation sourceCoefficient_variation sensitivity sourceCoefficient_sensitivity
  escape from (SourceLeadingCoefficient) escape continues (open)

end D5.S3.ArithUnits.SharmaPrimitivePolynomialRefutation
