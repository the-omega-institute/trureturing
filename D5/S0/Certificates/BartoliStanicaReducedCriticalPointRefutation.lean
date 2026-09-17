/- GID: D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.Field.MinimalAxioms, mathlib/module/Mathlib.Algebra.CharP.Two, mathlib/module/Mathlib.Data.BitVec, mathlib/module/Mathlib.Algebra.Polynomial.Derivative, mathlib/module/Mathlib.Tactic]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.claim; result=D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.result; claim=D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.claim
   digest: The fixed F32 reduced polynomial refutes Bartoli--Stănică arXiv:2608.30808v1 Conjecture 2. -/

import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.BitVec
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S0.Certificates.BartoliStanicaReducedCriticalPointRefutation

def differentialFiberSize {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (f : Polynomial K) (a b : K) : Nat :=
  (Finset.univ.filter fun x : K => f.eval (x + a) + f.eval x = b).card

def exactAPN {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (f : Polynomial K) : Prop :=
  (∀ a b : K, a ≠ 0 → differentialFiberSize f a b ≤ 2) ∧
  (∃ a b : K, a ≠ 0 ∧ differentialFiberSize f a b = 2)

def claim : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] [CharP K 2],
    ∀ m : Nat, 0 < m → Fintype.card K = 2 ^ m →
    ∀ f : Polynomial K, f.degree < (2 ^ m : Nat) →
      Function.Bijective (fun x : K => f.eval x) →
      exactAPN f → ∃ a : K, f.derivative.eval a = 0

namespace Witness

-- Binary coefficient vectors in F2[t]/(t^5+t^2+1), modulus 0b100101.
def xtime (a : BitVec 5) : BitVec 5 :=
  (a <<< 1) ^^^ (if a.getLsbD 4 then 5 else 0)

def multiply (a b : BitVec 5) : BitVec 5 :=
  (if b.getLsbD 0 then a else 0) ^^^
  (if b.getLsbD 1 then xtime a else 0) ^^^
  (if b.getLsbD 2 then xtime (xtime a) else 0) ^^^
  (if b.getLsbD 3 then xtime (xtime (xtime a)) else 0) ^^^
  (if b.getLsbD 4 then xtime (xtime (xtime (xtime a))) else 0)

def power (a : BitVec 5) : Nat → BitVec 5
  | 0 => 1
  | n + 1 => multiply (power a n) a

structure F32 where
  bits : BitVec 5
  deriving DecidableEq

instance : Fintype F32 := Fintype.ofEquiv (Fin 32)
  { toFun := fun n => F32.mk (BitVec.ofFin n)
    invFun := fun a => a.bits.toFin
    left_inv := fun _ => rfl
    right_inv := fun a => by cases a; rfl }

instance : Zero F32 := ⟨⟨0⟩⟩
instance : One F32 := ⟨⟨1⟩⟩
instance : Add F32 := ⟨fun a b => ⟨a.bits ^^^ b.bits⟩⟩
instance : Neg F32 := ⟨id⟩
instance : Mul F32 := ⟨fun a b => ⟨multiply a.bits b.bits⟩⟩
instance : Inv F32 := ⟨fun a => ⟨power a.bits 30⟩⟩

end Witness

open Polynomial Witness

-- All substantive construction and computation stays inside this negation.
theorem result : Not claim := by
  letI : Field F32 := Field.ofMinimalAxioms F32
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    ⟨⟨0⟩, ⟨1⟩, by decide⟩
  letI : CharP F32 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero (by decide) (by decide)
  have hcard : Fintype.card F32 = 2 ^ 5 := by decide +kernel
  -- Each mk numeral is a binary coefficient vector, not a field nat-cast.
  let f : Polynomial F32 :=
    monomial 0 (F32.mk 30) + monomial 1 (F32.mk 30) +
    monomial 2 (F32.mk 31) + monomial 3 (F32.mk 12) +
    monomial 4 (F32.mk 3) + monomial 5 (F32.mk 30) +
    monomial 6 (F32.mk 29) + monomial 8 (F32.mk 9) +
    monomial 9 (F32.mk 27) + monomial 10 (F32.mk 7) +
    monomial 12 (F32.mk 5) + monomial 16 (F32.mk 9) +
    monomial 17 (F32.mk 26) + monomial 18 (F32.mk 11) +
    monomial 20 (F32.mk 28) + monomial 24 (F32.mk 6)
  let values : Fin 32 → BitVec 5 :=
    ![30, 1, 14, 20, 3, 29, 11, 16, 28, 10, 27, 8, 26, 13, 5, 23,
      22, 15, 24, 4, 7, 31, 17, 12, 25, 9, 0, 21, 19, 2, 18, 6]
  have hdegree : f.degree = 24 := by
    dsimp only [f]
    compute_degree <;> decide +kernel
  have hreduced : f.degree < (2 ^ 5 : Nat) := by
    rw [hdegree]
    norm_num
  have heval : ∀ a : F32, f.eval a = F32.mk (values a.bits.toFin) := by
    simp only [f, eval_add, eval_monomial]
    decide +kernel
  have hbijective : Function.Bijective (fun a : F32 => f.eval a) := by
    have heq : (fun a : F32 => f.eval a) =
        (fun a : F32 => F32.mk (values a.bits.toFin)) := funext heval
    rw [heq]
    decide +kernel
  have hbound : ∀ a b : F32, a ≠ 0 →
      (Finset.univ.filter fun x : F32 =>
        F32.mk (values (x + a).bits.toFin) + F32.mk (values x.bits.toFin) = b).card
        ≤ 2 := by
    decide +kernel
  have hattainment :
      (Finset.univ.filter fun x : F32 =>
        F32.mk (values (x + F32.mk 1).bits.toFin) +
          F32.mk (values x.bits.toFin) = F32.mk 16) =
        {F32.mk 24, F32.mk 25} := by
    decide +kernel
  have hapn : exactAPN f := by
    constructor
    · simpa only [differentialFiberSize, heval] using hbound
    · refine ⟨F32.mk 1, F32.mk 16, by decide, ?_⟩
      simp only [differentialFiberSize, heval, hattainment]
      decide +kernel
  have hderivative : ∀ a : F32, f.derivative.eval a ≠ 0 := by
    simp only [f, derivative_add, derivative_monomial, eval_add, eval_monomial]
    decide +kernel
  intro hclaim
  obtain ⟨a, ha⟩ := hclaim F32 5 (by decide) hcard f hreduced hbijective hapn
  exact hderivative a ha

#print axioms result

run_cmd do
  let axioms ← Lean.collectAxioms ``result
  for a in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "unpermitted endpoint axiom: {a}"

end D5.S0.Certificates.BartoliStanicaReducedCriticalPointRefutation
