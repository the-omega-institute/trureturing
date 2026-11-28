/- GID: D5/S3/Arith/ResidueRings/MesyanDomainCommutativity
   generality: I
   mirror-B: D5/B/S3/Arith/ResidueRings/MesyanDomainCommutativity
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.Submonoid.Pointwise]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/ResidueRings/MesyanDomainCommutativity.claim; result=D5/S3/Arith/ResidueRings/MesyanDomainCommutativity.result; claim=D5/S3/Arith/ResidueRings/MesyanDomainCommutativity.claim
   digest: A noncommutative domain has a commutative additive-submonoid quantale. -/

module

public import Mathlib.Algebra.Ring.Submonoid.Pointwise
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Ring.WithZero
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import OmegaBuild.Commands

/-!
Adjoining an external zero to Mesyan's Example 6 over the field of three
elements gives a counterexample to the domain equivalence in Question 34.
-/

compile_only_with_mathlib

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Pointwise

namespace D5.S3.Arith.ResidueRings.MesyanDomainCommutativity

/-- The domain clause of Mesyan's Question 34. -/
@[expose] def claim : Prop :=
  ∀ (R : Type) [NonUnitalSemiring R] [Nontrivial R] [NoZeroDivisors R],
    (∀ x y : R, x * y = y * x) ↔
      (∀ A B : AddSubmonoid R, A * B = B * A)

private def ExampleSix := ZMod 3 × ZMod 3 × ZMod 3

private instance : AddCommMonoid ExampleSix :=
  inferInstanceAs (AddCommMonoid (ZMod 3 × ZMod 3 × ZMod 3))

private def tripleMul (x y : ExampleSix) : ExampleSix :=
  let (a, b, _) := x
  let (d, e, _) := y
  (0, 0, a * e - b * d)

private instance : Semigroup ExampleSix where
  mul := tripleMul
  mul_assoc := by
    rintro ⟨a, b, c⟩ ⟨d, e, f⟩ ⟨g, h, i⟩
    change (0, 0, 0 * h - 0 * g) = (0, 0, a * 0 - b * 0)
    simp

private instance : Distrib ExampleSix where
  left_distrib := by
    rintro ⟨a, b, c⟩ ⟨d, e, f⟩ ⟨g, h, i⟩
    change (0, 0, a * (e + h) - b * (d + g)) =
      (0, 0, (a * e - b * d) + (a * h - b * g))
    congr 2
    ring
  right_distrib := by
    rintro ⟨a, b, c⟩ ⟨d, e, f⟩ ⟨g, h, i⟩
    change (0, 0, (a + d) * h - (b + e) * g) =
      (0, 0, (a * h - b * g) + (d * h - e * g))
    congr 2
    ring

private instance : NonUnitalSemiring (WithZero ExampleSix) where
  __ := (inferInstance : AddCommMonoid (WithZero ExampleSix))
  __ := (inferInstance : SemigroupWithZero (WithZero ExampleSix))
  __ := (inferInstance : Distrib (WithZero ExampleSix))

private abbrev Counterexample := WithZero ExampleSix

private def leftGenerator : Counterexample := some (1, 0, 0)

private def rightGenerator : Counterexample := some (0, 1, 0)

private theorem generators_do_not_commute :
    leftGenerator * rightGenerator ≠ rightGenerator * leftGenerator := by
  change (some (0, 0, 1) : Counterexample) ≠ some (0, 0, 2)
  intro h
  exact (by decide : (1 : ZMod 3) ≠ 2)
    (congrArg (fun x : ZMod 3 × ZMod 3 × ZMod 3 => x.2.2) (Option.some.inj h))

private theorem reverse_mul (x y : Counterexample) : y * x = 2 • (x * y) := by
  rw [two_nsmul]
  rcases x with _ | ⟨a, b, c⟩ <;> rcases y with _ | ⟨d, e, f⟩
  · rfl
  · rfl
  · rfl
  · change (some (0, 0, d * b - e * a) : Counterexample) =
      some (0, 0, (a * e - b * d) + (a * e - b * d))
    congr 3
    calc
      d * b - e * a = -1 * (a * e - b * d) := by ring
      _ = 2 * (a * e - b * d) := by rw [show (-1 : ZMod 3) = 2 by decide]
      _ = (a * e - b * d) + (a * e - b * d) := two_mul _

/-- The zero adjoined to Example 6 over the field of three elements gives a
domain with noncommuting elements and commuting additive submonoids. -/
theorem result : ¬ claim := by
  intro h
  have inclusion (A B : AddSubmonoid Counterexample) : A * B ≤ B * A :=
    AddSubmonoid.mul_le.2 fun x hx y hy => by
      rw [reverse_mul y x]
      exact (B * A).nsmul_mem (AddSubmonoid.mul_mem_mul hy hx) 2
  have commuteSubmonoids (A B : AddSubmonoid Counterexample) : A * B = B * A :=
    le_antisymm (inclusion A B) (inclusion B A)
  exact generators_do_not_commute ((h Counterexample).2 commuteSubmonoids
    leftGenerator rightGenerator)

end D5.S3.Arith.ResidueRings.MesyanDomainCommutativity
