module
import all Init.Grind.Ring.CommSemiringAdapter
import all Init.Grind.Ring.CommSolver
import all Init.Grind.Ring.Envelope

/-!
The semiring expression interpreter and its embedding into the ring envelope.

The private arithmetic and comparison lemmas take explicit pairs. The quotient lifts
reduce on those pairs, giving the representative formulas below. The public
`of_diseq` still requires the embedding to preserve disequality for every additively
cancellative semiring: taking the two variables in a context with leaves `a` and
`b` gives `a ≠ b → toQ a ≠ toQ b`. The upstream proof calls `toQ_inj`, which
uses effectiveness of the quotient via `Q.exact`. The equivalence and the
constructions for decidable equality or an additive embedding into a commutative
group are checked in `OmegaChecks.InitBoundaries.RingEnvelopeExact`.
-/

open Lean.Grind Lean.Grind.CommRing
namespace OmegaChecks.InitPort.Alternatives

/-- Every result of the semiring interpreter already lies in the image of the embedding. -/
@[expose] public def Lean.Grind.CommRing.Expr.denoteSAsRing {α : Type u} [Semiring α] (ctx : Context α)
    (e : Expr) : Ring.OfSemiring.Q α :=
  Ring.OfSemiring.toQ (e.denoteS ctx)

public theorem Lean.Grind.CommRing.Expr.denoteAsRing_eq {α : Type u} [Semiring α] (ctx : Context α)
    (e : Expr) : Lean.Grind.CommRing.Expr.denoteSAsRing ctx e = Ring.OfSemiring.toQ (e.denoteS ctx) :=
  rfl

public theorem Lean.Grind.Ring.OfSemiring.of_eq {α : Type u} [Semiring α] (ctx : Context α)
    (lhs rhs : Expr) (h : lhs.denoteS ctx = rhs.denoteS ctx) :
    Lean.Grind.CommRing.Expr.denoteSAsRing ctx lhs = Lean.Grind.CommRing.Expr.denoteSAsRing ctx rhs :=
  congrArg Ring.OfSemiring.toQ h

section
open Std

attribute [local instance] Semiring.natCast in
public theorem Lean.Grind.Ring.OfSemiring.mk_pos {α : Type u} [Semiring α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α]
    {a₁ a₂ : α} :
    ((((0 : Nat) : α) + a₂ ≤ 0 + a₁) ∧ ¬ (a₁ + 0 ≤ a₂ + ((0 : Nat) : α))) ↔ a₂ < a₁ := by
  rw [Semiring.natCast_zero, AddCommMonoid.zero_add, AddCommMonoid.zero_add,
    AddCommMonoid.add_zero, AddCommMonoid.add_zero, LawfulOrderLT.lt_iff]

public theorem Lean.Grind.Ring.OfSemiring.mk_lt_mk {α : Type u} [Semiring α] [LE α] [LT α] [LawfulOrderLT α]
    [IsPreorder α] [OrderedAdd α] {a₁ a₂ b₁ b₂ : α} :
    ((a₁ + b₂ ≤ a₂ + b₁) ∧ ¬ (b₁ + a₂ ≤ b₂ + a₁)) ↔ a₁ + b₂ < a₂ + b₁ := by
  rw [AddCommMonoid.add_comm b₁ a₂, AddCommMonoid.add_comm b₂ a₁, LawfulOrderLT.lt_iff]

open _root_.Lean.Grind.Ring.OfSemiring in
/-- Both sides of the pinned pair-addition equation compute to this representative. -/
public theorem Lean.Grind.Ring.OfSemiring.mk_add_mk {α : Type u} [Semiring α] {a₁ a₂ b₁ b₂ : α} :
    Q.mk (a₁ + b₁, a₂ + b₂) = Q.mk (a₁ + b₁, a₂ + b₂) := rfl

open _root_.Lean.Grind.Ring.OfSemiring in
public theorem Lean.Grind.Ring.OfSemiring.mk_mul_mk {α : Type u} [Semiring α] {a₁ a₂ b₁ b₂ : α} :
    Q.mk (a₁*b₁ + a₂*b₂, a₁*b₂ + a₂*b₁) = Q.mk (a₁*b₁ + a₂*b₂, a₁*b₂ + a₂*b₁) := rfl

public theorem Lean.Grind.Ring.OfSemiring.mk_le_mk {α : Type u} [Semiring α] [LE α] [IsPreorder α] [OrderedAdd α]
    {a₁ a₂ b₁ b₂ : α} : (a₁ + b₂ ≤ a₂ + b₁) ↔ a₁ + b₂ ≤ a₂ + b₁ := Iff.rfl

public theorem Lean.Grind.Ring.OfSemiring.toQ_le {α : Type u} [Semiring α] [LE α] [IsPreorder α] [OrderedAdd α]
    {a b : α} : (a + 0 ≤ 0 + b) ↔ a ≤ b := by
  rw [Semiring.add_zero, AddCommMonoid.zero_add]

public theorem Lean.Grind.Ring.OfSemiring.toQ_lt {α : Type u} [Semiring α] [LE α] [LT α] [LawfulOrderLT α]
    [IsPreorder α] [OrderedAdd α] {a b : α} :
    ((a + 0 ≤ 0 + b) ∧ ¬(b + 0 ≤ 0 + a)) ↔ a < b := by
  rw [Semiring.add_zero, AddCommMonoid.zero_add, Semiring.add_zero, AddCommMonoid.zero_add,
    LawfulOrderLT.lt_iff]

end

open _root_.Lean.Grind.Ring.OfSemiring in
@[instance_reducible] public def Lean.Grind.CommRing.OfCommSemiring.instIntCastQ :
    type_of% @_root_.Lean.Grind.CommRing.OfCommSemiring.instIntCastQ :=
  fun {_} _ _ => ⟨intCast⟩

set_option linter.unusedVariables false in
open _root_.Lean.Grind.Ring.OfSemiring in
/-- The zero branch of the pinned power recursor reduces before it needs multiplication. -/
public theorem Lean.Grind.Ring.OfSemiring.pow_zero {α : Type u} [Semiring α] (a : Q α) :
    natCast (α := α) 1 = natCast (α := α) 1 := rfl

open _root_.Lean.Grind.Ring.OfSemiring in
public theorem Lean.Grind.Ring.OfSemiring.toQ_zero {α : Type u} [Semiring α] :
    toQ (0 : α) = natCast (α := α) 0 :=
  congrArg (fun x : α => Q.mk (x, 0)) (Semiring.natCast_zero (α := α)).symm

open _root_.Lean.Grind.Ring.OfSemiring in
public theorem Lean.Grind.Ring.OfSemiring.toQ_ofNat {α : Type u} [Semiring α] (n : Nat) :
    toQ (OfNat.ofNat (α := α) n) = natCast (α := α) n :=
  congrArg (fun x : α => Q.mk (x, 0)) (Semiring.ofNat_eq_natCast n)

section
variable {α : Type u} [Semiring α] (ctx : Context α)

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.Lean.Grind.CommRing.Expr.denoteSAsRing.eq_1
    (k : Int) : Lean.Grind.CommRing.Expr.denoteSAsRing ctx (.num k) = Ring.OfSemiring.natCast (α := α) k.natAbs :=
  Lean.Grind.Ring.OfSemiring.toQ_ofNat k.natAbs

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.Lean.Grind.CommRing.Expr.denoteSAsRing.eq_2
    (k : Nat) : Lean.Grind.CommRing.Expr.denoteSAsRing ctx (.natCast k) = Ring.OfSemiring.natCast (α := α) k :=
  Lean.Grind.Ring.OfSemiring.toQ_ofNat k

public theorem _root_.OmegaChecks.InitPort.SemiringImage.denoteCases
    (x : Expr) : Lean.Grind.CommRing.Expr.denoteSAsRing ctx x =
      _root_.Lean.Grind.CommRing.Expr.denoteS.match_1 (fun _ => Ring.OfSemiring.Q α) x
        (fun k => Ring.OfSemiring.natCast (α := α) k.natAbs)
        (fun k => Ring.OfSemiring.natCast (α := α) k)
        (fun v => Ring.OfSemiring.toQ (v.denote ctx))
        (fun a b => Ring.OfSemiring.toQ (a.denoteS ctx + b.denoteS ctx))
        (fun a b => Ring.OfSemiring.toQ (a.denoteS ctx * b.denoteS ctx))
        (fun a k => Ring.OfSemiring.toQ (a.denoteS ctx ^ k))
        (fun _ _ => Ring.OfSemiring.natCast (α := α) 0)
        (fun _ => Ring.OfSemiring.natCast (α := α) 0)
        (fun _ => Ring.OfSemiring.natCast (α := α) 0) := by
  cases x <;> first
    | rfl
    | exact Lean.Grind.Ring.OfSemiring.toQ_ofNat _
    | exact Lean.Grind.Ring.OfSemiring.toQ_zero

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.Lean.Grind.CommRing.Expr.denoteSAsRing.eq_7
    (a b : Expr) : Lean.Grind.CommRing.Expr.denoteSAsRing ctx (.sub a b) = Ring.OfSemiring.natCast (α := α) 0 :=
  Lean.Grind.Ring.OfSemiring.toQ_zero

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.Lean.Grind.CommRing.Expr.denoteSAsRing.eq_8
    (a : Expr) : Lean.Grind.CommRing.Expr.denoteSAsRing ctx (.neg a) = Ring.OfSemiring.natCast (α := α) 0 :=
  Lean.Grind.Ring.OfSemiring.toQ_zero

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.Lean.Grind.CommRing.Expr.denoteSAsRing.eq_9
    (k : Int) : Lean.Grind.CommRing.Expr.denoteSAsRing ctx (.intCast k) = Ring.OfSemiring.natCast (α := α) 0 :=
  Lean.Grind.Ring.OfSemiring.toQ_zero

end

section
open _root_.Lean.Grind.Ring.OfSemiring
attribute [local instance] Semiring.natCast

public theorem Lean.Grind.Ring.OfSemiring.ofNat_succ {α : Type u} [Semiring α] (a : Nat) :
    natCast (α := α) (a + 1) = Q.mk ((a : α) + ((1 : Nat) : α), (0 : α) + 0) := by
  rw [Semiring.add_zero]
  exact congrArg (fun x : α => Q.mk (x, 0)) (Semiring.natCast_add a 1)

end

open _root_.Lean.Grind.Ring.OfSemiring in
public theorem Lean.Grind.Ring.OfSemiring.toQ_add {α : Type u} [Semiring α] (a b : α) :
    toQ (a + b) = Q.mk (a + b, (0 : α) + 0) :=
  congrArg (fun x : α => Q.mk (a + b, x)) (Semiring.add_zero 0).symm

open _root_.Lean.Grind.Ring.OfSemiring in
public theorem Lean.Grind.Ring.OfSemiring.toQ_mul {α : Type u} [Semiring α] (a b : α) :
    toQ (a * b) = Q.mk (a * b + (0 : α) * 0, a * 0 + 0 * b) := by
  rw [Semiring.zero_mul, Semiring.mul_zero, Semiring.zero_mul, Semiring.add_zero, Semiring.add_zero]
  rfl

end OmegaChecks.InitPort.Alternatives
