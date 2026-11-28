module
public import Init.Grind.Ring.CommSemiringAdapter

/-! The pinned types of `denoteSAsRing.eq_4`, `eq_5`, `eq_6` and `eq_def` project arithmetic
from `Lean.Grind.Ring.OfSemiring.ofSemiring`. The strict interpreter evaluates in the base
semiring and embeds the result. Its public theorems expose the addition, multiplication,
power and all nine expression cases. The pinned interpreter recurses in the quotient ring.
Their whole bodies differ under kernel conversion. Ordinary strict imports use the named
equations for these computations. The standalone ring instance is unavailable. -/
open Lean.Grind Lean.Grind.CommRing
namespace OmegaChecks.InitPort.SemiringImage

variable {α : Type u} [Semiring α] (ctx : Context α)

@[expose] public def addReference (a b : Expr) :=
  Ring.OfSemiring.add (a.denoteSAsRing ctx) (b.denoteSAsRing ctx)

public def add (a b : Expr) := Ring.OfSemiring.toQ (a.denoteS ctx + b.denoteS ctx)

public theorem addAgreement : @addReference = @add := by
  funext α inst ctx a b
  unfold addReference add
  rw [Expr.denoteAsRing_eq, Expr.denoteAsRing_eq]
  exact (Ring.OfSemiring.toQ_add _ _).symm

@[expose] public def mulReference (a b : Expr) :=
  Ring.OfSemiring.mul (a.denoteSAsRing ctx) (b.denoteSAsRing ctx)

public def mul (a b : Expr) := Ring.OfSemiring.toQ (a.denoteS ctx * b.denoteS ctx)

public theorem mulAgreement : @mulReference = @mul := by
  funext α inst ctx a b
  unfold mulReference mul
  rw [Expr.denoteAsRing_eq, Expr.denoteAsRing_eq]
  exact (Ring.OfSemiring.toQ_mul _ _).symm

@[expose] public def powReference (a : Expr) (k : Nat) := Ring.OfSemiring.npow (a.denoteSAsRing ctx) k

public def pow (a : Expr) (k : Nat) := Ring.OfSemiring.toQ (a.denoteS ctx ^ k)

public theorem powAgreement : @powReference = @pow := by
  funext α inst ctx a k
  unfold powReference pow
  rw [Expr.denoteAsRing_eq]
  exact (Ring.OfSemiring.toQ_pow _ _).symm

public theorem addImage (a b : Expr) :
    (.add a b : Expr).denoteSAsRing ctx = Ring.OfSemiring.toQ (a.denoteS ctx + b.denoteS ctx) := by
  rw [Expr.denoteAsRing_eq, Expr.denoteS.eq_4]

public theorem mulImage (a b : Expr) :
    (.mul a b : Expr).denoteSAsRing ctx = Ring.OfSemiring.toQ (a.denoteS ctx * b.denoteS ctx) := by
  rw [Expr.denoteAsRing_eq, Expr.denoteS.eq_5]

public theorem powImage (a : Expr) (k : Nat) :
    (.pow a k : Expr).denoteSAsRing ctx = Ring.OfSemiring.toQ (a.denoteS ctx ^ k) := by
  rw [Expr.denoteAsRing_eq, Expr.denoteS.eq_6]

public theorem casesEq
    (x : Expr) : x.denoteSAsRing ctx =
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
  cases x <;> rw [Expr.denoteAsRing_eq] <;> first
    | rfl
    | exact Ring.OfSemiring.toQ_ofNat _
    | exact Ring.OfSemiring.toQ_zero

public abbrev constructorCases
    (x : Expr) : Prop := x.denoteSAsRing ctx =
      _root_.Lean.Grind.CommRing.Expr.denoteS.match_1 (fun _ => Ring.OfSemiring.Q α) x
        (fun k => Ring.OfSemiring.natCast (α := α) k.natAbs)
        (fun k => Ring.OfSemiring.natCast (α := α) k)
        (fun v => Ring.OfSemiring.toQ (v.denote ctx))
        (fun a b => (.add a b : Expr).denoteSAsRing ctx)
        (fun a b => (.mul a b : Expr).denoteSAsRing ctx)
        (fun a k => (.pow a k : Expr).denoteSAsRing ctx)
        (fun _ _ => Ring.OfSemiring.natCast (α := α) 0)
        (fun _ => Ring.OfSemiring.natCast (α := α) 0)
        (fun _ => Ring.OfSemiring.natCast (α := α) 0)

public theorem constructorCasesEq : ∀ {α : Type u} [Semiring α] (ctx : Context α) (e : Expr), constructorCases ctx e :=
  @Expr.denoteSAsRing.eq_def

end OmegaChecks.InitPort.SemiringImage
