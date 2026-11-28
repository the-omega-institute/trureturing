module
public import Init.Grind.Ring.CommSemiringAdapter

/-! The semiring interpreter supplies a representative for each operand of these operations.
The pinned right endpoints of `denoteSAsRing.eq_4`, `eq_5` and `eq_6` call
`Lean.Grind.Ring.OfSemiring.ofSemiring`, which is missing from the strict public interface. -/

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

end OmegaChecks.InitPort.SemiringImage
