/- GID: D5/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SpacetimeExpressions/IntegerExpressionCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native integer expressions preserve all guards, values and numerical quotient equality. -/

import D5.S0.Rewriting.Expressions.GuardedArithmeticTerms
import D5.S3.ConceptDynamics.SpacetimeArithmetic.IntegerExactDivision
import D5.S3.ConceptDynamics.SpacetimeArithmetic.IntegerQuotient

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.SpacetimeExpressions.IntegerExpressionCompatibility

open Spacetime.ComplementCharge Spacetime.ComplementFibers
open Spacetime.ParallelComposition Spacetime.GeneratedProduct
open SpacetimeArithmetic
open D5.S0.Rewriting.Expressions.GuardedArithmeticTerms

noncomputable section
universe u
variable {d : Nat} {V : Type u}

def richAlgebra (d : Nat) : Algebra Int (BalancedRich d) where
  const := balancedSection d
  neg := complementBalanced
  add := parallelBalanced
  mul := productBalanced
  guard := IntegerExactDivision.ExactGuard
  divide := IntegerExactDivision.exactDivide

/-- Every integer division is partial, including divisions in internal subterms. -/
def ordinaryAlgebra : Algebra Int Int where
  const := id
  neg := Neg.neg
  add := Int.add
  mul := Int.mul
  guard x y := y ≠ 0 ∧ y ∣ x
  divide x y _ := x / y

theorem guard_iff (x y : BalancedRich d) :
    (richAlgebra d).guard x y ↔
      (balancedQ y ≠ 0 ∧ balancedQ y ∣ balancedQ x) := Iff.rfl

/-- The usual quotient equals the selected exact quotient only on the exact domain. -/
theorem exactQuotient_eq_div (x y : BalancedRich d)
    (h : IntegerExactDivision.ExactGuard x y) :
    IntegerExactDivision.exactQuotient x y h = balancedQ x / balancedQ y :=
  IntegerExactDivision.exactQuotient_unique x y h _ (Int.ediv_mul_cancel h.2).symm

theorem divide_readout (x y : BalancedRich d)
    (h : IntegerExactDivision.ExactGuard x y) :
    balancedQ (IntegerExactDivision.exactDivide x y h) = balancedQ x / balancedQ y :=
  (IntegerExactDivision.exactDivide_readout x y h).trans (exactQuotient_eq_div x y h)

def richEval (env : V → BalancedRich d) : Expr Int V → Option (BalancedRich d) :=
  eval (richAlgebra d) env

def ordinaryEval (env : V → Int) : Expr Int V → Option Int :=
  eval ordinaryAlgebra env

/-- All finite terms and all assignments of actual native histories. -/
theorem readout_eval (env : V → BalancedRich d) (e : Expr Int V) :
    (richEval env e).map balancedQ = ordinaryEval (balancedQ ∘ env) e :=
  eval_map (richAlgebra d) ordinaryAlgebra balancedQ (balancedSection_rightInverse d)
    complementBalanced_readout (fun x y => q_parallel x.val y.val)
    (fun x y => q_product x.val y.val) guard_iff divide_readout env e

theorem legality_iff (env : V → BalancedRich d) (e : Expr Int V) :
    Legal (richAlgebra d) env e ↔ Legal ordinaryAlgebra (balancedQ ∘ env) e :=
  legal_iff_of_eval_map _ _ _ env e (readout_eval env e)

/-- The right side recursively retains every child and every nonzero/divisibility guard. -/
theorem legal_iff_all_nodes (env : V → BalancedRich d) (e : Expr Int V) :
    Legal (richAlgebra d) env e ↔ AllLegal ordinaryAlgebra (balancedQ ∘ env) e :=
  (legality_iff env e).trans (legal_iff_allLegal _ _ _)

theorem division_node_guards (env : V → BalancedRich d) (a b : Expr Int V) :
    AllLegal ordinaryAlgebra (balancedQ ∘ env) (div a b) ↔
      AllLegal ordinaryAlgebra (balancedQ ∘ env) a ∧
      AllLegal ordinaryAlgebra (balancedQ ∘ env) b ∧
      ∃ m n, ordinaryEval (balancedQ ∘ env) a = some m ∧
        ordinaryEval (balancedQ ∘ env) b = some n ∧ n ≠ 0 ∧ n ∣ m :=
  allLegal_div _ _ _ _

theorem ordinary_of_rich (env : V → BalancedRich d) (e : Expr Int V)
    {x : BalancedRich d} (h : richEval env e = some x) :
    ordinaryEval (balancedQ ∘ env) e = some (balancedQ x) := by
  rw [← readout_eval, h, Option.map_some]

theorem value_eq (env : V → BalancedRich d) (e : Expr Int V)
    {x : BalancedRich d} {n : Int} (hx : richEval env e = some x)
    (hn : ordinaryEval (balancedQ ∘ env) e = some n) : balancedQ x = n :=
  Option.some.inj ((ordinary_of_rich env e hx).symm.trans hn)

/-- Equality is in the actual integer quotient, with no assertion of raw history equality. -/
theorem value_eq_iff_class_eq (env : V → BalancedRich d) (a b : Expr Int V)
    {x y : BalancedRich d} {m n : Int}
    (hx : richEval env a = some x) (hy : richEval env b = some y)
    (hm : ordinaryEval (balancedQ ∘ env) a = some m)
    (hn : ordinaryEval (balancedQ ∘ env) b = some n) :
    m = n ↔ IntegerQuotient.classOf x = IntegerQuotient.classOf y := by
  rw [← value_eq env a hx hm, ← value_eq env b hy hn]
  exact (IntegerQuotient.class_eq_iff x y).symm

end
end D5.S3.ConceptDynamics.SpacetimeExpressions.IntegerExpressionCompatibility
