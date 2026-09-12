/- GID: D5/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SpacetimeExpressions/RationalExpressionCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native rational expressions preserve guards, values and numerical quotient equality. -/

import D5.S0.Rewriting.Expressions.GuardedArithmeticTerms
import D5.S3.ConceptDynamics.SpacetimeArithmetic.RationalQuotient

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.SpacetimeExpressions.RationalExpressionCompatibility

open SpacetimeArithmetic
open D5.S0.Rewriting.Expressions.GuardedArithmeticTerms

noncomputable section
universe u
variable {d : Nat} {V : Type u}

def richAlgebra (d : Nat) : Algebra Rat (RichRational.Fraction d) where
  const := RationalQuotient.rationalSection d
  neg := RichRational.neg
  add := RichRational.add
  mul := RichRational.mul
  guard _ s := RichRational.DivisionGuard s
  divide r s h := RichRational.div r s h

/-- Rat's total convention at zero is excluded at every division node. -/
def ordinaryAlgebra : Algebra Rat Rat where
  const := id
  neg := Neg.neg
  add := HAdd.hAdd
  mul := HMul.hMul
  guard _ s := s ≠ 0
  divide r s _ := r / s

theorem guard_iff (r s : RichRational.Fraction d) :
    (richAlgebra d).guard r s ↔ RichRational.readout s ≠ 0 :=
  RichRational.division_guard_iff s

def richEval (env : V → RichRational.Fraction d) : Expr Rat V →
    Option (RichRational.Fraction d) := eval (richAlgebra d) env

def ordinaryEval (env : V → Rat) : Expr Rat V → Option Rat :=
  eval ordinaryAlgebra env

theorem readout_eval (env : V → RichRational.Fraction d) (e : Expr Rat V) :
    (richEval env e).map RichRational.readout =
      ordinaryEval (RichRational.readout ∘ env) e :=
  eval_map (richAlgebra d) ordinaryAlgebra RichRational.readout
    (RationalQuotient.rationalSection_rightInverse d) RichRational.neg_readout
    RichRational.add_readout RichRational.mul_readout guard_iff RichRational.div_readout env e

theorem legality_iff (env : V → RichRational.Fraction d) (e : Expr Rat V) :
    Legal (richAlgebra d) env e ↔
      Legal ordinaryAlgebra (RichRational.readout ∘ env) e :=
  legal_iff_of_eval_map _ _ _ env e (readout_eval env e)

theorem legal_iff_all_nodes (env : V → RichRational.Fraction d) (e : Expr Rat V) :
    Legal (richAlgebra d) env e ↔
      AllLegal ordinaryAlgebra (RichRational.readout ∘ env) e :=
  (legality_iff env e).trans (legal_iff_allLegal _ _ _)

theorem division_node_guards (env : V → RichRational.Fraction d) (a b : Expr Rat V) :
    AllLegal ordinaryAlgebra (RichRational.readout ∘ env) (div a b) ↔
      AllLegal ordinaryAlgebra (RichRational.readout ∘ env) a ∧
      AllLegal ordinaryAlgebra (RichRational.readout ∘ env) b ∧
      ∃ r s, ordinaryEval (RichRational.readout ∘ env) a = some r ∧
        ordinaryEval (RichRational.readout ∘ env) b = some s ∧ s ≠ 0 :=
  allLegal_div _ _ _ _

theorem ordinary_of_rich (env : V → RichRational.Fraction d) (e : Expr Rat V)
    {r : RichRational.Fraction d} (h : richEval env e = some r) :
    ordinaryEval (RichRational.readout ∘ env) e = some (RichRational.readout r) := by
  rw [← readout_eval, h, Option.map_some]

theorem value_eq (env : V → RichRational.Fraction d) (e : Expr Rat V)
    {r : RichRational.Fraction d} {q : Rat} (hr : richEval env e = some r)
    (hq : ordinaryEval (RichRational.readout ∘ env) e = some q) :
    RichRational.readout r = q :=
  Option.some.inj ((ordinary_of_rich env e hr).symm.trans hq)

theorem value_eq_iff_class_eq (env : V → RichRational.Fraction d) (a b : Expr Rat V)
    {r s : RichRational.Fraction d} {p q : Rat}
    (hr : richEval env a = some r) (hs : richEval env b = some s)
    (hp : ordinaryEval (RichRational.readout ∘ env) a = some p)
    (hq : ordinaryEval (RichRational.readout ∘ env) b = some q) :
    p = q ↔ RationalQuotient.classOf r = RationalQuotient.classOf s := by
  rw [← value_eq env a hr hp, ← value_eq env b hs hq]
  exact (RichRational.cross_iff_readout r s).symm.trans
    (RationalQuotient.class_eq_iff r s).symm

end
end D5.S3.ConceptDynamics.SpacetimeExpressions.RationalExpressionCompatibility
