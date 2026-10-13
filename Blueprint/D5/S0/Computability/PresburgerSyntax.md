# Integer affine expressions and formulas

## Abstract

Integer affine coordinates and Boolean atoms have total executable semantics.

An Affine is an integer constant and a finite coefficient list. Its value is the constant plus the recursive dot product with a valuation list. The dot product stops when either list ends, so missing coefficients and missing valuation entries contribute zero. Coefficient addition retains the unmatched suffix; negation and scaling map the coefficients and change the constant.

Atoms express zero less than or equal to an affine value, divisibility by a positive natural modulus, or its negation. The positivity proof is part of the divisibility constructor. Atom.eval and QF.eval return Bool; QF has truth, falsity, atoms, conjunction, disjunction and negation. An empty atom conjunction and an empty formula conjunction are true; an empty disjunction is false.

Formula adds integer existential quantification to the Boolean constructors. Formula.holds is a proposition; its existential case conses the newly bound integer onto the valuation. Formula.all is the derived not-exists-not constructor. Sentence is an abbreviation of Formula, and evaluating at the empty valuation supplies the sentence convention. These syntax and arithmetic laws are supplied by ProveIt.

**Theorem 1.1 (Affine addition preserves values).**

$$\forall s \in Affine,\; \forall t \in Affine,\; \forall xs \in \operatorname{List}\left(Int\right),\; \operatorname{eval}\left(\operatorname{add}\left(s, t\right), xs\right) = \operatorname{eval}\left(s, xs\right) + \operatorname{eval}\left(t, xs\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerSyntax.eval_add` (`✓ std3`). ∎

*Citation.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

Induction on coefficient lists proves dot_coeffAdd. Arithmetic distribution then gives the displayed identity. The companion laws eval_neg, eval_scale and eval_const state respectively negation, scalar multiplication and constant evaluation; eval_consCoeff at x::xs is a*x plus the tail value.

**Theorem 1.2 (Finite conjunction is list.all).**

$$\forall as \in \operatorname{List}\left(Atom\right),\; \forall xs \in \operatorname{List}\left(Int\right),\; \operatorname{eval}\left(\operatorname{conjunction}\left(as\right), xs\right) = \operatorname{all}\left(as, \operatorname{at}\left(xs\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerSyntax.eval_conjunction` (`✓ std3`). ∎

*Citation.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

Here at(xs) is the function sending an atom a to Atom.eval a xs. Structural list induction includes the empty case. eval_disjunction replaces conjunction/all by disjunction/any, and eval_conjList applies the same all law to a list of QF formulas.

## References

- Truth anchor: `D5/S0/Computability/PresburgerSyntax.eval_add`
- Truth anchor: `D5/S0/Computability/PresburgerSyntax.eval_conjunction`
