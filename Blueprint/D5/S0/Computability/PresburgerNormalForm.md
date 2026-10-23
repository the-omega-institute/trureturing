# Polarity and disjunctive normal form

## Abstract

Polarity conversion preserves Boolean evaluation, including nested negation.

A Clause is a list of atoms interpreted by all; a DNF is a list of clauses interpreted by any. DNF.cross forms all concatenations of a clause from each input. Thus cross implements conjunction and append implements disjunction. The empty DNF is false, whereas the singleton empty clause is true.

Atom.negate changes zero<=t into zero<=-t-1. The minus one uses discreteness of integers: it expresses strict negativity without a new atom constructor. Divisibility and nondivisibility swap. DNF.ofPolarity pushes negation through every constructor; negative conjunction becomes appended negative branches and negative disjunction becomes a cross product. No assumption restricts the nesting of negation.

**Theorem 1.1 (Exact atom complement).**

$$\forall a \in Atom,\; \forall xs \in \operatorname{List}\left(Int\right),\; \operatorname{eval}\left(\operatorname{negate}\left(a\right), xs\right) = \operatorname{not}\left(\operatorname{eval}\left(a, xs\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerNormalForm.eval_negate` (`✓ std3`). ∎

*Citation.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

Integer order separates the le case into nonnegative and negative values. The divisibility cases use Boolean complementation. This law feeds the negative atom branch of the polarity induction.

**Theorem 1.2 (Positive and negative conversion).**

$$\forall b \in Bool,\; \forall p \in QF,\; \forall xs \in \operatorname{List}\left(Int\right),\; \operatorname{evalDNF}\left(\operatorname{ofPolarity}\left(b, p\right), xs\right) = \operatorname{if}\left(b, \operatorname{eval}\left(p, xs\right), \operatorname{not}\left(\operatorname{eval}\left(p, xs\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerNormalForm.eval_ofPolarity` (`✓ std3`). ∎

*Citation.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

evalDNF denotes DNF.eval. Induction on p, generalized over b, combines eval_cross, eval_append and eval_negate. evalClause_append is Boolean conjunction of the two clauses. Finally eval_toQF states that rebuilding a disjunction of atom conjunctions preserves DNF.eval.

## References

- Truth anchor: `D5/S0/Computability/PresburgerNormalForm.eval_negate`
- Truth anchor: `D5/S0/Computability/PresburgerNormalForm.eval_ofPolarity`
- Dependency: [D5/S0/Computability/PresburgerSyntax](PresburgerSyntax.md)
