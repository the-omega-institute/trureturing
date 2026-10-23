# Eliminating one integer coordinate

## Abstract

Coefficient normalization and finite periodic tests preserve existential semantics.

Affine.substHead replaces the first coordinate by an affine expression on the remaining coordinates. eval_head decomposes a value as head*x+tail.eval(xs). Both affine and atom substitution preserve evaluation at replacement.eval(xs)::xs.

Cooper.commonCoefficient is a positive common multiple of the nonzero head coefficient magnitudes. Normalization replaces x by y=L*x and scales each nonzero coefficient to its sign. Divisibility moduli scale by the same positive quotient; zero head coefficients retain their fixed values. normalizeClause adds the atom L divides y, so the reverse direction can recover an integer x. Normal inequalities have head coefficient -1, 0 or 1.

A normalized clause splits into fixed atoms, affine lower bounds, affine upper bounds and periodic divisibility atoms. The period is a positive common multiple of the moduli. Adding this period to the head value preserves all periodic atoms, including nondivisibility. eval_normalizedClause_iff states the conjunction of the fixed test, all lower bounds, all upper bounds and the periodic test. Empty lists are handled by their ordinary all/any semantics.

boundedPair enumerates k in List.range m and checks lo+k<=hi together with the periodic clause at lo+k. elimVariable uses the one-sided residue disjunction when a bound list is empty and the conjunction of pair tests otherwise. elimNormalizedClause also retains fixed atoms. elimClause first normalizes; eliminate distributes this procedure over positive DNF. The finite residue enumeration is the upstream Cooper algorithm.

**Theorem 1.1 (Normalization preserves existence).**

$$\forall c \in Clause,\; \forall xs \in \operatorname{List}\left(Int\right),\; (\exists x \in Int,\; \operatorname{evalClause}\left(c, \operatorname{cons}\left(x, xs\right)\right) = true) \iff (\exists y \in Int,\; \operatorname{evalClause}\left(\operatorname{normalizeClause}\left(c\right), \operatorname{cons}\left(y, xs\right)\right) = true)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerElimination.normalizeClause_exists_iff` (`✓ std3`). ∎

*Citation.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

The forward proof substitutes y=L*x. The reverse proof uses the added divisibility atom to write y=L*x, then cancels the positive scaling factors in each inequality or divisibility test.

**Theorem 1.2 (Clause elimination).**

$$\forall c \in Clause,\; \forall xs \in \operatorname{List}\left(Int\right),\; (\operatorname{eval}\left(\operatorname{elimClause}\left(c\right), xs\right) = true) \iff (\exists x \in Int,\; \operatorname{evalClause}\left(c, \operatorname{cons}\left(x, xs\right)\right) = true)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerElimination.elimClause_correct` (`✓ std3`). ∎

*Citation.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

Normalization equivalence combines with elimNormalizedClause_correct. Fixed constraints are independent of the eliminated head; the periodic finite criterion supplies that head when the remaining tests hold.

**Theorem 1.3 (Quantifier-free elimination).**

$$\forall p \in QF,\; \forall xs \in \operatorname{List}\left(Int\right),\; (\operatorname{eval}\left(\operatorname{eliminate}\left(p\right), xs\right) = true) \iff (\exists x \in Int,\; \operatorname{eval}\left(p, \operatorname{cons}\left(x, xs\right)\right) = true)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerElimination.eliminate_correct` (`✓ std3`). ∎

*Citation.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

Polarity conversion identifies a satisfied clause in either direction. Applying elimClause_correct to that clause removes exactly one existential integer coordinate; the remaining valuation is unrestricted.

## References

- Truth anchor: `D5/S0/Computability/PresburgerElimination.elimClause_correct`
- Truth anchor: `D5/S0/Computability/PresburgerElimination.eliminate_correct`
- Truth anchor: `D5/S0/Computability/PresburgerElimination.normalizeClause_exists_iff`
- Dependency: [D5/S0/Computability/PresburgerCooper](PresburgerCooper.md)
- Dependency: [D5/S0/Computability/PresburgerNormalForm](PresburgerNormalForm.md)
