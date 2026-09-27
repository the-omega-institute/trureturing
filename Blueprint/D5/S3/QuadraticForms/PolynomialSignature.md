# Polynomial Sign Formulas for Matrix Signatures

## Abstract

Finite polynomial-sign formulas characterize actual symmetric matrix signatures.

**Theorem 1.1 (Exact signature compiler).**

$$holds(x,compile(n,A,z)) \iff sigPos(Q)-sigNeg(Q)=z$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/PolynomialSignature.compile_iff_signature` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let sigma be any type of variables, n any natural dimension, A an n by n matrix of multivariate polynomials over the reals in those variables, z any integer, and x any real assignment to sigma. Assume only that the evaluated matrix A(x) is symmetric at this same x. Then holds(x,compile(n,A,z)) is equivalent to the actual signature of Q(v) = sum over i,j of v(i) A(x)(i,j) v(j) being z. The signature is its positive index minus its negative index.

A formula is a finite list of clauses, and a clause is a finite list of pairs consisting of a polynomial and a negative, zero, or positive sign. A formula holds when some clause has every sign condition satisfied at x. Empty disjunctions are false and empty conjunctions are true. All polynomials remain in the original sigma coordinates; no auxiliary real variables or semantic decision oracle occur.

At dimension zero the formula tests z = 0. At positive dimension one branch checks that every entry is zero and z = 0. A positive or negative diagonal entry selects a one-coordinate polynomial residual and shifts z by minus or plus one. When all diagonal entries vanish, a nonzero off-diagonal entry selects a two-coordinate residual without shifting z. Finite conjunction and disjunction distribute these branches into the output formula.

Polynomial evaluation commutes with both residual constructions. Two-step induction on dimension therefore identifies the formula with the recursive pivot relation. The characterization of that relation by the actual quadratic-form signature proves the equivalence. Every pivot condition is checked at the same assignment as its residual.

No nonsingularity, fixed rank, fixed degree, global polynomial symmetry, or nonvanishing pivot is assumed. Singular matrices, zero diagonals with nonzero off-diagonal entries, and every rank or degree drop under specialization are included. The construction gives finite mathematical syntax and its meaning; it makes no complexity claim or executable decision procedure for arbitrary real inputs.

## References

- Truth anchor: `D5/S3/QuadraticForms/PolynomialSignature.compile_iff_signature`
- Dependency: [D5/S3/QuadraticForms/ActualSignature](ActualSignature.md)
