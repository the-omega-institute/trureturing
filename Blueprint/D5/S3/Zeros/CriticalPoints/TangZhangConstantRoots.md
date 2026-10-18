# The constant-root equality direction

## Abstract

Coincident nonzero polynomial roots attain the Tang–Zhang real-order coefficient.

**Theorem 1.1 (The exact constant-root moment).**

Lean statement: `D5/S3/Zeros/CriticalPoints/TangZhangConstantRoots.constant_roots_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/TangZhangConstantRoots.constant_roots_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n≥1, nonzero complex a and real p, the sum of norm(w)^(−p) over roots of the derivative of P(Z)=Z(Z−a)^n equals c(n,p) times the sum of norm(a)^(−p) over Fin n, where c(n,p)=((n+1)^p+n−1)/n. The derivative has the root a with multiplicity n−1 and the root a/(n+1), including the case n=1.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/TangZhangConstantRoots.constant_roots_moment`
- Dependency: [D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo](TangZhangOrderMinusTwo.md)
