# The exact ordered trace bridge

## Abstract

The ordered integer matrix trace is exactly the Boolean phase sum for every positive length.

**Theorem 1.1 (The ordered trace is the exact Boolean phase sum).**

$$\forall n \in \mathrm{Nat},\; {0 < n} \Rightarrow {\forall b \in \mathrm{Word}\left(n\right),\; \forall a \in \mathrm{Word}\left(n\right),\; \mathrm{sourceTrace}\left(b, a\right) = \sum_{x \in \mathrm{Word}\left(n\right)} \mathrm{sign}\left({\mathrm{dot}\left(b, x\right)} + {\mathrm{dot}\left(a, \mathrm{chi}\left(x\right)\right)}\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Trace.sourceTrace_eq_phase_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* ricardorr (MathOverflow user 49534; real-name attribution unverified) (2026). *Does the support of a cyclic trace of 2x2 sign matrices always span a hyperplane in Z_2^n?*. URL: <https://mathoverflow.net/questions/512655>.

*Commentary.*

At every positive length n and for all words b,a, the literal ordered matrix trace is the sum over every x of sign(dot(b,x)+dot(a,chi(x))). Length one and all coincident cyclic indices are included. This identity also applies to even lengths; oddness is needed only for the inverse construction.

For a list of r+1 matrices, expand its (i,j) entry over all r intermediate states. The row tuple is i followed by the intermediate states; the column tuple is those states followed by j. Induction uses the first matrix factor and the ordinary Matrix.mul entry formula, preserving the complete list order. Taking the trace identifies j with i. Joining the initial state to the intermediate tuple gives every cyclic path exactly once; the final column is the initial state, including for a one-factor product.

The path product is the sign of the sum of its entry exponents. Reindex the a_(k-2)x_k term by k=i+2 and the a_(k-1)x_k x_(k+1) term by k=i+1. The coefficient of a_i becomes x_i+x_(i+2)+x_(i+1)x_(i+2), exactly chi(x)_i. These are bijections of the actual cyclic index set, so repeated indices need no separate independence assumption.

## References

- Truth anchor: `D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Trace.sourceTrace_eq_phase_sum`
- Dependency: [D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Prelude](Prelude.md)
