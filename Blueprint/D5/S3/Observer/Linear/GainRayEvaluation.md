# Distinct clocks and polynomial coefficient evaluation

## Abstract

Distinct clocks and polynomial coefficient evaluation

evaluation(d,n,t) has entries t(i) to the power k for i in Fin n and k in Fin(d+1), with the usual convention that a zeroth power is one. evaluate is its real linear multiplication map on ordinary coefficients. It is exactly evaluation of gain d beta at the specified nodes.

The nodes are explicit. clocks n i is the real cast of the original natural index i. Interpolation at arbitrary distinct nodes is an algebraic interface; literal acquisition continues to use every consecutive original clock. The zero-node case and the empty value vector are included.

evaluationRightInverse chooses a right inverse from evaluation_surjective whenever n<=d+1 and t is injective. No nonzero-gain promise is used in this linear interpolation interface. A compatible legal-world construction must separately ensure the whole coefficient vector is nonzero.

**Theorem 1.1 (Enough distinct clocks determine all coefficients).**

Lean statement: `D5/S3/Observer/Linear/GainRayEvaluation.evaluation_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayEvaluation.evaluation_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d,n and t:Fin n to the reals, injectivity of t and d+1<=n imply injectivity of evaluate d n t. Two coefficient vectors with these evaluations equal represent polynomials of degree less than d+1 agreeing at n distinct nodes, so they coincide.

**Theorem 1.2 (Every short vector of prescribed values occurs).**

Lean statement: `D5/S3/Observer/Linear/GainRayEvaluation.evaluation_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayEvaluation.evaluation_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d,n and injective t:Fin n to the reals, n<=d+1 implies surjectivity of evaluate d n t. Lagrange interpolation supplies a polynomial of degree less than n; its first d+1 coefficients give the witness. For n=0 the unique empty vector is attained by zero.

**Theorem 1.3 (Coefficient-and-drift history extension is onto).**

Lean statement: `D5/S3/Observer/Linear/GainRayEvaluation.pureJ_history_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/GainRayEvaluation.pureJ_history_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d,n with n<=d+1, the map from Coeff d times the reals to real Fin n vectors, sending (beta,delta) to the vector gain(d,beta)(clocks n i)+delta, is surjective. The witness may take drift zero. This is the extension to the full coefficient space; it does not claim nonzero-gain fiber completion.

## References

- Truth anchor: `D5/S3/Observer/Linear/GainRayEvaluation.evaluation_injective`
- Truth anchor: `D5/S3/Observer/Linear/GainRayEvaluation.evaluation_surjective`
- Truth anchor: `D5/S3/Observer/Linear/GainRayEvaluation.pureJ_history_surjective`
- Dependency: [D5/S3/Observer/Linear/GainRayWorld](GainRayWorld.md)
