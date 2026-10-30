# Failure of differentiability

## Abstract

A faithful four-level example with a corner in its asymptotic overlap.

**Definition 1.1 (Two competing overlap branches).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Result.counterexamplePsi`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/Result.counterexamplePsi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set p=(16,9,4,1)/30 and q=(4,1,9,16)/30. Let C(s) be the sum of p(i) to the power s times q(i) to the power one minus s. The two-element group exchanges the first two and the last two coordinates, and its other relative overlap is C(1-s). The asymptotic function is the maximum of log C(s) and log C(1-s). All four entries of both probability vectors are strictly positive.

**Theorem 1.2 (Distinct derivatives at the common value).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Result.one_sided_derivs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/Result.one_sided_derivs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At s=1/2 the two overlaps both equal 7/10. Their logarithmic derivatives are opposite, with absolute value (2/7) log(4/3). The left difference quotients of their maximum converge to the negative value and the right difference quotients converge to the positive value. At a common value, division by a negative increment exchanges maximum with minimum; division by a positive increment preserves maximum. This gives the two limits directly from the branch derivatives.

**Theorem 1.3 (The differentiability assertion is false).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/hiai-mosonyi-hayashi-2009-group-invariant-psi-differentiability-refutation` (refuted) by `D5/S3/Quantum/Information/GroupInvariantPsi/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hiai-mosonyi-hayashi-2009-group-invariant-psi-differentiability-refutation","declaration_gid":"D5/S3/Quantum/Information/GroupInvariantPsi/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Use diagonal density matrices with diagonals p and q on four complex dimensions and the permutation representation of the two-element group. The matrices are positive definite and have trace one. The tensor mixture sandwich proves convergence throughout the interval (0,1) and identifies its selected limit with the two-branch maximum. Differentiability at one half would make the left and right difference quotients converge to the same number, contradicting the two distinct limits. Finite groups are compact with uniform normalized Haar measure, so this example also refutes the corresponding assertion over compact groups. The proof uses this single explicit instance; it does not require a parameterized family.

## References

- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Result.counterexamplePsi`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Result.one_sided_derivs`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Result.result`
- Dependency: [D5/S3/Quantum/Information/GroupInvariantPsi/Sandwich](Sandwich.md)
