# Equal branch Choi Gram and unequal recovery fidelity

## Abstract

Two explicit four-dimensional channels share an exact Choi Gram and have unequal optimal recovery fidelity.

**Theorem 1.1 (Optimal score 3/4 for the conjugate pair).**

Lean statement: `D5/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation.exampleA_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation.exampleA_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In dimension four, the equally weighted branches are the identity and W_A with diagonal (exp(iπ/3), exp(iπ/3), exp(−iπ/3), exp(−iπ/3)). Every actual CPTP decoder scores at most 3/4. The diagonal decoder whose entries align 1+conj(z) at the corresponding diagonal entries z attains 3/4. The dual bound groups the two repeated conjugate phases and applies Cauchy–Schwarz.

**Theorem 1.2 (Optimal score 3/8 + √2/4 for the second pair).**

Lean statement: `D5/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation.exampleB_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation.exampleB_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second equally weighted channel has branches the identity and W_B = diag(1,1,i,−i). Every actual CPTP decoder scores at most 3/8 + √2/4. The same phase rule on these entries attains this value. In the dual bound, the two entries equal to one contribute at most 2 and the two imaginary entries contribute at most √2 before squaring and dividing by 16.

**Theorem 1.3 (Equality of the exact normalized branch Choi Grams).**

Lean statement: `D5/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation.equal_branch_choi_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation.equal_branch_choi_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The branch vector for a unitary U is (U ⊗ I) times the normalized canonical maximally entangled vector. Both relative unitaries have trace two, so the two exact unweighted two-by-two Grams have ones on the diagonal and 1/2 off the diagonal, in identity-then-unitary order.

**Theorem 1.4 (One exact Gram has two different optimal scores).**

Lean statement: `D5/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation.equal_gram_strict_recovery_separation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation.equal_gram_strict_recovery_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two normalized branch Choi Grams are equal. Every CPTP decoder for channel B scores strictly below the explicit unitary decoder for channel A, since 3/8 + √2/4 < 3/4. The score is single-use canonical entanglement fidelity at I/4 with the reference untouched.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation.equal_branch_choi_gram`
- Truth anchor: `D5/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation.equal_gram_strict_recovery_separation`
- Truth anchor: `D5/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation.exampleA_exact`
- Truth anchor: `D5/S3/Quantum/Recovery/EqualChoiGramRecoverySeparation.exampleB_exact`
- Dependency: [D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel](BinaryRandomUnitaryChannel.md)
