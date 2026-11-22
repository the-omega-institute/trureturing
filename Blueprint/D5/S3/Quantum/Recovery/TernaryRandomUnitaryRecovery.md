# Nonunitary optimal recovery for three commuting branches

## Abstract

Exact recovery for a three-branch commuting random-unitary channel.

**Theorem 1.1 (Commuting unitary branches).**

Lean statement: `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.branches_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.branches_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal phase columns are (1, −i, i, 1), (1, i, 1, −i), and (1, 1, −i, i).

**Theorem 1.2 (Equal-weight channel action).**

Lean statement: `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.channel_action`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.channel_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual CPTP noise acts by averaging the three unitary conjugations.

**Theorem 1.3 (Upper bound for all CPTP decoders).**

Lean statement: `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.score_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.score_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the maximally mixed input with an untouched reference, the score of every CPTP decoder is at most 1/4 + √3/6. The canonical Kraus trace identity uses the conjugated diagonals of the decoder Kraus matrices. Trace preservation bounds their squared row norms. The Hermitian slack M satisfies M² = 4√3 M, so the loss in each coordinate column is a sum of squared moduli divided by 4√3.

**Theorem 1.4 (Two diagonal Kraus operators).**

Lean statement: `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.optimalDecoder_action`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.optimalDecoder_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put a = 2√3/3 − 1 and ω = (−1 − i√3)/2. The two diagonals are the conjugates of (1,a,a,a) and √(1−a²)(0,1,ω,ω²). Their coordinatewise squared moduli sum to one.

**Theorem 1.5 (Attainment of the exact CPTP endpoint).**

Lean statement: `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.score_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.score_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two conjugated Kraus diagonals lie in the kernel of the slack, so the decoder attains 1/4 + √3/6.

**Theorem 1.6 (Strict bound for every unitary decoder).**

Lean statement: `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.unitary_score_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.unitary_score_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary unitary decoder, equality would force unit squared modulus at all four diagonal entries and place the conjugated diagonal in the slack kernel. The explicit projector expresses any kernel vector as a combination of the two displayed directions. Equal moduli in the last three coordinates force the coefficient of the cube-root direction to vanish, which contradicts the first-coordinate modulus and a < 1.

**Theorem 1.7 (Three branches are necessary).**

Lean statement: `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.no_binary_representation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.no_binary_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The checked binary recovery theorem gives a unitary optimum in every positive dimension and allows zero weights. Therefore this channel has no one- or two-branch random-unitary representation.

The separate dimension bound uses simultaneous diagonalization of commuting normal matrices and the Li–Tam bound r² ≤ d for an extreme complex correlation matrix of rank r and size d. For d ≤ 3 a maximizing extreme correlation matrix has rank one and yields a diagonal unitary decoder.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.branches_commute`
- Truth anchor: `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.channel_action`
- Truth anchor: `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.no_binary_representation`
- Truth anchor: `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.optimalDecoder_action`
- Truth anchor: `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.score_attained`
- Truth anchor: `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.score_le`
- Truth anchor: `D5/S3/Quantum/Recovery/TernaryRandomUnitaryRecovery.unitary_score_lt`
- Dependency: [D5/S3/Quantum/Recovery/BinaryRandomUnitaryRecovery](BinaryRandomUnitaryRecovery.md)
