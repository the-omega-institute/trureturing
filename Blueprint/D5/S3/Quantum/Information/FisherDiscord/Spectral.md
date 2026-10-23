# Fisher discord and the spectrum

## Abstract

Spectral formulas for Fisher discord in every finite dimension.

**Definition 1.1 (Spectral pair kernel).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Spectral.pairKernel`

*Formalization.* `D5/S3/Quantum/Information/FisherDiscord/Spectral.pairKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The kernel is twice sqrt(ab) times the squared difference of sqrt(a) and sqrt(b), divided by a+b. Real division assigns zero to a zero denominator.

**Theorem 1.2 (Diagonal Fisher formula).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Spectral.fisherSLD_diag`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FisherDiscord/Spectral.fisherSLD_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonnegative real diagonal and every Hermitian SLD solution, Fisher information is one half of the sum over ordered pairs of (a-b)^2/(a+b) times the squared modulus of the observable entry. The SLD may be arbitrary on the joint zero eigenspace; the trace weights erase that freedom.

**Theorem 1.3 (Diagonal skew formula).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Spectral.skewWY_diag`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FisherDiscord/Spectral.skewWY_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonnegative diagonal and a Hermitian observable, skew information is one half of the sum over ordered pairs of the squared difference of square roots times the squared modulus of the observable entry.

**Theorem 1.4 (Diagonal discord formula).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Spectral.discord_diag`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FisherDiscord/Spectral.discord_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting skew information from Fisher information gives one half of the sum of the pair kernel times the squared modulus of each observable entry. All SLD solutions have this same value.

**Theorem 1.5 (Nonnegative pair kernel).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Spectral.pairKernel_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FisherDiscord/Spectral.pairKernel_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pair kernel is nonnegative for all nonnegative arguments, including the boundary where either or both arguments vanish.

**Theorem 1.6 (Nonnegative diagonal discord).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Spectral.discord_nonneg_diag`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FisherDiscord/Spectral.discord_nonneg_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spectral terms are nonnegative for every nonnegative diagonal, Hermitian observable and Hermitian SLD solution.

**Theorem 1.7 (Fisher formula in an eigenbasis).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Spectral.fisherSLD_spectral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FisherDiscord/Spectral.fisherSLD_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal formula applies to every positive semidefinite matrix after conjugation by its eigenvector unitary. The observable entries are taken in that eigenbasis, and the formula holds for every Hermitian SLD solution.

**Theorem 1.8 (Skew formula in an eigenbasis).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Spectral.skewWY_spectral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FisherDiscord/Spectral.skewWY_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive square root and skew information respect unitary conjugation. The diagonal skew formula therefore applies to the eigenvalues of every positive semidefinite matrix.

**Theorem 1.9 (Discord formula in an eigenbasis).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Spectral.discord_spectral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FisherDiscord/Spectral.discord_spectral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In an eigenbasis of an arbitrary positive semidefinite matrix, Fisher discord is one half of the sum of the nonnegative pair kernel times squared observable entries. No choice of SLD changes this value.

**Theorem 1.10 (Nonnegative Fisher discord).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Spectral.discord_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/FisherDiscord/Spectral.discord_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite positive semidefinite matrix and Hermitian observable, Fisher information minus skew information is nonnegative for every Hermitian SLD solution.

## References

- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Spectral.discord_diag`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Spectral.discord_nonneg`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Spectral.discord_nonneg_diag`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Spectral.discord_spectral`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Spectral.fisherSLD_diag`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Spectral.fisherSLD_spectral`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Spectral.pairKernel`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Spectral.pairKernel_nonneg`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Spectral.skewWY_diag`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Spectral.skewWY_spectral`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Information/FisherDiscord/Defs](Defs.md)
