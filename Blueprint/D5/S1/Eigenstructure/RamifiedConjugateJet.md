# Ramified Conjugate Jet

## Abstract

A repeated residue eigenvalue retains the infinite power jet of its nilpotent part.

**Definition 1.1 (The ramified jet records every positive residual power).**

$$\operatorname{RamJet}\left(lambdaZero, T\right) = (lambdaZero, (k \mapsto (T - lambdaZero I)^{k + 1})).$$

*Formalization.* `D5/S1/Eigenstructure/RamifiedConjugateJet.ramifiedConjugateJet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar center is followed by a natural-number-indexed sequence. Index zero stores the first residual power, so the definition is an infinite sequence rather than a truncated tuple.

**Theorem 1.2 (A nonzero square-zero direction realizes the golden ramified jet).**

$$\begin{aligned}\exists N, T \in \operatorname{Matrix}\left(2, \operatorname{ZMod}\left(5\right)\right),\\N = \operatorname{single}\left(0, 1, 1\right) \land T = 3 I + N,\\N \neq 0 \land N^{2} = 0 \land \operatorname{rank}\left(N\right) = 1,\\\operatorname{charpoly}\left(T\right) = (X - 3)^{2} \land \operatorname{rootMultiplicity}\left(3, \operatorname{charpoly}\left(T\right)\right) = 2,\\\operatorname{RamJet}\left(3, T\right) = (3, (k \mapsto N^{k + 1})),\\\operatorname{tail}\left(\operatorname{RamJet}\left(3, T\right), 0\right) = N \land \forall k \geq 1, \operatorname{tail}\left(\operatorname{RamJet}\left(3, T\right), k\right) = 0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/RamifiedConjugateJet.exists_golden_ramified_conjugate_jet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over ZMod 5, the upper off-diagonal matrix N is nonzero, has rank one, and satisfies N squared equals zero. Translating it by three times the identity gives a matrix whose characteristic polynomial has three as a root of multiplicity two.

The resulting jet has N as its index-zero term and N to the power k+1 at every index k. Square-zero nilpotence makes every term after index zero vanish, while preserving a nontrivial first direction.

The proof reuses the repository's standard rank-one nilpotent matrix witness and Mathlib's two-by-two characteristic-polynomial and root-multiplicity theorems.

## References

- Truth anchor: `D5/S1/Eigenstructure/RamifiedConjugateJet.exists_golden_ramified_conjugate_jet`
- Truth anchor: `D5/S1/Eigenstructure/RamifiedConjugateJet.ramifiedConjugateJet`
- Dependency: [D5/S0/Observation/PowerTraceSimilarityCountermodel](../../S0/Observation/PowerTraceSimilarityCountermodel.md)
