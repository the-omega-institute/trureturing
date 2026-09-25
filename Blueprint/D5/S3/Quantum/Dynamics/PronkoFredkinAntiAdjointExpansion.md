# Pronko's operators as finite anti-adjoint expansions

## Abstract

The total spin operators and the anti-adjoint action are defined on the spin-word basis of the periodic Fredkin chain. Pronko's nonlocal raising and lowering operators are then finite anti-adjoint expansions of the total spin operators, with one family of coefficients for both signs and every number of sites.

**Definition 1.1 (The anti-adjoint action).**

$$\forall N \in \mathbb{N},\; \forall a \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall b \in \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{antiAd}\left(a, b\right) = ((a) \cdot (b)) + ((b) \cdot (a))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.antiAd` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

For square complex matrices a and b indexed by spin words, the anti-adjoint action of a on b is the anticommutator a b + b a, as printed with Conjecture 2.

**Definition 1.2 (The total raising operator).**

$$\forall N \in \mathbb{N},\; \operatorname{totalPlus}\left(N\right) = \sum_{j \in \operatorname{Fin}\left(N\right)} (\operatorname{site}\left(N, j, sigmaPlus\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.totalPlus` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

The total raising operator is the sum over every site j in Fin N of the one-site raising matrix sigmaPlus acting at site j, matching the normalization chosen in section 2.1 without a factor one half.

**Definition 1.3 (The total lowering operator).**

$$\forall N \in \mathbb{N},\; \operatorname{totalMinus}\left(N\right) = \sum_{j \in \operatorname{Fin}\left(N\right)} (\operatorname{site}\left(N, j, sigmaMinus\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.totalMinus` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

The total lowering operator is the sum over every site j in Fin N of the one-site lowering matrix sigmaMinus acting at site j.

**Definition 1.4 (Pronko's Conjecture 2).**

$$claim \Leftrightarrow (\forall N \in \mathbb{N},\; \exists gamma \in \operatorname{Fin}\left(\left\lfloor\frac{(N) + (1)}{2}\right\rfloor\right) \to \mathbb{C},\; (\operatorname{Sigma}\left(N, 1\right) = \sum_{k \in \operatorname{Fin}\left(\left\lfloor\frac{(N) + (1)}{2}\right\rfloor\right)} ((gamma\left(k\right)) \cdot (\operatorname{Nat.iterate}\left((X \mapsto \operatorname{antiAd}\left(\operatorname{totalPlus}\left(N\right), \operatorname{antiAd}\left(\operatorname{totalMinus}\left(N\right), X\right)\right)), k, \operatorname{totalPlus}\left(N\right)\right)))) \land (\operatorname{Sigma}\left(N, -(1)\right) = \sum_{k \in \operatorname{Fin}\left(\left\lfloor\frac{(N) + (1)}{2}\right\rfloor\right)} ((gamma\left(k\right)) \cdot (\operatorname{Nat.iterate}\left((X \mapsto \operatorname{antiAd}\left(\operatorname{totalMinus}\left(N\right), \operatorname{antiAd}\left(\operatorname{totalPlus}\left(N\right), X\right)\right)), k, \operatorname{totalMinus}\left(N\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.claim` (`✓ std3`).

*Citation.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

For every number of sites N there is a single complex coefficient family gamma indexed by Fin of the floor of (N + 1)/2, which equals the ceiling of N/2. The Lean index k corresponds to the printed index k + 1, so the exponent k of the iterated map is the printed exponent k - 1. For the raising sign the iterated map sends X to the anti-adjoint action of totalPlus N on the anti-adjoint action of totalMinus N on X, applied to totalPlus N; for the lowering sign the two total spin operators are exchanged. Sigma N 1 and Sigma N (-1) are the operators of equation (3.1). The printed table lists the coefficients for N from 3 to 10; the statement covers every natural number N.

**Theorem 1.5 (Conjecture 2 holds).**

$$\forall N \in \mathbb{N},\; \exists gamma \in \operatorname{Fin}\left(\left\lfloor\frac{(N) + (1)}{2}\right\rfloor\right) \to \mathbb{C},\; (\operatorname{Sigma}\left(N, 1\right) = \sum_{k \in \operatorname{Fin}\left(\left\lfloor\frac{(N) + (1)}{2}\right\rfloor\right)} ((gamma\left(k\right)) \cdot (\operatorname{Nat.iterate}\left((X \mapsto \operatorname{antiAd}\left(\operatorname{totalPlus}\left(N\right), \operatorname{antiAd}\left(\operatorname{totalMinus}\left(N\right), X\right)\right)), k, \operatorname{totalPlus}\left(N\right)\right)))) \land (\operatorname{Sigma}\left(N, -(1)\right) = \sum_{k \in \operatorname{Fin}\left(\left\lfloor\frac{(N) + (1)}{2}\right\rfloor\right)} ((gamma\left(k\right)) \cdot (\operatorname{Nat.iterate}\left((X \mapsto \operatorname{antiAd}\left(\operatorname{totalMinus}\left(N\right), \operatorname{antiAd}\left(\operatorname{totalPlus}\left(N\right), X\right)\right)), k, \operatorname{totalMinus}\left(N\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.result` (`✓ std3`). ∎

*Resolves.* `Problems/pronko-2025-fredkin-anti-adjoint-expansion` (proved) by `D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pronko-2025-fredkin-anti-adjoint-expansion","declaration_gid":"D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Andrei G. Pronko (2025). *Symmetries of the periodic Fredkin chain*. DOI: [10.1088/1751-8121/ae1644](https://doi.org/10.1088/1751-8121/ae1644). URL: <https://doi.org/10.1088/1751-8121/ae1644>.

*Commentary.*

For spin words y and x let b count the sites with y up and x down, and c the sites with y down and x up. Let Z_r be the matrix with entry one exactly when b = r + 1 and c = r, and E_s the matrix with entry one exactly when b = c = s. Summing single-site flips site by site gives the anticommutator identities {S^-, Z_r} = 2(r + 1) E_(r+1) + (N - 2r) E_r and {S^+, E_s} = 2(s + 1) Z_s + (N - 2s + 1) Z_(s-1), where the counts of sites with equal letters combine to N - b - c. Composing them, the map X to {S^+, {S^-, X}} sends Z_r to 4(r + 1)(r + 2) Z_(r+1) + 2(r + 1)(2N - 4r - 1) Z_r + (N - 2r)(N - 2r + 1) Z_(r-1). The case s = 0 gives S^+ = Z_0 because E_0 is the identity, and the leading coefficient 4(r + 1)(r + 2) is nonzero, so by induction on r each Z_r lies in the span of the first r + 1 iterates of that map applied to S^+. Reading the Kronecker sum (3.1) entrywise gives Sigma^+(y, x) = 1 exactly when b - c = 1, and b + c is at most N, so Sigma^+ is the sum of Z_r over r below the ceiling of N/2 and lies in the span of the first ceiling of N/2 iterates, which yields the coefficients. Transposition exchanges sigmaPlus with sigmaMinus, maps Sigma^+ to Sigma^- and each raising iterate to the corresponding lowering iterate, so the same coefficients give the lowering identity.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.antiAd`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.totalMinus`
- Truth anchor: `D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.totalPlus`
- Dependency: [D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation](PronkoFredkinNonCyclicAnnihilation.md)
