# QubitEntropyContraction

## Abstract

Quadratic contraction for an actual symmetric qubit ensemble

**Theorem 1.1 (Quadratic contraction for an actual symmetric qubit ensemble).**

$$\forall x,z,t:\mathbb{R},\ {(x^{2})+(z^{2})\le 1\land 0\le t\land t\le 1}\implies 0\le \operatorname{qubitHolevo}(x, (t)\times (z))\land \operatorname{qubitHolevo}(x, (t)\times (z))\le (t^{2})\times (\operatorname{qubitHolevo}(x, z))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/QubitEntropyContraction.qubit_holevo_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

For every point of the closed qubit disk and every t in [0,1], the symmetric binary Holevo entropy is nonnegative and contracts by at most t squared when z is replaced by tz. The proof derives concavity of u mapped to binary entropy of (1+sqrt(u))/2 from scalar derivatives on (0,1), with continuity at both endpoints. The matrix statement then uses the actual qubit density states and their spectral entropy, including pure, zero-separation and maximal-mixing cases.

## References

- Truth anchor: `D5/S3/Quantum/Information/QubitEntropyContraction.qubit_holevo_contraction`
- Dependency: [D5/S3/Quantum/Information/QubitNormalFormState](QubitNormalFormState.md)
