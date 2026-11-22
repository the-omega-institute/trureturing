# Sharp conditional entropy and Bayes error

## Abstract

Sharp binary conditional entropy and Bayes error frontiers.

**Theorem 1.1 (Posterior decision rule attains the minimum error).**

Lean statement: `D5/S3/Entropy/BinaryCompression.bayesError_isLeast`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/BinaryCompression.bayesError_isLeast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fair label and any finite stochastic view, choose the more probable label at each view. The posterior formula gives the least probability of error, including ties.

**Theorem 1.2 (The posterior formula gives conditional entropy in bits).**

Lean statement: `D5/S3/Entropy/BinaryCompression.entropyBits_eq_conditionalEntropy`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/BinaryCompression.entropyBits_eq_conditionalEntropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint law has masses equal to half the compression entries. The posterior expression equals the repository conditional entropy divided by log two. A zero-mass view contributes zero.

**Theorem 1.3 (Sharp binary entropy and error inequalities).**

Lean statement: `D5/S3/Entropy/BinaryCompression.entropy_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/BinaryCompression.entropy_budget` (`✓ std3`). ∎

*Citation.* Meir Feder; Neri Merhav (1994). *Relations between entropy and error probability*. DOI: [10.1109/18.272494](https://doi.org/10.1109/18.272494). URL: <https://doi.org/10.1109/18.272494>.

*Commentary.*

For Bayes error e and conditional entropy H in bits, 2e ≤ H ≤ h₂(e). The lower bound integrates the chord of binary entropy on [0, 1/2], and the upper bound applies sharp finite Fano in the two-label case.

**Theorem 1.4 (Erasure and symmetric flip attain the bounds).**

Lean statement: `D5/S3/Entropy/BinaryCompression.entropy_frontiers`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/BinaryCompression.entropy_frontiers` (`✓ std3`). ∎

*Citation.* Meir Feder; Neri Merhav (1994). *Relations between entropy and error probability*. DOI: [10.1109/18.272494](https://doi.org/10.1109/18.272494). URL: <https://doi.org/10.1109/18.272494>.

*Commentary.*

At each entropy H between zero and one, the erasure view has error H/2. The symmetric flip with error t has entropy h₂(t), where t is the unique inverse on [0, 1/2]. The formulas include both endpoints.

## References

- Truth anchor: `D5/S3/Entropy/BinaryCompression.bayesError_isLeast`
- Truth anchor: `D5/S3/Entropy/BinaryCompression.entropyBits_eq_conditionalEntropy`
- Truth anchor: `D5/S3/Entropy/BinaryCompression.entropy_budget`
- Truth anchor: `D5/S3/Entropy/BinaryCompression.entropy_frontiers`
- Dependency: [D5/S3/Entropy/ConditionalEntropy](ConditionalEntropy.md)
- Dependency: [D5/S3/Estimation/FanoSharp](../Estimation/FanoSharp.md)
