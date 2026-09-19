# A Counterexample to the Somer-Krizek Uniform-Subsequence Conjecture

## Abstract

A third-order integer recurrence refutes the proposed higher-order uniform-subsequence law.

Somer and Krizek define a k-th order integer recurrence with coefficients listed from the newest preceding term to the oldest. The formal recurrence therefore reverses that list for LinearRecurrence, whose coefficient at index i multiplies the term shifted by i.

**Definition 1.1 (The paper-order recurrence).**

Lean statement: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.paperRecurrence`

*Formalization.* `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.paperRecurrence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The order is k and coefficient i is the reversed paper coefficient.

**Definition 1.2 (Least positive modular period).**

Lean statement: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.IsLeastPositivePeriodMod`

*Formalization.* `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.IsLeastPositivePeriodMod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proposed period is positive, is a period after reduction modulo the modulus, and is at most every other positive modular period.

**Definition 1.3 (Uniform counts on a full period).**

Lean statement: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.UniformCounts`

*Formalization.* `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.UniformCounts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every residue in Fin(modulus), exactly copies indices below modulus times copies reduce to that residue.

**Definition 1.4 (Uniform arithmetic-subsequence counts).**

Lean statement: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.UniformSubsequenceCounts`

*Formalization.* `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.UniformSubsequenceCounts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every residue in Fin(modulus), exactly copies sampled values at start+n*step, for n below modulus times copies, reduce to that residue.

**Definition 1.5 (Somer and Krizek's Conjecture 4.2).**

$$fullClaim = \forall k: \mathbb{N}, ((2 \le k) \implies (\forall a: \operatorname{Fin}\left(k\right) \to \mathbb{Z}, (\forall w: \mathbb{N} \to \mathbb{Z}, ((\operatorname{IsSolution}\left(\operatorname{paperRecurrence}\left(a\right), w\right)) \implies (\forall p: \mathbb{N}, (\forall e: \mathbb{N}, (\forall E: \mathbb{N}, ((\operatorname{Prime}\left(p\right)) \implies ((1 \le e) \implies ((0 < E) \implies ((\operatorname{gcd}\left(\operatorname{a}\left((k) - (1)\right), p\right) = 1) \implies ((\operatorname{IsLeastPositivePeriodMod}\left(p^{e}, w, (p^{e}) \cdot (E)\right)) \implies ((\operatorname{UniformCounts}\left(p^{e}, E, w\right)) \implies (\forall g: \mathbb{N}, ((0 < g) \implies ((\operatorname{Coprime}\left(g, p\right)) \implies (\forall s: \mathbb{N}, (\operatorname{UniformSubsequenceCounts}\left(p^{e}, (E) / (\operatorname{gcd}\left(g, E\right)), g, s, w\right)))))))))))))))))))$$

*Formalization.* `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.fullClaim` (`✓ std3`).

*Citation.* Lawrence Somer; Michal Krizek (2025). *Generalization of a Theorem of Velez on Uniform Distribution in Second-Order Linear Recurrences*. DOI: [10.5281/zenodo.14679256](https://doi.org/10.5281/zenodo.14679256). URL: <https://math.colgate.edu/~integers/z1/z1.pdf>.

*Commentary.*

For every order k at least two, every integer coefficient vector and every integer solution, the source hypotheses quantify over a prime p, an exponent e at least one and a positive E. They require the last paper coefficient to be coprime to p, exact least period p^e E, and E copies of every residue in that period. For every positive g coprime to p and every nonnegative start s, the conclusion requires E/gcd(g,E) copies of every residue in the prescribed sampled range.

**Definition 1.6 (Six-code certificate words).**

Lean statement: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.CertificateWord`

*Formalization.* `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.CertificateWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A certificate word assigns one code in Fin 5 to each of six positions.

**Definition 1.7 (The actual encoded period).**

$$actualWord = (2, 3, 4, 2, 1, 0)$$

*Formalization.* `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.actualWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The codes (2,3,4,2,1,0) decode to the integer period (0,1,2,0,-1,-2).

**Definition 1.8 (Decoding a finite code).**

Lean statement: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.decodeCode`

*Formalization.* `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.decodeCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural value of a Fin 5 code is cast to the integers and shifted down by two.

**Definition 1.9 (The periodic integer sequence).**

Lean statement: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.sequenceOfWord`

*Formalization.* `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.sequenceOfWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At index n, the word is read at n modulo six and its finite code is decoded.

**Definition 1.10 (The third-order coefficients).**

$$actualCoefficients = (0, 0, -1)$$

*Formalization.* `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.actualCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The paper-order coefficient vector is (0,0,-1), so the recurrence is w(n+3)=-w(n).

**Definition 1.11 (The complete counterexample certificate).**

Lean statement: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.CounterexampleCertificate`

*Formalization.* `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.CounterexampleCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A certificate proves the all-index recurrence, exact least modular period six, two occurrences of every residue in the full orbit, and failure of the step-two sampled count.

**Definition 1.12 (Reusable refutation evidence).**

Lean statement: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.RefutationEvidence`

*Formalization.* `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.RefutationEvidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The evidence package contains the actual complete certificate and the map from any such certificate to the negation of the full source claim.

**Definition 1.13 (The proved refutation evidence).**

Lean statement: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.actualRefutationEvidence`

*Formalization.* `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.actualRefutationEvidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The private all-index proofs establish the actual certificate. Its refutation map instantiates every source quantifier at k=3, p=3, e=1, E=2, g=2 and s=0, then contradicts the sampled uniformity conclusion.

**Theorem 1.14 (Conjecture 4.2 is false).**

$$\operatorname{let}(counterexample = actualWord); \neg fullClaim$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lawrence Somer; Michal Krizek (2025). *Generalization of a Theorem of Velez on Uniform Distribution in Second-Order Linear Recurrences*. DOI: [10.5281/zenodo.14679256](https://doi.org/10.5281/zenodo.14679256). URL: <https://math.colgate.edu/~integers/z1/z1.pdf>.

*Commentary.*

The integer period is (0,1,2,0,-1,-2). It satisfies w(n+3)=-w(n) for every natural n. Modulo three, its least period is six and each residue occurs twice. With g=2 and s=0, E/gcd(g,E)=1 while the first three sampled residues are 0,2,2, so residue one occurs zero times. The retained let-bound actualWord is the same complete certificate used by the information readout.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.CertificateWord`
- Truth anchor: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.CounterexampleCertificate`
- Truth anchor: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.IsLeastPositivePeriodMod`
- Truth anchor: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.RefutationEvidence`
- Truth anchor: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.UniformCounts`
- Truth anchor: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.UniformSubsequenceCounts`
- Truth anchor: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.actualCoefficients`
- Truth anchor: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.actualRefutationEvidence`
- Truth anchor: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.actualWord`
- Truth anchor: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.decodeCode`
- Truth anchor: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.fullClaim`
- Truth anchor: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.paperRecurrence`
- Truth anchor: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.result`
- Truth anchor: `D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.sequenceOfWord`
