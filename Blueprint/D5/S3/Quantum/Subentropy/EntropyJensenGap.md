# Finite entropy Jensen gap

## Abstract

Finite entropy Jensen gaps are nonnegative, homogeneous and jointly convex.

**Definition 1.1 (Uniform finite average).**

Lean statement: `D5/S3/Quantum/Subentropy/EntropyJensenGap.finiteAverage`

*Formalization.* `D5/S3/Quantum/Subentropy/EntropyJensenGap.finiteAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite real family a indexed by S, finiteAverage(a)=sum_s a_s/card(S). The entropy inequalities use nonempty S.

**Definition 1.2 (Entropy Jensen gap).**

Lean statement: `D5/S3/Quantum/Subentropy/EntropyJensenGap.entropyJensenGap`

*Formalization.* `D5/S3/Quantum/Subentropy/EntropyJensenGap.entropyJensenGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entropy Jensen gap is J(a)=η(av(a))−av(η(a)), where η(u)=−u log u uses the continuous value η(0)=0.

**Theorem 1.3 (The full nonnegative cone).**

Lean statement: `D5/S3/Quantum/Subentropy/EntropyJensenGap.entropyJensenGap_laws`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/EntropyJensenGap.entropyJensenGap_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonempty finite index type S, let av(a)=sum_s a_s/card(S) and η(u)=−u log u, with η(0)=0. The gap J(a)=η(av(a))−av(η(a)) is nonnegative, satisfies J(ca)=cJ(a) for c≥0, and is jointly convex for all nonnegative real vectors.

Nonnegativity is finite Jensen applied to the concave function η. The product identity η(cx)=xη(c)+cη(x) gives homogeneity. For nonzero means A=av(a) and B=av(b), normalize by A and B. Concavity of η with weights A/(A+B), B/(A+B), followed by averaging and multiplication by A+B, gives J(a+b)≤J(a)+J(b). Zero mean forces every nonnegative coordinate to vanish. Subadditivity and homogeneity yield joint convexity, including all boundary faces.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/EntropyJensenGap.entropyJensenGap`
- Truth anchor: `D5/S3/Quantum/Subentropy/EntropyJensenGap.entropyJensenGap_laws`
- Truth anchor: `D5/S3/Quantum/Subentropy/EntropyJensenGap.finiteAverage`
