# Blake's Noncentral Twist Conjecture

## Abstract

Q₈ sequences of length at least two and Q₈ arrays with a first axis of length at least two and an odd transverse cardinality have a nonzero off-period autocorrelation for each noncentral twist.

**Definition 1.1 (The six noncentral twists).**

$$\operatorname{Noncentral}\left(u\right) \Leftrightarrow \left(u = \langle0, 1, 0, 0\rangle \lor \left(u = -\langle0, 1, 0, 0\rangle \lor \left(u = \langle0, 0, 1, 0\rangle \lor \left(u = -\langle0, 0, 1, 0\rangle \lor \left(u = \langle0, 0, 0, 1\rangle \lor u = -\langle0, 0, 0, 1\rangle\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.Noncentral` (`✓ std3`).

*Citation.* Sam Blake (2026). *A Recursive Construction of Perfect and Odd Perfect Sequences of Unbounded Length over the Unit Quaternions*. DOI: [10.48550/arXiv.2611.19627](https://doi.org/10.48550/arXiv.2611.19627). URL: <https://arxiv.org/abs/2611.19627v1>.

*Commentary.*

The coordinates are ordered by the real component and the coefficients of i, j and k. The displayed three coordinate units and their negatives are the six twists of Conjecture 5.2.

**Definition 1.2 (The quaternion alphabet).**

$$\operatorname{IsQ8}\left(u\right) \Leftrightarrow \left(u = 1 \lor \left(u = -1 \lor \operatorname{Noncentral}\left(u\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.IsQ8` (`✓ std3`).

*Citation.* Sam Blake (2026). *A Recursive Construction of Perfect and Odd Perfect Sequences of Unbounded Length over the Unit Quaternions*. DOI: [10.48550/arXiv.2611.19627](https://doi.org/10.48550/arXiv.2611.19627). URL: <https://arxiv.org/abs/2611.19627v1>.

*Commentary.*

The eight letters are the central units 1 and −1 and the six noncentral units. Their integer coordinates carry Hamilton multiplication and quaternion conjugation. The inclusion into the real Hamilton quaternions preserves these operations and is injective coordinatewise.

**Definition 1.3 (Right-twisted extension).**

$$\operatorname{extension}\left(s, u, q \cdot M + r\right) = s\left(r\right) \cdot u^{q}$$

*Formalization.* `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.extension` (`✓ std3`).

*Citation.* Sam Blake (2026). *A Recursive Construction of Perfect and Odd Perfect Sequences of Unbounded Length over the Unit Quaternions*. DOI: [10.48550/arXiv.2611.19627](https://doi.org/10.48550/arXiv.2611.19627). URL: <https://arxiv.org/abs/2611.19627v1>.

*Commentary.*

The positive length proof hM and the noncentrality proof hu are implicit in the display. For any integer n, Euclidean division by the positive length gives n = qM + r with 0 ≤ r < M. The definition uses that remainder as the sequence index. It multiplies on the right by the integer power of the twist unit, whose inverse is its quaternion conjugate. Thus the formula holds for negative q as well.

**Definition 1.4 (Twisted quaternion autocorrelation).**

$$\operatorname{correlation}\left(s, u, \tau\right) = \sum_{r:\operatorname{Fin}\left(M\right)} s\left(r\right) \cdot \operatorname{star}\left(\operatorname{extension}\left(s, u, r + \tau\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.correlation` (`✓ std3`).

*Citation.* Sam Blake (2026). *A Recursive Construction of Perfect and Odd Perfect Sequences of Unbounded Length over the Unit Quaternions*. DOI: [10.48550/arXiv.2611.19627](https://doi.org/10.48550/arXiv.2611.19627). URL: <https://arxiv.org/abs/2611.19627v1>.

*Commentary.*

The summation runs over Fin M and casts the summation index to an integer inside the extension. The star is quaternion conjugation. For a positive shift below M each wrapped term is the product of the original letter, the conjugate of u, and the conjugate of the wrapped letter, in that order.

**Theorem 1.5 (Nonvanishing at a positive off-period shift).**

$$\forall M \in \mathbb{N},\; 2 \le M \Rightarrow \left(\forall s \in \operatorname{Fin}\left(M\right) \to \operatorname{Quaternion}\left(\mathbb{Z}\right),\; (\forall r \in \operatorname{Fin}\left(M\right),\; \operatorname{IsQ8}\left(s\left(r\right)\right)) \Rightarrow \left(\forall u \in \operatorname{Quaternion}\left(\mathbb{Z}\right),\; \operatorname{Noncentral}\left(u\right) \Rightarrow \left(\exists tau \in \mathbb{Z},\; 0 < tau \land \left(tau < M \land \left(\left(\neg (M \mid tau)\right) \land \operatorname{correlation}\left(s, u, tau\right) \ne 0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.blake_conjecture_5_2` (`✓ std3`). ∎

*Resolves.* `Problems/blake-noncentral-quaternion-twist` (proved) by `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.blake_conjecture_5_2`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"blake-noncentral-quaternion-twist","declaration_gid":"D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.blake_conjecture_5_2","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sam Blake (2026). *A Recursive Construction of Perfect and Odd Perfect Sequences of Unbounded Length over the Unit Quaternions*. DOI: [10.48550/arXiv.2611.19627](https://doi.org/10.48550/arXiv.2611.19627). URL: <https://arxiv.org/abs/2611.19627v1>.

*Commentary.*

Conjecture 5.2 states "No sequence of length M ≥ 2 over Q₈ has type ±i, ±j or ±k." A positive integer shift below M is off-period, so the displayed existence statement excludes the asserted type.

Suppose that the correlations vanish at all positive shifts below M. The shift-one correlation maps to M in the field with two elements under the character that sends every letter to one. Hence M is even. Write M = dm with d its power-of-two part and m odd.

In the polynomial quotient by T to the power 2d, put W = 1 + T and V equal to one plus the d-th power of T. Characteristic two gives V = W to the power d and V squared equals one, so W to the power M equals V. A Hamilton quaternion algebra homomorphism sends i and k to V and j to one for the i and k twists. For the j twists it sends j and k to V and i to one. It identifies both signs and preserves the image of a letter under conjugation.

Form two weighted sums of the mapped letters with exponents r and M − 1 − r. Group the terms in the product by the difference of the two indices modulo M. A wrapped term has M extra powers of W, exactly the factor V in the mapped correlation. The off-diagonal groups therefore vanish. The diagonal is M times W to the power M − 1, which is zero.

Lift each letter to a polynomial of the form one or one plus T to the power d. Through degree d − 1 both factors have the coefficients of the same geometric sum. Multiplication by T sends that geometric sum to W to the power M minus one, which is T to the power d in the quotient. Each factor has its first nonzero coefficient at degree d − 1, with value one. Their product has coefficient one at degree 2d − 2, which survives the quotient and contradicts its vanishing.

**Definition 1.6 (Right-twisted base correlation).**

$$\forall T \in Type,\; [\operatorname{Fintype}\left(T\right)] [\operatorname{AddCommGroup}\left(T\right)] \forall M \in \mathbb{N},\; 0 < M \Rightarrow \left(\forall A \in \operatorname{Fin}\left(M\right) \to T \to \operatorname{Quaternion}\left(\mathbb{Z}\right),\; \forall u \in \operatorname{Quaternion}\left(\mathbb{Z}\right),\; \operatorname{Noncentral}\left(u\right) \Rightarrow \left(\forall tau \in \operatorname{Fin}\left(M\right),\; \forall sigma \in T,\; \operatorname{baseCorrelation}\left(A, u, tau, sigma\right) = \sum_{r:\operatorname{Fin}\left(M\right)} \sum_{t:T} A\left(r, t\right) \cdot \operatorname{star}\left(\operatorname{extension}\left((j \mapsto A\left(j, t + sigma\right)), u, \operatorname{int}\left(r\right) + \operatorname{int}\left(tau\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.baseCorrelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Definition 2.1 of Blake, arXiv:2611.20804v1, extends the first axis on the right. At each transverse coordinate t the existing extension acts on the column indexed by t. The transverse coordinate of the shifted entry is t plus sigma in the finite additive group. In the display, int takes the integer value of a finite index or natural number. The first-axis shift tau has integer representative between zero and M minus one.

**Definition 1.7 (Autocorrelation over the full extension period).**

$$\forall T \in Type,\; [\operatorname{Fintype}\left(T\right)] [\operatorname{AddCommGroup}\left(T\right)] \forall M \in \mathbb{N},\; 0 < M \Rightarrow \left(\forall A \in \operatorname{Fin}\left(M\right) \to T \to \operatorname{Quaternion}\left(\mathbb{Z}\right),\; \forall u \in \operatorname{Quaternion}\left(\mathbb{Z}\right),\; \operatorname{Noncentral}\left(u\right) \Rightarrow \left(\forall tau \in \operatorname{Fin}\left(M\right),\; \forall sigma \in T,\; \operatorname{fullPeriodCorrelation}\left(A, u, tau, sigma\right) = \sum_{q:\operatorname{Fin}\left(4\right)} \sum_{r:\operatorname{Fin}\left(M\right)} \sum_{t:T} \operatorname{extension}\left((j \mapsto A\left(j, t\right)), u, \operatorname{int}\left(q\right) \cdot \operatorname{int}\left(M\right) + \operatorname{int}\left(r\right)\right) \cdot \operatorname{star}\left(\operatorname{extension}\left((j \mapsto A\left(j, t + sigma\right)), u, \operatorname{int}\left(q\right) \cdot \operatorname{int}\left(M\right) + \operatorname{int}\left(r\right) + \operatorname{int}\left(tau\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.fullPeriodCorrelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three indices enumerate the period of first-axis length 4M as qM plus r, with q in Fin 4 and r in Fin M, and the transverse coordinate t in T. The star is quaternion conjugation. In equation (2.1) each of the two lifted entries has its block factor on the right. Taking the star of the second entry brings the two factors together in the order u to the power q followed by its conjugate. Their product is one, giving four times the base correlation.

**Theorem 1.8 (Nonvanishing for odd transverse cardinality).**

$$\forall T \in Type,\; [\operatorname{Fintype}\left(T\right)] [\operatorname{AddCommGroup}\left(T\right)] \forall M \in \mathbb{N},\; 2 \le M \Rightarrow \left(\forall A \in \operatorname{Fin}\left(M\right) \to T \to \operatorname{Quaternion}\left(\mathbb{Z}\right),\; \forall u \in \operatorname{Quaternion}\left(\mathbb{Z}\right),\; \operatorname{Noncentral}\left(u\right) \Rightarrow \left(\operatorname{Odd}\left(\operatorname{card}\left(T\right)\right) \Rightarrow \left((\forall r \in \operatorname{Fin}\left(M\right),\; \forall t \in T,\; \operatorname{IsQ8}\left(A\left(r, t\right)\right)) \Rightarrow \left(\exists tau \in \operatorname{Fin}\left(M\right),\; \exists sigma \in T,\; (tau, sigma) \ne (0, 0) \land \left(\operatorname{baseCorrelation}\left(A, u, tau, sigma\right) \ne 0 \land \operatorname{fullPeriodCorrelation}\left(A, u, tau, sigma\right) \ne 0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.odd_transverse_nonvanishing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first question in Section 9 of Blake, arXiv:2611.20804v1, asks which shapes admit arrays of noncentral type. Products of positive cyclic axes of odd cardinality give the finite additive groups in the statement. A shift different from the zero pair is off-period because the first coordinate is represented in the range zero through M minus one.

If every off-period base correlation vanishes, the trivial character at the shift with first coordinate one and transverse coordinate zero gives M times the cardinality of T equal to zero in characteristic two. Thus M is even. For every fixed first-axis shift, summing the character images over all transverse shifts pairs each transverse entry with every entry in the other column. The wrap factor depends only on the two first-axis indices. The zero shift contributes the diagonal M times the cardinality of T.

Let d be the power-of-two part of M. Use a character sending the twist to one plus X to the power d in the quotient by X to the power 2d. Odd transverse cardinality makes each column sum lift to one plus a multiple of X to the power d. The aggregated correlations force the cyclic product of the two weighted column sums to vanish. Its coefficient at degree 2d minus two is one, a contradiction. The factor four gives the same nonzero shift for the full period, since the quaternions have integer coordinates.

This excludes the odd-transverse family with first length at least two. The even transverse shapes, including the paper's two-by-two example, lie outside this family.

## References

- Truth anchor: `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.IsQ8`
- Truth anchor: `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.Noncentral`
- Truth anchor: `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.baseCorrelation`
- Truth anchor: `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.blake_conjecture_5_2`
- Truth anchor: `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.correlation`
- Truth anchor: `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.extension`
- Truth anchor: `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.fullPeriodCorrelation`
- Truth anchor: `D5/S3/Combinatorics/QuaternionSequences/BlakeConjecture52.odd_transverse_nonvanishing`
