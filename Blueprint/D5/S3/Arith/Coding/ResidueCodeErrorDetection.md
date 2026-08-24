# Minimum-Distance Error Detection

## Abstract

A code of minimum distance at least d detects every nonzero error of weight at most d - 1, and this guarantee is sharp.

**Lemma 1.1 (Codewords closer than the minimum distance coincide).**

$$\forall C, c, x, d, (\operatorname{MinDistanceAtLeast}\left(C, d\right) \land c \in C \land x \in C \land \operatorname{hammingDist}\left(c, x\right) < d) \Rightarrow x = c.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/ResidueCodeErrorDetection.codeword_eq_of_hammingDist_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose every distinct pair of words in a code is separated by at least d coordinates. If two codewords c and x have Hamming distance strictly below d, they cannot be distinct and hence must be the same word.

**Theorem 1.2 (Minimum distance detects errors through d minus one).**

$$\forall C, c, x, d, (\operatorname{MinDistanceAtLeast}\left(C, d\right) \land c \in C \land 1 \leq \operatorname{hammingDist}\left(c, x\right) \land \operatorname{hammingDist}\left(c, x\right) \leq d - 1) \Rightarrow \neg (x \in C).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/ResidueCodeErrorDetection.detects_up_to_min_distance_minus_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c be a transmitted codeword and x the received word. Positive Hamming distance makes the error nonzero, while a distance at most d - 1 places x strictly inside the minimum-distance radius. If x were another codeword, the code's distance condition would force its distance from c to be at least d, a contradiction.

**Theorem 1.3 (The d minus one detection bound is sharp).**

$$\forall d \in \mathbb{N}, 0 < d \Rightarrow \exists C \subseteq \{0, 1\}^{d}, \exists c, x, (\operatorname{MinDistanceAtLeast}\left(C, d\right) \land c \in C \land x \in C \land c \neq x \land \operatorname{hammingDist}\left(c, x\right) = d).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/ResidueCodeErrorDetection.detection_bound_is_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive d, take the two Boolean words of length d that are constantly false and constantly true. They differ in every coordinate, so their Hamming distance is exactly d, and the two-word code has minimum distance d. An error of weight d can therefore carry one valid codeword to the other.

## References

- Truth anchor: `D5/S3/Arith/Coding/ResidueCodeErrorDetection.codeword_eq_of_hammingDist_lt`
- Truth anchor: `D5/S3/Arith/Coding/ResidueCodeErrorDetection.detection_bound_is_sharp`
- Truth anchor: `D5/S3/Arith/Coding/ResidueCodeErrorDetection.detects_up_to_min_distance_minus_one`
