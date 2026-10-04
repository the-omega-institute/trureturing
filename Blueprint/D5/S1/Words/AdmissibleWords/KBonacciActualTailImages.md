# Exact suffix images of actual words

## Abstract

Literal terminal-one and trailing-zero conditions give exact image decompositions for actual admissible Boolean words over any commutative ring.

Fix a commutative ring C, a point x in C, and an order k at least two. A word of length n is a function from Fin n to Bool, accepted by the original scanner forbidding k consecutive true bits. Its value is the sum of x^j over its true positions, counted from the constant term. Let I_n be the set of values of these accepted length-n words, and let S_s be the sum of x^j for zero at most j below s.

T_(n,s) imposes s at most n, true bits in the final s positions, and a false bit at position n-s-1 whenever that position exists. Z_(n,z) imposes z at most n and false bits in the final z positions. Both sets use the same actual accepted words as I_n.

**Theorem 1.1 (All terminal-one and trailing-zero branches).**

$$T_{n,s}=\begin{cases}\emptyset&n<s\\\{S_s\}&n=s\\I_{n-s-1}+x^{n-s}S_s&s+1\leq n\end{cases}\qquad\land\qquad Z_{n,z}=\begin{cases}\emptyset&n<z\\I_{n-z}&z\leq n\end{cases}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciActualTailImages.actual_tail_zero_image_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equations hold for every natural n, every s below k, and every positive z. At n=s the only word is the all-true word, including the empty word when s=0. For n at least s+1, every exact-tail word has the form v followed by a false bit and then s true bits, with v of length n-s-1.

Deleting the suffix preserves acceptance. Conversely, the scanner through a prefix followed by a false delimiter is the conjunction of its prefix scan and a fresh full-budget scan of the remaining suffix. This equation preserves rejection of the prefix, and the true suffix is accepted because s is below k. The suffix contributes x^(n-s) times S_s to the value.

A word with z trailing false bits is a legal prefix of length n-z followed by z actual zero positions. Those positions preserve acceptance and value. A suffix longer than the actual word is impossible. Ring multiplication and addition are those of C; when C is a common polynomial image subring, the same one polynomial supplies every quotient coordinate.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciActualTailImages.actual_tail_zero_image_decomposition`
- Dependency: [D5/S0/Tower/DBonacci/Substitution](../../../S0/Tower/DBonacci/Substitution.md)
