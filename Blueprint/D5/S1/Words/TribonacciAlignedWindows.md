# Aligned Repetition Windows in the Tribonacci Word

## Abstract

The actual Tribonacci word contains uniformly large odd repetition windows at even starts in all sufficiently long even substitution prefixes.

The alphabet is Fin 3. Letters A, B and C mean 0, 1 and 2, respectively. All indices and lengths below are natural numbers, and the first letter has index zero.

**Definition 1.1 (The literal substitution).**

$$sigma\left(0\right) = List\left(0, 1\right) \land \left(sigma\left(1\right) = List\left(0, 2\right) \land sigma\left(2\right) = List\left(0\right)\right)$$

*Formalization.* `D5/S1/Words/TribonacciAlignedWindows.sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The substitution is exactly A to AB, B to AC and C to A. It is the order-three instance of phi in MBonacciSentinelDesubstitution.

**Definition 1.2 (The closed infinite word).**

$$\forall n \in \mathbb{N},\; W\left(n\right) = word\left(3, n\right)$$

*Formalization.* `D5/S1/Words/TribonacciAlignedWindows.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W is the actual closed word supplied by MBonacciSentinelDesubstitution.word at order three. Its nth letter is read from the (n+1)st iterate on A. Nested, unbounded iterates make this reading agree with every sufficiently long finite iterate. No occurrence or recurrence hypothesis is assumed.

**Definition 1.3 (Actual iterate lengths).**

$$\forall j \in \mathbb{N},\; L\left(j\right) = length\left(image\left(sigma, j, 0\right)\right)$$

*Formalization.* `D5/S1/Words/TribonacciAlignedWindows.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L(j) is the length of the actual jth substitution iterate on A, including L(0)=1. The generic image function uses identity at level zero and literal substitution at each successor.

**Definition 1.4 (Rounding to an even prefix).**

$$\forall j \in \mathbb{N},\; N\left(j\right) = 2 \cdot natDiv\left(L\left(j\right), 2\right)$$

*Formalization.* `D5/S1/Words/TribonacciAlignedWindows.N` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(j)=2 times the natural quotient L(j)/2. It is the greatest even natural not exceeding L(j); at most one final letter is removed.

**Theorem 1.5 (A uniform repetition event).**

$$\exists K \in \mathbb{N},\; 0 < K \land \left(\exists J \in \mathbb{N},\; 1 \le J \land \left(\forall j \in \mathbb{N},\; J \le j \Rightarrow \left(\exists m \in \mathbb{N},\; \exists s \in \mathbb{N},\; 3 \le m \land \left(Odd\left(m\right) \land \left(Even\left(s\right) \land \left(N\left(j\right) \le K \cdot m \land \left(s + 2 \cdot m \le N\left(j\right) \land \left(\forall i \in \mathbb{N},\; i < m - 1 \Rightarrow W\left(s + i + m\right) = W\left(s + i\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TribonacciAlignedWindows.aligned_windows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are positive natural constants K and J, with J at least one, such that every j at least J admits natural m and s. The block length m is odd and at least three, s is even, N(j) is at most K times m, and s+2m is at most N(j). Every natural i less than m-1 satisfies literal equality W(s+i+m)=W(s+i). The constants are independent of j and of every hopping parameter.

One may take K=128 and J=4. Write q as the natural quotient (j-4)/4 and k=4q, so k+4 is at most j and j is at most k+7. The fourth iterate on A is ABAC followed by ABA, ABA and CAB. Apply k substitutions to all four pieces. The two images of ABA coincide literally. The starting prefix has length 2 times the A-image length plus the B- and C-image lengths; each repeated block has length 2 times the A-image length plus the B-image length.

At every level divisible by four all three letter-image lengths are odd. This follows by induction from the explicit fourth images, of lengths 13, 11 and 7. Consequently the starting prefix has even length and the repeated block has odd length. All letter images are nonempty, so the repeated block has at least three letters and the terminal image of CAB leaves a nonempty suffix. Removing at most one final letter therefore preserves the whole square. Each substitution increases length by at most a factor of two, and seven successive steps give the factor 128. The repeated block contains the kth A-image, which supplies the comparison with N(j).

For a hopping model encoded by this actual word, the conclusion supplies the odd length, even start, literal repetition, proportional scale and containment needed to select a finite inverse-matrix window. The matrix theorem odd_square_inverse_paired_mass is a downstream algebraic supplier; it does not supply these word occurrences. Embedding that window into the full physical-prefix inverse, controlling the resulting norm and spectrum, and deriving the entropy conclusion remain separate unproved interfaces. No global spectral or entropy conclusion follows here.

## References

- Truth anchor: `D5/S1/Words/TribonacciAlignedWindows.L`
- Truth anchor: `D5/S1/Words/TribonacciAlignedWindows.N`
- Truth anchor: `D5/S1/Words/TribonacciAlignedWindows.W`
- Truth anchor: `D5/S1/Words/TribonacciAlignedWindows.aligned_windows`
- Truth anchor: `D5/S1/Words/TribonacciAlignedWindows.sigma`
- Dependency: [D5/S1/Words/MBonacciSentinelDesubstitution](MBonacciSentinelDesubstitution.md)
