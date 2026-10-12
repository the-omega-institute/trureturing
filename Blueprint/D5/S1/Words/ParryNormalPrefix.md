# Greedy Remainders and Ordered Image Prefixes

## Abstract

An ordered greedy cut theorem for zero-run substitutions with dominant zero images.

Let A be any alphabet, let z be a letter, and let f map letters to finite ordered lists. Extend f to lists by concatenation and let I(k,a) be its kth iterate on the singleton a, with I(0,a) equal to [a]. Put F(k)=length(I(k,z)). The substitution has the form f(a)=z repeated digit(a) times, followed by the optional successor next(a). A missing successor permits the terminal image of a simple Parry substitution; a successor can also return to an earlier state, as in a non-simple Parry substitution.

Assume F(k) is positive and length(I(k,a)) is at most F(k) for every natural k and every letter a. These are explicit hypotheses. No relation between a greedy expansion and a word prefix is assumed.

**Definition 1.1 (Finite concatenation power).**

$$wordPower\left(w, d\right) = flatten\left(replicate\left(d, w\right)\right)$$

*Formalization.* `D5/S1/Words/ParryNormalPrefix.wordPower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

wordPower(w,d) concatenates d copies of w. The zeroth power is the empty list, and the order within every copy is preserved. This is the concatenation power of `D5/S1/Words/Powers/WordPower` with the word argument first here. Its length is d times length(w).

**Definition 1.2 (Blocks from every greedy step).**

$$greedyBlocks\left(f, z, k + 1, n\right) = append\left(wordPower\left(I\left(k, z\right), div\left(n, F\left(k\right)\right)\right), greedyBlocks\left(f, z, k, mod\left(n, F\left(k\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/ParryNormalPrefix.greedyBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

greedyBlocks(f,z,0,n) is the empty list. With count k+1, append n div F(k) copies of I(k,z), then recurse at count k with n mod F(k). Thus count N+1 includes all image exponents from N down through zero. A zero quotient contributes an empty block without ending the recursion. The chosen height is an input; it need not be minimal.

**Theorem 1.3 (All proper image prefixes are reconstructed in order).**

$$\forall A \in Type,\; \forall f \in Morphism\left(A\right),\; \forall z \in A,\; \forall digit \in DigitMap\left(A\right),\; \forall next \in OptionalSuccessor\left(A\right),\; \left(\left(\forall a \in A,\; f\left(a\right) = append\left(replicate\left(digit\left(a\right), z\right), toList\left(next\left(a\right)\right)\right)\right) \land \left(\left(\forall k \in \mathbb{N},\; 0 < length\left(image\left(f, k, z\right)\right)\right) \land \left(\forall k \in \mathbb{N},\; \forall a \in A,\; length\left(image\left(f, k, a\right)\right) \le length\left(image\left(f, k, z\right)\right)\right)\right)\right) \Rightarrow \left(\forall k \in \mathbb{N},\; \forall a \in A,\; \forall n \in \mathbb{N},\; n < length\left(image\left(f, k, a\right)\right) \Rightarrow take\left(n, image\left(f, k, a\right)\right) = greedyBlocks\left(f, z, k, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ParryNormalPrefix.greedy_remainder_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the next iterate, the actual image is digit(a) copies of I(k,z), followed by the image of the optional successor. The latter has length at most F(k). A proper cut therefore has quotient at most digit(a). If the quotient is smaller, its remainder lies strictly inside a zero-image block. If it equals digit(a), the remainder lies strictly inside the successor image. Induction applies to the actual letter in either branch, proving equality of complete ordered lists.

The empty prefix is included. At exponent zero the only proper cut of [a] has length zero. To apply the theorem to a normal representation at height N, use k=N+1, a=z and n<F(N+1). Passing from the finite iterate to the infinite fixed word additionally requires its exact prefix compatibility.

Turek, Abelian complexity and Abelian co-decomposition, Proposition 2.7 and Section 2.2, https://arxiv.org/pdf/1201.2109v1, give the full known Parry-word reconstruction result, including leading zero padding. The theorem here isolates its ordered cut mechanism. Deriving the required dominance from the full Parry admissibility conditions, and constructing the compatible fixed word for both substitution families, remain separate requirements. The displayed exponent bounds in Turek (6) alone are not substituted for those admissibility conditions.

**Definition 1.4 (Finite lexicographic successor windows).**

$$\forall a \in A,\; \forall k \in \mathbb{N},\; \left(\forall i \in \mathbb{N},\; i < k \Rightarrow c\left(iterate\left(s, i, a\right)\right) = c\left(iterate\left(s, i, z\right)\right)\right) \lor \left(\exists q \in \mathbb{N},\; q < k \land \left(\left(\forall i \in \mathbb{N},\; i < q \Rightarrow c\left(iterate\left(s, i, a\right)\right) = c\left(iterate\left(s, i, z\right)\right)\right) \land c\left(iterate\left(s, q, a\right)\right) < c\left(iterate\left(s, q, z\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/ParryNormalPrefix.SuccessorDominated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each letter a and each window length k, compare c(s iterated i times on a) with c(s iterated i times on z), for i below k. Either every pair agrees, or there is a first differing position q below k at which the digit from a is smaller. Equality of entire successor streams is allowed.

**Theorem 1.5 (Successor digits determine the ordered greedy prefix).**

$$\forall A \in Type,\; \forall f \in Morphism\left(A\right),\; \forall z \in A,\; \forall c \in DigitMap\left(A\right),\; \forall s \in Successor\left(A\right),\; \left(\left(\forall a \in A,\; f\left(a\right) = append\left(replicate\left(c\left(a\right), z\right), singleton\left(s\left(a\right)\right)\right)\right) \land SuccessorDominated\left(c, s, z\right)\right) \Rightarrow \left(\forall k \in \mathbb{N},\; \forall a \in A,\; \forall n \in \mathbb{N},\; n < length\left(image\left(f, k, a\right)\right) \Rightarrow take\left(n, image\left(f, k, a\right)\right) = greedyBlocks\left(f, z, k, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ParryNormalPrefix.greedy_prefix_of_successor_dominance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here every literal image has the form z repeated c(a) times followed by the actual letter s(a). Positivity follows from this last letter. If two successor windows agree, their equal weighted contributions cancel, leaving equal singleton lengths at depth zero. At the first differing digit, one root-image weight bounds the entire remaining smaller-side image by strong induction at a lower depth. The larger-side remaining image is positive. Thus every image length is bounded by the root-image length, which permits the ordered greedy cut theorem to apply.

For a simple Parry substitution, its last literal image z repeated t_m times can be written as z repeated t_m minus one times followed by z. This distinguishes a final actual letter without changing the substitution. For a non-simple substitution the successor is already the final letter, including its cyclic return. The theorem proves reconstruction from SuccessorDominated; the conversion of full Parry admissibility to this condition and the infinite fixed-word construction are separate obligations.

The full source target is the following known result: for either Parry substitution family, its actual fixed word u, every positive n, and every N with n<F(N+1), the normal greedy digits d_N through d_0 reconstruct the ordered prefix u[n] as I(N,0) repeated d_N times, then I(N-1,0) repeated d_(N-1) times, down through the letter zero repeated d_0 times. Leading zero padding and N=0 are included. The finite-image theorems here do not yet establish this full statement.

The association uses the actual Renyi expansion D=d_beta(1) for beta>1, not just bounds on individual exponents. Every positive shift of D is strictly lexicographically smaller than D. In the simple case D=t_1...t_m followed by zeros, with t_m positive; in the non-simple case D=t_1...t_m(t_(m+1)...t_(m+p)) repeated periodically, with a positive digit in the period and minimal preperiod and period. In both cases the substitution exponent at state i is t_(i+1); the last state terminates in the simple case and returns to state m in the non-simple case. These definitions and the shift condition are stated in Frougny, Masakova and Pelantova, Infinite special branches in words associated with beta-expansions, pp.129-130, https://doi.org/10.46298/dmtcs.415. Its later assumption that all digits are positive is not imposed here. For the simple final-letter presentation, the modified root successor stream is periodic, so equality with a shift must be allowed in SuccessorDominated. The exact bridge from these source expansions to that finite-window condition remains unproved.

Digitwise exponent bounds alone do not give the needed condition. For the simple-shaped substitution 0 maps to 001, 1 to 2, 2 to 003, and 3 to 00, all exponents are at most two and the last exponent is positive. Its root-image lengths start 1,3,7,17,42. At n=41 and height N=3 the greedy digits are 2,1,0,0. The actual length-41 prefix of the fourth iterate ends in zero, whereas the reconstruction ends in two. This substitution fails full Parry admissibility and does not contradict Proposition 2.7.

## References

- Truth anchor: `D5/S1/Words/ParryNormalPrefix.SuccessorDominated`
- Truth anchor: `D5/S1/Words/ParryNormalPrefix.greedyBlocks`
- Truth anchor: `D5/S1/Words/ParryNormalPrefix.greedy_prefix_of_successor_dominance`
- Truth anchor: `D5/S1/Words/ParryNormalPrefix.greedy_remainder_prefix`
- Truth anchor: `D5/S1/Words/ParryNormalPrefix.wordPower`
- Dependency: [D5/S1/Words/RankOneMorphismIterationBoundDefs](RankOneMorphismIterationBoundDefs.md)
- Narrative reference: [D5/S1/Words/Powers/WordPower](Powers/WordPower.md)
