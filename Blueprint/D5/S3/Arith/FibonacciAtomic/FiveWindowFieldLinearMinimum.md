# Minimum Field Dimensions of Fibonacci Window Responses

## Abstract

Integer-induced Fibonacci window responses have exact minimum linear dimension six or four according to the characteristic.

Let K be any field. Windows null, [2], [3], [25], [5] are read high to low, with a seam retaining the previous higher window's low bit. An old seam one and a new high bit one are incompatible. The initial seam is zero, the composition is (0,0), and the unit bit is zero. Empty words, leading null windows and all finite prefixes are included. Integer composition is updated first; its output is then mapped coordinatewise from Z to K. A legal quantity q has output (1,q), whereas every illegal word has output (0,0).

**Definition 1.1 (The two homogeneous seam blocks).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.SixState`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.SixState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SixState(K)=K^6 has coordinates (a_0,b_0,c_0,a_1,b_1,c_1), one three-coordinate block for each seam.

**Definition 1.2 (Homogeneous affine updates).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixUpdate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixUpdate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For displacement (d_a,d_b), an allowed source block (a,b,c) maps to (a+2b+d_a c,2a+3b+d_b c,c) in the new seam block. The five displacements are (0,0),(1,0),(0,1),(2,1),(1,1). Disallowed source blocks map to zero, and allowed blocks with the same destination contribute by addition.

**Definition 1.3 (Linear operators for the windows).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixTransition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixTransition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each homogeneous update defines a K-linear endomorphism on the entire six-coordinate space.

**Definition 1.4 (Legality and quantity).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixOutput`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear output of x is (c_0+c_1,2(a_0+a_1)+3(b_0+b_1)). Legality is retained separately from quantity.

**Definition 1.5 (The full word representation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixDimensional`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixDimensional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The representation has initial vector (0,0,1,0,0,0), window operators sixTransition and output sixOutput. The existing chronological wordMap applies letters in input order.

**Definition 1.6 (Embedding actual integer states).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixEmbed`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixEmbed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An actual legal integer state occupies only its seam block, with composition mapped from Z to K and homogeneous coordinate one. The absorbing error embeds as zero.

**Definition 1.7 (Six actual histories).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixPrefixes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixPrefixes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The prefixes are the empty word, [3], [5], [2], [3][2], [5][2], in this order.

**Definition 1.8 (The four-coordinate quotient).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.FourState`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.FourState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FourState(K)=K^4 has coordinates (b_0,c_0,b_1,c_1), retaining two homogeneous coordinates per seam.

**Definition 1.9 (Projection onto the second composition coordinate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourTrim`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourTrim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The K-linear projection discards a_0 and a_1 and retains (b_0,c_0,b_1,c_1).

**Definition 1.10 (Updates after projection).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourUpdate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourUpdate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Allowed source blocks map (b,c) to (b+d_b c,c) in the new seam block. Null and [2] have d_b=0, and [3], [25], [5] have d_b=1. Disallowed source blocks map to zero; contributions to a common destination are added.

**Definition 1.11 (Quotient letter operators).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourTransition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourTransition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each fourUpdate is regarded as a K-linear endomorphism on K^4.

**Definition 1.12 (Quotient observations).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourOutput`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear output is (c_0+c_1,b_0+b_1). It agrees with sixOutput after projection when 2=0 in K.

**Definition 1.13 (The quotient word representation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourDimensional`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourDimensional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial vector is (0,1,0,0), the letter operators are fourTransition, and the output is fourOutput.

**Definition 1.14 (Six actual scalar continuation tests).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixSuffixes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixSuffixes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six rows query [5] legality, [5] quantity, [5]null quantity, null[5] legality, null[5] quantity and null[5]null quantity, in this order.

**Definition 1.15 (Six-by-six actual responses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixResponseMinor`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixResponseMinor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H6(K) has entry in row i and column j equal to the selected scalar output of f_K after sixPrefixes(j) followed by sixSuffixes(i). Rows zero and three select legality; all other rows select quantity.

**Definition 1.16 (Four-by-four actual responses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourResponseMinor`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourResponseMinor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H4(K) uses the existing four prefixes and four suffixes. Rows zero and two select legality, and rows one and three select quantity.

**Theorem 1.17 (All-word correctness, reachable span and attained minimum).**

$$\forall K, (\operatorname{Realizes}\left(FK, fK\right)) \land \\(\operatorname{dimK}\left(VK\right) = 6) \land \\(\operatorname{LinearIndependentK}\left(PK\right)) \land \\(\operatorname{spanK}\left(\operatorname{range}\left(AK\right)\right) = VK) \land \\((\operatorname{Nonzero}\left(\operatorname{twoK}\left(K\right)\right)) \implies ((\operatorname{Nonsingular}\left(H6K\right)) \land \\(\forall V, \forall R, ((\operatorname{FiniteKSpace}\left(V\right)) \land \\(\operatorname{LinearWordRep}\left(R, V\right))) \implies ((\operatorname{Realizes}\left(R, fK\right)) \implies (6 \leq \operatorname{dimK}\left(V\right)))))) \land \\((\operatorname{twoK}\left(K\right) = 0) \implies ((\operatorname{Realizes}\left(GK, fK\right)) \land \\(\operatorname{dimK}\left(WK\right) = 4) \land \\(\operatorname{LinearIndependentK}\left(QK\right)) \land \\(\operatorname{spanK}\left(\operatorname{range}\left(BK\right)\right) = WK) \land \\(\operatorname{Nonsingular}\left(H4K\right)) \land \\(\forall V, \forall R, ((\operatorname{FiniteKSpace}\left(V\right)) \land \\(\operatorname{LinearWordRep}\left(R, V\right))) \implies ((\operatorname{Realizes}\left(R, fK\right)) \implies (4 \leq \operatorname{dimK}\left(V\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each field K, F_K denotes sixDimensional(K), f_K denotes integerFieldTask(K), and V_K denotes SixState(K). P_K(j) is the vector reached after prefix j of sixPrefixes, for j in Fin(6). A_K(w) is the reached vector after any finite word w. Realizes(F_K,f_K) means equality of outputs for every finite window word, including illegal words. G_K denotes fourDimensional(K), W_K denotes FourState(K), and B_K(w) is its reached vector after w. Q_K is its reached family for the four existing prefixes: the empty word, [3], [2], [3][2]. The scalar twoK(K) is 2 in K; twoK(K)=0 is the characteristic-two field condition. H6K and H4K denote sixResponseMinor(K) and fourResponseMinor(K). V ranges over every finite-dimensional K-vector space, and R ranges over linear Window representations on V with output in K^2. FiniteKSpace(V) and LinearWordRep(R,V) specify these domains; Nonsingular(H) means det(H) is nonzero. No reachability or observability condition is imposed on competing representations.

The integer-state embedding commutes with each window operator. Induction on word length transports the complete integer reader to the homogeneous representation. A forbidden seam erases the unique occupied block, and subsequent linear operations preserve zero.

The first three histories reach (0,0,1),(0,1,1),(1,1,1) in seam zero. Appending [2] gives the three seam-one vectors (1,0,1),(3,3,1),(4,5,1). The six reached columns have determinant minus one, so they form a basis over every field. Consequently the span of all actual reached vectors is the whole state space. This does not assert that each state vector is itself reached by a word.

When 2=0 in K, the clock on composition is the identity and quantity reads b. Projection intertwines every letter operator and preserves the linear output. Word induction extends this relation to all finite words. The four actual prefix vectors are (0,1,0,0), (1,1,0,0),(0,0,0,1),(0,0,1,1). Their determinant is one, so they form a basis of the quotient space over every characteristic-two field.

The six continuation tests have observation matrix O with diagonal blocks R0 and R0 A0, where R0 has rows (0,0,1), (8,13,5), (34,55,21), and A0 is the homogeneous zero-displacement clock. Its determinant is minus four. The reached-prefix matrix P has determinant minus one, so the actual response matrix H6K=OP has determinant four. This is nonzero whenever twoK(K) is nonzero.

In characteristic two, H4K has rows (1,1,0,0), (1,2,0,0), (1,1,1,1), (1,2,1,2), interpreted in K. Its determinant is one. For every competing all-word realization, actual suffix observations linearly map its reached-prefix vectors to the columns of the corresponding response matrix. Nonsingularity forces six or four independent reached vectors. The explicit realizations attain these respective lower bounds.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.FourState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.SixState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourDimensional`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourOutput`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourResponseMinor`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourTransition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourTrim`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.fourUpdate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixDimensional`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixEmbed`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixOutput`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixPrefixes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixResponseMinor`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixSuffixes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixTransition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.sixUpdate`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum](ParityLiftRationalMinimum.md)
