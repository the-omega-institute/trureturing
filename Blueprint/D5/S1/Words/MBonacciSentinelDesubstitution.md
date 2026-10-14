# Sentinel Desubstitution of the m-bonacci Word

## Abstract

The actual m-bonacci word admits unique sentinel desubstitution and strict fully right-special descent for every order at least two.

**Theorem 1.1 (Exact factor length).**

$$\forall m \in \mathbb{N},\; \forall x \in (\mathbb{N} \to Fin\left(m\right)),\; \forall i \in \mathbb{N},\; \forall n \in \mathbb{N},\; length\left(factor\left(x, i, n\right)\right) = n$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.factor_len` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every alphabet size m, every function x from the naturals to Fin m, and all natural i and n, the length-n factor of x at i has length n. This identity gives the lengths of finite prefixes in periodic intervals.

**Theorem 1.2 (Nested actual iterates).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall k \in \mathbb{N},\; \forall t \in \mathbb{N},\; k \le t \Rightarrow IsPrefix\left(image\left(phi\left(m\right), k, zero\left(m\right)\right), image\left(phi\left(m\right), t, zero\left(m\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.iterate_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every order m at least two and natural k at most t, the kth iterate on zero is a prefix of the tth iterate.

**Theorem 1.3 (Unbounded actual image lengths).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall k \in \mathbb{N},\; k + 1 \le length\left(image\left(phi\left(m\right), k, zero\left(m\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.iterate_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every order m at least two and every natural k, the kth iterate on zero has length at least k+1. Each substitution step adds a nonempty image.

**Theorem 1.4 (Compatible readings of the actual word).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall k \in \mathbb{N},\; \forall n \in \mathbb{N},\; n < length\left(image\left(phi\left(m\right), k, zero\left(m\right)\right)\right) \Rightarrow word\left(m, n\right) = getElem\left(image\left(phi\left(m\right), k, zero\left(m\right)\right), n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.word_eq_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every order m at least two, every k and every n less than the kth image length, the actual letter at n equals the letter at n of that iterate.

**Theorem 1.5 (The exact letter of a factor).**

$$\forall m \in \mathbb{N},\; \forall x \in (\mathbb{N} \to Fin\left(m\right)),\; \forall i \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; j < n \Rightarrow getElem\left(factor\left(x, i, n\right), j\right) = x\left(i + j\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.factor_get` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any order m, any function x from the naturals to Fin m, and naturals i,n,j with j<n, the jth letter of the length-n factor of x at i equals x(i+j).

**Theorem 1.6 (Every natural start has a source block).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall q \in \mathbb{N},\; \exists i \in \mathbb{N},\; boundary\left(m, i\right) \le q \land q < boundary\left(m, i + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.boundary_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least two and every natural q, some i satisfies boundary(i) at most q and q less than boundary(i+1). The original strict and unbounded block construction includes q equal to zero. Images have at most two letters, so the converse has exactly the boundary offset zero or one cases.

**Theorem 1.7 (Exact contiguous factor concatenation).**

$$\forall m \in \mathbb{N},\; \forall x \in (\mathbb{N} \to Fin\left(m\right)),\; \forall i \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall t \in \mathbb{N},\; factor\left(x, i, n + t\right) = append\left(factor\left(x, i, n\right), factor\left(x, i + n, t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.factor_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every alphabet size, every infinite word x and all natural i,n,t, factor(x,i,n+t) is factor(x,i,n) followed by factor(x,i+n,t). The converse uses this original identity to choose the next source letter at the end of a complete predecessor window.

**Theorem 1.8 (Exact first-letter removal).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in Fin\left(m\right),\; \forall s \in List\left(Fin\left(m\right)\right),\; \forall q \in \mathbb{N},\; Occ\left(m, cons\left(a, s\right), q\right) \Leftrightarrow \left(word\left(m, q\right) = a \land Occ\left(m, s, q + 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.occ_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual source order at least two, letter a, list s and natural q, occurrence of a followed by s at q is equivalent to word(q) equal to a and occurrence of s at q+1. This original bridge removes the first output zero in both offset-one cases.

**Theorem 1.9 (The original sentinel starts in zero).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall s \in List\left(Fin\left(m\right)\right),\; \exists v \in List\left(Fin\left(m\right)\right),\; T\left(m, s\right) = cons\left(0, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.t_head` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual source order at least two and every source list s, T(s) is zero followed by a list. This includes empty s. It is the original first-letter supplier for additive count cancellation in the clipped transport.

The alphabet is Fin m, with m at least two. Every occurrence is a contiguous list factor at a natural starting position. Position zero and the empty source word are included. No recurrence or fixed-word assumption is needed: the infinite word is constructed from the nested finite iterates.

**Definition 1.10 (The zero letter).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow val\left(zero\right) = 0$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.zero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The order bound supplies the positivity needed to form the zero of Fin m.

**Definition 1.11 (Cyclic successor).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in Fin\left(m\right),\; val\left(rot\left(a\right)\right) = mod\left(val\left(a\right) + 1, m\right)\right)$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.rot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Successor sends a to a+1 below m and sends m-1 to zero. It is a permutation of the alphabet; its value is (a+1) modulo m.

**Definition 1.12 (The literal substitution).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in Fin\left(m\right),\; \left(val\left(a\right) + 1 < m \Rightarrow phi\left(a\right) = [0,val\left(a\right) + 1]\right) \land \left(val\left(a\right) + 1 = m \Rightarrow phi\left(a\right) = [0]\right)\right)$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every nonterminal letter a has image [0,a+1], and the terminal letter m-1 has image [0]. Thus every image is nonempty, begins in zero and has length at most two. The generic substitution and finite iterate operators are reused.

**Definition 1.13 (The actual infinite word).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall n \in \mathbb{N},\; word\left(n\right) = getElem\left(image\left(phi, n + 1, 0\right), n\right)\right)$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Letter n is read at position n of the (n+1)st iterate on zero. The iterates are nested: the next iterate is the current iterate followed by the iterate on one. The latter is nonempty, so the kth iterate has length at least k+1. Comparing both readings in a common longer iterate proves compatibility.

**Definition 1.14 (True block boundaries).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall i \in \mathbb{N},\; boundary\left(i\right) = length\left(subst\left(phi, factor\left(word, 0, i\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The boundary B(i) is the length of the substituted prefix of i source letters. It also equals the sum of their individual image lengths.

**Definition 1.15 (Actual occurrence).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall s \in List\left(Fin\left(m\right)\right),\; \forall q \in \mathbb{N},\; Occ\left(s, q\right) \Leftrightarrow factor\left(word, q, length\left(s\right)\right) = s\right)$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.Occ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Occ(s,q) asserts equality of s with the supplied length-|s| list factor starting at q. No bounded prefix replaces the set of natural starts.

**Definition 1.16 (Reserved final zero).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall s \in List\left(Fin\left(m\right)\right),\; T\left(s\right) = append\left(subst\left(phi, s\right), [0]\right)\right)$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T(s) is the substituted source word followed by one zero. This last zero marks the next block and is reserved rather than decoded as a source letter.

**Definition 1.17 (Fully right-special factors).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall r \in List\left(Fin\left(m\right)\right),\; FRS\left(r\right) \Leftrightarrow \left(\forall a \in Fin\left(m\right),\; \exists q \in \mathbb{N},\; Occ\left(append\left(r, [a]\right), q\right)\right)\right)$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.FRS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A word is fully right-special when appending each alphabet letter gives an actual occurrence, with the starting position allowed to depend on the letter.

**Theorem 1.18 (Closed word and block laws).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\left(\forall k \in \mathbb{N},\; factor\left(word, 0, length\left(image\left(phi, k, 0\right)\right)\right) = image\left(phi, k, 0\right)\right) \land \left(StrictMono\left(boundary\right) \land \left(boundary\left(0\right) = 0 \land \left(\left(\forall i \in \mathbb{N},\; boundary\left(i\right) = \sum_{h \in range\left(i\right)} (length\left(phi\left(word\left(h\right)\right)\right))\right) \land \left(\left(\forall i \in \mathbb{N},\; factor\left(word, boundary\left(i\right), length\left(phi\left(word\left(i\right)\right)\right)\right) = phi\left(word\left(i\right)\right)\right) \land \left(\left(\forall q \in \mathbb{N},\; word\left(q\right) \ne 0 \Rightarrow word\left(q + 1\right) = 0\right) \land \left(\forall a \in Fin\left(m\right),\; val\left(rot\left(a\right)\right) = mod\left(val\left(a\right) + 1, m\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.actual_word_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite iterate is an exact prefix of the constructed word. Applying the substitution to a source prefix gives another exact prefix. Cancellation between successive prefixes yields the block at B(i). Positive image lengths make B strictly increasing, with B(0)=0 and the stated sum formula. A nonzero letter is the second position of a two-letter image; the next position is zero.

**Theorem 1.19 (Zeros identify unique boundaries).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall q \in \mathbb{N},\; word\left(q\right) = 0 \Leftrightarrow \exists! i:\mathbb{N}, q = boundary\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.zero_iff_unique_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural position lies between two successive boundaries. The only possible interior position is the nonzero second letter of a two-letter image. Hence zero positions are precisely boundaries, and strict growth gives uniqueness, including the boundary at zero.

**Theorem 1.20 (Transport of actual occurrences).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall s \in List\left(Fin\left(m\right)\right),\; \forall i \in \mathbb{N},\; Occ\left(s, i\right) \Rightarrow \left(Occ\left(subst\left(phi, s\right), boundary\left(i\right)\right) \land \left(Occ\left(T\left(s\right), boundary\left(i\right)\right) \land \left(s \ne [] \Rightarrow Occ\left(tail\left(subst\left(phi, s\right)\right), boundary\left(i\right) + 1\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.occurrence_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An occurrence of s at i lifts to the image and its sentinel at B(i). For nonempty s, removing the initial zero gives the image tail at B(i)+1. The first two transports also apply to the empty word.

**Theorem 1.21 (Exact sentinel occurrence bridge).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall s \in List\left(Fin\left(m\right)\right),\; \forall q \in \mathbb{N},\; Occ\left(T\left(s\right), q\right) \Leftrightarrow \left(\exists i \in \mathbb{N},\; q = boundary\left(i\right) \land Occ\left(s, i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.sentinel_occurrence_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The leading zero identifies a boundary. The next letter is the cyclic successor of the source letter, including zero for the terminal letter. Injectivity of cyclic successor identifies that source letter, and induction continues at the next boundary. The empty case is the single zero sentinel.

**Theorem 1.22 (Exact right-extension bridge).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall s \in List\left(Fin\left(m\right)\right),\; \forall b \in Fin\left(m\right),\; \forall q \in \mathbb{N},\; Occ\left(append\left(T\left(s\right), [rot\left(b\right)]\right), q\right) \Leftrightarrow \left(\exists i \in \mathbb{N},\; q = boundary\left(i\right) \land Occ\left(append\left(s, [b]\right), i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.right_extension_occurrence_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After T(s), the next position is one past B(i+|s|), so its letter is the cyclic successor of the next source letter. This proves both directions for every right extension using the same source word and boundary map.

**Theorem 1.23 (A common unique shorter preimage).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall r \in List\left(Fin\left(m\right)\right),\; r \ne [] \Rightarrow \left(\left(\exists q \in \mathbb{N},\; Occ\left(r, q\right)\right) \Rightarrow \left(headopt\left(r\right) = some\left(0\right) \Rightarrow \left(lastopt\left(r\right) = some\left(0\right) \Rightarrow \exists! s:List\left(Fin\left(m\right)\right), r = T\left(s\right) \land length\left(s\right) < length\left(r\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.common_unique_preimage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual nonempty factor beginning and ending in zero, its two endpoints are boundaries B(i) and B(j). Take the source factor from i to j. Substitution transport and the endpoint length identity give r=T(s). Comparing the first two letters of two sentinel encodings and then cancelling their common image proves uniqueness. Nonerasing images and the extra sentinel imply |s|<|r|. Adjacent zeros decode m-1; a zero, a nonzero b and the following zero decode b-1. The single zero has the empty preimage.

**Theorem 1.24 (Strict fully right-special descent).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall r \in List\left(Fin\left(m\right)\right),\; r \ne [] \Rightarrow \left(headopt\left(r\right) = some\left(0\right) \Rightarrow \left(FRS\left(r\right) \Rightarrow \exists! s:List\left(Fin\left(m\right)\right), r = T\left(s\right) \land \left(length\left(s\right) < length\left(r\right) \land \left(FRS\left(s\right) \land \left(\left(\forall q \in \mathbb{N},\; Occ\left(r, q\right) \Leftrightarrow \left(\exists i \in \mathbb{N},\; q = boundary\left(i\right) \land Occ\left(s, i\right)\right)\right) \land \left(\forall b \in Fin\left(m\right),\; \forall q \in \mathbb{N},\; Occ\left(append\left(r, [rot\left(b\right)]\right), q\right) \Leftrightarrow \left(\exists i \in \mathbb{N},\; q = boundary\left(i\right) \land Occ\left(append\left(s, [b]\right), i\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.fully_right_special_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a nonempty fully right-special factor ended in a nonzero letter, adjacency would force its next letter to be zero, contradicting its extension by one. It therefore ends in zero. Its unique shorter preimage is fully right-special: each extension by rot(b) descends to an extension by b. The same preimage satisfies both all-start occurrence equivalences, with no extra end-zero premise.

These are structural laws of the actual word. They do not determine its abelian complexity or characterize greedy numeration digits.

## References

- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.FRS`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.Occ`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.T`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.actual_word_laws`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.boundary`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.boundary_window`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.common_unique_preimage`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.factor_add`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.factor_get`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.factor_len`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.fully_right_special_descent`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.iterate_growth`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.iterate_prefix`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.occ_cons`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.occurrence_transport`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.phi`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.right_extension_occurrence_iff`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.rot`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.sentinel_occurrence_iff`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.t_head`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.word`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.word_eq_iterate`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.zero`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.zero_iff_unique_boundary`
- Dependency: [D5/S1/Words/RankOneMorphismIterationBoundDefs](RankOneMorphismIterationBoundDefs.md)
