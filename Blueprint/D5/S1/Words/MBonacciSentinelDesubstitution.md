# Sentinel Desubstitution of the m-bonacci Word

## Abstract

The actual m-bonacci word admits unique sentinel desubstitution and strict fully right-special descent for every order at least two.

The alphabet is Fin m, with m at least two. Every occurrence is a contiguous list factor at a natural starting position. Position zero and the empty source word are included. No recurrence or fixed-word assumption is needed: the infinite word is constructed from the nested finite iterates.

**Definition 1.1 (The zero letter).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow val\left(zero\right) = 0$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.zero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The order bound supplies the positivity needed to form the zero of Fin m.

**Definition 1.2 (Cyclic successor).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in Fin\left(m\right),\; val\left(rot\left(a\right)\right) = mod\left(val\left(a\right) + 1, m\right)\right)$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.rot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Successor sends a to a+1 below m and sends m-1 to zero. It is a permutation of the alphabet; its value is (a+1) modulo m.

**Definition 1.3 (The literal substitution).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall a \in Fin\left(m\right),\; \left(val\left(a\right) + 1 < m \Rightarrow phi\left(a\right) = [0,val\left(a\right) + 1]\right) \land \left(val\left(a\right) + 1 = m \Rightarrow phi\left(a\right) = [0]\right)\right)$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every nonterminal letter a has image [0,a+1], and the terminal letter m-1 has image [0]. Thus every image is nonempty, begins in zero and has length at most two. The generic substitution and finite iterate operators are reused.

**Definition 1.4 (The actual infinite word).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall n \in \mathbb{N},\; word\left(n\right) = getElem\left(image\left(phi, n + 1, 0\right), n\right)\right)$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Letter n is read at position n of the (n+1)st iterate on zero. The iterates are nested: the next iterate is the current iterate followed by the iterate on one. The latter is nonempty, so the kth iterate has length at least k+1. Comparing both readings in a common longer iterate proves compatibility.

**Definition 1.5 (True block boundaries).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall i \in \mathbb{N},\; boundary\left(i\right) = length\left(subst\left(phi, factor\left(word, 0, i\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The boundary B(i) is the length of the substituted prefix of i source letters. It also equals the sum of their individual image lengths.

**Definition 1.6 (Actual occurrence).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall s \in List\left(Fin\left(m\right)\right),\; \forall q \in \mathbb{N},\; Occ\left(s, q\right) \Leftrightarrow factor\left(word, q, length\left(s\right)\right) = s\right)$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.Occ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Occ(s,q) asserts equality of s with the supplied length-|s| list factor starting at q. No bounded prefix replaces the set of natural starts.

**Definition 1.7 (Reserved final zero).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall s \in List\left(Fin\left(m\right)\right),\; T\left(s\right) = append\left(subst\left(phi, s\right), [0]\right)\right)$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T(s) is the substituted source word followed by one zero. This last zero marks the next block and is reserved rather than decoded as a source letter.

**Definition 1.8 (Fully right-special factors).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall r \in List\left(Fin\left(m\right)\right),\; FRS\left(r\right) \Leftrightarrow \left(\forall a \in Fin\left(m\right),\; \exists q \in \mathbb{N},\; Occ\left(append\left(r, [a]\right), q\right)\right)\right)$$

*Formalization.* `D5/S1/Words/MBonacciSentinelDesubstitution.FRS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A word is fully right-special when appending each alphabet letter gives an actual occurrence, with the starting position allowed to depend on the letter.

**Theorem 1.9 (Closed word and block laws).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\left(\forall k \in \mathbb{N},\; factor\left(word, 0, length\left(image\left(phi, k, 0\right)\right)\right) = image\left(phi, k, 0\right)\right) \land \left(StrictMono\left(boundary\right) \land \left(boundary\left(0\right) = 0 \land \left(\left(\forall i \in \mathbb{N},\; boundary\left(i\right) = \sum_{h \in range\left(i\right)} (length\left(phi\left(word\left(h\right)\right)\right))\right) \land \left(\left(\forall i \in \mathbb{N},\; factor\left(word, boundary\left(i\right), length\left(phi\left(word\left(i\right)\right)\right)\right) = phi\left(word\left(i\right)\right)\right) \land \left(\left(\forall q \in \mathbb{N},\; word\left(q\right) \ne 0 \Rightarrow word\left(q + 1\right) = 0\right) \land \left(\forall a \in Fin\left(m\right),\; val\left(rot\left(a\right)\right) = mod\left(val\left(a\right) + 1, m\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.actual_word_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite iterate is an exact prefix of the constructed word. Applying the substitution to a source prefix gives another exact prefix. Cancellation between successive prefixes yields the block at B(i). Positive image lengths make B strictly increasing, with B(0)=0 and the stated sum formula. A nonzero letter is the second position of a two-letter image; the next position is zero.

**Theorem 1.10 (Zeros identify unique boundaries).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall q \in \mathbb{N},\; word\left(q\right) = 0 \Leftrightarrow \exists! i:\mathbb{N}, q = boundary\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.zero_iff_unique_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural position lies between two successive boundaries. The only possible interior position is the nonzero second letter of a two-letter image. Hence zero positions are precisely boundaries, and strict growth gives uniqueness, including the boundary at zero.

**Theorem 1.11 (Transport of actual occurrences).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall s \in List\left(Fin\left(m\right)\right),\; \forall i \in \mathbb{N},\; Occ\left(s, i\right) \Rightarrow \left(Occ\left(subst\left(phi, s\right), boundary\left(i\right)\right) \land \left(Occ\left(T\left(s\right), boundary\left(i\right)\right) \land \left(s \ne [] \Rightarrow Occ\left(tail\left(subst\left(phi, s\right)\right), boundary\left(i\right) + 1\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.occurrence_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An occurrence of s at i lifts to the image and its sentinel at B(i). For nonempty s, removing the initial zero gives the image tail at B(i)+1. The first two transports also apply to the empty word.

**Theorem 1.12 (Exact sentinel occurrence bridge).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall s \in List\left(Fin\left(m\right)\right),\; \forall q \in \mathbb{N},\; Occ\left(T\left(s\right), q\right) \Leftrightarrow \left(\exists i \in \mathbb{N},\; q = boundary\left(i\right) \land Occ\left(s, i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.sentinel_occurrence_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The leading zero identifies a boundary. The next letter is the cyclic successor of the source letter, including zero for the terminal letter. Injectivity of cyclic successor identifies that source letter, and induction continues at the next boundary. The empty case is the single zero sentinel.

**Theorem 1.13 (Exact right-extension bridge).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall s \in List\left(Fin\left(m\right)\right),\; \forall b \in Fin\left(m\right),\; \forall q \in \mathbb{N},\; Occ\left(append\left(T\left(s\right), [rot\left(b\right)]\right), q\right) \Leftrightarrow \left(\exists i \in \mathbb{N},\; q = boundary\left(i\right) \land Occ\left(append\left(s, [b]\right), i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.right_extension_occurrence_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After T(s), the next position is one past B(i+|s|), so its letter is the cyclic successor of the next source letter. This proves both directions for every right extension using the same source word and boundary map.

**Theorem 1.14 (A common unique shorter preimage).**

$$\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\forall r \in List\left(Fin\left(m\right)\right),\; r \ne [] \Rightarrow \left(\left(\exists q \in \mathbb{N},\; Occ\left(r, q\right)\right) \Rightarrow \left(headopt\left(r\right) = some\left(0\right) \Rightarrow \left(lastopt\left(r\right) = some\left(0\right) \Rightarrow \exists! s:List\left(Fin\left(m\right)\right), r = T\left(s\right) \land length\left(s\right) < length\left(r\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/MBonacciSentinelDesubstitution.common_unique_preimage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual nonempty factor beginning and ending in zero, its two endpoints are boundaries B(i) and B(j). Take the source factor from i to j. Substitution transport and the endpoint length identity give r=T(s). Comparing the first two letters of two sentinel encodings and then cancelling their common image proves uniqueness. Nonerasing images and the extra sentinel imply |s|<|r|. Adjacent zeros decode m-1; a zero, a nonzero b and the following zero decode b-1. The single zero has the empty preimage.

**Theorem 1.15 (Strict fully right-special descent).**

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
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.common_unique_preimage`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.fully_right_special_descent`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.occurrence_transport`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.phi`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.right_extension_occurrence_iff`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.rot`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.sentinel_occurrence_iff`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.word`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.zero`
- Truth anchor: `D5/S1/Words/MBonacciSentinelDesubstitution.zero_iff_unique_boundary`
- Dependency: [D5/S1/Words/RankOneMorphismIterationBoundDefs](RankOneMorphismIterationBoundDefs.md)
