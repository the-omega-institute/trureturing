# Exact Endpoint-Word Shuffle Support

## Abstract

The endpoint-gap rectangle is exactly the distinct ordinary self-shuffle support.

Represent zero by false and one by true. Ordinary shuffles may take the next symbol from either source, preserving each source's internal order. The list ordinaryShuffles retains schedule multiplicities; conversion to a finite set discards them. All cardinalities below count output words. All scalar indices are natural numbers.

**Definition 1.1 (Two endpoint ones).**

$$\forall (m:\mathbb{N}), \operatorname{endpointWord}\left(m\right) = \operatorname{concat}\left(one, \operatorname{zeros}\left(m\right), one\right)$$

*Formalization.* `D5/S1/Words/EndpointShuffleSupport.endpointWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The word consists of an initial one, m zeros and a final one. The value m=0 is allowed.

**Definition 1.2 (Words parametrized by their outer gaps).**

$$\forall (m:\mathbb{N}),(a:\mathbb{N}),(c:\mathbb{N}), \operatorname{endpointOutput}\left(m, a, c\right) = \operatorname{gap}\left(zero, \operatorname{list}\left(1, 1, 1, 1\right), \operatorname{list}\left(0, a, (m - a) + (m - c), c, 0\right)\right)$$

*Formalization.* `D5/S1/Words/EndpointShuffleSupport.endpointOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The five zero gaps around four ones are 0, a, (m-a)+(m-c), c and 0. When a and c are at most m, the total number of zeros is 2m.

**Definition 1.3 (The finite rectangle of output words).**

$$\forall (m:\mathbb{N}), \operatorname{endpointFamily}\left(m\right) = \operatorname{image}\left((a,c) \mapsto \operatorname{endpointOutput}\left(m, a, c\right), \operatorname{square}\left(\operatorname{Fin}\left(m + 1\right)\right)\right)$$

*Formalization.* `D5/S1/Words/EndpointShuffleSupport.endpointFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the image of Fin(m+1) times Fin(m+1) under the output map. Here a and c are the natural values of the two finite coordinates. The image is a finite set of words, rather than a set of schedules.

**Theorem 1.4 (Constructing every outer-gap pair).**

$$\forall m,a,c, a \le m\land c \le m\implies \operatorname{member}\left(\operatorname{endpointOutput}\left(m, a, c\right), \operatorname{ordinaryShuffles}\left(\operatorname{endpointWord}\left(m\right), \operatorname{endpointWord}\left(m\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EndpointShuffleSupport.endpointOutput_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Label the copies A and B. Read A for its initial one and a zeros, then B's initial one, then the remaining m-a zeros from A and m-c zeros from B, then A's last one, and finally B's c zeros and last one. Both source orders are preserved, including when any of these zero blocks is empty.

**Theorem 1.5 (Distinct parameter pairs give distinct words).**

$$\forall m, \operatorname{card}\left(\operatorname{endpointFamily}\left(m\right)\right) = \left(m + 1\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EndpointShuffleSupport.endpointFamily_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing uniqueness theorem for unary-gap words recovers the outer gaps from the resulting word. Thus the output map is injective and its finite image has (m+1)^2 elements.

**Theorem 1.6 (A universal lower bound for distinct support).**

$$\forall m, \left(m + 1\right)^{2} \le \operatorname{card}\left(\operatorname{toFinset}\left(\operatorname{ordinaryShuffles}\left(\operatorname{endpointWord}\left(m\right), \operatorname{endpointWord}\left(m\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EndpointShuffleSupport.endpoint_self_shuffle_card_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every word in the parameter image belongs to the actual self-shuffle support. Inclusion and the image cardinality give the displayed lower bound.

**Theorem 1.7 (Every output has two bounded outer gaps).**

$$\forall m,w, \operatorname{member}\left(w, \operatorname{ordinaryShuffles}\left(\operatorname{endpointWord}\left(m\right), \operatorname{endpointWord}\left(m\right)\right)\right)\implies \exists a,c, a \le m\land c \le m\land w = \operatorname{endpointOutput}\left(m, a, c\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EndpointShuffleSupport.endpoint_support_exhaustion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first output symbol is an initial one of one source. Before the second one there can only be zeros from that source, so their number a is at most m. After the third one only one final one remains; its preceding c zeros belong to that remaining source, so c is at most m. All four ones occur, no zeros precede the first or follow the last, and the 2m zeros leave the middle gap equal to (m-a)+(m-c). Recursively, shuffling two tails of r and s zeros followed by one gives b zeros, one, c zeros, one, where b+c=r+s and c is at most max(r,s). This supplies the bounds for every schedule, including adjacent ones and all empty zero blocks.

**Theorem 1.8 (Exact support equality).**

$$\forall m, \operatorname{toFinset}\left(\operatorname{ordinaryShuffles}\left(\operatorname{endpointWord}\left(m\right), \operatorname{endpointWord}\left(m\right)\right)\right) = \operatorname{endpointFamily}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EndpointShuffleSupport.endpoint_support_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Universal exhaustion gives one inclusion; the explicit construction of each bounded outer-gap pair gives the other. The equality concerns words with duplicates discarded, regardless of how many schedules produce a word.

**Theorem 1.9 (Exact cardinality for every zero-run length).**

$$\forall m, \operatorname{card}\left(\operatorname{toFinset}\left(\operatorname{ordinaryShuffles}\left(\operatorname{endpointWord}\left(m\right), \operatorname{endpointWord}\left(m\right)\right)\right)\right) = \left(m + 1\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EndpointShuffleSupport.endpoint_self_shuffle_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support equals the injectively parametrized rectangle, whose cardinality is (m+1)^2. This holds for every natural m, including m=0.

**Definition 1.10 (Ordinary binary numerals).**

$$\forall (n:\mathbb{N}), \operatorname{binaryWord}\left(n\right) = \operatorname{mapDigitEqualsOne}\left(\operatorname{reverse}\left(\operatorname{digits}\left(2, n\right)\right)\right)$$

*Formalization.* `D5/S1/Words/EndpointShuffleSupport.binaryWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive n, use its ordinary finite base-two digits, reverse the least-significant-first list to put the most significant digit first, and map 0 to false and 1 to true. The standard digits operation introduces no leading zeros. The definition extends to n=0 by the empty list.

**Definition 1.11 (Distinct output count).**

$$\forall (n:\mathbb{N}), \operatorname{distinctSelfShuffleCount}\left(n\right) = \operatorname{card}\left(\operatorname{toFinset}\left(\operatorname{ordinaryShuffles}\left(\operatorname{binaryWord}\left(n\right), \operatorname{binaryWord}\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/EndpointShuffleSupport.distinctSelfShuffleCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is a(n): arbitrary order-preserving interleavings of two identical ordinary binary numerals, counting each output word once.

**Theorem 1.12 (Binary bridge at every positive exponent).**

$$\forall k, 1 \le k\implies \operatorname{binaryWord}\left(2^{k} + 1\right) = \operatorname{endpointWord}\left(k - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EndpointShuffleSupport.binaryWord_pow_add_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k at least one, the binary numeral of 2^k+1 is one, k-1 zeros, one. The standard base-digit concatenation theorem gives this identity directly; reversal preserves this particular word.

**Theorem 1.13 (The eventual identity with threshold one).**

$$\exists K, 1 \le K\land \forall k, K \le k\implies \operatorname{distinctSelfShuffleCount}\left(2^{k} + 1\right) = k^{2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/EndpointShuffleSupport.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All variables are natural numbers. Choose K=1. For every k at least K, substitute m=k-1 into the exact support cardinality and use the ordinary binary bridge. Then (m+1)^2=k^2. This preserves the eventual quantifier and supplies a threshold valid uniformly for all subsequent exponents.

The selected source assertion is the standalone eventual identity a(2^k+1)=k^2 in OEIS A193020, introduced by John W. Layman and retained in revision 13 under the stated caveat that k must exceed a lower bound. Source: https://oeis.org/A193020, OEIS content licensed CC-BY-SA-4.0. The other identities listed there are separate assertions.

## References

- Truth anchor: `D5/S1/Words/EndpointShuffleSupport.binaryWord`
- Truth anchor: `D5/S1/Words/EndpointShuffleSupport.binaryWord_pow_add_one`
- Truth anchor: `D5/S1/Words/EndpointShuffleSupport.distinctSelfShuffleCount`
- Truth anchor: `D5/S1/Words/EndpointShuffleSupport.endpointFamily`
- Truth anchor: `D5/S1/Words/EndpointShuffleSupport.endpointFamily_card`
- Truth anchor: `D5/S1/Words/EndpointShuffleSupport.endpointOutput`
- Truth anchor: `D5/S1/Words/EndpointShuffleSupport.endpointOutput_mem`
- Truth anchor: `D5/S1/Words/EndpointShuffleSupport.endpointWord`
- Truth anchor: `D5/S1/Words/EndpointShuffleSupport.endpoint_self_shuffle_card`
- Truth anchor: `D5/S1/Words/EndpointShuffleSupport.endpoint_self_shuffle_card_lower`
- Truth anchor: `D5/S1/Words/EndpointShuffleSupport.endpoint_support_eq`
- Truth anchor: `D5/S1/Words/EndpointShuffleSupport.endpoint_support_exhaustion`
- Truth anchor: `D5/S1/Words/EndpointShuffleSupport.result`
- Dependency: [D5/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration](Complexity/ExactDecks/UpperBound/OverlapInfiltration.md)
- Dependency: [D5/S1/Words/UnaryGapWords](UnaryGapWords.md)
