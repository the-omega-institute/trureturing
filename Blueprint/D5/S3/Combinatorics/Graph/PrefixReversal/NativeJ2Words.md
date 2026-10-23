# The Five Literal Native J2 Words

## Abstract

Five literal native J2 generator words reach their independently specified actual ports and have the exact required lengths.

Configurations are actual permutations of Fin(m+1), with reversals a, b and c of lengths m+1, m and m-1. Here m is at least five, p=0, q=m, v=m-1 and A=(1,...,m-2). The actual right ports are R0=(q,p,A,v), R1=(p,A,q,v) and R2=(A,q,p,v). Each left port Li is Ri*b, and bar exchanges the actual label values p and q by left multiplication. These ports are defined independently of the words.

Write Uk=(ab)^k a and H=Um, retaining the actual generator lists. In index order 0,...,4 the words are abc U(m-2) c U(m-1); (ab)^(m-1) (cH)^(m-3) ca; a (cH)^(m-3) caba; ac U(m-2); and abc U(m-1). Their required port pairs are R0 to R2, L0 to bar(L1), R1 to bar(L2), L2 to bar(R2), and bar(R0) to bar(R1).

**Theorem 1.1 (All Five Actual Endpoint Identities).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall i \in \mathrm{Fin}\left(5\right),\; \mathrm{mul}\left(\mathrm{wordStart}\left(m, i\right), \mathrm{prod}\left(\mathrm{word}\left(m, i\right)\right)\right) = \mathrm{wordFinish}\left(m, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Words.native_j2_word_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five and every i in Fin(5), wordStart(m,i) multiplied by the actual list product of word(m,i) equals wordFinish(m,i). The proof reuses uWord_product, computes H=b, obtains (cb)^(m-3)=(bc)^3 from the earned complete E identity (bc)^m=1, and checks the remaining native Fin coordinates extensionally. The first and fourth words use the actual endpoint-swap/rotation identity, reversal conjugation and the three-label transposition braid; sizes five through seven use kernel decide. No endpoint identity is assumed.

**Theorem 1.2 (All Five Exact Literal Edge Counts).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall i \in \mathrm{Fin}\left(5\right),\; \mathrm{length}\left(\mathrm{word}\left(m, i\right)\right) = \mathrm{wordLength}\left(m, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Words.native_j2_word_lengths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five and every i in Fin(5), the actual list length is the independently specified wordLength(m,i). In index order these lengths are 4m, 2m^2-2m-6, 2m^2-4m-1, 2m-1 and 2m+2. The proof counts the literal append and repetition lists, using uWord_length for their alternating native blocks.

Endpoints and lengths alone do not prove that these words use surviving edges of the specific F2 factor, avoid the six J2 marked cuts, form complete path components, or yield an all-size Hamilton cycle. Those edge-inventory and whole-component obligations remain separate.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Words.native_j2_word_endpoints`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Words.native_j2_word_lengths`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership](NativeCircleOwnership.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing](NativeCoreSplicing.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeSwitches](NativeSwitches.md)
