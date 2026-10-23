# Native Birth-Vector Decoder

## Abstract

Complete-level native birth vectors decode exactly the finite original prefix pattern.

Address is the finite binary-word type and Source is the existing native source algebra. Pattern d is the finite original-prefix pattern at depth d. LevelAddress d contains exactly the addresses of length d, and a LevelVector d assigns a natural-number code to every such address. birthVector collects the recursively defined birthAt code: the empty address has code zero, an atomic source uses pathThreshold for alpha and its natural-number predecessor for beta, and a pair selects the child named by the first address bit without an epoch shift. patternVector is the corresponding code obtained from the decomposed original prefix.

The statements below concern these recursive codes. Interpreting birthAt as the least epoch of actual presence over the full Source/address family requires a separate bridge to native subtree navigation under iterated substitution; the decomposition and decoder identities do not supply that bridge.

decodeBirth tests the rightmost address for the alpha and beta sentinel codes at positive depth and otherwise recurses on the left and right blocks. Its proved guarantee is decodeBirth d (patternVector d p) = some p for every depth d and pattern p. Acceptance does not certify membership in the patternVector image: at depth zero every input returns some (), including a vector with nonzero entry, although every depth-zero pattern vector is zero.

**Theorem 1.1 (Native birth vectors are pattern vectors).**

$$\forall d \in Nat, \forall u \in Source, \operatorname{birthVector}\left(d, u\right) = \operatorname{patternVector}\left(d, \operatorname{decompose}\left(d, u\right).1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeBirthVectorDecoder.birthVector_decompose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The address recursion follows the root constructor. An atomic root uses the path threshold (or its predecessor for beta), while a pair root selects the child block matching the first address bit. Induction over depth therefore identifies the complete vector with the vector of the original prefix pattern.

**Theorem 1.2 (The decoder is exact on image vectors).**

$$\forall d \in Nat, \forall p \in \operatorname{Pattern}\left(d\right), \operatorname{decodeBirth}\left(d, \operatorname{patternVector}\left(d, p\right)\right) = \operatorname{some}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeBirthVectorDecoder.decodeBirth_patternVector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At depth zero the decoder returns the unique unit pattern. At positive depth, atomic alpha and beta roots are separated by the two rightmost sentinel values. For a pair root, the rightmost code is bounded below both sentinels, and the two block projections are the child pattern vectors. The induction hypothesis reconstructs both children and hence the pair pattern.

**Lemma 1.3 (Pattern-vector codes are bounded by twice the depth).**

$$\forall d \in Nat, \forall p \in \operatorname{Pattern}\left(d\right), \forall a \in \operatorname{LevelAddress}\left(d\right), \operatorname{patternVector}\left(d, p, a\right) \leq 2 \times d$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeBirthVectorDecoder.patternVector_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The path-threshold bound is proved by induction on the address. Pair patterns inherit the bound from the selected child at one smaller depth; atomic patterns use the same threshold bound and the predecessor inequality.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeBirthVectorDecoder.birthVector_decompose`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeBirthVectorDecoder.decodeBirth_patternVector`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeBirthVectorDecoder.patternVector_bound`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns](NativeDepthPatterns.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedNavigationCompiler](NativeRankedNavigationCompiler.md)
