# Signed support and dense occurrence ranks

## Abstract

CountedSignedGyrationSupport

**Definition 1.1 (Matrix support is tested on occurrence fibres).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.Supported`

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.Supported` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the existing CountedOrderTypeGyration entry type: the disjoint union of entries of R, of size n by m, and S, of size m by n. A vertex word is a pair a:Fin d to Fin n and b:Fin d to Fin m, with nonzero period d. Its R occurrence at t has entry (a t,b t); its S occurrence has entry (b t,a(t+1)). Supported means that every entry with a nonempty occurrence fibre is nonzero. It imposes no primitivity condition on the vertex word.

The original summand is wordWeight on the same ranked source and target product edges, multiplied by the product of Ring.choose(z e,widths T e) over all entries. A used zero entry has strictly positive width, so its factor is zero independently of all other signed entries. A positive entry equal to one contributes only widths zero or one; larger widths vanish. These vanishing laws restrict the original sum.

**Theorem 1.2 (The negative binomial factors remain).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.binomial_product`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.binomial_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a ternary tuple z taking values minus one, zero or one, restrict to Supported words and Normal patterns, where a one entry has width at most one. An absent occurrence fibre has the unique width-zero pattern and factor one. At a minus-one entry, Ring.choose(-1,k) is exactly (-1)^k for every allowed width k. All such widths are retained; a signed entry is not replaced by a nonnegative edge multiplicity. The product is therefore the product of these parity factors. The proof uses the binomial laws and the existing Pattern type; it does not reconstruct a different polynomial.

**Definition 1.3 (Dense labels are per occurrence fibre).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.rankVectors`

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.rankVectors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an S entry e, sSlots is its actual set of time occurrences. rankWidth is the cardinality of the image of the natural labels on that set. A rank vector l assigns a natural number to each time slot. At a negative S entry each label is below the number of occurrences of that same entry; elsewhere the preliminary bound is one. The additional filter requires each label to be below rankWidth of its own occurrence fibre. Consequently the image is exactly the initial interval from zero to rankWidth minus one, with no gaps. A positive used S entry has label zero. Empty fibres retain width zero without a separately supplied value.

patternOfNat constructs a Pattern from an already dense function: card(image) bounds the width, and the finite image in Fin(card(image)) has full cardinality, proving surjectivity. This differs from the existing realizationEquiv, which decomposes arbitrary labels in Fin z into an ordered pattern and an increasing realization. Here no compression of arbitrary natural labels, arbitrary ordering of the image, or new half-edge numbering is introduced.

**Theorem 1.4 (Recover the dependent word type).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.typeOfRanks_sRanks`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.typeOfRanks_sRanks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume R is binary, S is ternary, the word is supported and T is normal. sRanks extracts the natural S labels. sRanks_mem proves that they satisfy the fibre bounds and dense-image filter. typeOfRanks reconstructs R patterns from constant zero labels and S patterns from those dense labels. A Pattern's natural label image determines its width, so equality of its natural labels determines the dependent Pattern itself. The R labels vanish because every used R entry equals one; the S labels are recovered at their original occurrences. This proves typeOfRanks(sRanks T)=T. The converse sRanks(typeOfRanks l)=l is the definitional helper used in the surjectivity arm of the final finite-sum bijection.

**Theorem 1.5 (Reindex the original signed polynomial sum).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.signedGyrationLift_supported_surjections`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.signedGyrationLift_supported_surjections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural n,m and every nonzero d, with R:n by m binary and S:m by n ternary, the existing signedGyrationLift equals the sum over outside words a, supported middle words b, and dense S rank vectors l of rankedTerm. middleWords retains precisely the middle vertices with R(a t,b t) and S(b t,a(t+1)) nonzero. The proof first removes unsupported words and nonnormal patterns by their zero summands, then uses sRanks and typeOfRanks as the explicitly proved inverse maps in Finset.sum_bij. binomial_product and width_sRanks identify the surviving coefficient. rankedTerm still uses the original wordWeight, sourceEdge and targetEdge.

The cyclic group of time rotations continues to act on the actual ranked edge words. Repeated unlabelled vertex cycles remain in the index: their rank labels can change least-rotation comparisons. Empty dimensions and zero entries are included, and singular matrices require no extra premise. Period zero is excluded by NeZero d; divisibility by three is not required here. The signed polynomial itself is defined for arbitrary integer tuples, but this sparse reindexing requires exactly the binary R and ternary S hypotheses. The evaluator module applies this equality to express the same signed lift in natural coordinates. These derivations use existing finite-sum and binomial tools; they do not assert a full mod-six law or an original-h theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.Supported`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.binomial_product`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.rankVectors`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.signedGyrationLift_supported_surjections`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedSignedGyrationSupport.typeOfRanks_sRanks`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer](CountedPositiveTriangleLocalizedConsumer.md)
