# Original Root J: the zero Delta rank two layer

## Abstract

A fixed original leaf on the whole zero Delta history layer

The source assignment P ranges over all 256 original slots, indexed by the seven chronological binary digits followed by the copy digit, with J before M and copy 0 before copy 1. Each source is strictly positive, has rank one and trace one. Repeated sources are allowed. Only the two J^7 source signatures b+c are required to equal one; the other 254 sources remain arbitrary legal sources.

Blocks keeps all 1024 real coefficient coordinates, including the independent constant coefficient of every cubic or lower degree gain. Row keeps each nonreference descendant of each of the 254 nonempty chronological prefixes. Its depth counts are 254, 252, 248, 240, 224, 192 and 128, totaling 1538. The reference is the first descendant in the original order. B uses the native acquisition matrix at that exact prefix and clock, and V is the entire kernel of this one B. Zero coefficient blocks, lower degrees, signed coefficients and sample roots are retained.

**Theorem 1.1 (The actual normalized response row).**

Lean statement: `D5/S3/Observer/CubicGain/RootJDeltaZero.normalized_eval`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/RootJDeltaZero.normalized_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every chronological word w, every real two by two matrix P and every four component coefficient vector b, normalized(w,P)(b) equals trace(acquisition(w)*P) times [b(0)+length(w)*b(1)+length(w)^2*b(2)+length(w)^3*b(3)], minus b(0). The native acquisition left multiplies actions in chronological order. This response expansion is used in the prefix bridge and the full source tuple audit witness.

H removes the constant coefficient from the first original J^7 block. E is 3*H(4)-2*H(2), Delta is H(3)-H(1), and F is [H(1)+H(3)]/2+E. Rank H means the dimension of the image of H on this whole V; no assumption on the dimension of V is made. All history identities used below are identities of maps on that same V.

**Theorem 1.2 (A fixed original same source leaf has zero entire coefficient difference).**

Lean statement: `D5/S3/Observer/CubicGain/RootJDeltaZero.fixed_original_leaf`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/RootJDeltaZero.fixed_original_leaf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complete source assignment P, assume every P(q) is legal, the source signatures at slots 0 and 1 are one, the image of H has real dimension two, E is a nonzero linear form on V, and Delta is the zero linear form on V. Then at least one of the following three fixed alternatives holds: P(8)=P(9) and, for every x in V, x(8)=x(9); P(12)=P(13) and, for every x in V, x(12)=x(13); or P(10)=P(11) and, for every x in V, x(10)=x(11). Each x(q) is the entire four coefficient vector. The three pairs are exactly J^4MJJ, J^4MMJ and J^4MJM. Thus one fixed original leaf has equal sources and its entire four component D map is zero on all V.

The proof derives the common ancestor and response equations from the native B rows. Delta zero propagates the common nonconstant gain to every J^4 descendant, while rank H two and E nonzero give independent F and E forms. The fixed source case split first compares the J^4MJJ pair. In its unit branch the J^4MMJ pair has equal source and whole gain; in its nonunit branch the J^4MJM pair has equal source and whole gain. Positive fixed source parameters justify cancellation. No gain sample or value of a linear form at an individual vector is divided out.

The conclusion concerns this conditional rank two layer. It does not construct a tuple satisfying all original gain and separation guards or decide the full original decoding problem. The first J^7 signature already suffices for the proof; the statement retains the original pair of unit signature hypotheses.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/RootJDeltaZero.fixed_original_leaf`
- Truth anchor: `D5/S3/Observer/CubicGain/RootJDeltaZero.normalized_eval`
- Dependency: [D5/S3/Observer/Linear/GainRayNuisance](../Linear/GainRayNuisance.md)
- Dependency: [D5/S3/Observer/Linear/GainRayWordGeometry](../Linear/GainRayWordGeometry.md)
