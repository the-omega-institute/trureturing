# Prime Collinear Triple Translation Fibers

## Abstract

Translation fibers of admissible collinear triples over a prime residue field.

**Theorem 1.1 (Slope and translated abscissae classify translation orbits).**

$$\forall p \in \operatorname{Nat}\left(\right),\; \forall hp \in \operatorname{Prime}\left(p\right),\; \forall s \in \operatorname{Triple}\left(p\right),\; \forall t \in \operatorname{Triple}\left(p\right),\; (s \in \operatorname{orbit}\left(\operatorname{Point}\left(p\right), t\right)) \Leftrightarrow ((\operatorname{val}\left(\operatorname{fst}\left(\operatorname{fst}\left(\operatorname{parametersOfTriple}\left(p, hp, s\right)\right)\right)\right) = \operatorname{val}\left(\operatorname{fst}\left(\operatorname{fst}\left(\operatorname{parametersOfTriple}\left(p, hp, t\right)\right)\right)\right)) \land (\exists h \in \operatorname{ZMod}\left(p\right),\; \operatorname{val}\left(\operatorname{snd}\left(\operatorname{parametersOfTriple}\left(p, hp, s\right)\right)\right) = \operatorname{translate}\left(h, \operatorname{val}\left(\operatorname{snd}\left(\operatorname{parametersOfTriple}\left(p, hp, t\right)\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Collinear/PrimeCollinearTripleTranslationFibers.translation_orbit_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every admissible triple over a prime residue field is the graph of a unique nonzero-slope affine line on a three-element set of first coordinates. Translation by (h,k) sends the slope a, intercept b, and abscissa set X to (a,b+k-ah,h+X). Thus a translation preserves the slope and shifts X by h. Conversely, equal slopes and X'=h+X determine the vertical shift k=b'-b+ah, so the intercepts add no orbit obstruction. This includes the empty family at p=2 and the nonempty case p=3.

## References

- Truth anchor: `D5/S3/Factorization/Collinear/PrimeCollinearTripleTranslationFibers.translation_orbit_iff`
- Dependency: [D5/S3/Factorization/Collinear/PrimeCollinearTripleCensus](PrimeCollinearTripleCensus.md)
