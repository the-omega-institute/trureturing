# Five-row two-defect strips

## Abstract

Five-row HA arrays with exactly two equal-colour bonds.

There are 123 states, with 41 colour classes in each exact remaining-budget sector. All bonds join adjacent columns: five horizontal bonds and four antidiagonal bonds.

**Definition 1.1 (S).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229698}.\operatorname{HardinA229698StripData}.\operatorname{S}\left(\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right), \operatorname{Int}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.S` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

The 41 by 41 integer table counts successor columns with exactly two equal-colour HA bonds. Its entries are pinned by HardinA229698StripNew.quotient_rows.

**Definition 1.2 (B).**

$$\forall (i: \operatorname{Fin}\left(41\right)), ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229698}.\operatorname{HardinA229698StripData}.\operatorname{B}\left(i\right): \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right)\right) \to \operatorname{Int}) = \operatorname{Sum}.\operatorname{elim}\left(\operatorname{HardinA229590StripData}.\operatorname{R}\left(i\right), \operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229698}.\operatorname{HardinA229698StripData}.\operatorname{S}\left(i\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.B` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

The rectangular block joins the one-bond and two-bond transitions.

**Definition 1.3 (cl).**

$$\forall (p: \operatorname{HardinA233260Literal}.\operatorname{Col}\left(\right)), (\forall (d: \operatorname{Nat}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229698}.\operatorname{HardinA229698StripData}.\operatorname{cl}\left(p, d\right): \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right)\right)\right)) = (\operatorname{if} (d = 2) \operatorname{then} \operatorname{Sum}.\operatorname{inl}\left(\operatorname{HardinA233260Literal}.\operatorname{cls}\left(p\right)\right) \operatorname{else} \operatorname{Sum}.\operatorname{inr}\left(\operatorname{HardinA229590StripData}.\operatorname{cl}\left(p, d\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

The first summand has two defects left; the other summand keeps the one-defect classification.

**Definition 1.4 (T).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229698}.\operatorname{HardinA229698StripData}.\operatorname{T}\left(\right): \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right)\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right)\right)\right), \operatorname{Int}\right)) = \operatorname{Matrix}.\operatorname{fromBlocks}\left(\operatorname{HardinA233260Literal}.\operatorname{Q}\left(\right), \operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229698}.\operatorname{HardinA229698StripData}.\operatorname{B}\left(\right), (0: \operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right)\right), \operatorname{Fin}\left(41\right), \operatorname{Int}\right)), \operatorname{HardinA229590StripData}.\operatorname{T}\left(\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

The diagonal block on the last 82 states is the one-defect matrix.

**Definition 1.5 (initial).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229698}.\operatorname{HardinA229698StripData}.\operatorname{initial}\left(\right): \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right)\right)\right) \to \operatorname{Int}) = \operatorname{Sum}.\operatorname{elim}\left((\lambda (i: \operatorname{Fin}\left(41\right)) \mapsto \operatorname{HardinA229590StripData}.\operatorname{initial}\left(\operatorname{Sum}.\operatorname{inl}\left(i\right)\right)), (0: \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right)\right) \to \operatorname{Int})\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

Initial columns begin with two defects left and retain the original class multiplicities.

**Definition 1.6 (terminal).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229698}.\operatorname{HardinA229698StripData}.\operatorname{terminal}\left(\right): \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Sum}\left(\operatorname{Fin}\left(41\right), \operatorname{Fin}\left(41\right)\right)\right) \to \operatorname{Int}) = \operatorname{Sum}.\operatorname{elim}\left((0: \operatorname{Fin}\left(41\right) \to \operatorname{Int}), \operatorname{HardinA229590StripData}.\operatorname{terminal}\left(\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

Only the zero-budget sector contributes at the terminal boundary.

**Definition 1.7 (coefficients).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{StatisticalMechanics}.\operatorname{Potts}.\operatorname{StripDefectsWide}.\operatorname{A229698}.\operatorname{HardinA229698StripData}.\operatorname{coefficients}\left(\right): \operatorname{Fin}\left(21\right) \to \operatorname{Int}) = \begin{pmatrix}(-512)&9216&(-71424)&307392&(-774528)&1014720&(-28632)&(-2236608)&3547332&(-1660207)&(-1956780)&3520224&(-2005784)&(-166467)&997536&(-718624)&282276&(-68685)&10468&(-960)&48\end{pmatrix}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.coefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229698: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229698>.

*Commentary.*

Coefficients are listed from the smallest power to the largest power.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.B`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.S`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.coefficients`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal](../../../../Combinatorics/TraceAvoidingArrays/HardinA233260Literal.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripData](../A229590/HardinA229590StripData.md)
