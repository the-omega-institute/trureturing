# Recovering paired Boolean labels

## Abstract

Paired Boolean labels are determined by same-side membership and all pair distances, up to four global symmetries.

**Theorem 1.1 (Pair distances recover the four symmetry classes).**

$$\forall I:\operatorname{Type}\left(\right), (\forall f:I\to\operatorname{prod}\left(\operatorname{Bool}\left(\right), \operatorname{Bool}\left(\right)\right), (\forall g:I\to\operatorname{prod}\left(\operatorname{Bool}\left(\right), \operatorname{Bool}\left(\right)\right), ((\forall i:I, (\operatorname{sameSide}\left(f\left(i\right)\right) \Leftrightarrow \operatorname{sameSide}\left(g\left(i\right)\right))) \Rightarrow \left((\forall i:I, (\forall j:I, (\operatorname{pairDistance}\left(f\left(i\right), f\left(j\right)\right) = \operatorname{pairDistance}\left(g\left(i\right), g\left(j\right)\right)))) \Rightarrow \exists s:\operatorname{Bool}\left(\right), (\exists c:\operatorname{Bool}\left(\right), (\forall i:I, (g\left(i\right) = \operatorname{transform}\left(s, c, f\left(i\right)\right))))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PermutationCriteria/LabelRecovery.recover_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier I is an arbitrary type, including the empty type. A label is an ordered pair of Boolean values. sameSide(x) means that the two coordinates of x agree; pairDistance counts coordinate disagreements. The hypotheses preserve sameSide at every site and pairDistance for every ordered pair of sites. Within either sameSide sector, distance zero distinguishes equal first coordinates from unequal ones. The first coordinates therefore change by one constant Boolean XOR in each sector. The two sector constants combine into a global exchange of coordinates and a global simultaneous complement. transform(s,c,x) first exchanges coordinates when s is true, then applies XOR with c to both coordinates. Its four choices are the identity, simultaneous complement, coordinate exchange, and their composite.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PermutationCriteria/LabelRecovery.recover_labels`
