# A support obstruction to factorization

## Abstract

A homogeneous multiaffine quartic in eight variables with fewer than twenty zero squarefree quartic coefficients is irreducible.

Let k be any field and let the variable labels be Fin 8. For a set I of labels, squareExponent I is the sum of the single exponents at its members. The set fourSets consists of all four-element subsets of Fin 8; coeff(f,squareExponent(I)) denotes the corresponding squarefree quartic coefficient. The operator ite chooses its second argument when its first argument is true, and its third argument otherwise.

**Lemma 1.1 (Coordinates of a squarefree exponent).**

$$\forall I: \operatorname{Finset}(\operatorname{Fin}(8)), \forall i: \operatorname{Fin}(8), \operatorname{eval}(\operatorname{squareExponent}(I), i)=\operatorname{ite}(i\in I, 1, 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/SplitQuarticIrreducibility.square_exponent_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponent has coordinate one at each member of I and zero elsewhere. This identifies a squarefree monomial with its exact set of variable labels.

**Lemma 1.2 (Degree of a squarefree exponent).**

$$\forall I: \operatorname{Finset}(\operatorname{Fin}(8)), \operatorname{degree}(\operatorname{squareExponent}(I))=\operatorname{card}(I)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/SplitQuarticIrreducibility.square_exponent_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing these coordinates gives the cardinality of I. In particular, four-element sets give degree-four monomials.

**Theorem 1.3 (The arbitrary-factor obstruction).**

$$\forall k, \operatorname{Field}(k)\implies\forall f: \operatorname{MvPolynomial}(\operatorname{Fin}(8), k), \operatorname{IsHomogeneous}(f, 4)\land(\forall i: \operatorname{Fin}(8), \operatorname{degreeOf}(i, f)\le1)\land\operatorname{card}(\{I\in fourSets\mid\operatorname{coeff}(f, \operatorname{squareExponent}(I))=0\})<20\implies\operatorname{Irreducible}(f)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/SplitQuarticIrreducibility.irreducible_of_fewer_than_twenty_zeros` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are seventy squarefree quartic positions. Suppose fewer than twenty coefficients at these positions vanish. Then f is irreducible over k; neither algebraic closure nor characteristic zero is required.

For an arbitrary factorization f=FG, additivity of degree in each variable forces the variable sets of F and G to be disjoint. A nonzero monomial of each factor therefore multiplies without coefficient cancellation. Homogeneity of f forces every supported monomial of F to have the same degree. Consequently every nonzero squarefree coefficient of f has the same number of labels in the variable set of F.

Choose one label on each side of a nonempty proper cut. The remaining six labels have twenty triples. Adjoining either chosen label gives an exchange pair whose two intersection sizes differ by one; a fixed intersection size excludes at least one member of each pair. The twenty pairs are disjoint, so at least twenty quartic positions must vanish. This contradicts the assumed number of zero coefficients. Thus one factor must be a unit. The coefficient support argument applies to every factorization, rather than to factors of any prescribed shape.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/SplitQuarticIrreducibility.irreducible_of_fewer_than_twenty_zeros`
- Truth anchor: `D5/S3/Quantum/Algebra/SplitQuarticIrreducibility.square_exponent_apply`
- Truth anchor: `D5/S3/Quantum/Algebra/SplitQuarticIrreducibility.square_exponent_degree`
