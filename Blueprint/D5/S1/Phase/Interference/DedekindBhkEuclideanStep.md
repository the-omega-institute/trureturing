# Dedekind BHK Base, Euclidean Step, and Sign Obstruction

## Abstract

The finite Dedekind base and Euclidean reciprocity step hold, while a nonzero-walk certificate refutes the requested sign.

The frozen finite-residue formula evaluates the one-coefficient base. The frozen reciprocity theorem and numerator periodicity then give one exact Euclidean continued-fraction shift.

**Theorem 1.1 (The one-coefficient base).**

$$\forall c\in \mathbb{N},\ c>0 \Rightarrow \operatorname{dedekindSum}(1, c) = \frac{(c-1)(c-2)}{12c}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindBhkEuclideanStep.dedekind_sum_one_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After reducing the second residue with numerator one, every summand is a sawtooth square. The frozen linear and square sums give the displayed value.

**Theorem 1.2 (The corrected one-coefficient BHK base).**

$$\forall c\in \mathbb{N},\ c>0 \Rightarrow 12\times\operatorname{dedekindSum}(1, c) = -3 + \frac{1+1}{c} + \operatorname{alternatingWalk}([c])$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindBhkEuclideanStep.bhk_plus_walk_single_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting the closed base value and unfolding the frozen one-term walk gives the BHK equation with a plus walk. This is already incompatible with the requested minus-walk orientation.

**Theorem 1.3 (One Euclidean continued-fraction shift).**

$$\forall c, d\in \mathbb{N},\ c>0 \land d>0 \land \gcd(c, d)=1 \Rightarrow 12\times\operatorname{dedekindSum}(d, c) = -3 + \frac{c}{d} + \frac{d}{c} + \frac{1}{cd} - 12\times\operatorname{dedekindSum}(c \operatorname{mod} d, d)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindBhkEuclideanStep.dedekind_reciprocity_cf_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dedekind reciprocity supplies the explicit rational correction and flips the sum orientation. The periodicity theorem replaces the reversed numerator by its Euclidean remainder.

**Theorem 1.4 (A nonzero-walk sign counterexample).**

$$\frac{1}{2+\frac{1}{1+\frac{1}{1}}} = \frac{2}{5} \land (3\times2) \operatorname{mod} 5 = 1 \land \operatorname{alternatingWalk}([2, 1, 1]) = 2 \land \operatorname{dedekindSum}(2, 5) = 0 \land 12\times\operatorname{dedekindSum}(2, 5) \neq -3 + \frac{3+2}{5} - \operatorname{alternatingWalk}([2, 1, 1]) \land 12\times\operatorname{dedekindSum}(2, 5) = -3 + \frac{3+2}{5} + \operatorname{alternatingWalk}([2, 1, 1])$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindBhkEuclideanStep.bhk_minus_walk_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive odd expansion [0; 2, 1, 1] equals two fifths, three is the normalized inverse of two modulo five, and the frozen alternating walk equals two. The exact Dedekind sum is zero. Consequently the source's minus-walk equation is false here, while the plus-walk equation is exact.

The two earlier certificates both have zero alternating walk and therefore cannot distinguish these signs. The general finale remains open pending a corrected authoritative statement.

## References

- Truth anchor: `D5/S1/Phase/Interference/DedekindBhkEuclideanStep.bhk_minus_walk_counterexample`
- Truth anchor: `D5/S1/Phase/Interference/DedekindBhkEuclideanStep.bhk_plus_walk_single_coefficient`
- Truth anchor: `D5/S1/Phase/Interference/DedekindBhkEuclideanStep.dedekind_reciprocity_cf_step`
- Truth anchor: `D5/S1/Phase/Interference/DedekindBhkEuclideanStep.dedekind_sum_one_closed`
- Dependency: [D5/S1/Phase/Interference/DedekindBhkCertificates](DedekindBhkCertificates.md)
- Dependency: [D5/S1/Phase/Interference/DedekindReciprocity](DedekindReciprocity.md)
- Dependency: [D5/S1/Phase/Interference/DedekindReciprocityFiniteSums](DedekindReciprocityFiniteSums.md)
- Dependency: [D5/S1/Phase/WalkFormula](../WalkFormula.md)
