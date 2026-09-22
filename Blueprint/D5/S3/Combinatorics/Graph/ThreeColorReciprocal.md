# Three-color reciprocal inequality

## Abstract

A proper three-coloring whose mixed vertices have degree two forces a reciprocal potential of at least 23/12, without restrictions on the other degrees or on class sizes.

**Definition 1.1 (Coefficient sign test).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.nonnegativeCoefficients`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.nonnegativeCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sign test accepts a normalized integer polynomial exactly when every stored coefficient is nonnegative. Such a polynomial is nonnegative at every tuple of nonnegative rational arguments.

**Definition 1.2 (Ordinary-pair regions).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.Choice`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.Choice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A region is either a thin pair with a specified finite population and an empty opposite side, or a pair with both sides positive and a specified orientation. Positive pairs are parameterized by a smaller side minus one and a nonnegative difference.

**Definition 1.3 (Feasible region choices).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.choices`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.choices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For sorted mixed populations a at most b, equal populations permit the empty ordinary pair. Unequal populations permit a thin side of size between one and b-a, on the side with smaller mixed population. Both positive orientations are also included.

**Definition 1.4 (Symbolic side sizes).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.sizes`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.sizes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each positive pair uses two nonnegative variables: its smaller size is one plus the first variable, and its larger size adds the second variable. A thin pair has its specified constant size and a zero opposite side. Three pairs use six variables.

**Definition 1.5 (Positive-pair indicator).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.isFull`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.isFull` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This indicator distinguishes regions with both ordinary sides positive from thin regions. The case where all three pairs are positive is handled by the attachment-charge estimate.

**Definition 1.6 (Pair fractions).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.charge`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.charge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These rational-expression numerators and denominators encode twelve times a pair contribution. The quadratic branch uses six times each ordinary size squared and its degree-sum denominator; a thin side uses its exact mixed-population difference. The linear branch records the corresponding size-over-degree expression.

**Definition 1.7 (Cleared polynomial).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.numerator`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.numerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial multiplies twelve times the lower expression minus twenty-three by the product of its positive denominators. Its terms include the three class reciprocals, the mixed contribution, and the three ordinary-pair contributions.

**Definition 1.8 (Fixed mixed-population check).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.checkMixed`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.checkMixed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a fixed sorted triple of mixed populations, the check ranges over every permitted ordinary-pair region and tests nonnegativity of the cleared polynomial coefficients. The case of three positive pairs is reserved for the separate analytic estimate.

**Definition 1.9 (Fixed total mixed-population check).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.checkTotal`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.checkTotal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This check ranges over every sorted triple of mixed populations having the specified total. Totals zero through five contain 754 regions with at most two positive ordinary pairs; the six side parameters remain unrestricted nonnegative integers.

**Definition 1.10 (Numerical region sizes).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.side`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.side` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This evaluates a region at its two nonnegative integer parameters, retaining the specified orientation. Every feasible ordinary pair has one of these representations.

**Definition 1.11 (Six-variable evaluation context).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.context`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.context` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The evaluation context supplies the six nonnegative parameters of the three ordinary pairs to their symbolic polynomials.

**Definition 1.12 (Common-denominator construction).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.assembled`

*Formalization.* `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.assembled` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a constant and a list of rational-expression numerators and denominators, the construction forms their common-denominator numerator. Each fraction contributes its numerator times the product of all other denominators. Positivity of every denominator allows the sign of the rational sum to be read from this polynomial.

**Theorem 1.13 (Unrestricted numerical population inequality).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.population_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.population_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural populations with zero diagonal and the empty-side feasibility inequalities, the maximum of the attachment-charge and Cauchy expressions is at least 23/12. If the mixed total M is at least six and N is the ordinary total, Cauchy gives the lower bound M/6+9/(N+M+3)+N squared divided by N squared plus 2N plus 4M; a polynomial with nonnegative terms proves this is sufficient. For M at most five with all three ordinary pairs positive, the attachment estimate gives at least 9/4-M/36. In all remaining cases, sorting the mixed populations and representing every feasible ordinary pair reduces the inequality to the 754 cleared polynomials, each with nonnegative coefficients. There is no bound on the ordinary sizes.

**Theorem 1.14 (Three-color reciprocal bound).**

Lean statement: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.reciprocal_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.reciprocal_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite vertex set, symmetric adjacency relation, and specified proper coloring into three possibly empty classes, if every mixed vertex has degree exactly two then the potential is at least 23/12. Degrees and class sizes are unrestricted. Delete the isolated vertices; the remaining neighborhoods do not change. Removing r isolates from a class with a remaining vertices cannot increase the potential, since 1/(a+1) is at most 1/(a+r+1)+r/2. Apply the actual population reduction and the numerical inequality to the remaining graph.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.Choice`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.assembled`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.charge`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.checkMixed`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.checkTotal`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.choices`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.context`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.isFull`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.nonnegativeCoefficients`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.numerator`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.population_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.reciprocal_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.side`
- Truth anchor: `D5/S3/Combinatorics/Graph/ThreeColorReciprocal.sizes`
- Dependency: [D5/S3/Combinatorics/Graph/ThreeColorIncidence](ThreeColorIncidence.md)
