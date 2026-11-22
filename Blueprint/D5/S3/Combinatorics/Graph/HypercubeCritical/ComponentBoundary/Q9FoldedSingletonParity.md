# Residual singleton quota for a coordinate fold

## Abstract

Odd rows on fixed singleton sites give a lower bound on the number of extra singleton sites in a completion.

**Theorem 1.1 (Odd rows force a residual incidence quota).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSingletonParity.card_rows_le_residual_quota`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSingletonParity.card_rows_le_residual_quota` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be a finite set of rows, N(r) the finite set of sites adjacent to row r, and A the fixed sites. Suppose a completion S contains A. For each row in R, assume the degree on A is odd and the degree on S is even. If each site of S outside A is incident to at most m rows in R, then |R| ≤ m · (|S| − |A|).

At each row the degree on S adds the degree on A and the degree on S outside A. The last degree is odd by parity cancellation, hence positive. Counting the incidences between the rows and the chosen sites outside A gives at least one per row and at most m per such site. Mathlib's Finset.card_mul_le_card_mul supplies the incidence bound.

For a Huang-balanced induced cubic support of order 126, fold Q₉ along the archived axis to Q₈. At each folded centre, apply Q9FoldedIncidence.folded_degree_of_balanced_cubic with each of the two original cube parities as source. The degree for each source includes the centre label and the eight transverse labels. It is odd exactly when the centre belongs to the opposite folded parity set. Adding the two degrees modulo two therefore gives the singleton bit at the centre. The centre label already contributes that bit, so the sum of the eight transverse singleton bits is even.

For cases 2, 3 and 6, take S to be the singleton sites in the odd class of Q₈. The 18+3 dimer profile gives 168 transverse edges, since 3 · 126 / 2 − (18 + 3) = 168. On the odd class each of the three dimers accounts for four transverse incidences and each singleton for three. Thus the odd class has a quota of 52 singletons.

The verified signed-shadow domains and one pass of parity forcing give a fixed set A of 48 odd singleton sites in each case. The admissible extra sites are odd sites outside both the shadow and A. Take R to be all even centres with an odd number of transverse neighbours in A. The archive replay gives 24, 24 and 32 rows in cases 2, 3 and 6 respectively, and at most four incident rows per admissible extra site. The bound gives at least 6, 6 and 8 extra sites, hence at least 54, 54 and 56 odd singletons. Only four extra sites fit the quota.

The inputs on forced and admissible sites and the row counts come from the order126 archive's fold-parity-quota-result.json and fold-parity-quota.py replay. The incidence argument applies to cases 2, 3 and 6 of the seven archived degree-six order-eighteen supports with their inherited fold and verified shadow domains. The full value of f₂(Q₉) in Hong, Wu and Xia's Problem 2 remains open. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedSingletonParity.card_rows_le_residual_quota`
