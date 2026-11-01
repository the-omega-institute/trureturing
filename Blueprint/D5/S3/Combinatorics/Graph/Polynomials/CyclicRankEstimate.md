# Signed rank-state coefficient estimate

## Abstract

The signed rank-state polynomial has an exact finite coefficient decomposition. Forest states supply the negative-binomial coefficient, while a bounded cyclic-state count and a uniform term bound give the coefficient error estimate. The graph wrapper records the actual SimpleGraph rank state used by the eventual weaving application; its bounded-degeneracy counting and Jones/geometric identification remain later obligations.

**Definition 1.1 (State exponent).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponent`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite polynomial uses the Nat conversion of the integer exponent only after an explicit nonnegativity proof has been supplied.

**Definition 1.2 (Integer rank-state exponent).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponentInteger`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponentInteger` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exponent is first formed in Z as v − 1 + s − 2q, before any conversion to a polynomial Nat exponent.

**Theorem 1.3 (No-truncation exponent bridge).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponent_cast_eq_integer`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponent_cast_eq_integer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the explicit integer nonnegativity hypothesis, the Nat exponent used by the polynomial casts back to the original integer rank-state exponent.

**Definition 1.4 (Signed rank-state term).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateTerm`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each subset state contributes its sign, rank power and (1+z) exponent to the integer polynomial.

**Definition 1.5 (Signed rank-state polynomial).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.statePolynomial`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.statePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial is the finite sum over all edge-indexed subset states.

**Definition 1.6 (Forest states).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forestStates`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forestStates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

States with q(S)=|S| are selected as the forest part of the finite subset sum.

**Definition 1.7 (Cyclic states).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicStates`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicStates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

States with q(S)<|S| are selected as the cyclic part.

**Definition 1.8 (Coefficient of one state).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.termCoefficient`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.termCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient of z^k in one state term is the signed binomial contribution when q(S)≤k and is zero otherwise.

**Definition 1.9 (Ideal forest coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.idealCoefficient`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.idealCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The comparison coefficient is Ring.choose (−b) k over the integers.

**Theorem 1.10 (Negative-binomial coefficient formula).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.idealCoefficient_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.idealCoefficient_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ideal coefficient equals (−1)^k choose(b+k−1,k), including the b=k=0 boundary case.

**Theorem 1.11 (Exact state coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_stateTerm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_stateTerm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Polynomial coefficient extraction agrees with termCoefficient for every finite subset state.

**Theorem 1.12 (Exact finite coefficient sum).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_statePolynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_statePolynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of the full state polynomial is the finite sum of the state coefficients.

**Definition 1.13 (Forest coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forestCoefficient`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forestCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forest contribution is the sum of termCoefficient over forestStates.

**Definition 1.14 (Cyclic coefficient).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicCoefficient`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cyclic contribution is the sum of termCoefficient over cyclicStates.

**Theorem 1.15 (Forest/cyclic coefficient split).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the rank upper bound, every state belongs to exactly one of the forest and cyclic filters, so the full coefficient splits into the two contributions.

**Theorem 1.16 (Cyclic absolute coefficient bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.natAbs_cyclicCoefficient_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.natAbs_cyclicCoefficient_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A uniform per-state NatAbs bound B implies the cyclic coefficient is bounded by the cyclic-state cardinality times B.

**Theorem 1.17 (Signed coefficient estimate).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.signed_tutte_coefficient_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.signed_tutte_coefficient_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem consumes coeff_split and the cyclic absolute bound: if the forest coefficient is the ideal coefficient, the coefficient error is bounded by the cyclic count times the per-state bound, with the stated uniform growth envelope.

**Definition 1.18 (Actual simple-graph edge predicate).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphEdgePredicate`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphEdgePredicate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph wrapper lifts SimpleGraph adjacency to the unordered edge type Sym2(Fin n).

**Definition 1.19 (Actual graph edge type).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphEdge`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph wrapper restricts the finite edge index type to the actual adjacency predicate, so nonedges are not duplicated in the subset state sum.

**Definition 1.20 (Actual graph rank state).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphRank`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph wrapper computes rank from the connected-component count of the image of the actual edge subset, including isolated vertices.

**Definition 1.21 (Actual graph state polynomial).**

Lean statement: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphStatePolynomial`

*Formalization.* `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphStatePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph wrapper instantiates the signed state polynomial with graphRank; it is the consumer interface for the later bounded-degeneracy and weaving layer.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_split`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_statePolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.coeff_stateTerm`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicCoefficient`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.cyclicStates`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forestCoefficient`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.forestStates`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphEdge`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphEdgePredicate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphRank`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.graphStatePolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.idealCoefficient`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.idealCoefficient_formula`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.natAbs_cyclicCoefficient_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.signed_tutte_coefficient_estimate`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponent`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponentInteger`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateExponent_cast_eq_integer`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.statePolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.stateTerm`
- Truth anchor: `D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.termCoefficient`
