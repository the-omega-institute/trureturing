# Exact rational five-mode networks with internal zeros

## Abstract

Every nonnegative rational Boolean probability law is an exact finite five-mode marginal.

**Definition 1.1 (Ordered Boolean triples).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.Triple`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.Triple` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A triple is an ordered element of Bool times Bool times Bool. The two Boolean values are written zero and one.

**Definition 1.2 (Legal full probability tables).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.Table`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.Table` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A table assigns a nonnegative rational to each of the eight ordered Boolean triples. Its eight entries sum to one. It vanishes outside the existing relation A, consisting of 000, 100, 010, 110 and 001. Extra zeros within A are allowed; these are the W0 tables. Normalization concerns the full table even when a repeated scope visits fewer entries.

**Definition 1.3 (Scopes on actual variables).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.Factor`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.Factor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A factor on a variable type V consists of an ordered triple of members of V and a legal Table. Scope entries may repeat. There are no scope constructors for constants or complemented literals, and no extra equality, unary or multivariate primitive.

**Definition 1.4 (Evaluating a factor).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.value`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a Boolean assignment to V, evaluate its three actual scope variables in order and read that tuple's table entry.

**Definition 1.5 (Finite visible and hidden counts).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.Network`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.Network` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural n, m and k, a network consists of k factors whose variable names belong to the disjoint union Fin n plus Fin m. The first summand names the n visible variables; the second names the m hidden variables. Both m and k are arbitrary finite counts.

**Definition 1.6 (The full assignment weight).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.weight`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight at visible assignment a and hidden assignment h is the finite product over all factors, each evaluated in the combined assignment Sum.elim a h. An empty product is one.

**Definition 1.7 (Summing every hidden assignment).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.marginal`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.marginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The marginal at a sums the full assignment weight over every function from Fin m to Bool. No consistency predicate restricts this summation domain.

**Definition 1.8 (The partition function).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.partition`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.partition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The partition function sums the marginal over every visible assignment. Equivalently it sums the weight over all visible and hidden assignments.

**Definition 1.9 (Final normalization).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.law`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.law` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law at a is the marginal at a divided by the partition function. The representation theorem proves that the partition function is strictly positive.

**Definition 1.10 (The indicator potential).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.pinRaw`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.pinRaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The raw pin potential is one on each of the five tuples of A and zero on the remaining three tuples.

**Definition 1.11 (The normalized exclusion table).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.pinTable`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.pinTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Divide the raw pin potential by five. On (o,o,o) this forces the actual variable o to zero. On (u,u,w) it enforces that u and w are not simultaneously one, including a loop when u=w.

**Definition 1.12 (The full activity potential).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.unaryRaw`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.unaryRaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For rational r, the raw activity potential has value r at 110, value one at the four other tuples of A, and zero outside A. All eight entries are specified.

**Definition 1.13 (The normalized activity table).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.unaryTable`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.unaryTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For r nonnegative, divide the raw activity potential by four plus r. With an internally zero pin o, scope (u,u,o) has activities one and r, times the common normalization factor. When r is positive, every tuple of A has positive value.

**Definition 1.14 (Numbering finite hidden and factor types).**

Lean statement: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.numberedNetwork`

*Formalization.* `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.numberedNetwork` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given finite types H and J, a decidable equality on H and a family f indexed by J of actual factors on Fin n plus H, finite equivalences produce a Network n card(H) card(J). Visible names stay fixed. Hidden names and factor indices are renamed bijectively. Every Table is retained without alteration.

**Theorem 1.15 (Marginals are unchanged by finite numbering).**

$$\forall n \in \mathrm{Nat},\; \forall H \in \mathrm{Type},\; \forall J \in \mathrm{Type},\; [\operatorname{Fintype}\left(H\right)] [\operatorname{DecidableEq}\left(H\right)] [\operatorname{Fintype}\left(J\right)] \forall f \in (J) \to \operatorname{Factor}\left(\operatorname{Fin}\left(n\right) + H\right),\; \forall a \in (\operatorname{Fin}\left(n\right)) \to \mathrm{Bool},\; \operatorname{marginal}\left(\operatorname{numberedNetwork}\left(f\right), a\right) = \sum_{h \in (H) \to \mathrm{Bool}} \prod_{j \in J} \operatorname{value}\left(\operatorname{f}\left(j\right), \operatorname{combined}\left(a, h\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.numbered_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n, finite types H and J, a decidable equality on H, every factor family f on Fin n plus H and every visible assignment a, the canonical numbered Network marginal equals the sum over all h from H to Bool of the product over all j in J of the actual factor values in combined(a,h), the assignment Sum.elim a h. Empty types and empty products are included.

**Theorem 1.16 (Every rational law, including arbitrary zeros).**

$$\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (\forall P \in ((\operatorname{Fin}\left(n\right)) \to \mathrm{Bool}) \to \mathrm{Rat},\; ((\forall a \in (\operatorname{Fin}\left(n\right)) \to \mathrm{Bool},\; 0 \le \operatorname{P}\left(a\right)) \land (\sum_{a \in (\operatorname{Fin}\left(n\right)) \to \mathrm{Bool}} \operatorname{P}\left(a\right) = 1)) \Rightarrow (\exists m \in \mathrm{Nat},\; \exists k \in \mathrm{Nat},\; \exists net \in \operatorname{Network}\left(n, m, k\right),\; (0 < \operatorname{partition}\left(net\right)) \land (\forall a \in (\operatorname{Fin}\left(n\right)) \to \mathrm{Bool},\; \operatorname{law}\left(net, a\right) = \operatorname{P}\left(a\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be any natural number at least one. Let P be any rational function on the entire n-dimensional Boolean cube with nonnegative entries summing to one. There exist finite natural m and k and a Network n m k whose partition function is positive and whose normalized marginal equals P at every visible assignment. Arbitrary zero entries are included. No bound on the finite network size is asserted.

For each visible word s, build a NOR expression testing equality with s. A positive target bit uses the visible input; a negative target bit uses NOR of that input with itself. Conjunction is NOR of the two NOR-computed negations. A fold joins all n literals, seeded by the first literal; duplicating that literal preserves the indicator and requires no constant. The finite union of the expressions' gate subterms gives hidden wires. A shared subexpression denotes one actual wire. Structural induction proves that gate equations determine every hidden gate wire uniquely for each visible assignment.

The NOR factor is the indicator of the existing null-deleted relation N divided by four. Its four allowed triples are 100, 010, 110 and 001, so every gate factor is a legal W0 table. A fresh hidden wire o has the table indicator of A divided by five on scope (o,o,o). This internally forces o to zero. It supplies no external constant.

For each s, use the full table U with entries one at 000, 100, 010 and 001, entry P(s) at 110, and zero outside A. Its positive table sum is four plus P(s), including when P(s) is zero. Divide by that sum and attach it to (e_s,e_s,o), where e_s is the actual wire computing the equality indicator. Thus the apparent unary weight is implemented by an allowed ordered ternary factor.

Exactly one indicator is true at a, namely the one indexed by a. The unique gate-consistent hidden assignment therefore has weight C times P(a), where C is one fifth times one fourth for each gate times the product over s of one divided by the quantity four plus P(s). Every factor of C is positive rational. Every other hidden assignment violates the pin or a gate and contributes zero. The hidden marginal is exactly C times P(a); its total is C because P sums to one. Final normalization gives P exactly, with no limit. Finite equivalences number the hidden and factor sets without changing any sums or products.

This is an elementary constructive consequence of the five-mode relation and NOR computation. It concerns globally normalized potentials, not a supplied causal sampling kernel or an efficiency bound. The existing unweighted primitive-positive support theorem alone does not specify the rational masses.

## References

- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.Factor`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.Network`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.Table`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.Triple`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.law`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.marginal`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.numberedNetwork`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.numbered_marginal`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.partition`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.pinRaw`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.pinTable`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.result`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.unaryRaw`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.unaryTable`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.value`
- Truth anchor: `D5/S3/Combinatorics/ConstraintRelations/RationalZeroRealization.weight`
- Dependency: [D5/S3/Combinatorics/ConstraintRelations/BooleanNullBoundary](BooleanNullBoundary.md)
