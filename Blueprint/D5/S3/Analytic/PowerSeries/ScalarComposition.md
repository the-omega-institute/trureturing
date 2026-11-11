# Ordered scalar composition

## Abstract

Scalar substitution and multilinear composition agree over a topological ring algebra.

**Definition 1.1 (Realization of a scalar coefficient series).**

$$\forall K \in \operatorname{Type}\left(\right),\; \forall E \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Ring}\left(E\right)] [\operatorname{Algebra}\left(K, E\right)] [\operatorname{TopologicalSpace}\left(E\right)] [\operatorname{IsTopologicalRing}\left(E\right)] \forall P \in \operatorname{PowerSeries}\left(K\right),\; \forall n \in Nat,\; \forall v \in \operatorname{Fin}\left(n\right) \to E,\; \operatorname{toFMS}\left(E, P, n, v\right) = \operatorname{smul}\left(\operatorname{coeff}\left(n, P\right), \operatorname{prod}\left(\operatorname{ofFn}\left(v\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/PowerSeries/ScalarComposition.toFMS` (`✓ std3`).

*Citation.* Miyahara Kō (2026). *Scalar power series and formal multilinear composition*. URL: <https://github.com/Komyyy/ado/blob/acac59b08bfc356fdf5f3966ad95ad8edf7a3202/AdoArchive/Log.lean>.

*Commentary.*

For a field K and a possibly noncommutative ring E with a K-algebra structure, topology and topological-ring structure, the degree n term acts on a vector v by multiplying its entries in order and scaling by the nth coefficient. Empty products give the degree-zero term. This is FormalMultilinearSeries.ofScalars applied to the coefficient function.

**Lemma 1.2 (Evaluation on an arbitrary vector).**

$$\forall K \in \operatorname{Type}\left(\right),\; \forall E \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Ring}\left(E\right)] [\operatorname{Algebra}\left(K, E\right)] [\operatorname{TopologicalSpace}\left(E\right)] [\operatorname{IsTopologicalRing}\left(E\right)] \forall P \in \operatorname{PowerSeries}\left(K\right),\; \forall n \in Nat,\; \forall v \in \operatorname{Fin}\left(n\right) \to E,\; \operatorname{toFMS}\left(E, P, n, v\right) = \operatorname{smul}\left(\operatorname{coeff}\left(n, P\right), \operatorname{prod}\left(\operatorname{ofFn}\left(v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PowerSeries/ScalarComposition.toFMS_apply` (`✓ std3`). ∎

*Citation.* Miyahara Kō (2026). *Scalar power series and formal multilinear composition*. URL: <https://github.com/Komyyy/ado/blob/acac59b08bfc356fdf5f3966ad95ad8edf7a3202/AdoArchive/Log.lean>.

*Commentary.*

This evaluation formula includes every natural degree and every vector in Fin n to E. No commutativity of multiplication in E is required.

**Theorem 1.3 (Substitution realizes composition).**

$$\forall K \in \operatorname{Type}\left(\right),\; \forall E \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Ring}\left(E\right)] [\operatorname{Algebra}\left(K, E\right)] [\operatorname{TopologicalSpace}\left(E\right)] [\operatorname{IsTopologicalRing}\left(E\right)] \forall P \in \operatorname{PowerSeries}\left(K\right),\; \forall Q \in \operatorname{PowerSeries}\left(K\right),\; \operatorname{HasSubst}\left(P\right) \implies \operatorname{toFMS}\left(E, \operatorname{subst}\left(P, Q\right)\right) = \operatorname{comp}\left(\operatorname{toFMS}\left(E, Q\right), \operatorname{toFMS}\left(E, P\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PowerSeries/ScalarComposition.toFMS_subst` (`✓ std3`). ∎

*Citation.* Miyahara Kō (2026). *Scalar power series and formal multilinear composition*. URL: <https://github.com/Komyyy/ado/blob/acac59b08bfc356fdf5f3966ad95ad8edf7a3202/AdoArchive/Log.lean>.

*Commentary.*

The inner series P has nilpotent constant coefficient, expressed by HasSubst P. Over a field this coefficient is zero. Bare subst P Q means outer Q after inner P, matching the order of the two multilinear series on the right.

In each fixed degree, terms containing a zero-sized inner block vanish. The remaining finitely many positive block partitions correspond to compositions of that degree. Flattening these blocks preserves the order of the input vector. Scalar multiplication distributes through that ordered product by the algebra action laws, including for a noncommutative target ring.

The correspondence concerns formal series. To identify the coefficients of an analytic inverse, one must also supply an actual inverse germ, convergent expansions of the two functions, and one-dimensional uniqueness. It supplies no convergence radius or value at a specified endpoint.

## References

- Truth anchor: `D5/S3/Analytic/PowerSeries/ScalarComposition.toFMS`
- Truth anchor: `D5/S3/Analytic/PowerSeries/ScalarComposition.toFMS_apply`
- Truth anchor: `D5/S3/Analytic/PowerSeries/ScalarComposition.toFMS_subst`
