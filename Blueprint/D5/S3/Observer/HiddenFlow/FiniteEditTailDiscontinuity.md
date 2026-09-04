# Finite-Edit Tail Discontinuity

## Abstract

A nonconstant Boolean tail observable on a product is continuous nowhere.

**Theorem 1.1 (A nonconstant finite-edit tail observable is nowhere continuous).**

$$\begin{gathered}\forall X: \mathbb{N}_{>0} \to \operatorname{Type},\\{}[\forall n: \mathbb{N}_{>0}, \operatorname{TopologicalSpace}\left(X(n)\right)],\\{}F: \prod_{n\in \mathbb{N}_{>0}} X(n) \to Bool,\\{}(\forall x, y: \prod_{n\in \mathbb{N}_{>0}} X(n), \operatorname{Finite}\left(\left\{x(n) \ne y(n) \mid n \in \mathbb{N}_{>0}\right\}\right) \Rightarrow F(x) = F(y)) \land (\exists a, b: \prod_{n\in \mathbb{N}_{>0}} X(n), F(a) \ne F(b)) \Rightarrow\\{}\forall x: \prod_{n\in \mathbb{N}_{>0}} X(n), \neg \operatorname{ContinuousAt}\left(F, x\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/FiniteEditTailDiscontinuity.nonconstant_finite_edit_invariant_nowhere_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the coordinate spaces be indexed by the positive natural numbers and give their dependent product the product topology. A Boolean observable is assumed unchanged whenever two inputs differ at only finitely many coordinates.

Nonconstancy supplies two inputs with different readings. At any chosen point, continuity into discrete Bool would make its reading constant on a neighborhood. Mathlib's finite piecewise-neighborhood lemma places a finite edit of an input with the other reading inside that neighborhood, giving a contradiction.

Repository, pinned-Mathlib, Loogle, and LeanSearch queries found no exact finite-edit discontinuity theorem. The proof reuses exists_finset_piecewise_mem_of_mem_nhds for the product-topology step.

The statement records the named topological theorem. Later discussion of particular analytic models and possible stronger topologies is interpretive guidance rather than an additional theorem clause.

## References

- Truth anchor: `D5/S3/Observer/HiddenFlow/FiniteEditTailDiscontinuity.nonconstant_finite_edit_invariant_nowhere_continuous`
