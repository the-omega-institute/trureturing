# Observer Innovation Equation

## Abstract

A strict Gram spectral-floor drop identifies the unique innovation zero.

**Theorem 1.1 (The new Gram floor is the unique innovation zero).**

$$\forall K \in \operatorname{Type}\left(\right), V \in \operatorname{Type}\left(\right), iota \in \operatorname{Type}\left(\right), feature \in \operatorname{Sum}\left(iota, \operatorname{Unit}\left(\right)\right) \to V, alphaOld \in \operatorname{Real}\left(\right), alphaNew \in \operatorname{Real}\left(\right),\; let oldGram = \operatorname{gram}\left(K, \operatorname{compose}\left(feature, \operatorname{inl}\left(\right)\right)\right); let fullGram = \operatorname{gram}\left(K, feature\right); let coupling = \operatorname{matrix}\left(\operatorname{lambda}\left(i, \operatorname{lambda}\left(u, \operatorname{inner}\left(K, feature\left(\operatorname{inl}\left(i\right)\right), feature\left(\operatorname{inr}\left(\operatorname{unit}\left(\right)\right)\right)\right)\right)\right)\right); let innovation = \operatorname{lambda}\left(a, \operatorname{inner}\left(K, feature\left(\operatorname{inr}\left(\operatorname{unit}\left(\right)\right)\right), feature\left(\operatorname{inr}\left(\operatorname{unit}\left(\right)\right)\right)\right) - \operatorname{complex}\left(K, a\right) - \operatorname{entry}\left(\operatorname{multiply}\left(\operatorname{conjTranspose}\left(coupling\right), \operatorname{inverse}\left(oldGram - \operatorname{scalarMatrix}\left(K, iota, a\right)\right), coupling\right), \operatorname{unit}\left(\right), \operatorname{unit}\left(\right)\right)\right); \left(\left(\left(\left(\left(\left(\left(\left(\operatorname{RCLike}\left(K\right) \land \operatorname{NormedAddCommGroup}\left(V\right)\right) \land \operatorname{InnerProductSpace}\left(K, V\right)\right) \land \operatorname{Fintype}\left(iota\right)\right) \land \operatorname{DecidableEq}\left(iota\right)\right) \land \left(\forall a \in \operatorname{Real}\left(\right),\; \operatorname{PosDef}\left(oldGram - \operatorname{scalarMatrix}\left(K, iota, a\right)\right) \Leftrightarrow a < alphaOld\right)\right) \land \left(\forall a \in \operatorname{Real}\left(\right),\; \operatorname{PosSemidef}\left(fullGram - \operatorname{scalarMatrix}\left(K, \operatorname{Sum}\left(iota, \operatorname{Unit}\left(\right)\right), a\right)\right) \Leftrightarrow a \le alphaNew\right)\right) \land \left(\forall a \in \operatorname{Real}\left(\right),\; \operatorname{PosDef}\left(fullGram - \operatorname{scalarMatrix}\left(K, \operatorname{Sum}\left(iota, \operatorname{Unit}\left(\right)\right), a\right)\right) \Leftrightarrow a < alphaNew\right)\right) \land alphaNew < alphaOld\right) \Rightarrow \left(innovation\left(alphaNew\right) = 0 \land \left(\forall a \in \operatorname{Real}\left(\right),\; \left(a < alphaOld \land innovation\left(a\right) = 0\right) \Rightarrow a = alphaNew\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/ObserverInnovationEquation.observer_innovation_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The old and extended matrices are constructed from one indexed feature family by the canonical Gram operation. The three displayed floor equivalences are the positive-definite and positive-semidefinite threshold characterizations of their least eigenvalues.

Pinned Mathlib supplies the canonical Gram matrix, the Schur positivity equivalence, and the block determinant factorization. At the new floor the extended determinant vanishes while the old block remains invertible, forcing the innovation to vanish; the same factorization and the floor thresholds prove uniqueness below the old floor.

Repository and pinned-library searches found related Schur-energy and block-positivity declarations, but no exact innovation-root theorem on the source-constructed real-or-complex Gram carrier.

## References

- Truth anchor: `D5/S3/Observer/BlockStructure/ObserverInnovationEquation.observer_innovation_equation`
