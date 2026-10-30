# Characteristic-two opposite intersections

## Abstract

Characteristic-two opposite intersections obey an arbitrary-dimensional relation-deficiency bound.

**Theorem 1.1 (Three opposite intersections are controlled by twice the relation deficiency).**

$$\forall (F: Type), [Field\left(F\right)] [CharP\left(F, 2\right)] \forall (V: Type), [AddCommGroup\left(V\right)] [Module\left(F, V\right)] [FiniteDimensional\left(F, V\right)] \forall (A: Submodule\left(F, V\right)), \forall (B: Submodule\left(F, V\right)), \forall (C: Submodule\left(F, V\right)), \forall (Z: Submodule\left(F, V\right)), \operatorname{finrank}\left(F, \operatorname{sup}\left(\operatorname{sup}\left(\operatorname{inf}\left(\operatorname{sup}\left(A, B\right), \operatorname{sup}\left(C, Z\right)\right), \operatorname{inf}\left(\operatorname{sup}\left(A, C\right), \operatorname{sup}\left(B, Z\right)\right)\right), \operatorname{inf}\left(\operatorname{sup}\left(A, Z\right), \operatorname{sup}\left(B, C\right)\right)\right)\right) \le \operatorname{mul}\left(2, (\operatorname{finrank}\left(F, A\right)+\operatorname{finrank}\left(F, B\right)+\operatorname{finrank}\left(F, C\right)+\operatorname{finrank}\left(F, Z\right)-\operatorname{finrank}\left(F, \operatorname{sup}\left(\operatorname{sup}\left(\operatorname{sup}\left(A, B\right), C\right), Z\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CharacteristicTwoNonFano.finrank_opposite_sum_le_two_deficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna Blasiak; Robert Kleinberg; Eyal Lubetzky (2011). *Lexicographic products and the power of non-linear network coding*. URL: <https://arxiv.org/abs/1108.2489v1>.

*Commentary.*

For four arbitrary finite-dimensional submodules over characteristic two, the third opposite intersection is contained in the sum of the first two by the identity (a+b)+(a+c)=b+c. Grassmann's dimension formula bounds each of the first two intersections by the total relation deficiency. The proof allows overlapping, unequal, and zero subspaces. The cited Blasiak–Kleinberg–Lubetzky source supplies the earlier direct-sum projection-cancellation mechanism and codimension robustification; it is attribution, not a proof of this unrestricted declaration. The seven-subspace Phi elimination and the six-party physical bridge remain separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/CharacteristicTwoNonFano.finrank_opposite_sum_le_two_deficiency`
