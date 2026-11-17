# Native scalar-Gram existence in the first region

## Abstract

Original width-three factors realize every positive scalar column Gram in the first rectangular dimension region.

For arbitrary natural dimensions a,b,c,d with 2b ≤ 3a and 3c ≤ 2d, and every positive real scalar lambda, explicit original three-factor carriers have a tensor sum whose column Gram is lambda times the identity. The construction includes odd right dimensions, dependent factors, and all zero dimensions.

**Theorem 1.1 (Original scalar-Gram witness).**

$$\forall a \in Nat,\; \forall b \in Nat,\; \forall c \in Nat,\; \forall d \in Nat,\; (2 \cdot b \le 3 \cdot a) \Rightarrow ((3 \cdot c \le 2 \cdot d) \Rightarrow (\forall lambda \in Real,\; (0 < lambda) \Rightarrow (\exists M \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), Complex\right),\; \exists N \in \operatorname{Fin}\left(3\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(c\right), Complex\right),\; \operatorname{conjTranspose}\left(\sum_{r:\operatorname{Fin}\left(3\right)} \operatorname{kronecker}\left(M\left(r\right), N\left(r\right)\right)\right) \cdot \sum_{r:\operatorname{Fin}\left(3\right)} \operatorname{kronecker}\left(M\left(r\right), N\left(r\right)\right) = \operatorname{smul}\left(\operatorname{ofReal}\left(lambda\right), (1: \operatorname{Matrix}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(c\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(b\right), \operatorname{Fin}\left(c\right)\right), Complex\right))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeScalarGram.native_scalar_gram_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witnesses keep the native factorization F = Σᵣ M(r) ⊗ N(r), with M(r) an a-by-b complex matrix and N(r) a d-by-c complex matrix. The conclusion is FᴴF = lambda • I on Fin b × Fin c, where lambda is coerced from Real to Complex.

The left family is the canonical NativeSaturation.leftSlices supplier. For the right family, split the c input columns at c/2. The first residual block routes to right coordinates c+k, and the second routes to c+(k-c/2); their left coordinates are respectively even and odd residual slots. The first j<a branch uses the diagonal route (j,k).

The arithmetic hypotheses give 2(b-a) ≤ a and c+(c-c/2) ≤ d. Thus every route is well typed. The three branches are disjoint and recover both input coordinates, so the route is injective. Entrywise expansion identifies the tensor sum with SequentialRegisterCircuit.coordinateMatrix, whose column Gram is the identity. Multiplying the left family by the positive scalar sqrt(lambda) changes that identity Gram to lambda times the identity.

No premise a<b, parity premise on c, exact minimal d, factor independence, or universal necessity theorem is used. The statement is a sufficiency result for the two displayed dimension inequalities and does not assert a full all-dimension existence classification.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeScalarGram.native_scalar_gram_exists`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeSaturation](NativeSaturation.md)
