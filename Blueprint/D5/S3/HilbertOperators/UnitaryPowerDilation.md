# Common unitary dilation of all natural powers

## Abstract

Every contraction on a complete complex Hilbert space admits a unitary dilation in which every natural power of the contraction is the compression of the corresponding power of that same unitary operator.

**Theorem 1.1 (Arbitrary complex Hilbert-space power dilation).**

$$\forall (u: Universe), \forall (E: \operatorname{Type}(u)), [\operatorname{NormedAddCommGroup}(E)] [\operatorname{InnerProductSpace}(C, E)] [\operatorname{CompleteSpace}(E)] \forall (T: \operatorname{CLM}(C, E, E)), \operatorname{Norm}(T) \le 1 \implies \exists (H: \operatorname{Type}(u)), \exists (normedH: \operatorname{NormedAddCommGroup}(H)), \exists (innerH: \operatorname{InnerProductSpace}(C, H)), \exists (completeH: \operatorname{CompleteSpace}(H)), \exists (V: \operatorname{CLM}(C, E, H)), \exists (U: \operatorname{CLM}(C, H, H)), (\forall (x: E), \forall (y: E), \operatorname{Inner}(\operatorname{V}(x), \operatorname{V}(y)) = \operatorname{Inner}(x, y)) \land \operatorname{Unitary}(U) \land (\forall (n: N), \forall (x: E), \operatorname{Apply}(\operatorname{Adjoint}(V), \operatorname{Apply}(U^{n}, \operatorname{V}(x))) = \operatorname{Apply}(T^{n}, x))$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/UnitaryPowerDilation.exists_unitary_power_dilation` (`✓ std3`). ∎

*Citation.* Ezzeri Esa (2026). *Halmos and common-all-powers unitary dilation on arbitrary complex Hilbert spaces*. URL: <https://github.com/LeanPool/lean-pool/blob/89f2facbb6478492222a9b43047e9c837bc65be6/LeanPool/OperatorTheory/Operator/Dilation/Schaeffer.lean>.

*Commentary.*

Fix any universe u and any E in Type u with a normed additive commutative group structure, a complex inner product and completeness. Let T be a continuous complex-linear endomorphism of E with operator norm at most one. C denotes the complex numbers, N the natural numbers, and CLM(C,E,H) the continuous complex-linear maps from E to H. Norm, Inner and Adjoint denote the operator norm, complex inner product and Hilbert-space adjoint, respectively.

There exist H in the SAME Type u, its normed additive group, complex inner product and completeness structures, and continuous complex-linear maps V from E to H and U from H to H. The map V preserves the inner product of every pair x,y in E. U belongs to the unitary elements of the star algebra of bounded operators on H. For these SAME H, structures, V and U, every natural n and every x in E satisfy adjoint(V)((U^n)(V(x))) = (T^n)(x). The witnesses are chosen before n and x; there is one dilation for all natural powers, including n = 0.

The Hilbert space used in the construction is the square-summable family over the integers of pairs E plus E equipped with the Hilbert direct-sum norm: H = lp(fun i : Z => WithLp 2 (E times E)) 2. V inserts x into the first coordinate at site zero and puts zero in every other coordinate. Its adjoint extracts the first coordinate at site zero. No dimension, separability, basis or nontriviality assumption is used, so zero spaces are included.

First construct a Halmos unitary J on E plus E whose first coordinate on (x,0) is T(x). For the self-adjoint off-diagonal operator a(x,y) = (T(y),adjoint(T)(x)), the contraction bound allows continuous functional calculus to form the unitary a + I times sqrt(1-a^2). Its product with the coordinate flip has the required compression. The grading (x,y) maps to (x,-y) commutes with 1-a^2 and its square root; applying this relation to (0,x) makes the square root's first coordinate zero.

Apply this same J at every integer site and then shift only the second, environment coordinate one site to the right, leaving the system coordinates at their sites. The pointwise interaction and the routing map are linear isometry equivalences, hence their composition U is unitary. Square summability and equality of norms follow from the sum of the two coordinate norm squares and reindexing the integer sum.

For the orbit U^n(V(x)), prove one joint invariant by induction on n: the first coordinate at site zero is T^n(x), the second coordinate at site zero is zero, and every negative site is zero. At the successor step the zero second coordinate allows the local compression rule for J to advance the system to T^(n+1)(x). The site minus one is zero and supplies a zero environment input to site zero. The negative sites remain zero because both a negative site and its predecessor are zero. Thus both auxiliary parts of the invariant are needed to propagate the first part. Applying adjoint(V) extracts that first part and yields the compression identity for every n.

This is the classical unitary power-dilation existence theorem, using the cited formal source's repeated-interaction construction. The source construction uses the complex scalar I; an arbitrary RCLike scalar extension is outside this statement. No minimality, uniqueness, effective construction, finite environment or finite-dimensional witness is asserted. The larger Hilbert space may be infinite dimensional even when E is finite dimensional.

## References

- Truth anchor: `D5/S3/HilbertOperators/UnitaryPowerDilation.exists_unitary_power_dilation`
