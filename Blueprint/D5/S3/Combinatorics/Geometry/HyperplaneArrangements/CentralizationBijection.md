# Centralization convolution over coprime residue rings

## Abstract

A first-residue-preserving CRT bijection for integral affine arrangements.

Chen, Fu, Li and Wang, arXiv:2606.00599v1 (v1 submitted 30 May 2026), §4.2, printed p. 17, ask for a natural CRT bijection interpreting Corollary 1.2. Its indexing flats are the linear flats of the centralization. Theorem 4.6 of §4.2 instead treats Wang's convolution indexed by affine flats of the original arrangement.

**Definition 1.1 (Integral row evaluation).**

Lean statement: `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.row`

*Formalization.* `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yanru Chen; Houshan Fu; Ang Li; Suijie Wang (2026). *Convolution-type Identity for Characteristic Polynomials of Geometric Semilattices*. DOI: [10.48550/arXiv.2606.00599](https://doi.org/10.48550/arXiv.2606.00599). URL: <https://arxiv.org/abs/2606.00599v1>.

*Commentary.*

For an index type I and n coordinates, ring R, a : I → Fin n → ℤ, i in I and x : Fin n → R, row R a i x is the sum over Fin n of the product of the cast of a(i,j) to R and x(j).

**Definition 1.2 (Rational common kernel).**

Lean statement: `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.commonKernel`

*Formalization.* `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.commonKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yanru Chen; Houshan Fu; Ang Li; Suijie Wang (2026). *Convolution-type Identity for Characteristic Polynomials of Geometric Semilattices*. DOI: [10.48550/arXiv.2606.00599](https://doi.org/10.48550/arXiv.2606.00599). URL: <https://arxiv.org/abs/2606.00599v1>.

*Commentary.*

For any finite row subset S, commonKernel a S is the rational submodule of Fin n → ℚ consisting of exactly the vectors v with row ℚ a i v = 0 for every i in S.

**Definition 1.3 (Actual rational flats).**

Lean statement: `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.RationalFlat`

*Formalization.* `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.RationalFlat` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yanru Chen; Houshan Fu; Ang Li; Suijie Wang (2026). *Convolution-type Identity for Characteristic Polynomials of Geometric Semilattices*. DOI: [10.48550/arXiv.2606.00599](https://doi.org/10.48550/arXiv.2606.00599). URL: <https://arxiv.org/abs/2606.00599v1>.

*Commentary.*

RationalFlat a is the subtype of rational submodules K of Fin n → ℚ for which there exists S : Finset I with commonKernel a S = K.

**Definition 1.4 (Concrete affine complement).**

Lean statement: `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.Complement`

*Formalization.* `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.Complement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yanru Chen; Houshan Fu; Ang Li; Suijie Wang (2026). *Convolution-type Identity for Characteristic Polynomials of Geometric Semilattices*. DOI: [10.48550/arXiv.2606.00599](https://doi.org/10.48550/arXiv.2606.00599). URL: <https://arxiv.org/abs/2606.00599v1>.

*Commentary.*

Complement a b m is the subtype of vectors z : Fin n → ZMod m with row (ZMod m) a i z different from the cast of b(i) for every i in I.

**Theorem 1.5 (Exact bijection and first residue).**

$$\forall u \in \operatorname{UniverseLevel}\left(\right),\; \forall I \in \operatorname{Type}\left(u\right),\; \forall n \in \mathbb{N},\; (\operatorname{Finite}\left(I\right)) \Rightarrow (\forall a \in \operatorname{Rows}\left(I, n\right),\; \forall b \in \operatorname{Constants}\left(I\right),\; \exists D \in \mathbb{N},\; (0 < D) \land (\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; (1 < p) \Rightarrow ((1 < q) \Rightarrow ((\operatorname{Coprime}\left(p, q\right)) \Rightarrow ((\operatorname{Coprime}\left(p, D\right)) \Rightarrow ((\operatorname{Coprime}\left(q, D\right)) \Rightarrow (\exists e \in \operatorname{Equiv}\left(\operatorname{C}\left(a, b, p \cdot q\right), \operatorname{FiberSum}\left(a, b, p, q\right)\right),\; \forall z \in \operatorname{C}\left(a, b, p \cdot q\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{First}\left(e\left(z\right), j\right) = \operatorname{Cast}\left(p, q, \operatorname{Value}\left(z, j\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yanru Chen; Houshan Fu; Ang Li; Suijie Wang (2026). *Convolution-type Identity for Characteristic Polynomials of Geometric Semilattices*. DOI: [10.48550/arXiv.2606.00599](https://doi.org/10.48550/arXiv.2606.00599). URL: <https://arxiv.org/abs/2606.00599v1>.

*Commentary.*

For arbitrary universe u, the index type I has type Type u. Finite(I) is the original Finite instance, and n is the coordinate dimension. Rows(I,n) is I → Fin n → ℤ and Constants(I) is I → ℤ. The row evaluation over a ring R is the sum over Fin n of the integer coefficient cast to R times the corresponding coordinate. C(a,b,m) is Complement a b m, the subtype of vectors in (ℤ/mℤ)^n whose row evaluations differ from the cast of b(i) for every i in I.

FiberSum(a,b,p,q) is the dependent sum over RationalFlat a, the actual rational submodules of Fin n → ℚ equal to common kernels of finite row sets. For each such V let J(V) contain exactly those i whose rational row evaluation vanishes at every v in V. The first fibre is the subtype of x in (ℤ/pℤ)^n with row(a,i,x) different from b(i) for every i in J(V). The second is the subtype of y in (ℤ/qℤ)^n with row(a,i,y)=0 for every i in J(V) and row(a,i,y) different from 0 for every i outside J(V). The fibre is their product. Equiv denotes the actual equivalence of types with both inverse laws. First(e(z),j) is (e z).2.1.val j and Value(z,j) is z.val j. Cast(p,q,t) is ZMod.cast from ZMod(p*q) to ZMod p at t.

D is positive and is chosen from a and b before p and q. The proof constructs integer certificates for rational affine consistency and rational homogeneous implication of every subsystem. A rational point gives a denominator certificate, while an inconsistent direction gives an integer separating functional. The finite product of the requisite positive integers is coprime to every good modulus. The homogeneous implication also controls the exact zero rows of modular points.

Split z by CRT as (x,zq), choose a solution c(x) modulo q of the affine equations hit at x modulo p, and subtract c(x) from zq to obtain y. The exact homogeneous zero rows of y yield the rational common-kernel flat. An affine equation hit by x is hit by zq exactly when its homogeneous row vanishes at y. Inversion adds the same c(x) and applies inverse CRT. The rational flat equivalence reindexes the strata and preserves the underlying first vector. Both inverse laws and the literal first-residue equation are checked.

Integral minors compute the same ranks over ℚ and ℝ, so the rational and real flats correspond by extension of scalars and have the same row closures. Definition 2.4 identifies J(V) with the affine localization rows. A nonzero restriction to a linear flat is surjective over the field. Homogeneous implication good reduction identifies the reduced flat independently of the chosen finite generators and detects proper restrictions.

Any valid family of centers gives this construction. The checked implementation uses Classical.choose. Choosing the lexicographically least solution in coordinate order with residues 0 through q−1 gives a deterministic variant mathematically, since each solution set is finite and nonempty. The argument covers composite coprime moduli.

Taking cardinalities gives the exact complement count identity. The source's Proposition 4.4 evaluates characteristic polynomials for positive m greater than the arrangement-specific threshold qA and coprime to its period ρA. Lemma 4.5 identifies the reductions of affine subarrangements and restrictions. Use these results for A at pq, the affine localizations at p, and the centralization and its central restrictions at q, with integral coordinates on the rational flats compatible with reduction. For a real integral hyperplane arrangement, it suffices that coprime p and q each exceed the maximum of 1 and the applicable thresholds and each be coprime to the product of D, the applicable periods and the coordinate factors. This also suffices at pq. The Lean endpoint proves the complement equivalence. Characteristic-polynomial evaluation follows from the cited counting results.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.Complement`
- Truth anchor: `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.RationalFlat`
- Truth anchor: `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.commonKernel`
- Truth anchor: `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.result`
- Truth anchor: `D5/S3/Combinatorics/Geometry/HyperplaneArrangements/CentralizationBijection.row`
