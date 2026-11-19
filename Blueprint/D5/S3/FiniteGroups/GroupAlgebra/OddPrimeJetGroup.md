# Coherent lifts of actual labels

## Abstract

The full original odd-prime jet group

Let p be every odd prime, including three, F=ZMod p, and K a finite F-algebra field in an arbitrary independent universe. Suppose |K|=p^n with n at least one. For A:Fin(n-1) to K put q(x)=sum_i A_i(x^(p^(i+1))-x), R=sum_i A_i, and V=Polynomial.degreeLT K p. All linear operators and equivalences below are only F-linear. The original action is rho_x=exp(xD+q(x)D^(p-1)); its labels are the original additive group Multiplicative K.

G is the subgroup of pairs (P,phi) in GL_F(V) times Aut(Multiplicative K) satisfying P rho_x=rho_(phi(x)) P for every original label x. Its label projection has image S. The finite original-pair classification forces each label of S uniquely to have phi(x)=c sigma(x), with c a unit, sigma an F-algebra automorphism, and A_i=c^(-w_i) sigma(A_i), w_i=p^(i+1)-p+1. Thus S is the actual label stabilizer, rather than a group of independently chosen coefficient data.

**Theorem 1.1 (Every original operator intertwines).**

$$\forall p \in \mathbb{N},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] [\operatorname{Fact}\left(2 < p\right)] \forall K \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] [\operatorname{Algebra}\left(\operatorname{ZMod}\left(p\right), K\right)] \forall n \in \mathbb{N},\; \left(1 \le n \land \operatorname{card}\left(K\right) = p^{n}\right) \Rightarrow \left(\forall A \in \operatorname{Function}\left(\operatorname{Fin}\left(n - 1\right), K\right),\; \forall g \in \operatorname{S}\left(p, K, n, A\right),\; \forall x \in \operatorname{Multiplicative}\left(K\right),\; \forall v \in \operatorname{V}\left(p, K\right),\; \operatorname{T}\left(g, \operatorname{rho}\left(A, x, v\right)\right) = \operatorname{rho}\left(A, \operatorname{label}\left(g, x\right), \operatorname{T}\left(g, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.coherentLift_intertwines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write H=shear(-R), where shear(b)=I+b topShear. The degree lift B_g has coefficient j equal to c^(-j) sigma(v_j). The lift is T_g=H^(-1) B_g H. Since B_(gh)=B_g B_h, these lifts form a genuine group homomorphism. The same fixed H appears at every composition, so its adjacent inverse cancels exactly. The normalized coefficient function is q(x)+Rx=sum_i A_i x^(p^(i+1)); its weighted transformation proves intertwining of infinitesimal operators, and the existing finite-exponential bridge proves intertwining for every original representation operator.

**Theorem 1.2 (A coherent group section).**

$$\forall p \in \mathbb{N},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] [\operatorname{Fact}\left(2 < p\right)] \forall K \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] [\operatorname{Algebra}\left(\operatorname{ZMod}\left(p\right), K\right)] \forall n \in \mathbb{N},\; \left(1 \le n \land \operatorname{card}\left(K\right) = p^{n}\right) \Rightarrow \left(\forall A \in \operatorname{Function}\left(\operatorname{Fin}\left(n - 1\right), K\right),\; \operatorname{MonoidHom}\left(\operatorname{S}\left(p, K, n, A\right), \operatorname{G}\left(p, K, n, A\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.sectionHom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The homomorphism sends g to the actual pair (coherentLift(g),g). Its multiplication proof is the exact operator equality T_(gh)=T_g composed with T_h, with the ordinary product convention of original label automorphisms.

**Theorem 1.3 (The section preserves actual labels).**

$$\forall p \in \mathbb{N},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] [\operatorname{Fact}\left(2 < p\right)] \forall K \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] [\operatorname{Algebra}\left(\operatorname{ZMod}\left(p\right), K\right)] \forall n \in \mathbb{N},\; \left(1 \le n \land \operatorname{card}\left(K\right) = p^{n}\right) \Rightarrow \left(\forall A \in \operatorname{Function}\left(\operatorname{Fin}\left(n - 1\right), K\right),\; \forall g \in \operatorname{S}\left(p, K, n, A\right),\; \operatorname{project}\left(\operatorname{section}\left(A, g\right)\right) = g\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.project_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projection of the constructed original pair is the given original label itself.

**Theorem 1.4 (Unique actual factorization).**

$$\forall p \in \mathbb{N},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] [\operatorname{Fact}\left(2 < p\right)] \forall K \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] [\operatorname{Algebra}\left(\operatorname{ZMod}\left(p\right), K\right)] \forall n \in \mathbb{N},\; \left(1 \le n \land \operatorname{card}\left(K\right) = p^{n}\right) \Rightarrow \left(\forall A \in \operatorname{Function}\left(\operatorname{Fin}\left(n - 1\right), K\right),\; \forall z \in \operatorname{G}\left(p, K, n, A\right),\; \exists x \in \operatorname{product}\left(\operatorname{C}\left(A\right), \operatorname{S}\left(p, K, n, A\right)\right),\; \operatorname{val}\left(\operatorname{fst}\left(x\right)\right) \cdot \operatorname{section}\left(A, \operatorname{snd}\left(x\right)\right) = z \land \left(\forall y \in \operatorname{product}\left(\operatorname{C}\left(A\right), \operatorname{S}\left(p, K, n, A\right)\right),\; \operatorname{val}\left(\operatorname{fst}\left(y\right)\right) \cdot \operatorname{section}\left(A, \operatorname{snd}\left(y\right)\right) = z \Rightarrow y = x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.unique_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

C is the kernel of the actual label projection, embedded as original pairs (X,id). It is exactly the group of invertible operators in the full actual commutant. For each z the unique factors are s=project(z) and k=z section(s)^(-1). Multiplication uses ordinary operator composition. The action on C is actual conjugation by section(s).

**Theorem 1.5 (The original group is a semidirect product).**

$$\forall p \in \mathbb{N},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] [\operatorname{Fact}\left(2 < p\right)] \forall K \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] [\operatorname{Algebra}\left(\operatorname{ZMod}\left(p\right), K\right)] \forall n \in \mathbb{N},\; \left(1 \le n \land \operatorname{card}\left(K\right) = p^{n}\right) \Rightarrow \left(\forall A \in \operatorname{Function}\left(\operatorname{Fin}\left(n - 1\right), K\right),\; \operatorname{MulEquiv}\left(\operatorname{G}\left(p, K, n, A\right), \operatorname{SemidirectProduct}\left(\operatorname{C}\left(A\right), \operatorname{S}\left(p, K, n, A\right), \operatorname{conjugation}\left(A\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.semidirectEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib SemidirectProduct.lift maps (k,s) to k section(s). The unique-factorization proof makes it bijective. This splits the full original group over its entire actual label stabilizer. It does not assert that the separate scalar/Galois projection of that stabilizer splits: such a further projection can remain nonsplit.

**Theorem 1.6 (Cardinality of the actual factors).**

$$\forall p \in \mathbb{N},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] [\operatorname{Fact}\left(2 < p\right)] \forall K \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] [\operatorname{Algebra}\left(\operatorname{ZMod}\left(p\right), K\right)] \forall n \in \mathbb{N},\; \left(1 \le n \land \operatorname{card}\left(K\right) = p^{n}\right) \Rightarrow \left(\forall A \in \operatorname{Function}\left(\operatorname{Fin}\left(n - 1\right), K\right),\; \operatorname{card}\left(\operatorname{G}\left(p, K, n, A\right)\right) = \operatorname{card}\left(\operatorname{C}\left(A\right)\right) \cdot \operatorname{card}\left(\operatorname{S}\left(p, K, n, A\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.full_card_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native multiplicative equivalence yields a bijection with the product of the complete commutant-unit kernel and the actual label image.

**Theorem 1.7 (The unrestricted kernel count).**

$$\forall p \in \mathbb{N},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] [\operatorname{Fact}\left(2 < p\right)] \forall K \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] [\operatorname{Algebra}\left(\operatorname{ZMod}\left(p\right), K\right)] \forall n \in \mathbb{N},\; \left(1 \le n \land \operatorname{card}\left(K\right) = p^{n}\right) \Rightarrow \left(\forall A \in \operatorname{Function}\left(\operatorname{Fin}\left(n - 1\right), K\right),\; \operatorname{card}\left(\operatorname{C}\left(A\right)\right) = \left(p^{n} - 1\right) \cdot p^{n \cdot \left(p - 2\right) + n \cdot n}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.commutant_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing unique Toeplitz coordinates and unit criterion supply one nonzero leading scalar, p-2 arbitrary field scalars, and an entirely unrestricted T in End_F(K). The latter has F-dimension n squared. The degree coordinates reserve c_0=0 and use c_(p-1) for the leading shift scalar; no coefficient is counted twice.

**Theorem 1.8 (The full group count).**

$$\forall p \in \mathbb{N},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] [\operatorname{Fact}\left(2 < p\right)] \forall K \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] [\operatorname{Algebra}\left(\operatorname{ZMod}\left(p\right), K\right)] \forall n \in \mathbb{N},\; \left(1 \le n \land \operatorname{card}\left(K\right) = p^{n}\right) \Rightarrow \left(\forall A \in \operatorname{Function}\left(\operatorname{Fin}\left(n - 1\right), K\right),\; \operatorname{card}\left(\operatorname{G}\left(p, K, n, A\right)\right) = \left(p^{n} - 1\right) \cdot p^{n \cdot \left(p - 2\right) + n \cdot n} \cdot \operatorname{card}\left(\operatorname{S}\left(p, K, n, A\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.full_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The label-stabilizer factor multiplies the commutant-unit count. The commutant alone never supplies the full group order. The source reuses the native original-pair classification, the actual commutant theorem, and Mathlib semidirect products and finite-dimensional cardinality. No literature-priority claim is made.

**Theorem 1.9 (The native weighted stabilizer).**

$$\forall p \in \mathbb{N},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] [\operatorname{Fact}\left(2 < p\right)] \forall K \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] [\operatorname{Algebra}\left(\operatorname{ZMod}\left(p\right), K\right)] \forall n \in \mathbb{N},\; \left(1 \le n \land \operatorname{card}\left(K\right) = p^{n}\right) \Rightarrow \left(\forall A \in \operatorname{Function}\left(\operatorname{Fin}\left(n - 1\right), K\right),\; \forall L \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(L\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{Algebra}\left(\operatorname{ZMod}\left(p\right), L\right)] \forall e \in \operatorname{AlgEquiv}\left(\operatorname{ZMod}\left(p\right), K, L\right),\; \operatorname{MulEquiv}\left(\operatorname{weightedStabilizer}\left(A, e\right), \operatorname{S}\left(p, K, n, A\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.weightedStabilizerEquiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual F-algebra equivalence e from K to a small finite field L, the existing native WeightedSemilinear stabilizer of the tuple e(A) is multiplicatively equivalent to S. The map sends (c,sigma) to the original label x maps to e^(-1)(c) e^(-1)(sigma(e(x))). Evaluation at one determines c and cancellation then determines sigma, proving faithfulness. The inverse weighted coefficient criterion proves exactly the image condition. Taking L=Shrink K gives this result for every original universe of K without narrowing that universe.

**Theorem 1.10 (The unrestricted conjugation law).**

$$\forall p \in \mathbb{N},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] [\operatorname{Fact}\left(2 < p\right)] \forall K \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] [\operatorname{Algebra}\left(\operatorname{ZMod}\left(p\right), K\right)] \forall n \in \mathbb{N},\; \left(1 \le n \land \operatorname{card}\left(K\right) = p^{n}\right) \Rightarrow \left(\forall A \in \operatorname{Function}\left(\operatorname{Fin}\left(n - 1\right), K\right),\; \forall g \in \operatorname{S}\left(p, K, n, A\right),\; \forall a \in \operatorname{Function}\left(\operatorname{Fin}\left(p - 1\right), K\right),\; \forall T \in \operatorname{LinearMap}\left(\operatorname{ZMod}\left(p\right), K, K\right),\; \forall v \in \operatorname{V}\left(p, K\right),\; \operatorname{degreeLift}\left(g, \operatorname{toeplitz}\left(a, T, v\right)\right) = \operatorname{toeplitz}\left(\operatorname{shiftTransform}\left(g, a\right), \operatorname{transformedTop}\left(g, T\right), \operatorname{degreeLift}\left(g, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.normalized_conjugation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here shiftTransform(g,a)_r means c^r sigma(a_r), and transformedTop(g,T)=sigma composed with T composed with sigma^(-1) composed with m(c^(p-1)). The scalar acts on the input, before sigma^(-1) and T. This is proved as equality on actual polynomial operators for every F-linear T, without replacing T by a scalar. Applying the degree lift to D^(p-1)v and reading its constant coefficient supplies the required input relation.

**Theorem 1.11 (The fixed shear changes only the top coefficient).**

$$\forall p \in \mathbb{N},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] [\operatorname{Fact}\left(2 < p\right)] \forall K \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] [\operatorname{Algebra}\left(\operatorname{ZMod}\left(p\right), K\right)] \forall s \in K,\; \forall a \in \operatorname{Function}\left(\operatorname{Fin}\left(p - 1\right), K\right),\; \forall T \in \operatorname{LinearMap}\left(\operatorname{ZMod}\left(p\right), K, K\right),\; \forall v \in \operatorname{V}\left(p, K\right),\; \operatorname{shear}\left(-s, \operatorname{toeplitz}\left(a, T, v\right)\right) = \operatorname{toeplitz}\left(a, T + \operatorname{fieldScalar}\left(s \cdot \operatorname{eval}\left(a, 1\right)\right), \operatorname{shear}\left(-s, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.shear_conjugation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Thus conjugation by H_s=shear(-s) leaves every lower shift coefficient unchanged and sends T to T+m(s a_1). The proof uses that topShear annihilates positive derivative inputs, D topShear=D^(p-1), and D squared topShear=0. It uses K-linearity only on the degree-one image of topShear, where the unrestricted top map vanishes; it never assumes that the entire commutant operator is K-linear.

**Theorem 1.12 (Every original normalized coefficient map).**

$$\forall p \in \mathbb{N},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] [\operatorname{Fact}\left(2 < p\right)] \forall K \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] [\operatorname{Algebra}\left(\operatorname{ZMod}\left(p\right), K\right)] \forall n \in \mathbb{N},\; \left(1 \le n \land \operatorname{card}\left(K\right) = p^{n}\right) \Rightarrow \left(\forall q \in \operatorname{LinearMap}\left(\operatorname{ZMod}\left(p\right), K, K\right),\; \operatorname{eval}\left(q, 1\right) = 0 \Rightarrow \left(\exists alpha \in \operatorname{MonoidHom}\left(\operatorname{labelGroup}\left(q\right), \operatorname{MulAut}\left(\operatorname{kernel}\left(\operatorname{project}\left(q\right)\right)\right)\right),\; \operatorname{Nonempty}\left(\operatorname{MulEquiv}\left(\operatorname{originalGroup}\left(q\right), \operatorname{SemidirectProduct}\left(\operatorname{kernel}\left(\operatorname{project}\left(q\right)\right), \operatorname{labelGroup}\left(q\right), alpha\right)\right)\right) \land \left(\operatorname{card}\left(\operatorname{kernel}\left(\operatorname{project}\left(q\right)\right)\right) = \left(p^{n} - 1\right) \cdot p^{n \cdot \left(p - 2\right) + n \cdot n} \land \operatorname{card}\left(\operatorname{originalGroup}\left(q\right)\right) = \left(p^{n} - 1\right) \cdot p^{n \cdot \left(p - 2\right) + n \cdot n} \cdot \operatorname{card}\left(\operatorname{labelGroup}\left(q\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.normalized_group_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary F-linear q with q(1)=0, the existing coefficient bijection supplies A with Q(A)=q. Substitution gives an action on the actual kernel, a multiplicative equivalence of the entire original pair group with its semidirect product, and both exact cardinalities. Thus the coefficient presentation imposes no restriction on the original normalized q.

**Theorem 1.13 (The prime-field full count).**

$$\forall p \in \mathbb{N},\; [\operatorname{Fact}\left(\operatorname{Prime}\left(p\right)\right)] [\operatorname{Fact}\left(2 < p\right)] \forall K \in \operatorname{Type}\left(\right),\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(K\right)] [\operatorname{Algebra}\left(\operatorname{ZMod}\left(p\right), K\right)] \operatorname{card}\left(K\right) = p \Rightarrow \operatorname{card}\left(\operatorname{originalGroup}\left(0\right)\right) = \left(p - 1\right)^{2} \cdot p^{p - 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.prime_field_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When |K|=p, the normalized coefficient tuple is empty and q=0. The weighted stabilizer is the whole native scalar-semilinear group; the Galois group has order one and the scalar group has order p-1. Therefore the full count is (p-1) squared times p^(p-1), whereas the kernel alone has order (p-1) times p^(p-1). The scalar factor is retained even for n=1.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.coherentLift_intertwines`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.commutant_cardinality`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.full_card_factorization`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.full_cardinality`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.normalized_conjugation`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.normalized_group_structure`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.prime_field_cardinality`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.project_section`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.sectionHom`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.semidirectEquiv`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.shear_conjugation`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.unique_factorization`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGroup.weightedStabilizerEquiv`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/FiniteJetOrbits](FiniteJetOrbits.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetCommutant](OddPrimeJetCommutant.md)
