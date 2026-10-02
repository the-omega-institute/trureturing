# A mixed-sign Gaussian refutes Galindo–Rowell Conjecture 10.6

## Abstract

A mixed-sign Gaussian in dimension fifteen refutes the Pauli-direction rigidity conjecture for cyclic unitary Yang–Baxter operators.

**Definition 1.1 (The cyclic clock matrix).**

$$\forall w: \mathbb{C}, \forall d: \mathbb{N}, \operatorname{clockZ}\left(w, d\right) = \operatorname{diagonal}\left(\lambda j: \operatorname{ZMod}\left(d\right) \mapsto w^{\operatorname{val}\left(j\right)}\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.clockZ` (`✓ std3`).

*Citation.* C. Galindo; E. C. Rowell (2026). *Unitary Yang–Baxter Operators: Towards a Classification*. URL: <https://arxiv.org/abs/2608.16865>.

*Commentary.*

The source fixes the clock by (arXiv:2608.16865v1, §10.2): "Ze_j=w^je_j". The diagonal entry at j is w raised to the canonical ZMod representative.

**Definition 1.2 (The Pauli-direction operator).**

$$\forall d: \mathbb{N}, [\operatorname{NeZero}\left(d\right)], \forall w: \mathbb{C}, \forall alpha: \operatorname{Units}\left(\operatorname{ZMod}\left(d\right)\right), \operatorname{P}\left(w, alpha\right) = \operatorname{kronecker}\left(\operatorname{shiftMatrix}\left(d\right), \operatorname{clockZ}\left(w, d\right)^{\operatorname{val}\left(\operatorname{val}\left(alpha\right)\right)}\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.P` (`✓ std3`).

*Citation.* C. Galindo; E. C. Rowell (2026). *Unitary Yang–Baxter Operators: Towards a Classification*. URL: <https://arxiv.org/abs/2608.16865>.

*Commentary.*

The source writes (arXiv:2608.16865v1, §10.2): "P_α=X⊗Z^α". The Lean definition is the Kronecker product of the shift and the α-th clock power. The inner val is Units.val and the outer val is ZMod.val.

**Definition 1.3 (The cyclic coefficient operator).**

$$\forall d: \mathbb{N}, [\operatorname{NeZero}\left(d\right)], \forall w: \mathbb{C}, \forall alpha: \operatorname{Units}\left(\operatorname{ZMod}\left(d\right)\right), \forall a: \operatorname{ZMod}\left(d\right) \to \mathbb{C}, \operatorname{R}\left(w, alpha, a\right) = \operatorname{sum}\left(t\in\operatorname{ZMod}\left(d\right), a t \cdot \operatorname{P}\left(w, alpha\right)^{\operatorname{val}\left(t\right)}\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.R` (`✓ std3`).

*Citation.* C. Galindo; E. C. Rowell (2026). *Unitary Yang–Baxter Operators: Towards a Classification*. URL: <https://arxiv.org/abs/2608.16865>.

*Commentary.*

The source writes (arXiv:2608.16865v1, §10.2): "R(a)=∑_{t=0}^{d−1}a_tP^t". The Lean sum ranges over ZMod d and uses the literal P power and coefficient scalar multiplication.

**Definition 1.4 (The braid Yang–Baxter equation).**

$$\forall d: \mathbb{N}, [\operatorname{NeZero}\left(d\right)], \forall r: \operatorname{Matrix}\left((\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)), (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)), \mathbb{C}\right), \operatorname{BraidYBE}\left(r\right) = ((\operatorname{mul}\left(\operatorname{mul}\left(\operatorname{reindex}\left(\operatorname{prodAssoc}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right)\right), \operatorname{prodAssoc}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right)\right), \operatorname{kronecker}\left(r, 1\right)\right), \operatorname{kronecker}\left(1, r\right)\right), \operatorname{reindex}\left(\operatorname{prodAssoc}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right)\right), \operatorname{prodAssoc}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right)\right), \operatorname{kronecker}\left(r, 1\right)\right)\right)) = (\operatorname{mul}\left(\operatorname{mul}\left(\operatorname{kronecker}\left(1, r\right), \operatorname{reindex}\left(\operatorname{prodAssoc}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right)\right), \operatorname{prodAssoc}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right)\right), \operatorname{kronecker}\left(r, 1\right)\right)\right), \operatorname{kronecker}\left(1, r\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.BraidYBE` (`✓ std3`).

*Citation.* C. Galindo; E. C. Rowell (2026). *Unitary Yang–Baxter Operators: Towards a Classification*. URL: <https://arxiv.org/abs/2608.16865>.

*Commentary.*

Section 2 of arXiv:2608.16865v1 displays "(R⊗I)(I⊗R)(R⊗I) = (I⊗R)(R⊗I)(I⊗R)". The symbols prodAssoc, reindex and kronecker denote Equiv.prodAssoc, Matrix.reindex and Matrix.kronecker. Both identity matrices have type Matrix (ZMod d) (ZMod d) Complex. The reindexed first placement and the second placement act on ZMod d × (ZMod d × ZMod d).

**Definition 1.5 (Projective unitarity).**

$$\forall d: \mathbb{N}, [\operatorname{NeZero}\left(d\right)], \forall r: \operatorname{Matrix}\left((\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)), (\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)), \mathbb{C}\right), \operatorname{ProjectivelyUnitary}\left(r\right) = (\exists c: \mathbb{C}, c \neq 0 \land c \cdot r \in \operatorname{unitaryGroup}\left((\operatorname{ZMod}\left(d\right) \times \operatorname{ZMod}\left(d\right)), \mathbb{C}\right))$$

*Formalization.* `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.ProjectivelyUnitary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Projectively unitary means that some nonzero complex scalar multiple of the operator is a member of the Mathlib Matrix.unitaryGroup object. Its matrix index type is ZMod d × ZMod d and its scalar type is Complex.

**Definition 1.6 (Galindo–Rowell Conjecture 10.6).**

$$\forall d: \mathbb{N}, (2 \leq d) \Rightarrow \neg (4 \mid d) \Rightarrow \forall w: \mathbb{C}, \operatorname{IsPrimitiveRoot}\left(w, d\right) \Rightarrow \forall alpha: \operatorname{Units}\left(\operatorname{ZMod}\left(d\right)\right), \forall a: \operatorname{ZMod}\left(d\right) \to \mathbb{C}, \operatorname{a}\left(0\right) = 1 \Rightarrow (\forall t: \operatorname{ZMod}\left(d\right), \operatorname{norm}\left(\operatorname{a}\left(t\right)\right) = 1) \Rightarrow \operatorname{BraidYBE}\left(\operatorname{R}\left(w, alpha, a\right)\right) \Rightarrow \operatorname{ProjectivelyUnitary}\left(\operatorname{R}\left(w, alpha, a\right)\right) \Rightarrow \exists eps: \operatorname{ZMod}\left(d\right), (eps = 1 \lor eps = -1) \land (\forall s: \operatorname{ZMod}\left(d\right), \forall t: \operatorname{ZMod}\left(d\right), \operatorname{a}\left(s + t\right) = \operatorname{a}\left(s\right) \times \operatorname{a}\left(t\right) \times w^{\operatorname{val}\left(eps \times \operatorname{val}\left(alpha\right) \times s \times t\right)})$$

*Formalization.* `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.claim` (`✓ std3`).

*Citation.* C. Galindo; E. C. Rowell (2026). *Unitary Yang–Baxter Operators: Towards a Classification*. URL: <https://arxiv.org/abs/2608.16865>.

*Commentary.*

Galindo–Rowell, Conjecture 10.6, arXiv:2608.16865v1, p. 43, §10.2.7: "Let d≥2 with 4∤d, let α∈(Z/dZ)^×, and put P_α=X⊗Z^α, τ_α(s,t)=w^{αst} (s,t∈Z/dZ). Suppose that a=(1,a_1,…,a_{d−1})∈T_d^{coef} and that R_α(a)=∑_{t∈Z/dZ}a_tP_α^t satisfies the Yang--Baxter equation and is projectively unitary. Then a belongs to one of the two signed Gaussian torsors for τ_α: there exists ε∈{+1,−1} such that a_{s+t}=a_sa_tτ_α(s,t)^ε (s,t∈Z/dZ)." The encoding uses ZMod d, primitive roots in Complex, unit alpha, a 0 = 1, and the unit-modulus phase-torus condition for every index.

**Theorem 1.7 (Conjecture 10.6 is refuted).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At d=15, α=1, and a_t=w^(2t²) for a primitive fifteenth root, the coefficient-to-braid identity and a translation of the finite character sum prove the braid equation. Character orthogonality gives R R†=15·I, hence projective unitarity. At s=t=1 the two signs would require w^8=w^5 or w^8=w^3, both impossible for a primitive fifteenth root.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.BraidYBE`
- Truth anchor: `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.P`
- Truth anchor: `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.ProjectivelyUnitary`
- Truth anchor: `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.R`
- Truth anchor: `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.clockZ`
- Truth anchor: `D5/S3/Quantum/Algebra/CyclicYangBaxterPauliRigidityRefutation.result`
- Dependency: [D5/S3/Observer/WindowRegister](../../Observer/WindowRegister.md)
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacementAdjoint](WeylDisplacementAdjoint.md)
