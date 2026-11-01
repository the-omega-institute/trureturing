# The actual normally ordered cubic ghost charge

## Abstract

Statewise locally finite cubic ghost charge

The formulas are the classical bc ghost BRST construction, with vacuum cuts b at minus one and c at two. See Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. No novelty of these formulas is claimed. The formal carrier is the original complex finitely supported occupation space.

**Definition 1.1 (cubic).**

$$\forall p \in Int,\; \forall q \in Int,\; \operatorname{cubic}\left(p, q\right) = \operatorname{ite}\left(\operatorname{LE}.\operatorname{le}\left(p, 1\right), \operatorname{ite}\left(\operatorname{LE}.\operatorname{le}\left(q, 1\right), \operatorname{c}\left(p\right) \cdot \operatorname{c}\left(q\right) \cdot \operatorname{b}\left(-p - q\right), \operatorname{ite}\left(\operatorname{LE}.\operatorname{le}\left(-p - q, -2\right), -\left(\operatorname{c}\left(p\right) \cdot \operatorname{b}\left(-p - q\right) \cdot \operatorname{c}\left(q\right)\right), \operatorname{c}\left(p\right) \cdot \operatorname{c}\left(q\right) \cdot \operatorname{b}\left(-p - q\right)\right)\right), \operatorname{ite}\left(\operatorname{LE}.\operatorname{le}\left(q, 1\right), \operatorname{ite}\left(\operatorname{LE}.\operatorname{le}\left(-p - q, -2\right), \operatorname{c}\left(q\right) \cdot \operatorname{b}\left(-p - q\right) \cdot \operatorname{c}\left(p\right), -\left(\operatorname{c}\left(q\right) \cdot \operatorname{c}\left(p\right) \cdot \operatorname{b}\left(-p - q\right)\right)\right), \operatorname{ite}\left(\operatorname{LE}.\operatorname{le}\left(-p - q, -2\right), \operatorname{b}\left(-p - q\right) \cdot \operatorname{c}\left(p\right) \cdot \operatorname{c}\left(q\right), \operatorname{c}\left(p\right) \cdot \operatorname{c}\left(q\right) \cdot \operatorname{b}\left(-p - q\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostCubic.cubic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Creators precede annihilators before summation. When b is a creator its cyclic move through both c factors has positive sign. Anticommuting the c factors gives exactly the stable fermionic order; no contraction is added by definition.

**Definition 1.2 (cubicTerm).**

$$\forall pq \in \operatorname{Prod}\left(Int, Int\right),\; \operatorname{cubicTerm}\left(pq\right) = \operatorname{smul}\left(\operatorname{div}\left(1, 2\right) \cdot \operatorname{Int}.\operatorname{cast}\left(\operatorname{Prod}.\operatorname{fst}\left(pq\right) - \operatorname{Prod}.\operatorname{snd}\left(pq\right)\right), \operatorname{cubic}\left(\operatorname{Prod}.\operatorname{fst}\left(pq\right), \operatorname{Prod}.\operatorname{snd}\left(pq\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostCubic.cubicTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full ordered pair sum carries the classical factor one half.

**Theorem 1.3 (cubic finite).**

$$\forall v \in Fock,\; \operatorname{Function}.\operatorname{HasFiniteSupport}\left((pq\mapsto\operatorname{cubic}\left(\operatorname{Prod}.\operatorname{fst}\left(pq\right), \operatorname{Prod}.\operatorname{snd}\left(pq\right), v\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostCubic.cubic_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a basis occupation S, put A equal to its largest site plus three. A live cubic has p and q at most A and p plus q at least minus A. Both indices therefore lie in the finite interval from minus twice A to A. Finite linear combinations give the assertion for every actual state.

**Theorem 1.4 (cubicTerm finite).**

$$\forall v \in Fock,\; \operatorname{Function}.\operatorname{HasFiniteSupport}\left((pq\mapsto\operatorname{cubicTerm}\left(pq, v\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostCubic.cubicTerm_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weighting cannot enlarge the pointwise support. This fact is consumed by the linear charge and every sum exchange.

**Definition 1.5 (Qg).**

$$\forall v \in Fock,\; \operatorname{Qg}\left(v\right) = \sum_{pq\in \operatorname{Prod}\left(Int, Int\right)}^{fin}\operatorname{cubicTerm}\left(pq, v\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostCubic.Qg` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is a genuine complex-linear endomorphism. Its value is defined by a statewise finite sum; the operator family itself is not declared finitely supported.

**Theorem 1.6 (cubic b).**

$$\forall p \in Int,\; \forall q \in Int,\; \forall r \in Int,\; \operatorname{cubic}\left(p, q\right) \cdot \operatorname{b}\left(r\right) + \operatorname{b}\left(r\right) \cdot \operatorname{cubic}\left(p, q\right) = \operatorname{ite}\left(q + r = 0, \operatorname{normal}\left(-p - q, p\right), 0\right) - \operatorname{ite}\left(p + r = 0, \operatorname{normal}\left(-p - q, q\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostCubic.cubic_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite CAR reduces the individual cubic to two bilinears with the Virasoro normal ordering.

**Theorem 1.7 (cubic c).**

$$\forall p \in Int,\; \forall q \in Int,\; \forall r \in Int,\; \operatorname{cubic}\left(p, q\right) \cdot \operatorname{c}\left(r\right) + \operatorname{c}\left(r\right) \cdot \operatorname{cubic}\left(p, q\right) = \operatorname{ite}\left(-p - q + r = 0, \operatorname{c}\left(p\right) \cdot \operatorname{c}\left(q\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostCubic.cubic_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only the b contraction remains. All signs are checked in the actual operator algebra.

**Theorem 1.8 (Qg vacuum).**

$$\operatorname{Qg}\left(\operatorname{vacuum}\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostCubic.Qg_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An all-creator cubic on the vacuum forces p and q both equal to one, whose repeated c factor is zero. Every other branch has an annihilator on the right. The square proof consumes this vacuum identity.

This is an algebraic ghost-sector construction. It supplies a dependency for the broader Monster, vertex algebra, conformal field theory and string programme. It does not establish the matter-tensor BRST charge, its cohomology, a no-ghost theorem, string dynamics or AdS/CFT.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCubic.Qg`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCubic.Qg_vacuum`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCubic.cubic`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCubic.cubicTerm`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCubic.cubicTerm_finite`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCubic.cubic_b`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCubic.cubic_c`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostCubic.cubic_finite`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostVirasoro](BcGhostVirasoro.md)
