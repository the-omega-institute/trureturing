# The signed occupation form and the cubic ghost charge

## Abstract

Hermitian symmetry of the original cubic ghost charge

The carrier is the complex vector space of finitely supported countable occupations. The form Hg is the original signed coefficient pairing, conjugate linear in its first argument and linear in its second; its vacuum functional is minus the coefficient of the occupation {1,3,5}. The b and c modes, their vacuum cuts and the normally ordered cubic are unchanged. The classical bc BRST conventions are described in Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. No new physical construction is asserted.

**Definition 1.1 (cubicDefect).**

$$\forall p \in Int,\; \forall q \in Int,\; \operatorname{cubicDefect}\left(p, q\right) = \operatorname{ite}\left(-1 \le p + q \land p + q \le 1, \operatorname{ite}\left(p = 0, 1, 0\right) - \operatorname{ite}\left(q = 0, 1, 0\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostBRSTHermitian.cubicDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reversing the actual three-factor word and reflecting its modes crosses the normal-order boundary only when minus one is at most p plus q and p plus q is at most one. In that strip the two mixed CAR contractions give delta(p,0) minus delta(q,0).

**Theorem 1.2 (Hg cubic).**

$$\forall p \in Int,\; \forall q \in Int,\; \forall x \in Fock,\; \forall y \in Fock,\; \operatorname{Hg}\left(\operatorname{cubic}\left(p, q, x\right), y\right) = -\operatorname{Hg}\left(x, \operatorname{cubic}\left(-p, -q, y\right)\right) + \operatorname{cubicDefect}\left(p, q\right) \cdot \operatorname{Hg}\left(x, \operatorname{c}\left(0, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostBRSTHermitian.Hg_cubic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the all-integer b and c adjoint identities in reverse word order. Away from the middle strip, exchanging the two c factors supplies the minus sign. In the strip, retain both mixed CAR contractions before simplifying their coefficients. This identity includes zero modes and both strip endpoints.

**Definition 1.3 (cubicTermDefect).**

$$\forall pq \in \operatorname{Prod}\left(Int, Int\right),\; \operatorname{cubicTermDefect}\left(pq\right) = \operatorname{ite}\left(pq = \operatorname{Prod}.\operatorname{mk}\left(0, 1\right), -\operatorname{div}\left(1, 2\right), 0\right) + \operatorname{ite}\left(pq = \operatorname{Prod}.\operatorname{mk}\left(1, 0\right), -\operatorname{div}\left(1, 2\right), 0\right) + \operatorname{ite}\left(pq = \operatorname{Prod}.\operatorname{mk}\left(0, -1\right), \operatorname{div}\left(1, 2\right), 0\right) + \operatorname{ite}\left(pq = \operatorname{Prod}.\operatorname{mk}\left(-1, 0\right), \operatorname{div}\left(1, 2\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostBRSTHermitian.cubicTermDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiplying by the original real coefficient (p minus q) divided by two leaves exactly four nonzero defects. The pairs (0,1) and (1,0) carry minus one half; (0,minus one) and (minus one,0) carry plus one half.

**Theorem 1.4 (Hg cubicTerm).**

$$\forall p \in Int,\; \forall q \in Int,\; \forall x \in Fock,\; \forall y \in Fock,\; \operatorname{Hg}\left(\operatorname{cubicTerm}\left(\operatorname{Prod}.\operatorname{mk}\left(p, q\right), x\right), y\right) = \operatorname{Hg}\left(x, \operatorname{cubicTerm}\left(\operatorname{Prod}.\operatorname{mk}\left(-p, -q\right), y\right)\right) + \operatorname{cubicTermDefect}\left(\operatorname{Prod}.\operatorname{mk}\left(p, q\right)\right) \cdot \operatorname{Hg}\left(x, \operatorname{c}\left(0, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostBRSTHermitian.Hg_cubicTerm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugating the real coefficient leaves it fixed, while simultaneous mode negation reverses it. Together with the cubic transposition sign this yields the reflected weighted term plus its four boundary defects.

**Theorem 1.5 (Hg Qg).**

$$\forall x \in Fock,\; \forall y \in Fock,\; \operatorname{Hg}\left(\operatorname{Qg}\left(x\right), y\right) = \operatorname{Hg}\left(x, \operatorname{Qg}\left(y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostBRSTHermitian.Hg_Qg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the given two states, take the union of their actual finite action supports and the four defect pairs, then adjoin its reflected image. The resulting finite set captures both original statewise sums and is closed under reflection. Finite sesquilinearity and reindexing transpose the sum; the four boundary coefficients add to zero. No finite support of the operator family or common external mode cutoff is assumed.

This proves Hermitian symmetry of the original ghost cubic charge on the algebraic signed form. It supplies the ghost adjoint component for a total BRST construction. Total-charge Hermitian integration, nilpotence, cohomology, a no-ghost theorem, Monster moonshine, vertex operator algebra and conformal field theory structures, anomaly and fusion results, string dynamics and AdS/CFT are separate obligations.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostBRSTHermitian.Hg_Qg`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostBRSTHermitian.Hg_cubic`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostBRSTHermitian.Hg_cubicTerm`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostBRSTHermitian.cubicDefect`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostBRSTHermitian.cubicTermDefect`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostCubic](BcGhostCubic.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostHermitian](BcGhostHermitian.md)
