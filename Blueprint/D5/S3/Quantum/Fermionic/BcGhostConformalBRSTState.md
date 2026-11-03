# Original bc conformal state and cubic-current zero mode

## Abstract

Conformal and cubic-current states of the original occupation ghost fields.

These are the classical algebraic bc ghost formulas in the original finite-occupation Fock representation, with b vacuum cut at minus one and c cut at two. The conventions follow Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. The proofs use the existing original all-state Y and signed integer iterate; no abstract replacement state-field map or transported charge is introduced.

**Definition 1.1 (The explicit conformal state).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.Omega`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.Omega` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Omega is minus twice ket{0,3} plus ket{1,2}, equivalently minus twice b(-2)c(0)vacuum minus b(-3)c(1)vacuum. The sorted-occupation signs and original mode shifts are retained.

**Definition 1.2 (The explicit raw odd cubic-current state).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.Jg`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.Jg` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Jg is ket{0,1,3}, literally b(-2)c(1)c(0)vacuum. There is no improvement term.

**Theorem 1.3 (Every integer conformal mode is the original Virasoro mode).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.conformal_modes`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.conformal_modes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer m, the (m+1)-st mode of Y(Omega) equals the original BcGhostVirasoro.L(m). The two negative-residue normal products are reindexed on their actual statewise finite integer half-lines. Their coefficients combine to the literal weight m+q in the original normal-ordered bilinear sum.

**Theorem 1.4 (Actual odd parity of the cubic state).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.current_odd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.current_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Parity sends the sorted three-occupation state Jg to minus Jg. This supplies the odd sign in the zero-residue identity and is consumed in the current comparison and signed derivation.

**Theorem 1.5 (The current zero mode is the entire original cubic charge).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.current_zero_mode`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.current_zero_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero mode Y(Jg)[[0]] equals the complete original locally finite sum over integer pairs (p,q), with coefficient one half times (p-q) and the original normal ordering of c(p)c(q)b(-p-q). Its anticommutators on all b and c modes follow from actual generator contractions and the zero-residue iterate. The difference from Qg anticommutes with the generators; composing with parity gives an ordinary commutant, to which scalar_commutant legitimately applies. Vacuum vanishing removes the scalar, and parity involution removes the composition.

**Theorem 1.6 (Signed derivation on every actual homogeneous-state field mode).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.Qg_signed_derivation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.Qg_signed_derivation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Fock state a, every natural parity exponent p with parity(a)=(-1)^p a, and every integer n, Qg Y(a)[[n]] minus (-1)^p Y(a)[[n]] Qg equals Y(Qg a)[[n]]. This is an operator equality on the full original finite-occupation carrier. The signed integer iterate at residue zero collapses to its i=0 terms; the actual current equality and odd parity identify the operator with Qg. No ambient square-zero, rank-26 or matter-plus-ghost premise is used.

The pure ghost charge is anomalous: no nilpotence is asserted. These results do not establish a total coupled BRST system, BRST cohomology, a no-ghost theorem, Monster moonshine, string dynamics or AdS/CFT. Native verification, independent review and official admission are distinct statuses.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.Jg`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.Omega`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.Qg_signed_derivation`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.conformal_modes`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.current_odd`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostConformalBRSTState.current_zero_mode`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostBRST](BcGhostBRST.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostStateFieldIterate](BcGhostStateFieldIterate.md)
