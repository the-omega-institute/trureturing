# The half-normal form of the original ghost charge

## Abstract

The original cubic ghost charge has an all-state half-normal c/L expression.

This document describes the two public definitions and three public theorems of BcGhostChargeNormalForm. The carrier is the original CountableOccupationFock.Fock, the complex vector space of finitely supported functions on finite subsets of the natural numbers. Every state is an arbitrary finite complex linear combination of occupation kets, not just a vacuum, a chosen basis state or a truncated sector.

The operators are the existing BcGhostFock.b and c, BcGhostVirasoro.L and BcGhostBRST.Qg, with the original vacuum cuts b at minus one and c at two. L uses the original statewise finite Virasoro sum and Qg the original statewise finite ordered-pair cubic sum. The identity compares those operators directly; it neither introduces a replacement charge nor recreates a historical lattice namespace.

This is the classical algebraic bc ghost construction of weights two and minus one. See Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. Attribution retained from the mathematical source also includes Scott Carnahan's vertexAlg, Apache-2.0, revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, for the related field and normal-product constructions recorded in BcGhostStateField. The source credits the retained LatticeBcGhostBrstCharge.N/A source mechanism for its outer ordering and half coefficient, with retained source SHA256 c86ba73030f046ed86c83c5e4103a9970910a7b6c83eb1f76860c284b8ccd3a8; this is provenance, not a dependency imported by this module. No novelty of the ghost formulas is claimed.

**Definition 1.1 (orderedTerm).**

$$\forall n \in Int,\; (\operatorname{orderedTerm}\left(n\right):\operatorname{Module}.\operatorname{End}\left(Complex, Fock\right)) = \operatorname{ite}\left(-1 \le n, \operatorname{c}\left(-n\right) \cdot \operatorname{L}\left(n\right), \operatorname{L}\left(n\right) \cdot \operatorname{c}\left(-n\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostChargeNormalForm.orderedTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every integer n this is an actual complex-linear endomorphism of the original Fock space. Multiplication of endomorphisms means composition, with the right factor acting first. The endpoint n = -1 is in the first branch: its value on v is c 1 (L (-1) v). There is no half coefficient in this term; that coefficient belongs outside the complete sum.

**Theorem 1.2 (orderedTerm support).**

$$\forall v \in Fock,\; \exists A \in Int,\; 0 \le A \land \operatorname{Function}.\operatorname{support}\left((n\mapsto\operatorname{orderedTerm}\left(n, v\right))\right) \subseteq \operatorname{Set}.\operatorname{Icc}\left(-A, 2 \cdot A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostChargeNormalForm.orderedTerm_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete assertion is that each input v has some nonnegative integer A bounding the support between -A and 2*A. In the proof, a basis occupation S uses A = S.sup id + 3. For n < -A the rightmost c (-n) kills ket S, and for n > 2*A the rightmost L n kills ket S. Finite linear combinations are handled by linear induction, using the maximum of the bounds for two summands. The bound depends on v; this asserts neither a global cutoff nor finite support of the endomorphism family itself.

**Theorem 1.3 (orderedTerm finite).**

$$\forall v \in Fock,\; \operatorname{Function}.\operatorname{HasFiniteSupport}\left((n\mapsto\operatorname{orderedTerm}\left(n, v\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostChargeNormalForm.orderedTerm_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original state, the function n mapped to orderedTerm n v has finite support. The proof obtains this from containment in the finite integer interval of orderedTerm_support. This statewise fact is available before sum additivity and scalar compatibility are used; there is no analytic convergence or limiting prescription.

**Definition 1.4 (halfNormalCharge).**

$$\forall v \in Fock,\; \operatorname{halfNormalCharge}\left(v\right) = \operatorname{smul}\left((\operatorname{div}\left(1, 2\right):Complex), \sum_{n\in Int}^{fin}\operatorname{orderedTerm}\left(n, v\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostChargeNormalForm.halfNormalCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition has type Module.End Complex Fock, and this equation specifies its value on every v. Additivity uses orderedTerm_finite on both inputs before distributing the finite-support sum. Complex linearity likewise uses the actual finite support before moving a scalar through the sum. The scalar is exactly (1/2 : Complex), applied once to the entire sum.

Joint support is needed in addition to finite support of the outer ordered family. The proof expands each L n using the original summand n q. Its private expandedTerm n q is c (-n) composed with summand n q in the n >= -1 branch, and summand n q composed with c (-n) otherwise. The four ordering cases in the private CAR calculation give expandedTerm n q = (2 : Complex) smul cubicTerm (-n,q). In the crossed cuts the mixed CAR contraction is zero, so this calculation introduces no boundary correction. The existing cubicTerm_finite v then gives finite support of the actual pair-indexed expansion (n,q) on every v, by the first-coordinate sign involution. These are statewise supports of the original operators.

Only after that joint support is established does the proof flatten the iterated sum over n and q into a sum over integer pairs. The expansion through c (-n) also uses summand_finite n v in its first branch; in the other branch the Virasoro sum is evaluated on the actual state c (-n) v. The sole pair reindexing is the bijection (n,q) mapped to (-n,q), identifying the pair sum with twice the original cubic charge. The exterior half cancels that factor two. The finite-support hypotheses justify this algebraic sum exchange without an analytic convergence assumption.

**Theorem 1.5 (Qg eq halfNormalCharge).**

$$\forall v \in Fock,\; \operatorname{Qg}\left(v\right) = \operatorname{smul}\left((\operatorname{div}\left(1, 2\right):Complex), \sum_{n\in Int}^{fin}\operatorname{ite}\left(-1 \le n, \operatorname{c}\left(-n, \operatorname{L}\left(n, v\right)\right), \operatorname{L}\left(n, \operatorname{c}\left(-n, v\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostChargeNormalForm.Qg_eq_halfNormalCharge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal endpoint is Qg v = (1/2 : Complex) smul finsum (n : Int), if -1 <= n then c (-n) (L n v) else L n (c (-n) v). It quantifies over every original Fock state with no additional premise. In particular it assumes no lattice, rank, Gram form, criticality, nilpotence or cohomology condition. The proof first identifies Qg v with halfNormalCharge v and then unfolds the actual orderedTerm; the public theorem itself states the displayed sum, not just the name of the comparison operator.

The exact scope is this algebraic ghost-sector operator identity and its statewise finite-support infrastructure. It supplies a connected prerequisite for further original-operator arguments. It does not establish the matter-tensor BRST construction, nilpotence, cohomology, a no-ghost theorem, a Borcherds identity, the Moonshine/VOA/CFT and anomaly/fusion programme, full string theory or AdS/CFT.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostChargeNormalForm.Qg_eq_halfNormalCharge`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostChargeNormalForm.halfNormalCharge`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostChargeNormalForm.orderedTerm`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostChargeNormalForm.orderedTerm_finite`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostChargeNormalForm.orderedTerm_support`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostBRST](BcGhostBRST.md)
