# Integer bc ghost CAR

## Abstract

All integer bc ghost modes act on the algebraic countable finite-excitation carrier with the exact mixed delta, vacuum cuts, odd parity, a one-dimensional common annihilator kernel and scalar commutant.

Fock, its signed creators and annihilators, vacuum and parity are those of CountableOccupationFock. Even sites encode the b-creator and c-annihilator pair; odd sites encode the c-creator and b-annihilator pair. Int.toNat is applied to a nonnegative expression in every active branch. CAR is transferred from the original finite Jordan–Wigner matrices through the proved occupation intertwinings and exact finite capture, then consumed by the exhaustive integer branch calculation.

**Definition 1.1 (b).**

$$\forall m \in Int,\; \operatorname{b}\left(m\right) = \operatorname{ite}\left(m \le -2, \operatorname{create}\left(2 \cdot \operatorname{Int}.\operatorname{toNat}\left(-m - 2\right)\right), \operatorname{annihilate}\left(2 \cdot \operatorname{Int}.\operatorname{toNat}\left(m + 1\right) + 1\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostFock.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The creation branch ends at m equal to minus two; the annihilation branch starts at minus one.

**Definition 1.2 (c).**

$$\forall n \in Int,\; \operatorname{c}\left(n\right) = \operatorname{ite}\left(n \le 1, \operatorname{create}\left(2 \cdot \operatorname{Int}.\operatorname{toNat}\left(1 - n\right) + 1\right), \operatorname{annihilate}\left(2 \cdot \operatorname{Int}.\operatorname{toNat}\left(n - 2\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostFock.c` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The creation branch ends at n equal to one; the annihilation branch starts at two.

**Theorem 1.3 (mode correspondence).**

$$\forall j \in Nat,\; \operatorname{b}\left(-\operatorname{Int}.\operatorname{ofNat}\left(j\right) - 2\right) = \operatorname{create}\left(2 \cdot j\right) \land \left(\operatorname{c}\left(\operatorname{Int}.\operatorname{ofNat}\left(j\right) + 2\right) = \operatorname{annihilate}\left(2 \cdot j\right) \land \left(\operatorname{c}\left(1 - \operatorname{Int}.\operatorname{ofNat}\left(j\right)\right) = \operatorname{create}\left(2 \cdot j + 1\right) \land \operatorname{b}\left(\operatorname{Int}.\operatorname{ofNat}\left(j\right) - 1\right) = \operatorname{annihilate}\left(2 \cdot j + 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostFock.mode_correspondence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

These four inverse formulas cover every natural occupation index and establish the zero-mode convention.

**Theorem 1.4 (ghost b car).**

$$\forall m \in Int,\; \forall n \in Int,\; \operatorname{b}\left(m\right) \cdot \operatorname{b}\left(n\right) + \operatorname{b}\left(n\right) \cdot \operatorname{b}\left(m\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostFock.ghost_b_car` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Same-species b modes anticommute. Cross-branch occupation indices have distinct parity.

**Theorem 1.5 (ghost c car).**

$$\forall m \in Int,\; \forall n \in Int,\; \operatorname{c}\left(m\right) \cdot \operatorname{c}\left(n\right) + \operatorname{c}\left(n\right) \cdot \operatorname{c}\left(m\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostFock.ghost_c_car` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Same-species c modes anticommute for the same exhaustive branch reason.

**Theorem 1.6 (ghost mixed car).**

$$\forall m \in Int,\; \forall n \in Int,\; \operatorname{b}\left(m\right) \cdot \operatorname{c}\left(n\right) + \operatorname{c}\left(n\right) \cdot \operatorname{b}\left(m\right) = \operatorname{ite}\left(m + n = 0, (1:\operatorname{Module}.\operatorname{End}\left(Complex, Fock\right)), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostFock.ghost_mixed_car` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only an even creator with its even annihilator, or an odd annihilator with its odd creator, contributes. In either case equality of occupation indices is equivalent to m plus n equal to zero. In particular the mixed zero-mode anticommutator is the identity.

**Theorem 1.7 (ghost vacuum).**

$$\left(\forall m \in Int,\; -1 \le m \Rightarrow \operatorname{b}\left(m, vacuum\right) = 0\right) \land \left(\left(\forall n \in Int,\; 2 \le n \Rightarrow \operatorname{c}\left(n, vacuum\right) = 0\right) \land \left(\operatorname{c}\left(1, vacuum\right) = \operatorname{ket}\left(\operatorname{Finset}.\operatorname{singleton}\left(1\right)\right) \land \left(\operatorname{c}\left(0, vacuum\right) = \operatorname{ket}\left(\operatorname{Finset}.\operatorname{singleton}\left(3\right)\right) \land \left(\operatorname{c}\left(1, vacuum\right) \ne 0 \land \operatorname{c}\left(0, vacuum\right) \ne 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostFock.ghost_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The annihilation cuts are exact. The states c one vacuum and c zero vacuum are the distinct nonzero singleton occupations one and three.

**Theorem 1.8 (ghost parity).**

$$\forall m \in Int,\; parity \cdot \operatorname{b}\left(m\right) + \operatorname{b}\left(m\right) \cdot parity = 0 \land parity \cdot \operatorname{c}\left(m\right) + \operatorname{c}\left(m\right) \cdot parity = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostFock.ghost_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both ghost families are odd for the actual occupation parity involution.

**Theorem 1.9 (ghost common annihilator kernel).**

$$\forall v \in Fock,\; \left(\left(\forall m \in Int,\; -1 \le m \Rightarrow \operatorname{b}\left(m, v\right) = 0\right) \land \left(\forall n \in Int,\; 2 \le n \Rightarrow \operatorname{c}\left(n, v\right) = 0\right)\right) \Leftrightarrow \left(\exists alpha \in Complex,\; v = \operatorname{smul}\left(alpha, vacuum\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostFock.ghost_common_annihilator_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The c annihilation branch enumerates every even source index and the b annihilation branch every odd source index. The inverse formulas in mode_correspondence reduce the two complete integer cuts to the actual common annihilator kernel. The reverse inclusion uses both cuts of ghost_vacuum.

**Theorem 1.10 (scalar commutant).**

$$\forall A \in \operatorname{Module}.\operatorname{End}\left(Complex, Fock\right),\; \left(\forall m \in Int,\; A \cdot \operatorname{b}\left(m\right) = \operatorname{b}\left(m\right) \cdot A\right) \Rightarrow \left(\left(\forall n \in Int,\; A \cdot \operatorname{c}\left(n\right) = \operatorname{c}\left(n\right) \cdot A\right) \Rightarrow \left(\exists alpha \in Complex,\; A = \operatorname{smul}\left(alpha, (1:\operatorname{Module}.\operatorname{End}\left(Complex, Fock\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostFock.scalar_commutant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary complex linear endomorphism commuting with all integer b and c, the exact vacuum cuts show that A vacuum lies in the joint ghost annihilator kernel, hence equals alpha times vacuum. The two creator branches of mode_correspondence give commutation with every actual source creator. Creator-word induction and the full countable creator_spanning theorem then prove A equals alpha times the identity on the entire carrier. No continuity, assumed irreducibility, positivity or finite-cutoff restriction is used.

This is the algebraic CAR and vacuum representation. It does not assert positive ghost unitarity, nonnegative ghost energy or uniqueness of a degree-zero vacuum. The common annihilator vacuum line and scalar commutant do not imply those spectral statements. Pointwise finite odd normal sums, primary commutators, integer degree and the evaluated minus twenty-six anomaly remain further obligations. An all-state super vertex algebra, the intended matter and graded tensor realization, the actual BRST charge, its domain and normal constant, nilpotence and cohomology, no-ghost and Monster–Lorentz identifications, fusion, sewing, CFT, string and AdS conclusions require their own proofs.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostFock.b`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostFock.c`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostFock.ghost_b_car`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostFock.ghost_c_car`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostFock.ghost_common_annihilator_kernel`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostFock.ghost_mixed_car`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostFock.ghost_parity`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostFock.ghost_vacuum`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostFock.mode_correspondence`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostFock.scalar_commutant`
- Dependency: [D5/S3/Quantum/Fermionic/CountableOccupationFock](CountableOccupationFock.md)
