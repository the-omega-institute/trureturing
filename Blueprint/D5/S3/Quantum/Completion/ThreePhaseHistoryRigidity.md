# Three-Phase History Rigidity

## Abstract

All ordered finite histories supply an energy-growth estimate; raw comparison balance yields marker readouts.

**Definition 1.1 (Phase words retain order and multiplicity).**

$$(\operatorname{PhaseWords}\left(0\right) = \operatorname{Unit}\left(\right) \land (\forall n: \mathbb{N}, \operatorname{PhaseWords}\left(n+1\right) = \operatorname{PhaseWords}\left(n\right) \times \operatorname{ZMod}\left(3\right)))$$

*Formalization.* `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.PhaseWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The phase words have cardinality 3^n for every natural n. Distinct words remain distinct indices even when their original magma labels coincide.

**Definition 1.2 (Actual original left-bracketed histories).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, u: M, ((\forall w: \operatorname{PhaseWords}\left(0\right), \operatorname{orderedHistory}\left(U, u, 0, w\right) = 1) \land (\forall n: \mathbb{N}, (\forall w: \operatorname{PhaseWords}\left(n\right), (\forall k: \operatorname{ZMod}\left(3\right), \operatorname{orderedHistory}\left(U, u, n+1, \operatorname{pair}\left(w, k\right)\right) = \operatorname{orderedHistory}\left(U, u, n, w\right) \cdot \operatorname{iterate}\left(U, \operatorname{val}\left(k\right), u\right)))))$$

*Formalization.* `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.orderedHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original type M is any MulOneClass. Each child applies its given binary operation once on the right of the existing history. No associativity or commutativity is used, and no depth cap or deduplication is introduced.

**Theorem 1.3 (Energy growth over every ordered history depth).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, u: M, N: \operatorname{Set}\left(M\right), E: M \to \mathbb{R}, d: \mathbb{R}, (1 \in N \land (\forall x: M, x \in N \Rightarrow (\forall k: \operatorname{ZMod}\left(3\right), x \cdot \operatorname{iterate}\left(U, \operatorname{val}\left(k\right), u\right) \in N)) \land (\forall x: M, x \in N \Rightarrow 3 \cdot (\operatorname{E}\left(x\right) + d) \le \sum_{k: \operatorname{ZMod}\left(3\right)} \operatorname{E}\left(x \cdot \operatorname{iterate}\left(U, \operatorname{val}\left(k\right), u\right)\right))) \Rightarrow (\forall n: \mathbb{N}, 3^{n} \cdot (\operatorname{E}\left(1\right) + n \cdot d) \le \sum_{w: \operatorname{PhaseWords}\left(n\right)} \operatorname{E}\left(\operatorname{orderedHistory}\left(U, u, n, w\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.history_energy_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original unital magma, a set containing the unit and closed under each of the three original children, a real energy E and increment d, assume 3(E(x)+d)<=sum_k E(x*U^k(u)) on that set. Induction gives the displayed lower bound for every natural depth n. The sum is over every phase word with its original order and multiplicity, even when labels coincide. The bounded-increment proof in RawAnchoredFourierQuotient compares this same sum with 3^n*C, divides by the positive 3^n and uses the Archimedean property. Its Fourier mode consumer is then applied to both actual ordered pairings in RawAnchoredRadicalDescent.

The cardinality identity phaseWords_card and membership induction history_mem are used in the upper-bound comparison by bounded_energy_increment_nonpos in RawAnchoredFourierQuotient. The cardinality is exactly 3^n, and membership follows for every original ordered history from unit membership and closure under every original phase child.

**Definition 1.4 (The original raw balance hypotheses).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, \operatorname{RawBalance}\left(U, c\right) = ((\operatorname{U}\left(1\right) = 1) \land ((((\forall a: M, (\forall b: M, 0 \le \operatorname{c}\left(a, b\right)))) \land ((((\forall a: M, \operatorname{c}\left(a, a\right) = 0)) \land ((\forall a: M, (\forall b: M, (\forall u: M, (\forall v: M, \operatorname{c}\left((a \cdot u), (b \cdot v)\right) + \operatorname{c}\left((a \cdot \operatorname{U}\left(u\right)), (b \cdot \operatorname{U}\left(v\right))\right) + \operatorname{c}\left((a \cdot \operatorname{U}\left(\operatorname{U}\left(u\right)\right)), (b \cdot \operatorname{U}\left(\operatorname{U}\left(v\right)\right))\right) = 3 \cdot \operatorname{c}\left(a, b\right) + 3 \cdot \operatorname{c}\left(u, v\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.RawBalance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M has only a binary operation and a two-sided unit. U is an arbitrary self-map fixing the unit, and c is finite and real-valued. No associativity, commutativity, cancellation, inverse, marker homomorphism, surjectivity, periodicity, symmetry or positive-semidefinite form is assumed.

**Theorem 1.5 (The comparison has derived marker invariance).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, (\operatorname{RawBalance}\left(U, c\right) \Rightarrow (((\forall u: M, (\forall v: M, \operatorname{c}\left(\operatorname{U}\left(u\right), \operatorname{U}\left(v\right)\right) = \operatorname{c}\left(u, v\right)))) \land ((((\forall a: M, (\forall b: M, (\forall u: M, (\forall v: M, \operatorname{c}\left((a \cdot \operatorname{U}\left(\operatorname{U}\left(\operatorname{U}\left(u\right)\right)\right)), (b \cdot \operatorname{U}\left(\operatorname{U}\left(\operatorname{U}\left(v\right)\right)\right))\right) = \operatorname{c}\left((a \cdot u), (b \cdot v)\right)))))) \land ((\forall u: M, (\forall z: M, ((\operatorname{c}\left(\operatorname{U}\left(\operatorname{U}\left(\operatorname{U}\left(u\right)\right)\right), z\right) = \operatorname{c}\left(u, z\right)) \land (\operatorname{c}\left(z, \operatorname{U}\left(\operatorname{U}\left(\operatorname{U}\left(u\right)\right)\right)\right) = \operatorname{c}\left(z, u\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.raw_marker_readouts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For s(n)=c(U^n u,U^n v), the raw law at the two units gives s(n+1)+s(n+2)=2s(n). Apply ThreeWayBalance.nonneg_recurrence_constant directly, exchanging the summands. Subtracting consecutive original balance identities gives contextual invariance. Specializing either contextual input to the unit gives every row and column equality. These equalities supply the ordered anchored-kernel descent below. Only the readings have period three; the original marker need not have period three.

The raw law and marker readings feed the ordered Fourier quotient. The ordered energy-growth estimate supplies its bounded-increment and bounded Fourier mode theorems, and the original-domain consumer derives both uniform pairing bounds before applying that theorem twice. The actual original operation is never assumed associative or commutative.

## References

- Truth anchor: `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.PhaseWords`
- Truth anchor: `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.RawBalance`
- Truth anchor: `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.history_energy_growth`
- Truth anchor: `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.orderedHistory`
- Truth anchor: `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.raw_marker_readouts`
- Dependency: [D5/S3/QuadraticForms/ThreeWayBalance](../../QuadraticForms/ThreeWayBalance.md)
