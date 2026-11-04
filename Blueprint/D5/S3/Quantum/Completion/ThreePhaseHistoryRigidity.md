# Three-Phase History Rigidity

## Abstract

All ordered finite histories and character orthogonality eliminate a bounded complex Fourier increment.

**Definition 1.1 (Phase words retain order and multiplicity).**

$$\operatorname{PhaseWords}\left(0\right) = \operatorname{Unit}\left(\right), \operatorname{PhaseWords}\left(n+1\right) = \operatorname{PhaseWords}\left(n\right) \times \operatorname{ZMod}\left(3\right)$$

*Formalization.* `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.PhaseWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The phase words have cardinality 3^n for every natural n. Distinct words remain distinct indices even when their original magma labels coincide.

**Definition 1.2 (Actual original left-bracketed histories).**

$$\operatorname{orderedHistory}\left(U, u, 0, w\right) = 1, \operatorname{orderedHistory}\left(U, u, n+1, \operatorname{pair}\left(w, k\right)\right) = \operatorname{orderedHistory}\left(U, u, n, w\right) \cdot \operatorname{iterate}\left(U, \operatorname{val}\left(k\right), u\right)$$

*Formalization.* `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.orderedHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original type M is any MulOneClass. Each child applies its given binary operation once on the right of the existing history. No associativity or commutativity is used, and no depth cap or deduplication is introduced.

**Theorem 1.3 (Conditional vanishing from an assumed Fourier recursion).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, u: M, N: \operatorname{Set}\left(M\right), chi: \operatorname{AddChar}\left(\operatorname{ZMod}\left(3\right), \mathbb{C}\right), f, D: M \to \mathbb{C}, C: \mathbb{R}, (1 \in N \land (\forall x: M, x \in N \Rightarrow (\forall k: \operatorname{ZMod}\left(3\right), x \cdot \operatorname{iterate}\left(U, \operatorname{val}\left(k\right), u\right) \in N)) \land \operatorname{Injective}\left(chi\right) \land (\forall x: M, x \in N \Rightarrow \operatorname{normSq}\left(\operatorname{f}\left(x\right)\right) \le C) \land (\forall x: M, x \in N \Rightarrow (\forall k: \operatorname{ZMod}\left(3\right), \operatorname{f}\left(x \cdot \operatorname{iterate}\left(U, \operatorname{val}\left(k\right), u\right)\right) = \operatorname{f}\left(x\right) + \operatorname{chi}\left(k\right)\operatorname{f}\left(u\right) + \operatorname{chi}\left(-k\right)\operatorname{D}\left(x\right)))) \Rightarrow \operatorname{f}\left(u\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.bounded_phase_recursion_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full telescope is arbitrary M with only a two-sided unit, U:M to M, u:M, a subset N containing 1 and closed under x times U^k u for every x in N and k in ZMod 3, an injective complex additive character chi of ZMod 3, complex functions f and D, and a finite real C bounding normSq(f x) for every x in N. The displayed local recursion is an additional hypothesis. Character orthogonality yields a child energy of 3 times (normSq(f x)+normSq(f u)+normSq(D x)). Induction over every PhaseWords n gives 3^n times (normSq(f 1)+n normSq(f u)) as a lower bound on the total energy. The upper bound is 3^n C. An Archimedean argument forces normSq(f u)=0. AddChar.wInner_cWeight_eq_boole is the reused scalar orthogonality supplier; it imposes a group law only on the phase index.

This is a conditional Section 3 mechanism for C133 Continuation V. Neither the Fourier recursion nor its uniform bound is derived here from RawBalance. Applying it to both ordered bilinear pairings, constructing the raw radical quotient, proving beta(N)=0 and full gamma-fibre collapse, and the complete Hilbert criterion remain open. There is no full-Theorem-1.3 consumer or admission claim.

## References

- Truth anchor: `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.PhaseWords`
- Truth anchor: `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.bounded_phase_recursion_vanishes`
- Truth anchor: `D5/S3/Quantum/Completion/ThreePhaseHistoryRigidity.orderedHistory`
