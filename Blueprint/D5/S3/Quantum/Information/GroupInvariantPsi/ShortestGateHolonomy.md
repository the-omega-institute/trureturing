# Shortest gates and the return phase of a Bloch triangle

## Abstract

Shortest qubit rotor gates and the return phase of a triangle of Bloch directions.

A real three-vector r is represented by the Pauli combination r·σ = r₀σx + r₁σy + r₂σz of the module C129QubitBargmann, and P_r = (1 + r·σ)/2 is its Bloch projector. In this Pauli model of Cl(3,0) the geometric product of vectors is the matrix product and reversion is the conjugate transpose. Unit vectors a and b are non-antipodal when b ≠ −a; for unit vectors this is equivalent to 1 + a·b > 0.

**Definition 1.1 (Rotor gate).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.rotor`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.rotor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rotor a b is the matrix (1 + (b·σ)(a·σ)) / √(2(1 + a·b)), the Pauli form of the half-angle rotor (1 + ba)/√(2(1 + a·b)). The word shortest in the Lean names is a label; no minimality statement is proved here.

**Definition 1.2 (Normalized projection step).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.shortestGate`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.shortestGate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

shortestGate b ψ is P_b ψ divided by the square root of the real part of ⟨ψ|P_b|ψ⟩. For a unit spinor ψ with Bloch vector a, ⟨ψ|P_b|ψ⟩ is the real number (1 + a·b)/2, which the proof of the rotor theorem establishes.

**Definition 1.3 (Triangle scalar).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.triangleS`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.triangleS` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S = 1 + a·b + b·c + c·a.

**Definition 1.4 (Triangle volume).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.triangleD`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.triangleD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D = a·(b×c).

**Theorem 1.5 (The rotor gate between two Bloch directions).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.rotor_shortest_gate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.rotor_shortest_gate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chris Doran and Anthony Lasenby (2003). *Geometric Algebra for Physicists*. DOI: [10.1017/CBO9780511807497](https://doi.org/10.1017/CBO9780511807497). URL: <https://doi.org/10.1017/CBO9780511807497>.

*Commentary.*

Let a and b be unit vectors with b ≠ −a and R = rotor a b. The theorem states three facts. (1) R R† = 1. (2) R (a·σ) R† = b·σ. (3) For every unit spinor ψ with P_a ψ = ψ, R ψ = P_b ψ / √⟨ψ|P_b|ψ⟩, so on a state with Bloch vector a the gate is the normalized projection onto b.

Proof: the products (1 + (b·σ)(a·σ))(1 + (b·σ)(a·σ))† and (1 + (b·σ)(a·σ))(a·σ)(1 + (b·σ)(a·σ))† are computed entry by entry from the Pauli matrices, reducing with |a|² = |b|² = 1, and the scalar √(2(1 + a·b)) is positive by the non-antipodal hypothesis. For (3) the rank-one sandwich P_a X P_a = tr(P_a X) P_a gives ⟨ψ|X|ψ⟩ = tr(P_a X), so ⟨ψ|P_b|ψ⟩ = tr(P_a P_b) = (1 + a·b)/2, and R ψ = (ψ + (b·σ)ψ)/√(2(1 + a·b)) because (a·σ)ψ = ψ.

The half-angle rotor and its Pauli representation are textbook geometric algebra, as in Doran and Lasenby. The repository's contribution is the formal statement and proof in this matrix model. Not formalized: the exponential forms of the end-point product and of R, the claim that conjugation by R preserves grade, inner products and the orthogonal complement of the rotation plane, and any minimality or uniqueness of R.

**Theorem 1.6 (Gram identity of three unit vectors).**

$$\forall a \in (\operatorname{Fin}\left(3\right)) \to (\mathbb{R}),\; \forall b \in (\operatorname{Fin}\left(3\right)) \to (\mathbb{R}),\; \forall c \in (\operatorname{Fin}\left(3\right)) \to (\mathbb{R}),\; \operatorname{dotProduct}\left(a, a\right) = 1 \land \operatorname{dotProduct}\left(b, b\right) = 1 \land \operatorname{dotProduct}\left(c, c\right) = 1 \implies (\operatorname{triangleD}\left(a, b, c\right))^{2} = 1 + 2 \cdot \operatorname{dotProduct}\left(a, b\right) \cdot \operatorname{dotProduct}\left(b, c\right) \cdot \operatorname{dotProduct}\left(c, a\right) - (\operatorname{dotProduct}\left(a, b\right))^{2} - (\operatorname{dotProduct}\left(b, c\right))^{2} - (\operatorname{dotProduct}\left(c, a\right))^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.triangle_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For unit vectors a, b, c the squared oriented volume is the Gram determinant of the three vectors. No non-antipodal hypothesis is needed.

Proof: the general Gram identity D² = |a|²|b|²|c|² + 2(a·b)(b·c)(c·a) − |a|²(b·c)² − |b|²(c·a)² − |c|²(a·b)² is a polynomial identity in the coordinates; the unit hypotheses specialize it. This is classical linear algebra; the repository's contribution is the formal statement and proof.

**Theorem 1.7 (Return phase of the gates around a Bloch triangle).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.shortest_gate_triangle_holonomy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.shortest_gate_triangle_holonomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Pancharatnam (1956). *Generalized theory of interference, and its applications*. DOI: [10.1007/BF03046050](https://doi.org/10.1007/BF03046050). URL: <https://doi.org/10.1007/BF03046050>.

*Acknowledgement.* Joseph Samuel and Rajendra Bhandari (1988). *General Setting for Berry's Phase*. DOI: [10.1103/PhysRevLett.60.2339](https://doi.org/10.1103/PhysRevLett.60.2339). URL: <https://doi.org/10.1103/PhysRevLett.60.2339>.

*Acknowledgement.* A. Van Oosterom and J. Strackee (1983). *The Solid Angle of a Plane Triangle*. DOI: [10.1109/TBME.1983.325207](https://doi.org/10.1109/TBME.1983.325207). URL: <https://doi.org/10.1109/TBME.1983.325207>.

*Commentary.*

Let a, b, c be unit vectors, pairwise non-antipodal (b ≠ −a, c ≠ −b, a ≠ −c), and write S = triangleS a b c and D = triangleD a b c. The theorem states four facts. (0) S² + D² = 2(1 + a·b)(1 + b·c)(1 + c·a), obtained from the Gram identity by expanding S². (1) S² + D² > 0. (2) The three gates along a → b → c → a compose to rotor c a · rotor b c · rotor a b = (S·1 − iD (a·σ)) / √(S² + D²). (3) For every unit spinor ψ with P_a ψ = ψ, the three normalized projections onto b, then c, then a return h ψ with h = (S − iD)/√(S² + D²).

Fact (2) is the matrix form of the return phase; the octant e₃ → e₁ → e₂ → e₃ with S = D = 1 is an instance, where the product is (1 − iσz)/√2.

Proof: expanding (1 + (a·σ)(c·σ))(1 + (c·σ)(b·σ))(1 + (b·σ)(a·σ)) with the unit hypotheses gives 2S·1 − 2iD(a·σ). The product of the three normalizers is √(8(1 + a·b)(1 + b·c)(1 + c·a)) = 2√(S² + D²) by the Gram identity. Each normalized projection step equals the corresponding rotor gate, which is unitary and carries the projector of its source onto that of its target, so the three steps compose to the gate product applied to ψ, and (a·σ)ψ = ψ.

Classical context: the return phase of successive normalized projections is the Pancharatnam phase, placed in a general setting by Samuel and Bhandari. The scalar S and the oriented volume D are the real and imaginary parts of 4 tr(P_a P_b P_c), the three-state Bargmann invariant proved in C129QubitBargmann, and Ω/2 = arg(S + iD) is half the solid angle of the triangle by the formula of Van Oosterom and Strackee. The repository's contribution is the formal statement and proof; the identification with the solid angle is not formalized here.

## References

- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.rotor`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.rotor_shortest_gate`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.shortestGate`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.shortest_gate_triangle_holonomy`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.triangleD`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.triangleS`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/ShortestGateHolonomy.triangle_gram`
- Dependency: [D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann](C129QubitBargmann.md)
