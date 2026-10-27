# An explicit rate for the fixed control

## Abstract

The installed DU wash has an explicit Hilbert-Schmidt decay rate.

**Theorem 1.1 (The complete complex matrix domain and all natural powers).**

$$\left(\forall X \in \operatorname{ComplexTraceZeroMatrix}\left(3\right),\; \operatorname{HS}\left(\operatorname{Theta}\left(X\right)\right)^{2} \le \frac{5}{12} \cdot \operatorname{HS}\left(X\right)^{2} \land \left(\forall n \in Nat,\; \operatorname{HS}\left(\operatorname{iterateTheta}\left(n, X\right)\right) \le \frac{2}{3}^{n} \cdot \operatorname{HS}\left(X\right)\right)\right) \land \left(\forall sigma \in \operatorname{PositiveSemidefiniteTraceOneMatrix}\left(3\right),\; \forall n \in Nat,\; \operatorname{HS}\left(\operatorname{iterateTheta}\left(n, sigma\right)-\frac{1}{3}I\right) \le \operatorname{sqrt}\left(\frac{2}{3}\right) \cdot \frac{2}{3}^{n}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/OriginalQutritWash.explicit_wash_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

U exchanges coordinates 1 and 2, W exchanges 0 and 1, D=diag(1,1,-1), and N=DU is the single installed control. Lambda=Ad_U composed with (id+Ad_W)/2 and Theta=Lambda squared composed with Ad_N composed with Lambda squared. HS(X) is the norm of CartesianVariance.vectorize 3 X in the complex Euclidean space indexed by pairs of qutrit coordinates. It is the complex Frobenius norm. X ranges over every complex trace-zero 3 by 3 matrix; no Hermiticity assumption is imposed on this clause. The powers are raw repeated applications of Theta, including the identity at n=0. A density sigma means actual positive semidefiniteness and trace one.

Let A=Lambda squared and let v have zero diagonal and off-diagonal entries 1/sqrt(6). This is the normalized centered P_xi line. A fixes v, preserves its perpendicular complement in the trace-zero space, and contracts that complement by at most one half. For K=Ad_N, inner(v,Kv)=-1/3. The component of the adjoint image of v perpendicular to v has squared norm 8/9. Cauchy-Schwarz bounds its pairing with z=Ay. Writing X=alpha v+y yields HS(AKA X) squared at most (5/12) abs(alpha) squared +(19/48) HS(y) squared, hence at most (5/12) HS(X) squared. Since sqrt(5/12) is below 2/3, repeated application proves the power estimate.

The same actual map preserves trace and fixes the identity. It therefore commutes with centering a density at I/3, including under iteration. The density purity bound and the Hilbert-Schmidt centering identity give HS(sigma-I/3) squared at most 2/3, giving the stated prefactor. The density statement at n=0 is part of the result.

The physical application retains the separately supplied fixed-DU source, memoryless outgoing-record lift, complete returned-system branches and identity action on untouched references. A wash has chronology J J N J J; its four new outgoing carriers remain unread and inaccessible. The original C3 preparation and control are transported through the given code B into C5. Universality over mathematical input matrices grants no additional preparations, separate D or U calls, reset, inverse, forced outcome, arbitrary record unitary, returned carrier, archive decoder or coherent sink access. The trace-norm statement with a reference is a separate result. No exact scalar anchor, physical precision, duration or energy bound is inferred.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/OriginalQutritWash.explicit_wash_bound`
- Dependency: [D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound](../Entanglement/QutritWeylBlochNormSeparableBound.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/OriginalQutritGap](OriginalQutritGap.md)
- Dependency: [D5/S3/Quantum/Tomography/PurityPythagorasDecomposition](../Tomography/PurityPythagorasDecomposition.md)
