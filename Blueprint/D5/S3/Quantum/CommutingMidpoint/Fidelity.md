# Root Fidelity and Binary Preparation

## Abstract

Matrix root-fidelity identities and binary preparation estimates used by commuting midpoint contraction.

These matrix identities and preparation estimates are the foundation of commuting qubit midpoint contraction. The weighted-root norm identity has arbitrary finite decidable indices and no trace normalization. The qubit quotient allows singular density inputs; only its reference is positive definite. The half-order estimate needs no trace normalization on its second PSD matrix.

**Definition 1.1 (Root fidelity).**

$$\forall ( n: Type)[\operatorname{Fintype}\left( n\right)][\operatorname{DecidableEq}\left( n\right)]( S,  T:\operatorname{Matrix}\left( n,  n, \mathbb{ C}\right)),\quad\operatorname{U}\left( S,  T\right)=\Re(\operatorname{tr}\left(\sqrt{\sqrt{ S} T\sqrt{ S}}\right))$$

*Formalization.* `D5/S3/Quantum/CommutingMidpoint/Fidelity.rootFidelity` (`✓ std3`).

*Citation.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

For matrices on any finite decidable index type, U(S,T) is the real trace of sqrt(sqrt(S) T sqrt(S)). This is root fidelity, without a final square.

**Theorem 1.2 (The weighted-root norm identity).**

$$\forall ( n: Type)[\operatorname{Fintype}\left( n\right)][\operatorname{DecidableEq}\left( n\right)]( S,  V,  T:\operatorname{Matrix}\left( n,  n, \mathbb{ C}\right)),\quad\operatorname{PSD}\left( S\right)\land \operatorname{PSD}\left( V\right)\land \operatorname{PD}\left( T\right)\Rightarrow \operatorname{B}\left( T,  S,  V\right)=\Vert \operatorname{inv}\left(\sqrt{ T}\right)(\sqrt{\sqrt{ T} S\sqrt{ T}}-\sqrt{\sqrt{ T} V\sqrt{ T}})\Vert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CommutingMidpoint/Fidelity.bures_eq_weighted_root_norm_sq` (`✓ std3`). ∎

*Citation.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

For every finite decidable index type, PSD S,V and PD T, B(T,S,V) equals the squared Frobenius norm displayed above. No trace normalization is required. Expand the norm using the Frobenius trace identity. The diagonal terms are tr(S), tr(V); the two cross terms have equal real parts because they are conjugate traces. This proves nonnegativity even for singular S or V.

**Theorem 1.3 (The actual qubit quotient).**

$$\forall ( S:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right))( V:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right))( T:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right)),\quad\operatorname{PSD}\left( S\right)\land \operatorname{tr}\left( S\right)=1\land \operatorname{PSD}\left( V\right)\land \operatorname{tr}\left( V\right)=1\land \operatorname{PD}\left( T\right)\land \operatorname{tr}\left( T\right)=1\Rightarrow 0<\operatorname{U}\left( T,  S\right)\land 0<\operatorname{U}\left( T,  V\right)\land \Re(\operatorname{F}\left( T,  S,  V\right))=\frac{\operatorname{U}\left( T,  S\right)^{2}+\operatorname{U}\left( T,  V\right)^{2}+\operatorname{U}\left( S,  V\right)^{2}-1}{2\operatorname{U}\left( T,  S\right)\operatorname{U}\left( T,  V\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CommutingMidpoint/Fidelity.qubit_root_fidelity_quotient` (`✓ std3`). ∎

*Citation.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

Put a=U(T,S), b=U(T,V), c=U(S,V). For every pair of qubit density matrices and every trace-one PD reference T, a and b are strictly positive and the real ordered fidelity is the stated quotient. The proof uses the two-dimensional trace recurrence for actual matrix square roots and determinants, including singular S,V.

**Definition 1.4 (Binary root fidelity).**

$$\forall ( p:\mathbb{ R})( q:\mathbb{ R}),\quad\operatorname{H}\left( p,  q\right)=\sqrt{ p q}+\sqrt{(1- p)(1- q)}$$

*Formalization.* `D5/S3/Quantum/CommutingMidpoint/Fidelity.binaryFidelity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

H(p,q)=sqrt(pq)+sqrt((1-p)(1-q)); its probabilistic uses have p,q in [0,1].

**Theorem 1.5 (A half-order lower bound).**

$$\forall ( S:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right))( T:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right)),\quad\operatorname{PSD}\left( S\right)\land \operatorname{tr}\left( S\right)=1\land\operatorname{PSD}\left( T\right)\land\operatorname{PSD}\left( T-\frac{1}{2} S\right)\Rightarrow\frac{1}{2}\le\operatorname{U}\left( T,  S\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CommutingMidpoint/Fidelity.fidelity_sq_lower_bound_from_half_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

For every density S and PSD T with T-S/2 PSD, U(T,S) squared is at least one half. Congruence by sqrt(S), operator monotonicity of sqrt, and positivity of trace give U(S,T)>=sqrt(1/2). The actual qubit formula proves symmetry U(S,T)=U(T,S). There is no invertibility assumption on S and no trace-one requirement on T.

**Theorem 1.6 (Classical binary preparation).**

$$\forall ( p:\mathbb{ R})( q:\mathbb{ R})( x:\mathbb{ R})( y:\mathbb{ R}),\quad0\le p\le1\land 0\le q\le1\land 0\le x\le1\land 0\le y\le1\Rightarrow \operatorname{H}\left( p,  q\right)\le\operatorname{H}\left( p x+(1- p) y,  q x+(1- q) y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CommutingMidpoint/Fidelity.classical_binary_preparation_fidelity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

For all p,q,x,y in the closed unit interval, preparing binary probabilities x,y with mixing probabilities p,q cannot decrease H. Apply Cauchy-Schwarz to each coordinate and add the two inequalities. Zero probabilities are included.

## References

- Truth anchor: `D5/S3/Quantum/CommutingMidpoint/Fidelity.binaryFidelity`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint/Fidelity.bures_eq_weighted_root_norm_sq`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint/Fidelity.classical_binary_preparation_fidelity`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint/Fidelity.fidelity_sq_lower_bound_from_half_order`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint/Fidelity.qubit_root_fidelity_quotient`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint/Fidelity.rootFidelity`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S3/Quantum/GNSMatrix](../GNSMatrix.md)
- Dependency: [D5/S3/Quantum/GeneralizedFidelity](../GeneralizedFidelity.md)
- Dependency: [D5/S3/Quantum/Information/ActualQubitChordObstruction](../Information/ActualQubitChordObstruction.md)
