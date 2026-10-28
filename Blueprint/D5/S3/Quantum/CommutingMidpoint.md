# Commuting Qubit Midpoint Contraction

## Abstract

Commuting qubit density inputs contract generalized Bures distance at the scalar midpoint reference.

All matrices are complex. A density matrix is positive semidefinite with trace one. The root-fidelity definition and weighted-root norm identity allow any finite decidable index type; the remaining results concern two-by-two matrices. Every square root is the positive functional-calculus root; F is the ordered generalized fidelity, B(R,P,Q)=Re tr(P+Q)-2 Re F(R,P,Q), and the distance is sqrt(B). Only P and Q commute in the channel theorem. Their outputs can have arbitrary complex coherence. The transported reference must be positive definite.

Ma, Rajaei and Zhang, Generalized Fidelity, the Data Processing Inequality, and Convexity, arXiv:2609.09753v3, give the ordered-root quotient, Pauli and Bloch identities, the weighted-root norm formula and scalar sufficient criteria. Their unrestricted-DPI counterexample supersedes the unresolved unrestricted question in v1. Afham and Ferrie, arXiv:2410.04937v2, supply the generalized-fidelity and squared-Bures conventions and transported-reference question. Vuong, arXiv:2605.28885v1, recomputes pair-dependent polar references; these need not equal the transported midpoint. The results below concern this positive commuting-input family and the failure of scalar-balance necessity. They give no full classification of Good triples.

**Definition 1.1 (A full Bloch chord).**

$$\forall ( d:\operatorname{EuclideanSpace}\left(\mathbb{ R}, \operatorname{Fin}\left(3\right)\right))( e:\operatorname{EuclideanSpace}\left(\mathbb{ R}, \operatorname{Fin}\left(3\right)\right))( z:\mathbb{ R}),\quad\operatorname{r}\left( d,  e,  z\right)= d+\sqrt{1-\Vert  d\Vert^{2}}(2 z-1) e$$

*Formalization.* `D5/S3/Quantum/CommutingMidpoint.chordVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

For d,e in Euclidean three-space and real z, r(z)=d+sqrt(1-||d|| squared)(2z-1)e. The full physical chord has d perpendicular to e, ||e||=1, ||d|| squared<1 and z in [0,1].

**Definition 1.2 (Actual states on a chord).**

$$\forall ( d:\operatorname{EuclideanSpace}\left(\mathbb{ R}, \operatorname{Fin}\left(3\right)\right))( e:\operatorname{EuclideanSpace}\left(\mathbb{ R}, \operatorname{Fin}\left(3\right)\right))( z:\mathbb{ R}),\quad\operatorname{X}\left( d,  e,  z\right)=\operatorname{rho}\left(\operatorname{r}\left( d,  e,  z\right)\right)$$

*Formalization.* `D5/S3/Quantum/CommutingMidpoint.chordState` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

X(z) is blochMatrix(1,r(z)), the canonical complex qubit matrix. On the full physical chord it is PSD with trace one; interior parameters give PD states.

**Theorem 1.3 (The sign-sensitive chord factorization).**

$$\forall ( d:\operatorname{EuclideanSpace}\left(\mathbb{ R}, \operatorname{Fin}\left(3\right)\right))( e:\operatorname{EuclideanSpace}\left(\mathbb{ R}, \operatorname{Fin}\left(3\right)\right))( r:\mathbb{ R})( s:\mathbb{ R})( t:\mathbb{ R}),\quad\operatorname{inner}\left( d,  e\right)=0\land \operatorname{norm}\left( e\right)=1\land \operatorname{norm}\left( d\right)^{2}<1\land 0< r<1\land 0\le s\le1\land 0\le t\le1\Rightarrow \forall ( a,  b,  f,  w:\mathbb{ R}),\quad( a=\operatorname{U}\left(\operatorname{X}\left( d,  e,  r\right), \operatorname{X}\left( d,  e,  s\right)\right)\land  b=\operatorname{U}\left(\operatorname{X}\left( d,  e,  r\right), \operatorname{X}\left( d,  e,  t\right)\right)\land  f=\Re(\operatorname{F}\left(\operatorname{X}\left( d,  e,  r\right), \operatorname{X}\left( d,  e,  s\right), \operatorname{X}\left( d,  e,  t\right)\right))\land  w=\operatorname{H}\left( s,  t\right))\Rightarrow (0< a\land0< b\land0\le f\land0\le w\land( f^{2}- w^{2}) a^{2} b^{2}=\operatorname{norm}\left( d\right)^{2}(1- w^{2})( a^{2}+ b^{2}-1)\land(1\le a^{2}+ b^{2}\Rightarrow w\le f))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CommutingMidpoint.qubit_chord_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

ChordDomain means d perpendicular to e, ||e||=1, tau=||d|| squared<1, 0<r<1 and s,t in [0,1]. Put a=U(X(r),X(s)), b=U(X(r),X(t)), f=Re F(X(r),X(s),X(t)), w=H(s,t). All signs in the display hold. The binary Gram identity and U(X(x),X(y)) squared=tau+(1-tau)H(x,y) squared give the factorization. Since a,b>0 and f,w>=0, a squared+b squared>=1 implies f>=w.

**Theorem 1.4 (Strict comparison and degenerate boundaries).**

$$\forall ( d:\operatorname{EuclideanSpace}\left(\mathbb{ R}, \operatorname{Fin}\left(3\right)\right))( e:\operatorname{EuclideanSpace}\left(\mathbb{ R}, \operatorname{Fin}\left(3\right)\right))( r:\mathbb{ R})( s:\mathbb{ R})( t:\mathbb{ R}),\quad\operatorname{inner}\left( d,  e\right)=0\land \operatorname{norm}\left( e\right)=1\land \operatorname{norm}\left( d\right)^{2}<1\land 0< r<1\land 0\le s\le1\land 0\le t\le1\Rightarrow \forall ( a,  b,  f,  w:\mathbb{ R}),\quad( a=\operatorname{U}\left(\operatorname{X}\left( d,  e,  r\right), \operatorname{X}\left( d,  e,  s\right)\right)\land  b=\operatorname{U}\left(\operatorname{X}\left( d,  e,  r\right), \operatorname{X}\left( d,  e,  t\right)\right)\land  f=\Re(\operatorname{F}\left(\operatorname{X}\left( d,  e,  r\right), \operatorname{X}\left( d,  e,  s\right), \operatorname{X}\left( d,  e,  t\right)\right))\land  w=\operatorname{H}\left( s,  t\right))\Rightarrow ((0<\operatorname{norm}\left( d\right)^{2}\land s\neq  t\Rightarrow( w\le f\Leftrightarrow1\le a^{2}+ b^{2})\land( f= w\Leftrightarrow a^{2}+ b^{2}=1))\land(\operatorname{norm}\left( d\right)^{2}=0\Rightarrow f= w)\land( s= t\Rightarrow f= w=1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CommutingMidpoint.qubit_chord_strict_sign_and_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

Use the same chord domain and a,b,f,w,tau as above. If tau>0 and s differs from t, 1-w squared is strictly positive, giving both exact equivalences. On a diameter, tau=0 gives f=w. Equal states s=t give f=w=1. These are fixed-chord statements, without a classification of arbitrary channel triples.

**Definition 1.5 (Mixtures of actual matrices).**

$$\forall ( p:\mathbb{ R})( A:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right))( B:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right)),\quad\operatorname{mix}\left( p,  A,  B\right)= p A+(1- p) B$$

*Formalization.* `D5/S3/Quantum/CommutingMidpoint.mixture` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

mixture(p,A,B)=p A+(1-p)B, with real scalar multiplication on complex matrices.

**Theorem 1.6 (Arbitrary prepared outputs).**

$$\forall ( A:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right))( B:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right))( p:\mathbb{ R})( q:\mathbb{ R}),\quad\operatorname{PSD}\left( A\right)\land \operatorname{tr}\left( A\right)=1\land \operatorname{PSD}\left( B\right)\land \operatorname{tr}\left( B\right)=1\land 0\le p\le1\land 0\le q\le1\land \operatorname{PD}\left(\operatorname{mix}\left(\frac{1}{2},  A,  B\right)\right)\Rightarrow \operatorname{H}\left( p,  q\right)\le\Re(\operatorname{F}\left(\operatorname{mix}\left(\frac{1}{2},  A,  B\right), \operatorname{mix}\left( p,  A,  B\right), \operatorname{mix}\left( q,  A,  B\right)\right))\land 0\le\operatorname{B}\left(\operatorname{mix}\left(\frac{1}{2},  A,  B\right), \operatorname{mix}\left( p,  A,  B\right), \operatorname{mix}\left( q,  A,  B\right)\right)\land \operatorname{B}\left(\operatorname{mix}\left(\frac{1}{2},  A,  B\right), \operatorname{mix}\left( p,  A,  B\right), \operatorname{mix}\left( q,  A,  B\right)\right)\le2-2\operatorname{H}\left( p,  q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CommutingMidpoint.prepared_qubit_midpoint_fidelity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

For arbitrary complex qubit densities A,B set T=(A+B)/2, S=pA+(1-p)B and V=qA+(1-q)B, with p,q in [0,1]. If T is PD then the full displayed conclusion holds. The Bloch line through distinct A,B extends to a full chord. The midpoint dominates each prepared state by one half, so the chord comparison applies; classical preparation then gives H(p,q). Equal A,B are treated directly. No output commutation is required.

**Definition 1.7 (The scalar midpoint reference).**

$$ R_{0}=\frac{1}{2} I$$

*Formalization.* `D5/S3/Quantum/CommutingMidpoint.midpointReference` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

R0=I/2 as a complex two-by-two matrix; it is PD and has trace one.

**Theorem 1.8 (Every positive trace-preserving linear map).**

$$\forall ( P:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right))( Q:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right))( Phi:\operatorname{ComplexLinearMap}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right)\right)),\quad\operatorname{PSD}\left( P\right)\land \operatorname{tr}\left( P\right)=1\land \operatorname{PSD}\left( Q\right)\land \operatorname{tr}\left( Q\right)=1\land  P Q= Q P\land (\forall ( M:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right)),\quad(\operatorname{PSD}\left( M\right))\Rightarrow (\operatorname{PSD}\left(\operatorname{Phi}\left( M\right)\right)))\land (\forall ( M:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right)),\quad\operatorname{tr}\left(\operatorname{Phi}\left( M\right)\right)=\operatorname{tr}\left( M\right))\land \operatorname{PD}\left(\operatorname{Phi}\left( R_{0}\right)\right)\Rightarrow \operatorname{U}\left( P,  Q\right)=\Re(\operatorname{F}\left( R_{0},  P,  Q\right))\land \operatorname{U}\left( P,  Q\right)\le\Re(\operatorname{F}\left(\operatorname{Phi}\left( R_{0}\right), \operatorname{Phi}\left( P\right), \operatorname{Phi}\left( Q\right)\right))\land \operatorname{B}\left(\operatorname{Phi}\left( R_{0}\right), \operatorname{Phi}\left( P\right), \operatorname{Phi}\left( Q\right)\right)\le\operatorname{B}\left( R_{0},  P,  Q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CommutingMidpoint.commuting_midpoint_all_positive_trace_preserving` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

Phi ranges over every complex-linear map on all complex qubit matrices that maps each PSD matrix to a PSD matrix and preserves trace on every matrix. R0=I/2. For commuting density P,Q and PD Phi(R0), root fidelity equals the input ordered fidelity and is bounded by the output ordered fidelity; B contracts. For distinct inputs, the exact squared commutator trace forces their full Bloch chord to be a diameter. Its endpoints E1,E0 satisfy R0=(E1+E0)/2. Complex linearity sends the same three inputs to mixtures of Phi(E1),Phi(E0), so the prepared-output theorem applies. Equal inputs follow from the norm identity.

**Theorem 1.9 (Canonical physical channels).**

$$\forall ( P,  Q:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right))( Phi:\operatorname{QuantumChannel}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right)),\quad\operatorname{PSD}\left( P\right)\land \operatorname{tr}\left( P\right)=1\land \operatorname{PSD}\left( Q\right)\land \operatorname{tr}\left( Q\right)=1\land  P Q= Q P\land \operatorname{PD}\left(\operatorname{Phi}\left( R_{0}\right)\right)\Rightarrow 0\le\operatorname{B}\left(\operatorname{Phi}\left( R_{0}\right), \operatorname{Phi}\left( P\right), \operatorname{Phi}\left( Q\right)\right)\land 0\le\operatorname{B}\left( R_{0},  P,  Q\right)\land \operatorname{B}\left(\operatorname{Phi}\left( R_{0}\right), \operatorname{Phi}\left( P\right), \operatorname{Phi}\left( Q\right)\right)\le\operatorname{B}\left( R_{0},  P,  Q\right)\land \sqrt{\operatorname{B}\left(\operatorname{Phi}\left( R_{0}\right), \operatorname{Phi}\left( P\right), \operatorname{Phi}\left( Q\right)\right)}\le\sqrt{\operatorname{B}\left( R_{0},  P,  Q\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CommutingMidpoint.commuting_midpoint_canonical_CPTP` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

Phi is every existing QuantumChannel(Fin 2,Fin 2); its action is GeneralizedFidelity.rawMatrix. Here Bin=B(R0,P,Q) and Bout=B(Phi(R0),Phi(P),Phi(Q)). The input hypotheses are PSD trace-one P,Q with PQ=QP, and the only output-reference restriction is PD Phi(R0). The channel's all-amplification complete positivity implies ordinary positivity. Its canonical trace-preserving and complex-linear action gives the previous theorem. The norm identity establishes both nonnegativities before taking square roots.

**Definition 1.10 (Universal transported-reference contraction).**

$$\forall ( P:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right))( Q:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right))( R:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right)),\quad\operatorname{Good}\left( P,  Q,  R\right)\Leftrightarrow (\forall ( Phi:\operatorname{QuantumChannel}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right)),\quad(\operatorname{PD}\left(\operatorname{Phi}\left( R\right)\right))\Rightarrow (\operatorname{B}\left(\operatorname{Phi}\left( R\right), \operatorname{Phi}\left( P\right), \operatorname{Phi}\left( Q\right)\right)\le\operatorname{B}\left( R,  P,  Q\right)))$$

*Formalization.* `D5/S3/Quantum/CommutingMidpoint.Good` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

Good(P,Q,R) quantifies all canonical qubit CPTP channels with PD transported reference. Its physical uses require P,Q density matrices and R PD of trace one. The same channel acts on all three matrices.

**Theorem 1.11 (A faithful outside-balance triple).**

$$\forall ( P,  Q:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right)),\quad P=\operatorname{diag}\left(\frac{9}{10}, \frac{1}{10}\right)\land  Q=\operatorname{diag}\left(\frac{4}{5}, \frac{1}{5}\right)\Rightarrow \operatorname{PD}\left( P\right)\land \operatorname{PD}\left( Q\right)\land \operatorname{PD}\left( R_{0}\right)\land \operatorname{tr}\left( P\right)=1\land \operatorname{tr}\left( Q\right)=1\land \operatorname{tr}\left( R_{0}\right)=1\land \operatorname{Good}\left( P,  Q,  R_{0}\right)\land \operatorname{U}\left( R_{0},  P\right)^{2}=\frac{4}{5}\land \operatorname{U}\left( R_{0},  Q\right)^{2}=\frac{9}{10}\land \operatorname{U}\left( P,  Q\right)^{2}=\frac{49}{50}\land |\operatorname{U}\left( R_{0},  P\right)^{2}-\operatorname{U}\left( R_{0},  Q\right)^{2}|=\frac{1}{10}\land 1-\operatorname{U}\left( P,  Q\right)^{2}=\frac{1}{50}\land 1-\operatorname{U}\left( P,  Q\right)^{2}<|\operatorname{U}\left( R_{0},  P\right)^{2}-\operatorname{U}\left( R_{0},  Q\right)^{2}|\land \operatorname{B}\left( R_{0},  P,  Q\right)=2-\frac{7\sqrt{2}}{5}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CommutingMidpoint.faithful_Good_outside_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

Take P=diag(9/10,1/10), Q=diag(4/5,1/5), R0=I/2. All three matrices are PD densities. The theorem proves Good, the three exact squared root fidelities, absolute squared imbalance 1/10, residual 1/50 and their strict inequality. It also gives B(R0,P,Q)=2-7 sqrt(2)/5. Good follows from the universal channel theorem; the scalar values use the actual matrix trace-determinant root formula.

**Theorem 1.12 (A singular outside-balance triple).**

$$\forall ( P,  Q:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right)),\quad P=\operatorname{diag}\left(1, 0\right)\land  Q=\operatorname{diag}\left(\frac{3}{4}, \frac{1}{4}\right)\Rightarrow \operatorname{PSD}\left( P\right)\land \operatorname{PSD}\left( Q\right)\land \operatorname{PD}\left( R_{0}\right)\land \operatorname{tr}\left( P\right)=1\land \operatorname{tr}\left( Q\right)=1\land \operatorname{tr}\left( R_{0}\right)=1\land \operatorname{rank}\left( P\right)=1\land \operatorname{Good}\left( P,  Q,  R_{0}\right)\land \operatorname{U}\left( R_{0},  P\right)^{2}=\frac{1}{2}\land \operatorname{U}\left( R_{0},  Q\right)^{2}=\frac{1}{2}+\frac{\sqrt{3}}{4}\land \operatorname{U}\left( P,  Q\right)^{2}=\frac{3}{4}\land |\operatorname{U}\left( R_{0},  P\right)^{2}-\operatorname{U}\left( R_{0},  Q\right)^{2}|=\frac{\sqrt{3}}{4}\land 1-\operatorname{U}\left( P,  Q\right)^{2}=\frac{1}{4}\land 1-\operatorname{U}\left( P,  Q\right)^{2}<|\operatorname{U}\left( R_{0},  P\right)^{2}-\operatorname{U}\left( R_{0},  Q\right)^{2}|\land \operatorname{B}\left( R_{0},  P,  Q\right)=2-\sqrt{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CommutingMidpoint.singular_Good_outside_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

Take P=diag(1,0), Q=diag(3/4,1/4), R0=I/2. P,Q are PSD trace-one states, R0 is PD of trace one, and rank(P)=1. The theorem proves Good, the three exact squared root fidelities, imbalance sqrt(3)/4, residual 1/4 and the strict inequality. It also gives B(R0,P,Q)=2-sqrt(3). The rank and root values are exact, and the universal channel statement includes singular inputs.

**Definition 1.13 (The proposed scalar necessity).**

$$\operatorname{claim}\left(\right)\Leftrightarrow (\forall ( P:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right))( Q:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right))( R:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{ C}\right)),\quad(\operatorname{PSD}\left( P\right)\land \operatorname{tr}\left( P\right)=1\land \operatorname{PSD}\left( Q\right)\land \operatorname{tr}\left( Q\right)=1\land \operatorname{PD}\left( R\right)\land \operatorname{tr}\left( R\right)=1\land \operatorname{Good}\left( P,  Q,  R\right))\Rightarrow (|\operatorname{U}\left( R,  P\right)^{2}-\operatorname{U}\left( R,  Q\right)^{2}|\le1-\operatorname{U}\left( P,  Q\right)^{2}))$$

*Formalization.* `D5/S3/Quantum/CommutingMidpoint.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

The proposed necessity ranges over every PSD density pair P,Q and every PD trace-one reference R. It says that Good implies scalar balance. No commutation assumption occurs in this proposed global assertion.

**Theorem 1.14 (Scalar balance is not necessary).**

$$\neg \operatorname{claim}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/CommutingMidpoint.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma, Reza Rajaei, Wenlin Zhang (2026). *Generalized Fidelity, the Data Processing Inequality, and Convexity*. URL: <https://arxiv.org/html/2609.09753v3>.

*Commentary.*

The faithful triple above refutes claim. Thus there exist three PD density matrices with Good and strict failure of balance. The singular triple gives an additional boundary example. This disproves the proposed necessity and the corresponding full iff; it does not supply a replacement necessary-and-sufficient classification.

## References

- Truth anchor: `D5/S3/Quantum/CommutingMidpoint.Good`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint.chordState`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint.chordVector`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint.claim`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint.commuting_midpoint_all_positive_trace_preserving`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint.commuting_midpoint_canonical_CPTP`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint.faithful_Good_outside_balance`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint.midpointReference`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint.mixture`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint.prepared_qubit_midpoint_fidelity`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint.qubit_chord_factorization`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint.qubit_chord_strict_sign_and_boundary`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint.result`
- Truth anchor: `D5/S3/Quantum/CommutingMidpoint.singular_Good_outside_balance`
- Dependency: [D5/S3/Quantum/CommutingMidpoint/Fidelity](CommutingMidpoint/Fidelity.md)
