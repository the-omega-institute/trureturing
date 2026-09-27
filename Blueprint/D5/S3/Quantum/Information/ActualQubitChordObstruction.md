# Two signal probes force a qubit chord and a QFI bound

## Abstract

Two globally exact signal probes force a pure-ended qubit chord, an endpoint overlap bound, and a pointwise spectral QFI lower bound on the original program curve.

All matrices are complex. The signal index is Fin 3 and the program index is Fin 2. G is an arbitrary canonical completely positive trace-preserving map from matrices indexed by Fin 3 times Fin 2 to matrices indexed by Fin 3. Its complete positivity includes every finite amplification. The same G is used for both signals and for every parameter.

Write B(r) for the existing blochMatrix(1,r), Bzero(r) for blochMatrix(0,r), and R(M) for the existing bloch(M). Thus B(r) has diagonal entries (1+r2)/2 and (1-r2)/2 and upper off-diagonal entry (r0-i r1)/2. These coordinates retain arbitrary complex qubit states. A density matrix is positive semidefinite with trace one; a pure density matrix is also idempotent.

**Definition 1.1 (Two actual signal matrices).**

$$\begin {aligned} & W _ {0} = \frac {1} {3} \begin {pmatrix} 1 & 1 & 1 \\ 1 & 1 & 1 \\ 1 & 1 & 1 \end {pmatrix} \\ & W _ {1} = \frac {1} {2} \begin {pmatrix} 1 & 0 & 1 \\ 0 & 0 & 0 \\ 1 & 0 & 1 \end {pmatrix} \end {aligned}$$

*Formalization.* `D5/S3/Quantum/Information/ActualQubitChordObstruction.signalProbe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W0 is the uniform pure signal, and W1 is the balanced pure signal on coordinates zero and two. The formula gives signalProbe at both elements of Fin 2.

**Definition 1.2 (The required outputs).**

$$\begin {aligned} & \operatorname {Y} ( 0 ,   a ,   u ) = \frac {1} {3} \begin {pmatrix} 1 & a & u \\ a & 1 & a \\ u & a & 1 \end {pmatrix} \\ & \operatorname {Y} ( 1 ,   a ,   u ) = \frac {1} {2} \begin {pmatrix} 1 & 0 & u \\ 0 & 0 & 0 \\ u & 0 & 1 \end {pmatrix} \end {aligned}$$

*Formalization.* `D5/S3/Quantum/Information/ActualQubitChordObstruction.probeTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a and u, Yk(a,u) denotes probeTarget(a,u,k). These are the two specified signal outputs; no assertion about other signal matrices is included.

**Definition 1.3 (Program-to-output maps).**

$$\begin {aligned} & \forall   k \in   \operatorname {Fin} ( 2 ) ,   \operatorname {L} ( k ,   M ) = \operatorname {G} ( \operatorname {tensor} ( W _ {k} ,   M ) ) \\ & \operatorname {L} ( k ) : \mathbb {C} ^ {2\times2} \to _ {\mathbb {R}} \mathbb {C} ^ {3\times3} \end {aligned}$$

*Formalization.* `D5/S3/Quantum/Information/ActualQubitChordObstruction.programOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L(k,M) denotes programOutput(G,k,M), regarded as a real linear map on all complex program matrices. The tensor product uses the fixed signal Wk and the input program M.

**Definition 1.4 (The joint real observation).**

$$\begin {aligned} & A : \mathbb {R} ^ 3 \to _ {\mathbb {R}} ( \mathbb {C} ^ {3\times3} \times \mathbb {C} ^ {3\times3} ) \\ & \operatorname {A} ( r ) = ( \operatorname {L} ( 0 ,   \operatorname {Bzero} ( r ) ) , \operatorname {L} ( 1 ,   \operatorname {Bzero} ( r ) ) ) \end {aligned}$$

*Formalization.* `D5/S3/Quantum/Information/ActualQubitChordObstruction.jointObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A is jointObservation(G), a real linear map from Euclidean three-space to a pair of complex signal matrices. Both components are observations through the same processor. Let K be its kernel, Q the orthogonal complement of K, and P the orthogonal projection onto Q. P is a real orthogonal projection; no complete positivity of P is asserted.

**Theorem 1.5 (The physical affine chord, endpoint overlap, and pointwise QFI).**

$$\begin {aligned} & \forall   a \in   \mathbb {R} ,   \forall   G \in   \operatorname {CPTP} ( \operatorname {Fin} ( 3 ) \times \operatorname {Fin} ( 2 ) ,   \operatorname {Fin} ( 3 ) ) , \\ & \forall   \rho : \mathbb {R} \to \mathbb {C} ^ {2\times2} ,   ( 0 < a \land a < 1 \land   ( \forall   u \in   J ,   \operatorname {PSD} ( \rho ( u ) ) \land \operatorname {tr} ( \rho ( u ) ) = 1 ) \\ & \land   ( \forall   u \in   J ,   \forall   k ,   \operatorname {L} ( k ,   \rho ( u ) ) = \operatorname {Y} ( k ,   a ,   u ) ) ) \\ & \longrightarrow   ( ( \forall   k ,   \operatorname {Density} ( W _ {k} ) ) \land   ( \exists   c , v \in   \mathbb {R} ^ 3 ,   \exists   b \in   \mathbb {R} , ( \\ & v \neq   0 \land 2 {a} ^ {2} - 1 \le b \le 2 a - 1 \land b < 1 \land c , v \in   Q \\ & \land   ( \forall   u \in   J ,   \operatorname {P} ( \operatorname {R} ( \rho ( u ) ) ) = \operatorname {r} ( u ) ) \\ & \land   ( \forall   u \in   \mathbb {R} ,   \forall   k ,   \operatorname {L} ( k ,   \operatorname {B} ( \operatorname {r} ( u ) ) ) = \operatorname {Y} ( k ,   a ,   u ) ) \\ & \land   ( \forall   u \in   \mathbb {R} ,   \operatorname {norm} ( \operatorname {r} ( u ) ) \le 1 \iff b \le u \le 1 ) \\ & \land   ( \forall   u \in   \mathbb {R} ,   \operatorname {PSD} ( \operatorname {B} ( \operatorname {r} ( u ) ) ) \iff b \le u \le 1 ) \\ & \land   ( \forall   u \in   \mathbb {R} ,   \operatorname {tr} ( \operatorname {B} ( \operatorname {r} ( u ) ) ) = 1 ) \\ & \land   ( \forall   u \in   J ,   \operatorname {norm} ( \operatorname {r} ( u ) ) < 1 ) \\ & \land \operatorname {norm} ( c + v ) = 1 \land \operatorname {norm} ( c + b v ) = 1 \\ & \land {rhoPlus} ^ {2} = rhoPlus \land {rhoMinus} ^ {2} = rhoMinus \\ & \land 0 \le s \le \frac {1 + b} {2} \land s < 1 ) ) ) \\ & \land   ( \forall   u \in   J ,   \operatorname {DifferentiableAt} ( \mathbb {R} ,   \rho ,   u ) \longrightarrow \\ & \frac {1 - {a} ^ {2}} {( 1 - u ) ( 1 + u - 2 {a} ^ {2} )} \le \operatorname {spectralQFI} ( \rho ( u ) ,   \operatorname {deriv} ( \rho ,   u ) ,   \operatorname {hRho} ( u ) ) ) \end {aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualQubitChordObstruction.actual_two_probe_chord_and_qfi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the statement J is the open interval (2a-1,1), r(u)=c+uv, rhoPlus=B(c+v), rhoMinus=B(c+bv), and s is the real part of tr(rhoPlus rhoMinus). Density(Wk) means PSD(Wk) and tr(Wk)=1. Every quantifier over k ranges over Fin 2. The parameter u in the global affine identities ranges over all real numbers. All chord conclusions follow from density and exactness on J, without continuity, differentiability, purity or fixed rank of the original program family.

The final conjunction is quantified independently of the existential chord: at every u in J where the original complex matrix curve rho is differentiable over the reals, its spectralQFI is bounded below by (1-a squared)/((1-u)(1+u-2a squared)). Here deriv(rho,u) is its real derivative and hRho(u) is the positive semidefiniteness proof supplied by the density hypothesis. spectralQFI is the support-safe spectral sum: in an eigenbasis of rho, sum 2 times the squared modulus of each derivative entry divided by the sum of the corresponding eigenvalues, with zero denominators contributing zero. No constant-rank premise is needed.

Projecting the original Bloch vectors onto Q removes the common observation kernel. Two distinct interior parameters determine c and v; the nonzero slope of the second output makes v nonzero. Orthogonal projection decreases the norm, so the line remains in the Bloch ball on J.

For every physical point on this line, positivity of the first output tested against (1,0,-1) and (1,-2a,1) gives 2a squared minus 1 at most u at most 1. Continuity of the affine line, without any endpoint limit of the original family, forces the upper endpoint to have parameter 1 and norm one. Factoring its norm quadratic supplies the other endpoint b and the exact physical interval.

Pulling back the second signal projector gives the real linear readout f(M)=Re tr(W1 L(1,M)). Positivity and trace preservation give values between zero and one on every density matrix. In Bloch coordinates it has the form alpha plus the inner product of z and r, with norm(z) at most alpha and alpha plus norm(z) at most one. Its value one at c+v forces z to be norm(z) times c+v. Since norm(z) is at most one half, its value at the other endpoint bounds the pure-state overlap by (1+b)/2.

Fix an evaluation point u in J and put r=r(u). Since norm(r)<1, the vector ell=v+inner(r,v)/(1-norm(r) squared) times r is nonzero. Normalize it to n. Both r and v lie in Q, so n lies in Q. The two effects N0=B(n) and N1=B(-n) are positive semidefinite and sum to the identity. This is a physical two-outcome measurement, held fixed as the nearby parameter varies.

$$
\begin {aligned} & ell = v + \frac {\operatorname {inner} ( r ,   v )} {1 - {\operatorname {norm} ( r )} ^ {2}} r ,   n = \frac {ell} {\operatorname {norm} ( ell )} \\ & N _ {0} = \operatorname {B} ( n ) ,   N _ {1} = \operatorname {B} ( - n ) \\ & N _ {0} \ge 0 ,   N _ {1} \ge 0 ,   N _ {0} + N _ {1} = I \end {aligned}
$$

For every nearby x in J, orthogonality gives inner(n,R(rho(x)))=inner(n,c+xv). Consequently this fixed measurement on the original curve has strictly positive probabilities at u and locally affine readouts with velocities plus and minus inner(n,v)/2. Applying actual_fisher to t mapped to rho(u+t) bounds the classical Fisher information of this measurement by spectralQFI(rho(u),deriv(rho,u),hRho(u)). No quantum-channel interpretation of the projection is used.

The classical Fisher information is norm(v) squared plus inner(r,v) squared divided by 1-norm(r) squared. The endpoint identities turn this into (1-s)/((u-b)(1-u)). The overlap bound s at most (1+b)/2 and the endpoint bound b at least 2a squared minus 1 then give the stated QFI lower bound. This is a lower bound on the original program curve; it asserts no attainment, phase classification, or replacement exactness for signals other than the two specified probes.

## References

- Truth anchor: `D5/S3/Quantum/Information/ActualQubitChordObstruction.actual_two_probe_chord_and_qfi`
- Truth anchor: `D5/S3/Quantum/Information/ActualQubitChordObstruction.jointObservation`
- Truth anchor: `D5/S3/Quantum/Information/ActualQubitChordObstruction.probeTarget`
- Truth anchor: `D5/S3/Quantum/Information/ActualQubitChordObstruction.programOutput`
- Truth anchor: `D5/S3/Quantum/Information/ActualQubitChordObstruction.signalProbe`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitFisherRank](ActualPureQubitFisherRank.md)
