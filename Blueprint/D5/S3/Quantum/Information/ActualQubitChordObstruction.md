# Two signal probes force a qubit chord

## Abstract

Two globally exact signal probes of a fixed quantum processor force a pure-ended qubit chord and an endpoint overlap bound.

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

A is jointObservation(G), a real linear map from Euclidean three-space to a pair of complex signal matrices. Both components are observations through the same processor. Let K be its kernel, Q the orthogonal complement of K, and P the orthogonal projection onto Q.

**Theorem 1.5 (The physical affine chord and its endpoint overlap).**

$$\begin {aligned} & \forall   a \in   \mathbb {R} ,   0 < a < 1 ,   \forall   G \in   \operatorname {CPTP} ( \operatorname {Fin} ( 3 ) \times \operatorname {Fin} ( 2 ) ,   \operatorname {Fin} ( 3 ) ) , \\ & \forall   \rho : \mathbb {R} \to \mathbb {C} ^ {2\times2} ,   ( \forall   u \in   J ,   \operatorname {PSD} ( \rho ( u ) ) \land \operatorname {tr} ( \rho ( u ) ) = 1 ) \\ & \land   ( \forall   u \in   J ,   \forall   k ,   \operatorname {L} ( k ,   \rho ( u ) ) = \operatorname {Y} ( k ,   a ,   u ) ) \\ & \longrightarrow   ( \forall   k ,   \operatorname {Density} ( W _ {k} ) ) \land   \exists   c , v \in   \mathbb {R} ^ 3 ,   \exists   b \in   \mathbb {R} , \\ & v \neq   0 \land 2 {a} ^ {2} - 1 \le b \le 2 a - 1 \land b < 1 \land c , v \in   Q \\ & \land   ( \forall   u \in   J ,   \operatorname {P} ( \operatorname {R} ( \rho ( u ) ) ) = \operatorname {r} ( u ) ) \\ & \land   ( \forall   u \in   \mathbb {R} ,   \forall   k ,   \operatorname {L} ( k ,   \operatorname {B} ( \operatorname {r} ( u ) ) ) = \operatorname {Y} ( k ,   a ,   u ) ) \\ & \land   ( \forall   u \in   \mathbb {R} ,   \operatorname {norm} ( \operatorname {r} ( u ) ) \le 1 \iff b \le u \le 1 ) \\ & \land   ( \forall   u \in   \mathbb {R} ,   \operatorname {PSD} ( \operatorname {B} ( \operatorname {r} ( u ) ) ) \iff b \le u \le 1 ) \\ & \land   ( \forall   u \in   \mathbb {R} ,   \operatorname {tr} ( \operatorname {B} ( \operatorname {r} ( u ) ) ) = 1 ) \\ & \land   ( \forall   u \in   J ,   \operatorname {norm} ( \operatorname {r} ( u ) ) < 1 ) \\ & \land \operatorname {norm} ( c + v ) = 1 \land \operatorname {norm} ( c + b v ) = 1 \\ & \land {rhoPlus} ^ {2} = rhoPlus \land {rhoMinus} ^ {2} = rhoMinus \\ & \land 0 \le s \le \frac {1 + b} {2} \land s < 1 \end {aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualQubitChordObstruction.actual_two_probe_chord_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the statement J is the open interval (2a-1,1), r(u)=c+uv, rhoPlus=B(c+v), rhoMinus=B(c+bv), and s is the real part of tr(rhoPlus rhoMinus). Density(Wk) means PSD(Wk) and tr(Wk)=1. Every quantifier over k ranges over Fin 2. The parameter u in the global affine identities ranges over all real numbers. No continuity, differentiability, purity or fixed-rank condition is imposed on the original program family.

Projecting the original Bloch vectors onto Q removes the common observation kernel. Two distinct interior parameters determine c and v; the nonzero slope of the second output makes v nonzero. Orthogonal projection decreases the norm, so the line remains in the Bloch ball on J.

For every physical point on this line, positivity of the first output tested against (1,0,-1) and (1,-2a,1) gives 2a squared minus 1 at most u at most 1. Continuity of the affine line, without any endpoint limit of the original family, forces the upper endpoint to have parameter 1 and norm one. Factoring its norm quadratic supplies the other endpoint b and the exact physical interval.

Pulling back the second signal projector gives the real linear readout f(M)=Re tr(W1 L(1,M)). Positivity and trace preservation give values between zero and one on every density matrix. In Bloch coordinates it has the form alpha plus the inner product of z and r, with norm(z) at most alpha and alpha plus norm(z) at most one. Its value one at c+v forces z to be norm(z) times c+v. Since norm(z) is at most one half, its value at the other endpoint bounds the pure-state overlap by (1+b)/2.

## References

- Truth anchor: `D5/S3/Quantum/Information/ActualQubitChordObstruction.actual_two_probe_chord_obstruction`
- Truth anchor: `D5/S3/Quantum/Information/ActualQubitChordObstruction.jointObservation`
- Truth anchor: `D5/S3/Quantum/Information/ActualQubitChordObstruction.probeTarget`
- Truth anchor: `D5/S3/Quantum/Information/ActualQubitChordObstruction.programOutput`
- Truth anchor: `D5/S3/Quantum/Information/ActualQubitChordObstruction.signalProbe`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](ActualPureQubitGeometry.md)
