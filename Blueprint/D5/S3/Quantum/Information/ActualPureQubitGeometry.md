# Pure-qubit affine geometry

## Abstract

A rank-two affine measurement of a pure qubit curve has a strict arc parametrization.

Throughout, Jm denotes the finite index set Fin m; a subscript j denotes evaluation at j. Matrices are complex, PSD means positive semidefinite, and 1n is the identity on the indicated finite index set. C1(I) means continuously differentiable on I over the reals. Preconnected means that I cannot be separated into two nonempty relatively open sets; it does not require I to be nonempty. D2 is the canonical space of positive trace-one qubit density states, and mat recovers the underlying matrix. All unspecified scalar arguments in the definitions below are real. In radiusMap and extendedCost, w is a function from the reals to the reals; in root, upperDiag and effect it is a real scalar. Division by zero and the real square root use their total real conventions: a zero denominator gives zero and the square root of a negative number is zero.

For spectralQFI, U is the eigenvector unitary chosen for the Hermitian matrix, and the lambda entries are its eigenvalues. The positivity proof is shown after a semicolon when its quantification matters. A prime denotes the real derivative. In the rank-two statement, the orthonormal basis is indexed by Fin 3 and its coordinate isometry is denoted O with subscript B.

**Definition 1.1 (Spectral SLD information).**

$$\begin{aligned}&\forall n\ \mathrm{finite},\ \rho,D\in\mathbb C^{n\times n},\ h:\operatorname{PSD}(\rho),\\&U=U_h,\quad M=U^*DU,\quad\operatorname{spectralQFI}(\rho,D;h)=\sum_{i\in n}\sum_{j\in n}\frac{2|M_{ij}|^2}{\lambda_i+\lambda_j}\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.spectralQFI` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spectral expression uses the chosen Hermitian eigenbasis and assigns zero to terms with zero denominator.

**Definition 1.2 (Guarded real infimum).**

$$\begin{aligned}&\forall S\subseteq\mathbb R,\quad\operatorname{guardedInfimum}(S)=\begin{cases}\operatorname{inf}S&S\neq\emptyset\ \land\ \operatorname{BddBelow}(S)\\0&\mathrm{otherwise}\end{cases}\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.guardedInfimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Real infimum with explicit nonempty and bounded-below guard.

**Definition 1.3 (Canonical density-state bridge).**

$$\begin{aligned}&\forall M\in\mathbb C^{2\times2},\ h:\operatorname{PSD}(M),\ h_t:\operatorname{tr}(M)=1,\\&\operatorname{densityBridge}(M,h,h_t)\in\{r\in\mathcal D_2\mid\operatorname{mat}(r)=M\}\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.densityBridge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bridge constructs the canonical density state represented by the given positive trace-one matrix; its subtype includes the exact recovered-matrix equality.

**Definition 1.4 (Full actual program class).**

$$\begin{aligned}&\forall m\in\mathbb N,\ p,v:J_m\to\mathbb R,\ R,Q\in\mathbb R,\ N:J_m\to\mathbb C^{2\times2},\ \rho:\mathbb R\to\mathbb C^{2\times2},\ I\subseteq\mathbb R,\\&\operatorname{IsProgram}(p,v,R,N,\rho,I,Q)\ \Leftrightarrow\\&\operatorname{Open}(I)\land\operatorname{Preconnected}(I)\land[-R,R]\subseteq I\\&\land\ (\forall j\in J_m,\operatorname{PSD}(N_j))\land\sum_{j\in J_m}N_j=1_2\land\rho\in C^1(I)\\&\land\ (\forall u\in I,\operatorname{PSD}(\rho(u))\land\operatorname{tr}(\rho(u))=1\land\rho(u)^2=\rho(u)\\&\qquad\land\exists r\in\mathcal D_2,\operatorname{mat}(r)=\rho(u))\\&\land\ (\forall u\in I,\forall j\in J_m,\operatorname{tr}(N_j\rho(u))=p_j+uv_j\land0<p_j+uv_j)\\&\land\ (\forall h:\operatorname{PSD}(\rho(0)),\operatorname{spectralQFI}(\rho(0),\rho'(0);h)=Q)\end{aligned}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.IsProgram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate quantifies the full finite measurement and pure-curve data. The interval contains the closed radius interval, and the Born equation is an equality in the complex numbers with the real affine value embedded in them. The final clause quantifies over every proof of positivity at zero, exactly as displayed, even for arbitrary real R.

**Definition 1.5 (Attainable actual costs).**

$$\operatorname{costs}(p,v,R)=\{Q\in\mathbb R\mid\exists N,\rho,I,\operatorname{IsProgram}(p,v,R,N,\rho,I,Q)\}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.costs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set ranges over all actual programs in the preceding class.

**Definition 1.6 (Cost infimum).**

$$C_2(p,v,R)=\operatorname{guardedInfimum}(\operatorname{costs}(p,v,R))$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.C2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

C2 applies the guarded infimum to the attainable cost set; when the guard fails its value is zero.

**Definition 1.7 (Bloch vector).**

$$\operatorname{bloch}(M)=(2\operatorname{Re}M_{01},-2\mathrm{Im}M_{01},\operatorname{Re}M_{00}-\operatorname{Re}M_{11})\in\mathbb R^3$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.bloch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three real Bloch coordinates of a two by two matrix.

**Definition 1.8 (Bloch matrix).**

$$\operatorname{blochMatrix}(a,r)=\frac12\begin{pmatrix}a+r_2&r_0-\mathrm{i}r_1\\ r_0+\mathrm{i}r_1&a-r_2\end{pmatrix}\quad(a\in\mathbb R,\ r\in\mathbb R^3)$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Hermitian matrix with a specified real trace and Bloch vector.

**Definition 1.9 (Visible readout map).**

$$\operatorname{effectReadout}(N):\mathbb R^3\to\mathbb R^{J_m},\quad\operatorname{effectReadout}(N)(r)_j=\frac{\langle\operatorname{bloch}(N_j),r\rangle}{2}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.effectReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear part of the finite measurement readout sends a Bloch vector to its pairings with the effect vectors.

**Definition 1.10 (Orthogonal change of Bloch coordinates).**

$$\operatorname{reframe}(O,M)=\operatorname{blochMatrix}(\operatorname{Re}\operatorname{tr}(M),O(\operatorname{bloch}(M)))\quad(O:\mathbb R^3\equiv\mathbb R^3\ \mathrm{orthogonal})$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.reframe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An orthogonal change of the Bloch vector preserves the trace coordinate.

**Definition 1.11 (Linear Bloch map).**

$$\operatorname{blochLinear}:\mathbb C^{2\times2}\to_{\mathbb R}\mathbb R^3,\quad\operatorname{blochLinear}(M)=\operatorname{bloch}(M)$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Bloch coordinates form a real linear map on complex matrices.

**Definition 1.12 (Linear change of matrix coordinates).**

$$\operatorname{reframeLinear}(O):\mathbb C^{2\times2}\to_{\mathbb R}\mathbb C^{2\times2},\quad\operatorname{reframeLinear}(O)(M)=\operatorname{reframe}(O,M)$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.reframeLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A fixed orthogonal Bloch frame induces a real linear map on matrices.

**Definition 1.13 (Small quadratic root).**

$$\operatorname{root}(p,d,\alpha,e,w)=\frac{2(1-e)w^2d^2}{p-\alpha ewd+\sqrt{(p-\alpha ewd)^2-4e(1-e)w^2d^2}}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rationalized small root gives the lower diagonal effect coefficient, including zero individual scores.

**Definition 1.14 (Radius map).**

$$\operatorname{radiusMap}(B,\alpha,w)(t)=\frac{(2t\sqrt{1-t^2}-|\alpha|t^2)w(t^2)}{(1+t)\sqrt B}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.radiusMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This real function converts an arc parameter into a radius for the effect-family statement.

**Definition 1.15 (Extended family cost).**

$$\operatorname{extendedCost}(B,\alpha,w)(e)=\frac{B}{w(e)^2}\frac{4(1-e)}{4(1-e)-\alpha^2e}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.extendedCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cost formula extends through the zero transverse parameter for the normalization branch.

**Definition 1.16 (Upper diagonal coefficient).**

$$\operatorname{upperDiag}(p,d,\alpha,e,w)=\frac{p-\alpha ewd+\sqrt{(p-\alpha ewd)^2-4e(1-e)w^2d^2}}{2(1-e)}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.upperDiag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complementary quadratic root determines the upper diagonal effect coefficient.

**Definition 1.17 (Actual effect matrix).**

$$\operatorname{effect}(p,d,\alpha,e,w)=\begin{pmatrix}\operatorname{upperDiag}(p,d,\alpha,e,w)&wd\\ wd&\operatorname{root}(p,d,\alpha,e,w)\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.effect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two diagonal coefficients and the normalized direction determine each effect matrix.

**Definition 1.18 (Pure-state arc).**

$$\operatorname{arc}(e,x,c,u)=\operatorname{blochMatrix}(1,(x+cu,\sqrt{4e(1-e)-(x+cu)^2},1-2e))$$

*Formalization.* `D5/S3/Quantum/Information/ActualPureQubitGeometry.arc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Bloch curve has one affine coordinate, one square-root coordinate, and one constant coordinate.

**Theorem 1.19 (Actual rank-two arc and feasible coefficients).**

$$\begin{aligned}&\forall m\in\mathbb N,\ N:J_m\to\mathbb C^{2\times2},\ \rho:\mathbb R\to\mathbb C^{2\times2},\ p,v:J_m\to\mathbb R,\ I\subseteq\mathbb R,\\&\operatorname{Open}(I)\land\operatorname{Preconnected}(I)\land0\in I\land v\neq0\\&\land\ (\forall j\in J_m,\operatorname{PSD}(N_j))\land\sum_{j\in J_m}N_j=1_2\land\rho\in C^1(I)\\&\land\ (\forall u\in I,\operatorname{PSD}(\rho(u))\land\operatorname{tr}(\rho(u))=1\land\rho(u)^2=\rho(u))\\&\land\ (\forall u\in I,\forall j\in J_m,\operatorname{Re}\operatorname{tr}(N_j\rho(u))=p_j+uv_j)\\&\land\operatorname{rank}_{\mathbb R}(\operatorname{effectReadout}(N))=2\\&\longrightarrow\exists\mathcal B\ \mathrm{orthonormal\ basis\ of}\ \mathbb R^3,\ \exists x,c,\varepsilon,s\in\mathbb R,\ \exists A,q,b:J_m\to\mathbb R,\\&0<c\land0<\varepsilon\land\varepsilon\le\frac12\land(s=1\lor s=-1)\\&\land\ (\forall j\in J_m,\ 0\le q_j\land0\le A_j\land b_j^2\le A_jq_j\land b_j=v_j/c\land A_j=(p_j-b_jx-\varepsilon q_j)/(1-\varepsilon))\\&\land\sum_{j\in J_m}q_j=1\\&\land\ (\forall u\in I,\operatorname{reframe}(O_{\mathcal B},\rho(u))=\operatorname{blochMatrix}(1,(x+cu,s\sqrt{4\varepsilon(1-\varepsilon)-(x+cu)^2},1-2\varepsilon)))\\&\land\ (\forall u\in I,(x+cu)^2<4\varepsilon(1-\varepsilon))\\&\land\ (\forall R\in\mathbb R,\ 0\le R\land[-R,R]\subseteq I\longrightarrow|x|+cR<\sqrt{4\varepsilon(1-\varepsilon)})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitGeometry.actual_rank_two_parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The basis supplies a fixed coordinate frame. The coefficients and the signed square-root coordinate satisfy exactly the conjunction below; the last bound holds for every nonnegative radius whose closed interval lies in I.

## References

- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.C2`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.IsProgram`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.actual_rank_two_parameters`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.arc`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.bloch`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochLinear`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.blochMatrix`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.costs`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.densityBridge`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.effect`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.effectReadout`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.extendedCost`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.guardedInfimum`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.radiusMap`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.reframe`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.reframeLinear`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.root`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.spectralQFI`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitGeometry.upperDiag`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
