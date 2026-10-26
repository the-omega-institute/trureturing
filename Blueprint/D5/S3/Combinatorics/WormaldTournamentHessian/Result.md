# Wormald's tournament Hessian

## Abstract

The determinant polynomial and analytic Hessian of a regular tournament.

**Definition 1.1 (Regular tournaments).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \operatorname {IsRegularTournament}\left(A\right) = \left((\forall i \in \operatorname {Fin}\left(d\right),\; A\left(i, i\right) = false) \land ((\forall i \in \operatorname {Fin}\left(d\right),\; \forall j \in \operatorname {Fin}\left(d\right),\; (i \ne j) \Rightarrow ((A\left(i, j\right) = true) \Leftrightarrow (A\left(j, i\right) = false))) \land (\exists r \in \mathbb {N},\; \forall i \in \operatorname {Fin}\left(d\right),\; \sum_{j: \operatorname {Fin}\left(d\right)} \operatorname {ite}\left(A\left(i, j\right) = true, 1, 0\right) = r))\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Result.IsRegularTournament` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

The adjacency is Boolean. Each diagonal entry is false, and for distinct vertices exactly one direction is true. The out-degree is the same natural number at every vertex. No oddness hypothesis is added.

**Definition 1.2 (The integral adjacency matrix).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall i \in \operatorname {Fin}\left(d\right),\; \forall j \in \operatorname {Fin}\left(d\right),\; \operatorname {adjacency}\left(A, i, j\right) = \operatorname {ite}\left(A\left(i, j\right) = true, 1, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Result.adjacency` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

True edges have integral entry one and false edges have integral entry zero.

**Definition 1.3 (The skew adjacency matrix).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \operatorname {skewAdjacency}\left(A\right) = \operatorname {adjacency}\left(A\right) - \operatorname {Matrix.transpose}\left(\operatorname {adjacency}\left(A\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Result.skewAdjacency` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

The integral matrix S is A minus its transpose. It has zero diagonal and entries in {−1,0,1}.

**Definition 1.4 (The expansion point).**

$$\forall d \in \mathbb {N},\; \operatorname {z}\left(d\right) = \frac{2}{d}$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Result.z` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

The source defines z=2/d and the constant vector with this coordinate. Only d at least three enters the conjecture.

**Definition 1.5 (The determinant polynomial).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall y \in \operatorname {Fin}\left(d\right) \to \mathbb {C},\; \operatorname {K}\left(A, y\right) = \operatorname {Matrix.det}\left(1 - \left(\frac{1}{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {adjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \cdot \operatorname {Matrix.diagonal}\left(y\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Result.K` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

Section 1 defines B=I−(½I+A)Dᵧ and K(y)=det B. The map Int.castRingHom embeds the integral adjacency into the complex numbers. Matrix multiplication retains the source's column scaling by y.

**Definition 1.6 (The final implicit coordinate).**

$$\forall d \in \mathbb {N},\; \forall y \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C},\; \forall t \in \mathbb {C},\; \forall i \in \operatorname {Fin}\left(d\right),\; \operatorname {appendLast}\left(y, t, i\right) = \operatorname {Fin.snoc}\left(y, t, \operatorname {Fin.ofNat}\left(\operatorname {Nat.sub}\left(d, 1\right) + 1, \operatorname {Fin.val}\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Result.appendLast` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

Fin.snoc appends the scalar after the first d−1 coordinates. The index is lifted by its natural value to Fin((d−1)+1); for d positive this is the order-preserving identification with Fin d. The case d=0 has no indices.

**Definition 1.7 (A complex C2 local solution).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \operatorname {IsLocalSolution}\left(A, h\right) = \left((h\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right)\right) = \operatorname {z}\left(d\right)) \land ((\operatorname {ContDiffAt}\left(\mathbb {C}, 2, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right)\right)) \land (\operatorname {Filter.Eventually}\left((y: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\mapsto \operatorname {K}\left(A, \operatorname {appendLast}\left(y, h\left(y\right)\right)\right) = 0), \operatorname {nhds}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right)\right)\right)))\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Result.IsLocalSolution` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

Section 1: “one may solve K(y)=0 in the neighbourhood of z and obtain y_d=h(y_1,…,y_{d−1})”. The definition specifies h(z′)=z, ContDiffAt over the complex scalar field of order two, and an equation holding eventually in the neighbourhood filter at z′. It imposes no global equation on h.

**Definition 1.8 (Real angular coordinates).**

$$\forall d \in \mathbb {N},\; \forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall theta \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {R},\; \operatorname {phase}\left(h, theta\right) = \operatorname {Complex.log}\left(h\left((j: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right)\mapsto \operatorname {z}\left(d\right) \cdot \operatorname {Complex.exp}\left(\operatorname {Complex.I} \cdot theta\left(j\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Result.phase` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

Section 1 defines f̃(θ)=log h(ze^{iθ₁},…,ze^{iθ_{d−1}}). Complex.log is the principal logarithm. Its argument at zero is the positive real number z when h is a local solution and d is at least three.

**Definition 1.9 (The real angular Hessian).**

$$\forall d \in \mathbb {N},\; \forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall j \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \forall k \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \operatorname {hessian}\left(h, j, k\right) = \operatorname {fderiv}\left(\mathbb {R}, (theta: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {R}\mapsto \operatorname {fderiv}\left(\mathbb {R}, \operatorname {phase}\left(h\right), theta, \operatorname {Pi.single}\left(j, 1\right)\right)), 0, \operatorname {Pi.single}\left(k, 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Result.hessian` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

The entry in row j and column k differentiates θ↦fderiv ℝ (phase h) θ (Pi.single j 1) once more over ℝ in the direction Pi.single k 1, at θ=0. Thus the definition uses fderiv of fderiv and keeps the complex-valued output.

**Definition 1.10 (The Hessian determinant).**

$$\forall d \in \mathbb {N},\; \forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \operatorname {calH}\left(h\right) = \operatorname {Matrix.det}\left(\operatorname {hessian}\left(h\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Result.calH` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

Section 1 lets “H denote the determinant of the Hessian … of f̃ at θ_j=0”. The determinant has d−1 rows and columns.

**Definition 1.11 (Conjecture 6 with local existence).**

$$claim = \left(\forall d \in \mathbb {N},\; (3 \le d) \Rightarrow (\forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow ((\exists h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \operatorname {IsLocalSolution}\left(A, h\right)) \land (\forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; (\operatorname {IsLocalSolution}\left(A, h\right)) \Rightarrow ((\operatorname {calH}\left(h\right) \ne 0) \land (\exists q \in \mathbb {Q},\; \frac{d}{\operatorname {calH}\left(h\right)} = \operatorname {Rat.cast}\left(q\right)^{2})))))\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Result.claim` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

Section 1: “Conjecture 6. For every regular tournament $T^{*}$ on at least three vertices, $\mathcal {H} \ne 0$ and $\frac{d}{\mathcal {H}}$ is the square of a rational.”

The supplied source excerpt does not identify a printed page number. The formula includes existence of a complex C2 local solution and the same conclusion for every such solution. The rational is embedded into ℂ before squaring. The theorem result proves this full statement with the stated analytic definitions.

**Theorem 1.12 (The skew diagonal vanishes).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall i \in \operatorname {Fin}\left(d\right),\; \operatorname {skewAdjacency}\left(A, i, i\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.skewDiag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting a matrix from its transpose cancels the diagonal. This identifies the diagonal of each shifted matrix.

**Theorem 1.13 (Skew entries are bounded by one).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall i \in \operatorname {Fin}\left(d\right),\; \forall j \in \operatorname {Fin}\left(d\right),\; \operatorname {Norm.norm}\left(\operatorname {Int.castRingHom}\left(\mathbb {C}\right)\left(\operatorname {skewAdjacency}\left(A, i, j\right)\right)\right) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.skewNormLe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A difference of Boolean adjacency entries is −1, zero or one. Its complex norm is at most one.

**Theorem 1.14 (Strict diagonal dominance).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall c \in \mathbb {C},\; (\operatorname {Norm.norm}\left(c\right) = d) \Rightarrow (\operatorname {Matrix.det}\left(\operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) + c\cdot (1)\right) \ne 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.shiftedDetNeZero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal has norm d and the sum of the other entry norms in each row is at most d−1. Gershgorin's strict diagonal-dominance consequence gives a nonzero determinant. No tournament or parity assumption is needed.

**Theorem 1.15 (The imaginary shift in odd dimension).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {Odd}\left(d\right)) \Rightarrow (\operatorname {Complex.re}\left(\operatorname {Matrix.det}\left(\operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) + \operatorname {Complex.I} \cdot d\cdot (1)\right)\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.shiftedDetPureImaginary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shifted matrix is skew Hermitian. Conjugating its determinant multiplies it by −1 in odd dimension, so the real part vanishes.

**Theorem 1.16 (The imaginary determinant has integral coefficient).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {Odd}\left(d\right)) \Rightarrow (\exists b \in \mathbb {Z},\; \operatorname {Matrix.det}\left(\operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) + \operatorname {Complex.I} \cdot d\cdot (1)\right) = \operatorname {Int.cast}\left(b\right) \cdot \operatorname {Complex.I})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.imaginaryShiftIntegral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every entry of the imaginary shift is a Gaussian integer. Its determinant is a Gaussian integer with real part zero, and therefore equals bi for an integer b.

**Theorem 1.17 (The determinant quotient is rational).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {Odd}\left(d\right)) \Rightarrow (\exists q \in \mathbb {Q},\; (q \ne 0) \land (\frac{\operatorname {Matrix.det}\left(d\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)}{\frac{\operatorname {Matrix.det}\left(\operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) + \operatorname {Complex.I} \cdot d\cdot (1)\right)}{\operatorname {Complex.I}}} = \operatorname {Rat.cast}\left(q\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.algebraicRatioRational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real shift is an integral matrix. The imaginary-shift determinant divided by i is also an integer. Strict diagonal dominance makes both integers nonzero; their quotient supplies a nonzero rational.

**Theorem 1.18 (The degree and order identity).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\exists r \in \mathbb {N},\; (d = 2 \cdot r + 1) \land (\forall i \in \operatorname {Fin}\left(d\right),\; \sum_{j: \operatorname {Fin}\left(d\right)} \operatorname {adjacency}\left(A, i, j\right) = \operatorname {Nat.cast}\left(r\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularDegree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the common out-degree is r, counting both orientations gives 2dr=d(d−1). Positivity of d gives d=2r+1, and every integral adjacency row sums to r.

**Theorem 1.19 (Regular tournaments have odd order).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\operatorname {Odd}\left(d\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularOdd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every out-degree is r, summing the two orientations of each off-diagonal pair gives 2dr=d(d−1). Since d is positive, d=2r+1.

**Theorem 1.20 (A quotient of quadratic determinants is a rational square).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {Odd}\left(d\right)) \Rightarrow (\exists q \in \mathbb {Q},\; (q \ne 0) \land (\frac{\operatorname {Matrix.det}\left(d^{2}\cdot (1) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) \cdot \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)}{\operatorname {Matrix.det}\left(d^{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) \cdot \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)} = \operatorname {Rat.cast}\left(q\right)^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.algebraicSquareIdentity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transposition identifies the determinants of dI+S and dI−S. Factoring d²I−S² gives the square of the first determinant. Factoring d²I+S² and using odd dimension gives the square of det(S+idI)/i. Thus the quotient is the square of the previously constructed rational. The theorem calH_closedForm identifies this quotient with d divided by the analytic Hessian determinant.

**Theorem 1.21 (The algebraic square for regular tournaments).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\exists q \in \mathbb {Q},\; (q \ne 0) \land (\frac{\operatorname {Matrix.det}\left(d^{2}\cdot (1) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) \cdot \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)}{\operatorname {Matrix.det}\left(d^{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) \cdot \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)} = \operatorname {Rat.cast}\left(q\right)^{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularAlgebraicSquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Oddness of a regular tournament supplies the hypothesis of the quadratic determinant identity. The theorem calH_closedForm supplies the analytic identification, and regularLocalSolution supplies the required existence.

**Theorem 1.22 (The determinant vanishes at the expansion point).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\operatorname {K}\left(A, \operatorname {Function.const}\left(\operatorname {Fin}\left(d\right), \operatorname {z}\left(d\right)\right)\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.determinantAtBase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant vector one is in the kernel of I−(½I+A)D_z: each row of ½I+A sums to d/2. Hence its determinant is zero.

**Theorem 1.23 (Smoothness of the determinant polynomial).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \operatorname {ContDiff}\left(\mathbb {C}, 2, \operatorname {K}\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.polynomialSmooth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The permutation expansion of the determinant expresses K as a finite sum of products of affine coordinate functions. It is complex C2 everywhere.

**Theorem 1.24 (A local solution from the implicit function theorem).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow ((\operatorname {ContinuousLinearMap.IsInvertible}\left(\operatorname {ContinuousLinearMap.comp}\left(\operatorname {fderiv}\left(\mathbb {C}, (p: \operatorname {Prod}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}, \mathbb {C}\right)\mapsto \operatorname {K}\left(A, \operatorname {appendLast}\left(\operatorname {Prod.fst}\left(p\right), \operatorname {Prod.snd}\left(p\right)\right)\right)), \operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right), \operatorname {ContinuousLinearMap.inr}\left(\mathbb {C}, \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}, \mathbb {C}\right)\right)\right)) \Rightarrow (\exists h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \operatorname {IsLocalSolution}\left(A, h\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.localSolutionOfInvertible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the final-coordinate derivative at the expansion point is invertible, the complex implicit function theorem gives a C2 local solution. The zero value follows from the preceding determinant identity. This statement retains the invertibility hypothesis.

## Coordinate derivatives and local existence

**Theorem 1.25 (Appending coordinates is complex linear).**

$$\forall d \in \mathbb {N},\; \forall p \in \operatorname {Prod}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}, \mathbb {C}\right),\; \operatorname {appendLastLinear}\left(d\right)\left(p\right) = \operatorname {appendLast}\left(\operatorname {Prod.fst}\left(p\right), \operatorname {Prod.snd}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.appendLastLinearApply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The continuous complex linear map appendLastLinear appends the second component after the coordinates of the first component.

**Theorem 1.26 (Changing the final coordinate).**

$$\forall d \in \mathbb {N},\; (1 \le d) \Rightarrow (\forall t \in \mathbb {C},\; \operatorname {appendLast}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), t\right) = \operatorname {Function.update}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(d\right), \operatorname {z}\left(d\right)\right), \operatorname {Fin.mk}\left(d - 1\right), t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.appendLast_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive d, appending t to the constant vector replaces precisely the coordinate with natural value d minus one.

**Theorem 1.27 (Differentiating a single column).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall B \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall j \in iota,\; \forall u \in iota \to \mathbb {C},\; \forall v \in iota \to \mathbb {C},\; \forall t \in \mathbb {C},\; \operatorname {HasDerivAt}\left((s: \mathbb {C}\mapsto \operatorname {Matrix.det}\left(\operatorname {Matrix.updateCol}\left(B, j, u + s\cdot (v)\right)\right)), \operatorname {Matrix.det}\left(\operatorname {Matrix.updateCol}\left(B, j, v\right)\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.determinant_column_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multilinearity makes the determinant affine in the scalar multiplying one column. Its derivative is the determinant with that column replaced by its direction.

**Theorem 1.28 (A coordinate derivative of K).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall y \in \operatorname {Fin}\left(d\right) \to \mathbb {C},\; \forall j \in \operatorname {Fin}\left(d\right),\; \forall t \in \mathbb {C},\; \operatorname {HasDerivAt}\left((s: \mathbb {C}\mapsto \operatorname {K}\left(A, \operatorname {Function.update}\left(y, j, s\right)\right)), -\operatorname {Matrix.det}\left(\operatorname {Matrix.updateCol}\left(1 - \left(\frac{1}{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {adjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \cdot \operatorname {Matrix.diagonal}\left(y\right), j, (i: \operatorname {Fin}\left(d\right)\mapsto \left(\frac{1}{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {adjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)\left(i, j\right))\right)\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.K_coordinate_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative in coordinate j is minus the determinant obtained by replacing column j of the defining matrix by column j of one half I plus A. This holds at every y.

**Theorem 1.29 (Invertibility in one complex dimension).**

$$\forall L \in \operatorname {ContinuousLinearMap}\left(\mathbb {C}, \mathbb {C}, \mathbb {C}\right),\; (L\left(1\right) \ne 0) \Rightarrow (\operatorname {ContinuousLinearMap.IsInvertible}\left(L\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.scalar_map_invertible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complex linear map on the scalar field multiplies by its value at one. The reciprocal scalar defines a continuous linear inverse when that value is nonzero.

**Theorem 1.30 (A nonzero scalar partial derivative).**

$$\forall E \in Type,\; \forall group \in \operatorname {NormedAddCommGroup}\left(E\right),\; \forall space \in \operatorname {NormedSpace}\left(\mathbb {C}, E\right),\; \forall F \in \operatorname {Prod}\left(E, \mathbb {C}\right) \to \mathbb {C},\; \forall y \in E,\; \forall t \in \mathbb {C},\; \forall c \in \mathbb {C},\; (\operatorname {DifferentiableAt}\left(\mathbb {C}, F, \operatorname {Prod.mk}\left(y, t\right)\right)) \Rightarrow ((\operatorname {HasDerivAt}\left((s: \mathbb {C}\mapsto F\left(\operatorname {Prod.mk}\left(y, s\right)\right)), c, t\right)) \Rightarrow ((c \ne 0) \Rightarrow (\operatorname {ContinuousLinearMap.IsInvertible}\left(\operatorname {ContinuousLinearMap.comp}\left(\operatorname {fderiv}\left(\mathbb {C}, F, \operatorname {Prod.mk}\left(y, t\right)\right), \operatorname {ContinuousLinearMap.inr}\left(\mathbb {C}, E, \mathbb {C}\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.scalar_partial_invertible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composing the full derivative with the inclusion of the scalar coordinate gives a complex linear map whose value at one is the scalar partial derivative.

**Theorem 1.31 (The rank-one determinant identity).**

$$\forall d \in \mathbb {N},\; \forall Q \in \operatorname {Matrix}\left(\operatorname {Fin}\left(d\right), \operatorname {Fin}\left(d\right), \mathbb {C}\right),\; (\operatorname {Matrix.det}\left(Q\right) \ne 0) \Rightarrow (\operatorname {Matrix.det}\left(Q - \operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(d\right)\mapsto (j: \operatorname {Fin}\left(d\right)\mapsto 1))\right)\right) = \operatorname {Matrix.det}\left(Q\right) \cdot \left(1 - \sum_{i: \operatorname {Fin}\left(d\right)} \sum_{j: \operatorname {Fin}\left(d\right)} \operatorname {Inv.inv}\left(Q\right)\left(i, j\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.det_rank_one_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix determinant lemma evaluates subtraction of the all-ones matrix. Its correction factor is one minus the sum of all entries of the inverse.

**Theorem 1.32 (Completeness and skew adjacency).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (2\cdot (\frac{1}{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {adjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)) = \operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(d\right)\mapsto (j: \operatorname {Fin}\left(d\right)\mapsto 1))\right) + \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.tournamentCoefficientIdentity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tournament completeness gives twice the coefficient matrix as the sum of the all-ones matrix and the skew adjacency matrix.

**Theorem 1.33 (A resolvent factorization of K).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\forall y \in \operatorname {Fin}\left(d\right) \to \mathbb {C},\; (\forall j \in \operatorname {Fin}\left(d\right),\; y\left(j\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {Matrix.diagonal}\left((j: \operatorname {Fin}\left(d\right)\mapsto \frac{2}{y\left(j\right)})\right) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \ne 0) \Rightarrow (\operatorname {K}\left(A, y\right) = \operatorname {Matrix.det}\left(\operatorname {Matrix.diagonal}\left((j: \operatorname {Fin}\left(d\right)\mapsto \frac{2}{y\left(j\right)})\right) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \cdot \left(1 - \sum_{i: \operatorname {Fin}\left(d\right)} \sum_{j: \operatorname {Fin}\left(d\right)} \operatorname {Inv.inv}\left(\operatorname {Matrix.diagonal}\left((j: \operatorname {Fin}\left(d\right)\mapsto \frac{2}{y\left(j\right)})\right) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)\left(i, j\right)\right) \cdot \prod_{j: \operatorname {Fin}\left(d\right)} \frac{y\left(j\right)}{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.K_resolvent_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every coordinate and the resolvent determinant are nonzero, factor the defining matrix as the resolvent minus the all-ones matrix, followed by the diagonal matrix with entries y divided by two. The rank-one determinant identity then gives this formula.

**Theorem 1.34 (The equation as an inverse-entry sum).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\forall y \in \operatorname {Fin}\left(d\right) \to \mathbb {C},\; (\forall j \in \operatorname {Fin}\left(d\right),\; y\left(j\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {Matrix.diagonal}\left((j: \operatorname {Fin}\left(d\right)\mapsto \frac{2}{y\left(j\right)})\right) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \ne 0) \Rightarrow ((\operatorname {K}\left(A, y\right) = 0) \Leftrightarrow (\sum_{i: \operatorname {Fin}\left(d\right)} \sum_{j: \operatorname {Fin}\left(d\right)} \operatorname {Inv.inv}\left(\operatorname {Matrix.diagonal}\left((j: \operatorname {Fin}\left(d\right)\mapsto \frac{2}{y\left(j\right)})\right) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)\left(i, j\right) = 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.K_eq_zero_iff_resolvent_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonzero determinant and coordinate-product factors can be cancelled. Thus K vanishes exactly when the sum of all entries of the resolvent inverse equals one.

**Theorem 1.35 (The inverse-entry equation near the base point).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; (\operatorname {IsLocalSolution}\left(A, h\right)) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {Matrix.diagonal}\left((j: \operatorname {Fin}\left(d\right)\mapsto \frac{2}{\operatorname {Function.const}\left(\operatorname {Fin}\left(d\right), \operatorname {z}\left(d\right)\right)\left(j\right)})\right) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \ne 0) \Rightarrow (\operatorname {Filter.Eventually}\left((y: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\mapsto \sum_{i: \operatorname {Fin}\left(d\right)} \sum_{j: \operatorname {Fin}\left(d\right)} \operatorname {Inv.inv}\left(\operatorname {Matrix.diagonal}\left((j: \operatorname {Fin}\left(d\right)\mapsto \frac{2}{\operatorname {appendLast}\left(y, h\left(y\right)\right)\left(j\right)})\right) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)\left(i, j\right) = 1), \operatorname {nhds}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.localSolution_resolvent_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity keeps the coordinates and the resolvent determinant nonzero near the base point. Every C2 local solution therefore satisfies the inverse-entry equation on a neighbourhood.

**Theorem 1.36 (Existence of the analytic local solution).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\exists h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \operatorname {IsLocalSolution}\left(A, h\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularLocalSolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact coordinate derivative is nonzero by strict diagonal dominance of the shifted skew adjacency matrix. Its scalar continuous linear derivative is invertible, so the complex implicit function theorem gives the required C2 local solution.

## Cofactors and the nonzero coordinate derivative

**Theorem 1.37 (The determinant of a constant perturbation).**

$$\forall n \in \mathbb {N},\; \forall c \in \mathbb {C},\; \operatorname {Matrix.det}\left(1 + \operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(n\right)\mapsto (j: \operatorname {Fin}\left(n\right)\mapsto c))\right)\right) = 1 + \operatorname {Nat.cast}\left(n\right) \cdot c$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.det_const_perturb` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix determinant lemma reduces a constant perturbation of the identity to one scalar. The determinant is one plus the sum of the constant diagonal contributions.

**Theorem 1.38 (A column replacement in the constant-vector projection).**

$$\forall n \in \mathbb {N},\; \forall l \in \operatorname {Fin}\left(n + 1\right),\; \forall v \in \operatorname {Fin}\left(n + 1\right) \to \mathbb {C},\; \operatorname {Matrix.det}\left(\operatorname {Matrix.updateCol}\left(1 - \operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(n + 1\right)\mapsto (j: \operatorname {Fin}\left(n + 1\right)\mapsto \frac{1}{\operatorname {Nat.cast}\left(n\right) + 1}))\right), l, v\right)\right) = \frac{\sum_{i: \operatorname {Fin}\left(n + 1\right)} v\left(i\right)}{\operatorname {Nat.cast}\left(n\right) + 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.det_projection_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P=I−J/(n+1), where every entry of J is one. Replacing column l by v gives determinant equal to the sum of the coordinates of v divided by n+1. Summing the rows and expanding the resulting sparse row leaves a principal minor with determinant 1/(n+1).

**Theorem 1.39 (A cofactor of a centered doubly stochastic matrix).**

$$\forall n \in \mathbb {N},\; \forall l \in \operatorname {Fin}\left(n + 1\right),\; \forall A \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n + 1\right), \operatorname {Fin}\left(n + 1\right), \mathbb {C}\right),\; (\operatorname {Matrix.det}\left(A\right) \ne 0) \Rightarrow ((\forall i \in \operatorname {Fin}\left(n + 1\right),\; \sum_{j: \operatorname {Fin}\left(n + 1\right)} A\left(i, j\right) = 1) \Rightarrow ((\forall j \in \operatorname {Fin}\left(n + 1\right),\; \sum_{i: \operatorname {Fin}\left(n + 1\right)} A\left(i, j\right) = 1) \Rightarrow (\operatorname {Matrix.det}\left(\operatorname {Matrix.updateCol}\left(A - \operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(n + 1\right)\mapsto (j: \operatorname {Fin}\left(n + 1\right)\mapsto \frac{1}{\operatorname {Nat.cast}\left(n\right) + 1}))\right), l, \operatorname {Pi.single}\left(l, 1\right)\right)\right) = \frac{\operatorname {Matrix.det}\left(A\right)}{\operatorname {Nat.cast}\left(n\right) + 1})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.det_doubly_stochastic_cofactor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An invertible complex matrix whose rows and columns sum to one factors its centered matrix as A(I−J/(n+1)). The inverse image of the lth coordinate vector has coordinate sum one. The projection column formula therefore gives det A divided by n+1.

**Theorem 1.40 (A cofactor of a matrix with zero row and column sums).**

$$\forall n \in \mathbb {N},\; \forall l \in \operatorname {Fin}\left(n + 1\right),\; \forall B \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n + 1\right), \operatorname {Fin}\left(n + 1\right), \mathbb {C}\right),\; (\operatorname {Matrix.det}\left(B + \operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(n + 1\right)\mapsto (j: \operatorname {Fin}\left(n + 1\right)\mapsto \frac{1}{\operatorname {Nat.cast}\left(n\right) + 1}))\right)\right) \ne 0) \Rightarrow ((\forall i \in \operatorname {Fin}\left(n + 1\right),\; \sum_{j: \operatorname {Fin}\left(n + 1\right)} B\left(i, j\right) = 0) \Rightarrow ((\forall j \in \operatorname {Fin}\left(n + 1\right),\; \sum_{i: \operatorname {Fin}\left(n + 1\right)} B\left(i, j\right) = 0) \Rightarrow (\operatorname {Matrix.det}\left(\operatorname {Matrix.updateCol}\left(B, l, \operatorname {Pi.single}\left(l, 1\right)\right)\right) = \frac{\operatorname {Matrix.det}\left(B + \operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(n + 1\right)\mapsto (j: \operatorname {Fin}\left(n + 1\right)\mapsto \frac{1}{\operatorname {Nat.cast}\left(n\right) + 1}))\right)\right)}{\operatorname {Nat.cast}\left(n\right) + 1})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.cofactor_eq_of_zero_sums` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding J/(n+1) to B changes every row and column sum from zero to one. If the resulting determinant is nonzero, each diagonal cofactor of B equals that determinant divided by n+1.

**Theorem 1.41 (The common first-coordinate determinant coefficient).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\forall l \in \operatorname {Fin}\left(d\right),\; \operatorname {Matrix.det}\left(\operatorname {Matrix.updateCol}\left(1 - \left(\frac{1}{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {adjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \cdot \operatorname {Matrix.diagonal}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(d\right), \operatorname {z}\left(d\right)\right)\right), l, (i: \operatorname {Fin}\left(d\right)\mapsto \left(\frac{1}{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {adjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)\left(i, l\right))\right)\right) = \frac{\operatorname {Matrix.det}\left(\operatorname {Nat.cast}\left(d\right)\cdot (1) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)}{2 \cdot \operatorname {Nat.cast}\left(d\right)^{d}}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularColumnSlopeValue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put C=½I+A and B=I−CD_z. Regularity gives zero row and column sums for B and the factorization B+J/d=(dI−S)/d. Every determinant obtained by replacing column l of B with column l of C equals det(dI−S)/(2d^d), independently of l. The coordinate derivative of K is the negative of this column replacement determinant.

**Theorem 1.42 (Regular skew adjacency has zero row sums).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\forall i \in \operatorname {Fin}\left(d\right),\; \sum_{j: \operatorname {Fin}\left(d\right)} \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\left(i, j\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularSkewRowSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pair completeness and constant out-degree imply the same in-degree at every vertex. Subtracting the transpose therefore gives zero in every skew adjacency row sum.

**Theorem 1.43 (Regular skew adjacency has zero column sums).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\forall j \in \operatorname {Fin}\left(d\right),\; \sum_{i: \operatorname {Fin}\left(d\right)} \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\left(i, j\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularSkewColSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Skew symmetry identifies each column sum with the negative of the corresponding row sum. The zero row sums thus give zero column sums as well.

**Theorem 1.44 (The negative skew shift is nonsingular).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \operatorname {Matrix.det}\left(\operatorname {Nat.cast}\left(d\right)\cdot (1) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.shiftedNegativeDetNeZero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix dI−S is the transpose of S+dI. Its determinant equals the nonzero determinant furnished by strict diagonal dominance. This assertion does not require tournament regularity.

## Second derivatives of implicit phases

**Theorem 1.45 (The second derivative of a composition).**

$$\forall kappa \in Type,\; \forall fieldNorm \in \operatorname {NontriviallyNormedField}\left(kappa\right),\; \forall E \in Type,\; \forall EAdd \in \operatorname {NormedAddCommGroup}\left(E\right),\; \forall ESpace \in \operatorname {NormedSpace}\left(kappa, E\right),\; \forall F \in Type,\; \forall FAdd \in \operatorname {NormedAddCommGroup}\left(F\right),\; \forall FSpace \in \operatorname {NormedSpace}\left(kappa, F\right),\; \forall G \in Type,\; \forall GAdd \in \operatorname {NormedAddCommGroup}\left(G\right),\; \forall GSpace \in \operatorname {NormedSpace}\left(kappa, G\right),\; \forall f \in E \to F,\; \forall g \in F \to G,\; \forall x \in E,\; \forall v \in E,\; \forall w \in E,\; (\operatorname {ContDiffAt}\left(kappa, 2, f, x\right)) \Rightarrow ((\operatorname {ContDiffAt}\left(kappa, 2, g, f\left(x\right)\right)) \Rightarrow (\operatorname {second}\left(kappa, \operatorname {Function.comp}\left(g, f\right), x, v, w\right) = \operatorname {second}\left(kappa, g, f\left(x\right), \operatorname {fderiv}\left(kappa, f, x, v\right), \operatorname {fderiv}\left(kappa, f, x, w\right)\right) + \operatorname {fderiv}\left(kappa, g, f\left(x\right), \operatorname {second}\left(kappa, f, x, v, w\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write second(f,x,v,w) for the derivative in direction w of y mapped to Df(y)v. The chain rule gives the outer second derivative on the two inner velocities, plus the outer first derivative on the inner acceleration.

**Theorem 1.46 (A zero germ has zero second derivative).**

$$\forall kappa \in Type,\; \forall fieldNorm \in \operatorname {NontriviallyNormedField}\left(kappa\right),\; \forall E \in Type,\; \forall EAdd \in \operatorname {NormedAddCommGroup}\left(E\right),\; \forall ESpace \in \operatorname {NormedSpace}\left(kappa, E\right),\; \forall F \in Type,\; \forall FAdd \in \operatorname {NormedAddCommGroup}\left(F\right),\; \forall FSpace \in \operatorname {NormedSpace}\left(kappa, F\right),\; \forall f \in E \to F,\; \forall x \in E,\; \forall v \in E,\; \forall w \in E,\; (\operatorname {Filter.EventuallyEq}\left(\operatorname {nhds}\left(x\right), f, (y: E\mapsto 0)\right)) \Rightarrow (\operatorname {second}\left(kappa, f, x, v, w\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_eq_zero_of_eventually` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A function agreeing with zero on a neighbourhood has the same first and second Frechet derivatives as zero. No separate smoothness hypothesis is needed for this germ equality.

**Theorem 1.47 (The second derivative of a graph).**

$$\forall kappa \in Type,\; \forall fieldNorm \in \operatorname {NontriviallyNormedField}\left(kappa\right),\; \forall E \in Type,\; \forall EAdd \in \operatorname {NormedAddCommGroup}\left(E\right),\; \forall ESpace \in \operatorname {NormedSpace}\left(kappa, E\right),\; \forall F \in Type,\; \forall FAdd \in \operatorname {NormedAddCommGroup}\left(F\right),\; \forall FSpace \in \operatorname {NormedSpace}\left(kappa, F\right),\; \forall h \in E \to F,\; \forall x \in E,\; \forall v \in E,\; \forall w \in E,\; (\operatorname {ContDiffAt}\left(kappa, 2, h, x\right)) \Rightarrow (\operatorname {second}\left(kappa, (y: E\mapsto \operatorname {Prod.mk}\left(y, h\left(y\right)\right)), x, v, w\right) = \operatorname {Prod.mk}\left(0, \operatorname {second}\left(kappa, h, x, v, w\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity coordinate has zero acceleration, while the final coordinate has the second derivative of h.

**Theorem 1.48 (First differentiation of an implicit equation).**

$$\forall kappa \in Type,\; \forall fieldNorm \in \operatorname {NontriviallyNormedField}\left(kappa\right),\; \forall E \in Type,\; \forall EAdd \in \operatorname {NormedAddCommGroup}\left(E\right),\; \forall ESpace \in \operatorname {NormedSpace}\left(kappa, E\right),\; \forall F \in Type,\; \forall FAdd \in \operatorname {NormedAddCommGroup}\left(F\right),\; \forall FSpace \in \operatorname {NormedSpace}\left(kappa, F\right),\; \forall G \in Type,\; \forall GAdd \in \operatorname {NormedAddCommGroup}\left(G\right),\; \forall GSpace \in \operatorname {NormedSpace}\left(kappa, G\right),\; \forall h \in E \to F,\; \forall F0 \in \operatorname {Prod}\left(E, F\right) \to G,\; \forall x \in E,\; (\operatorname {ContDiffAt}\left(kappa, 2, h, x\right)) \Rightarrow ((\operatorname {ContDiffAt}\left(kappa, 2, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right)\right)) \Rightarrow ((\operatorname {Filter.EventuallyEq}\left(\operatorname {nhds}\left(x\right), \operatorname {Function.comp}\left(F0, (y: E\mapsto \operatorname {Prod.mk}\left(y, h\left(y\right)\right))\right), (y: E\mapsto 0)\right)) \Rightarrow (\forall v \in E,\; \operatorname {fderiv}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(v, \operatorname {fderiv}\left(kappa, h, x, v\right)\right)\right) = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.implicit_first_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative of a constant zero germ vanishes. Applying the chain rule to the graph y mapped to (y,h(y)) gives the first implicit derivative equation.

**Theorem 1.49 (Second differentiation of an implicit equation).**

$$\forall kappa \in Type,\; \forall fieldNorm \in \operatorname {NontriviallyNormedField}\left(kappa\right),\; \forall E \in Type,\; \forall EAdd \in \operatorname {NormedAddCommGroup}\left(E\right),\; \forall ESpace \in \operatorname {NormedSpace}\left(kappa, E\right),\; \forall F \in Type,\; \forall FAdd \in \operatorname {NormedAddCommGroup}\left(F\right),\; \forall FSpace \in \operatorname {NormedSpace}\left(kappa, F\right),\; \forall G \in Type,\; \forall GAdd \in \operatorname {NormedAddCommGroup}\left(G\right),\; \forall GSpace \in \operatorname {NormedSpace}\left(kappa, G\right),\; \forall h \in E \to F,\; \forall F0 \in \operatorname {Prod}\left(E, F\right) \to G,\; \forall x \in E,\; (\operatorname {ContDiffAt}\left(kappa, 2, h, x\right)) \Rightarrow ((\operatorname {ContDiffAt}\left(kappa, 2, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right)\right)) \Rightarrow ((\operatorname {Filter.EventuallyEq}\left(\operatorname {nhds}\left(x\right), \operatorname {Function.comp}\left(F0, (y: E\mapsto \operatorname {Prod.mk}\left(y, h\left(y\right)\right))\right), (y: E\mapsto 0)\right)) \Rightarrow (\forall v \in E,\; \forall w \in E,\; \operatorname {second}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(v, \operatorname {fderiv}\left(kappa, h, x, v\right)\right), \operatorname {Prod.mk}\left(w, \operatorname {fderiv}\left(kappa, h, x, w\right)\right)\right) + \operatorname {fderiv}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(0, \operatorname {second}\left(kappa, h, x, v, w\right)\right)\right) = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.implicit_second_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiating the zero germ twice gives the outer second derivative on graph tangent vectors, plus the final-coordinate derivative applied to the acceleration of h.

**Theorem 1.50 (Solving the first implicit derivative equation).**

$$\forall kappa \in Type,\; \forall fieldNorm \in \operatorname {NontriviallyNormedField}\left(kappa\right),\; \forall E \in Type,\; \forall EAdd \in \operatorname {NormedAddCommGroup}\left(E\right),\; \forall ESpace \in \operatorname {NormedSpace}\left(kappa, E\right),\; \forall h \in E \to kappa,\; \forall F0 \in \operatorname {Prod}\left(E, kappa\right) \to kappa,\; \forall x \in E,\; (\operatorname {ContDiffAt}\left(kappa, 2, h, x\right)) \Rightarrow ((\operatorname {ContDiffAt}\left(kappa, 2, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right)\right)) \Rightarrow ((\operatorname {Filter.EventuallyEq}\left(\operatorname {nhds}\left(x\right), \operatorname {Function.comp}\left(F0, (y: E\mapsto \operatorname {Prod.mk}\left(y, h\left(y\right)\right))\right), (y: E\mapsto 0)\right)) \Rightarrow ((\operatorname {fderiv}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(0, 1\right)\right) \ne 0) \Rightarrow (\forall v \in E,\; \operatorname {fderiv}\left(kappa, h, x, v\right) = \frac{0 - \operatorname {fderiv}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(v, 0\right)\right)}{\operatorname {fderiv}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(0, 1\right)\right)}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.implicit_first_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a scalar final coordinate, a nonzero final partial derivative permits division. The derivative of h is the negative ratio of the two partial derivatives.

**Theorem 1.51 (Solving the second implicit derivative equation).**

$$\forall kappa \in Type,\; \forall fieldNorm \in \operatorname {NontriviallyNormedField}\left(kappa\right),\; \forall E \in Type,\; \forall EAdd \in \operatorname {NormedAddCommGroup}\left(E\right),\; \forall ESpace \in \operatorname {NormedSpace}\left(kappa, E\right),\; \forall h \in E \to kappa,\; \forall F0 \in \operatorname {Prod}\left(E, kappa\right) \to kappa,\; \forall x \in E,\; (\operatorname {ContDiffAt}\left(kappa, 2, h, x\right)) \Rightarrow ((\operatorname {ContDiffAt}\left(kappa, 2, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right)\right)) \Rightarrow ((\operatorname {Filter.EventuallyEq}\left(\operatorname {nhds}\left(x\right), \operatorname {Function.comp}\left(F0, (y: E\mapsto \operatorname {Prod.mk}\left(y, h\left(y\right)\right))\right), (y: E\mapsto 0)\right)) \Rightarrow ((\operatorname {fderiv}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(0, 1\right)\right) \ne 0) \Rightarrow (\forall v \in E,\; \forall w \in E,\; \operatorname {second}\left(kappa, h, x, v, w\right) = \frac{0 - \operatorname {second}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(v, \operatorname {fderiv}\left(kappa, h, x, v\right)\right), \operatorname {Prod.mk}\left(w, \operatorname {fderiv}\left(kappa, h, x, w\right)\right)\right)}{\operatorname {fderiv}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(0, 1\right)\right)}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.implicit_second_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second derivative of h is the negative outer second derivative on graph tangent vectors divided by the final partial derivative.

**Theorem 1.52 (Constants do not affect second derivatives).**

$$\forall kappa \in Type,\; \forall fieldNorm \in \operatorname {NontriviallyNormedField}\left(kappa\right),\; \forall E \in Type,\; \forall EAdd \in \operatorname {NormedAddCommGroup}\left(E\right),\; \forall ESpace \in \operatorname {NormedSpace}\left(kappa, E\right),\; \forall F \in Type,\; \forall FAdd \in \operatorname {NormedAddCommGroup}\left(F\right),\; \forall FSpace \in \operatorname {NormedSpace}\left(kappa, F\right),\; \forall f \in E \to F,\; \forall c \in F,\; \forall x \in E,\; \forall v \in E,\; \forall w \in E,\; \operatorname {second}\left(kappa, (y: E\mapsto f\left(y\right) - c), x, v, w\right) = \operatorname {second}\left(kappa, f, x, v, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_sub_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting a constant leaves both derivatives unchanged.

**Theorem 1.53 (Second derivatives under a linear change of variables).**

$$\forall kappa \in Type,\; \forall fieldNorm \in \operatorname {NontriviallyNormedField}\left(kappa\right),\; \forall E \in Type,\; \forall EAdd \in \operatorname {NormedAddCommGroup}\left(E\right),\; \forall ESpace \in \operatorname {NormedSpace}\left(kappa, E\right),\; \forall F \in Type,\; \forall FAdd \in \operatorname {NormedAddCommGroup}\left(F\right),\; \forall FSpace \in \operatorname {NormedSpace}\left(kappa, F\right),\; \forall G \in Type,\; \forall GAdd \in \operatorname {NormedAddCommGroup}\left(G\right),\; \forall GSpace \in \operatorname {NormedSpace}\left(kappa, G\right),\; \forall L \in \operatorname {ContinuousLinearMap}\left(kappa, E, F\right),\; \forall f \in F \to G,\; \forall x \in E,\; \forall v \in E,\; \forall w \in E,\; (\operatorname {ContDiffAt}\left(kappa, 2, f, L\left(x\right)\right)) \Rightarrow (\operatorname {second}\left(kappa, \operatorname {Function.comp}\left(f, L\right), x, v, w\right) = \operatorname {second}\left(kappa, f, L\left(x\right), L\left(v\right), L\left(w\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_comp_clm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A continuous linear inner map has zero second derivative. Its two images are the directions supplied to the outer second derivative.

**Theorem 1.54 (The bilinear second derivative).**

$$\forall n \in \mathbb {N},\; \forall f \in \left(\operatorname {Fin}\left(n\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall x \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, f, x\right)) \Rightarrow (\forall v \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall w \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \operatorname {second}\left(\mathbb {C}, f, x, v, w\right) = \operatorname {fderiv}\left(\mathbb {C}, \operatorname {fderiv}\left(\mathbb {C}, f\right), x, w, v\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_eq_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex C2 function, differentiating its derivative and then evaluating in v gives the same directional second derivative. This expression is complex bilinear in v and w.

**Theorem 1.55 (Bilinearity on difference directions).**

$$\forall n \in \mathbb {N},\; \forall f \in \left(\operatorname {Fin}\left(n\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall x \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, f, x\right)) \Rightarrow (\forall a \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall b \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall c \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall d0 \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \operatorname {second}\left(\mathbb {C}, f, x, a - b, c - d0\right) = \operatorname {second}\left(\mathbb {C}, f, x, a, c\right) - \operatorname {second}\left(\mathbb {C}, f, x, a, d0\right) - \operatorname {second}\left(\mathbb {C}, f, x, b, c\right) + \operatorname {second}\left(\mathbb {C}, f, x, b, d0\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_sub_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding both difference directions gives the four terms of a two-coordinate minor.

**Theorem 1.56 (Restriction from complex to real derivatives).**

$$\forall n \in \mathbb {N},\; \forall f \in \left(\operatorname {Fin}\left(n\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall x \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, f, x\right)) \Rightarrow (\forall v \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall w \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \operatorname {second}\left(\mathbb {R}, f, x, v, w\right) = \operatorname {second}\left(\mathbb {C}, f, x, v, w\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_complex_to_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real derivative of a complex differentiable function is the scalar restriction of its complex derivative. Applying the same fact to the first derivative proves equality of the two second directional derivatives on complex vectors regarded as real vectors.

**Theorem 1.57 (The angular substitution negates the Hessian).**

$$\forall n \in \mathbb {N},\; \forall f \in \left(\operatorname {Fin}\left(n\right) \to \mathbb {C}\right) \to \mathbb {C},\; (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, f, 0\right)) \Rightarrow (\forall j \in \operatorname {Fin}\left(n\right),\; \forall k \in \operatorname {Fin}\left(n\right),\; \operatorname {second}\left(\mathbb {R}, (theta: \operatorname {Fin}\left(n\right) \to \mathbb {R}\mapsto f\left(\operatorname {angularMap}\left(theta\right)\right)), 0, \operatorname {Pi.single}\left(j, 1\right), \operatorname {Pi.single}\left(k, 1\right)\right) = 0 - \operatorname {second}\left(\mathbb {C}, f, 0, \operatorname {Pi.single}\left(j, 1\right), \operatorname {Pi.single}\left(k, 1\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_angular_substitution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real angular map sends each coordinate vector to i times the corresponding complex vector. Complex bilinearity contributes i squared, hence a factor of minus one.

**Theorem 1.58 (Smoothness in logarithmic coordinates).**

$$\forall n \in \mathbb {N},\; \forall a \in \mathbb {C},\; \forall h \in \left(\operatorname {Fin}\left(n\right) \to \mathbb {C}\right) \to \mathbb {C},\; (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right)\right)) \Rightarrow ((\operatorname {Membership.mem}\left(h\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right)\right), \operatorname {Complex.slitPlane}\right)) \Rightarrow (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, \operatorname {logarithmicPhase}\left(a, h\right), 0\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.logarithmicPhase_smooth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential coordinate map is entire. If h is complex C2 at the constant point and its value lies in the slit plane, composition with the principal logarithm is complex C2 at zero.

**Theorem 1.59 (The first derivative of exponential coordinates).**

$$\forall n \in \mathbb {N},\; \forall a \in \mathbb {C},\; \forall u \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall v \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \operatorname {fderiv}\left(\mathbb {C}, \operatorname {exponentialChart}\left(a\right), u, v\right) = (j: \operatorname {Fin}\left(n\right)\mapsto a \cdot \operatorname {Complex.exp}\left(u\left(j\right)\right) \cdot v\left(j\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.fderiv_exponentialChart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate map u_j mapped to a exp(u_j) has derivative a exp(u_j) v_j in direction v.

**Theorem 1.60 (The second derivative of exponential coordinates).**

$$\forall n \in \mathbb {N},\; \forall a \in \mathbb {C},\; \forall v \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall w \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \operatorname {second}\left(\mathbb {C}, \operatorname {exponentialChart}\left(a\right), 0, v, w\right) = (j: \operatorname {Fin}\left(n\right)\mapsto a \cdot v\left(j\right) \cdot w\left(j\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_exponentialChart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero, the second derivative in directions v and w has coordinate a v_j w_j.

**Theorem 1.61 (The second derivative of a logarithm).**

$$\forall n \in \mathbb {N},\; \forall g \in \left(\operatorname {Fin}\left(n\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall x \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, g, x\right)) \Rightarrow ((\operatorname {Membership.mem}\left(g\left(x\right), \operatorname {Complex.slitPlane}\right)) \Rightarrow (\forall v \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall w \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \operatorname {second}\left(\mathbb {C}, (y: \operatorname {Fin}\left(n\right) \to \mathbb {C}\mapsto \operatorname {Complex.log}\left(g\left(y\right)\right)), x, v, w\right) = \left(0 - \operatorname {Inv.inv}\left(g\left(x\right)^{2}\right)\right) \cdot \operatorname {fderiv}\left(\mathbb {C}, g, x, w\right) \cdot \operatorname {fderiv}\left(\mathbb {C}, g, x, v\right) + \operatorname {Inv.inv}\left(g\left(x\right)\right) \cdot \operatorname {second}\left(\mathbb {C}, g, x, v, w\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_clog` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative of log(g) is g inverse times Dg. The product rule gives g inverse times the second derivative, minus the product of the two first derivatives divided by g squared.

**Theorem 1.62 (The logarithmic-coordinate Hessian).**

$$\forall n \in \mathbb {N},\; \forall a \in \mathbb {C},\; \forall h \in \left(\operatorname {Fin}\left(n\right) \to \mathbb {C}\right) \to \mathbb {C},\; (a \ne 0) \Rightarrow ((\operatorname {ContDiffAt}\left(\mathbb {C}, 2, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right)\right)) \Rightarrow ((h\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right)\right) = a) \Rightarrow ((\operatorname {Membership.mem}\left(a, \operatorname {Complex.slitPlane}\right)) \Rightarrow (\forall j \in \operatorname {Fin}\left(n\right),\; \forall k \in \operatorname {Fin}\left(n\right),\; \operatorname {second}\left(\mathbb {C}, \operatorname {logarithmicPhase}\left(a, h\right), 0, \operatorname {Pi.single}\left(j, 1\right), \operatorname {Pi.single}\left(k, 1\right)\right) = a \cdot \operatorname {second}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right), \operatorname {Pi.single}\left(j, 1\right), \operatorname {Pi.single}\left(k, 1\right)\right) + \operatorname {ite}\left(j = k, \operatorname {fderiv}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right), \operatorname {Pi.single}\left(j, 1\right)\right), 0\right) - \operatorname {fderiv}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right), \operatorname {Pi.single}\left(j, 1\right)\right) \cdot \operatorname {fderiv}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right), \operatorname {Pi.single}\left(k, 1\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.logarithmicPhase_second` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At h(a,...,a)=a, the exponential and logarithm chain rules give a times the second derivative of h, the diagonal first-derivative term, and minus the product of first derivatives.

**Theorem 1.63 (The angular Hessian in derivatives of the local solution).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; (3 \le d) \Rightarrow ((\operatorname {IsLocalSolution}\left(A, h\right)) \Rightarrow (\forall j \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \forall k \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \operatorname {hessian}\left(h, j, k\right) = \operatorname {fderiv}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {Pi.single}\left(j, 1\right)\right) \cdot \operatorname {fderiv}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {Pi.single}\left(k, 1\right)\right) - \operatorname {z}\left(d\right) \cdot \operatorname {second}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {Pi.single}\left(j, 1\right), \operatorname {Pi.single}\left(k, 1\right)\right) - \operatorname {ite}\left(j = k, \operatorname {fderiv}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {Pi.single}\left(j, 1\right)\right), 0\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.actual_hessian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local solution takes the positive real value z at the base point, so the principal logarithm is smooth there. Combining logarithmic coordinates with the angular substitution gives H_jk=h_j h_k-z h_jk-delta_jk h_j, with all derivatives of h taken over the complex numbers at the base point.

**Theorem 1.64 (The Hessian from a scalar implicit equation).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall L \in \operatorname {ContinuousLinearMap}\left(\mathbb {C}, \operatorname {Prod}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}, \mathbb {C}\right), \operatorname {Fin}\left(d\right) \to \mathbb {C}\right),\; \forall alpha \in \left(\operatorname {Fin}\left(d\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall c \in \mathbb {C},\; (3 \le d) \Rightarrow ((\operatorname {IsLocalSolution}\left(A, h\right)) \Rightarrow ((\operatorname {ContDiffAt}\left(\mathbb {C}, 2, alpha, L\left(\operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right)\right)) \Rightarrow ((\operatorname {Filter.EventuallyEq}\left(\operatorname {nhds}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right)\right), (y: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\mapsto alpha\left(L\left(\operatorname {Prod.mk}\left(y, h\left(y\right)\right)\right)\right)), (y: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\mapsto 1)\right)) \Rightarrow ((c \ne 0) \Rightarrow ((\forall j \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \operatorname {fderiv}\left(\mathbb {C}, alpha, L\left(\operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right), L\left(\operatorname {Prod.mk}\left(\operatorname {Pi.single}\left(j, 1\right), 0\right)\right)\right) = c) \Rightarrow ((\operatorname {fderiv}\left(\mathbb {C}, alpha, L\left(\operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right), L\left(\operatorname {Prod.mk}\left(0, 1\right)\right)\right) = c) \Rightarrow (\forall j \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \forall k \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \operatorname {hessian}\left(h, j, k\right) = 1 + \operatorname {ite}\left(j = k, 1, 0\right) + \frac{\operatorname {z}\left(d\right)}{c} \cdot \operatorname {second}\left(\mathbb {C}, alpha, L\left(\operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right), L\left(\operatorname {Prod.mk}\left(\operatorname {Pi.single}\left(j, 1\right), 0 - 1\right)\right), L\left(\operatorname {Prod.mk}\left(\operatorname {Pi.single}\left(k, 1\right), 0 - 1\right)\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.hessian_of_implicit_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a C2 scalar equation has a constant nonzero first partial c in every appended coordinate and is constant along the graph of h, then h_j=-1. The second implicit derivative and the angular formula give H_jk=1+delta_jk+(z/c) D2alpha(L(e_j,-1),L(e_k,-1)).

**Theorem 1.65 (The Hessian from the coordinate derivatives of the scalar equation).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall L \in \operatorname {ContinuousLinearMap}\left(\mathbb {C}, \operatorname {Prod}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}, \mathbb {C}\right), \operatorname {Fin}\left(d\right) \to \mathbb {C}\right),\; \forall alpha \in \left(\operatorname {Fin}\left(d\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall c \in \mathbb {C},\; \forall iota \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \operatorname {Fin}\left(d\right),\; \forall last \in \operatorname {Fin}\left(d\right),\; \forall M \in \operatorname {Matrix}\left(\operatorname {Fin}\left(d\right), \operatorname {Fin}\left(d\right), \mathbb {C}\right),\; (3 \le d) \Rightarrow ((\operatorname {IsLocalSolution}\left(A, h\right)) \Rightarrow ((\operatorname {ContDiffAt}\left(\mathbb {C}, 2, alpha, L\left(\operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right)\right)) \Rightarrow ((\operatorname {Filter.EventuallyEq}\left(\operatorname {nhds}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right)\right), (y: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\mapsto alpha\left(L\left(\operatorname {Prod.mk}\left(y, h\left(y\right)\right)\right)\right)), (y: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\mapsto 1)\right)) \Rightarrow ((c \ne 0) \Rightarrow ((\forall j \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; L\left(\operatorname {Prod.mk}\left(\operatorname {Pi.single}\left(j, 1\right), 0\right)\right) = \operatorname {Pi.single}\left(iota\left(j\right), 1\right)) \Rightarrow ((L\left(\operatorname {Prod.mk}\left(0, 1\right)\right) = \operatorname {Pi.single}\left(last, 1\right)) \Rightarrow ((\forall i \in \operatorname {Fin}\left(d\right),\; \operatorname {fderiv}\left(\mathbb {C}, alpha, L\left(\operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right), \operatorname {Pi.single}\left(i, 1\right)\right) = c) \Rightarrow ((\forall i \in \operatorname {Fin}\left(d\right),\; \forall l \in \operatorname {Fin}\left(d\right),\; \operatorname {second}\left(\mathbb {C}, alpha, L\left(\operatorname {Prod.mk}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {z}\left(d\right)\right)\right), \operatorname {Pi.single}\left(i, 1\right), \operatorname {Pi.single}\left(l, 1\right)\right) = M\left(i, l\right)) \Rightarrow (\forall j \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \forall k \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \operatorname {hessian}\left(h, j, k\right) = 1 + \operatorname {ite}\left(j = k, 1, 0\right) + \frac{\operatorname {z}\left(d\right)}{c} \cdot \left(M\left(iota\left(j\right), iota\left(k\right)\right) - M\left(iota\left(j\right), last\right) - M\left(last, iota\left(k\right)\right) + M\left(last, last\right)\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.hessian_of_implicit_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If M is the matrix of second complex partial derivatives of the scalar equation, the graph tangent vectors are coordinate differences. Bilinearity gives the four-entry difference M_jk-M_jd-M_dk+M_dd in the angular Hessian formula.

## Matrix inverses and determinant bridges

**Theorem 1.66 (The determinant of the difference-and-constant basis).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \operatorname {Matrix.det}\left(\operatorname {bridgeU}\right) = \operatorname {Nat.cast}\left(\operatorname {Fintype.card}\left(iota\right)\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.bridgeU_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix with identity upper-left block, an all-one final column and an all-minus-one final row has determinant card(iota)+1, by its scalar Schur complement.

**Theorem 1.67 (Difference-basis columns).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall i \in \operatorname {Sum}\left(iota, Unit\right),\; \forall j \in iota,\; \operatorname {bridgeU}\left(i, \operatorname {Sum.inl}\left(j\right)\right) = \operatorname {ite}\left(i = \operatorname {Sum.inl}\left(j\right), 1, 0\right) - \operatorname {ite}\left(i = \operatorname {Sum.inr}\left(\operatorname {Unit.unit}\right), 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.bridgeU_entry_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each initial column is the corresponding coordinate vector minus the final coordinate vector.

**Theorem 1.68 (The constant-basis column).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall i \in \operatorname {Sum}\left(iota, Unit\right),\; \operatorname {bridgeU}\left(i, \operatorname {Sum.inr}\left(\operatorname {Unit.unit}\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.bridgeU_entry_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The final column of the basis matrix is the constant vector one.

**Theorem 1.69 (The block diagonal congruence).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall T \in \operatorname {Matrix}\left(\operatorname {Sum}\left(iota, Unit\right), \operatorname {Sum}\left(iota, Unit\right), \mathbb {C}\right),\; (\forall i \in \operatorname {Sum}\left(iota, Unit\right),\; \sum_{l: \operatorname {Sum}\left(iota, Unit\right)} T\left(i, l\right) = 0 - 1) \Rightarrow ((\forall j \in \operatorname {Sum}\left(iota, Unit\right),\; \sum_{l: \operatorname {Sum}\left(iota, Unit\right)} T\left(l, j\right) = 0 - 1) \Rightarrow (\operatorname {Matrix.transpose}\left(\operatorname {bridgeU}\right) \cdot T \cdot \operatorname {bridgeU} = \operatorname {Matrix.fromBlocks}\left(\operatorname {bridgeH}\left(T\right), 0, 0, \operatorname {Matrix.of}\left((i: Unit\mapsto (k: Unit\mapsto 0 - \left(\operatorname {Nat.cast}\left(\operatorname {Fintype.card}\left(iota\right)\right) + 1\right)))\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.bridgeU_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every row and column sums to minus one, congruence by the difference-and-constant basis has vanishing off-diagonal blocks, difference minor in the initial block and final entry minus (card(iota)+1).

**Theorem 1.70 (The determinant of the difference minor).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall T \in \operatorname {Matrix}\left(\operatorname {Sum}\left(iota, Unit\right), \operatorname {Sum}\left(iota, Unit\right), \mathbb {C}\right),\; (\forall i \in \operatorname {Sum}\left(iota, Unit\right),\; \sum_{l: \operatorname {Sum}\left(iota, Unit\right)} T\left(i, l\right) = 0 - 1) \Rightarrow ((\forall j \in \operatorname {Sum}\left(iota, Unit\right),\; \sum_{l: \operatorname {Sum}\left(iota, Unit\right)} T\left(l, j\right) = 0 - 1) \Rightarrow (\operatorname {Matrix.det}\left(\operatorname {bridgeH}\left(T\right)\right) = \left(0 - \left(\operatorname {Nat.cast}\left(\operatorname {Fintype.card}\left(iota\right)\right) + 1\right)\right) \cdot \operatorname {Matrix.det}\left(T\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.bridge_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking determinants of the block congruence and cancelling the nonzero basis determinant gives det(H)=−(card(iota)+1)det(T).

**Theorem 1.71 (The determinant of the symmetric resolvent expression).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall c \in \mathbb {C},\; (\operatorname {Matrix.transpose}\left(S\right) = 0 - S) \Rightarrow ((\operatorname {Odd}\left(\operatorname {Fintype.card}\left(iota\right)\right)) \Rightarrow ((\operatorname {Matrix.det}\left(c\cdot (1) - S\right) \ne 0) \Rightarrow (\operatorname {Matrix.det}\left(1 - c\cdot (\operatorname {Inv.inv}\left(c\cdot (1) - S\right) + \operatorname {Matrix.transpose}\left(\operatorname {Inv.inv}\left(c\cdot (1) - S\right)\right))\right) = \frac{0 - \operatorname {Matrix.det}\left(c^{2}\cdot (1) + S \cdot S\right)}{\operatorname {Matrix.det}\left(c^{2}\cdot (1) - S \cdot S\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.skew_resolvent_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying T by (cI−S)(cI+S) gives −(c²I+S²). Transposition gives invertibility of both factors. Taking determinants in odd dimension yields the negative quadratic determinant quotient.

**Theorem 1.72 (The finite-coordinate difference determinant).**

$$\forall n \in \mathbb {N},\; \forall T \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n + 1\right), \operatorname {Fin}\left(n + 1\right), \mathbb {C}\right),\; (\forall i \in \operatorname {Fin}\left(n + 1\right),\; \sum_{l: \operatorname {Fin}\left(n + 1\right)} T\left(i, l\right) = 0 - 1) \Rightarrow ((\forall j \in \operatorname {Fin}\left(n + 1\right),\; \sum_{l: \operatorname {Fin}\left(n + 1\right)} T\left(l, j\right) = 0 - 1) \Rightarrow (\operatorname {Matrix.det}\left(\operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(n\right)\mapsto (k: \operatorname {Fin}\left(n\right)\mapsto T\left(\operatorname {Fin.castSucc}\left(i\right), \operatorname {Fin.castSucc}\left(k\right)\right) - T\left(\operatorname {Fin.castSucc}\left(i\right), \operatorname {Fin.last}\left(n\right)\right) - T\left(\operatorname {Fin.last}\left(n\right), \operatorname {Fin.castSucc}\left(k\right)\right) + T\left(\operatorname {Fin.last}\left(n\right), \operatorname {Fin.last}\left(n\right)\right)))\right)\right) = \left(0 - \left(\operatorname {Nat.cast}\left(n\right) + 1\right)\right) \cdot \operatorname {Matrix.det}\left(T\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.differenceMinor_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindexing the difference-minor identity onto Fin(n+1) gives the determinant formula with multiplier −(n+1).

**Theorem 1.73 (Constant row sums of the inverse).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall Q \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall c \in \mathbb {C},\; (c \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(Q\right) \ne 0) \Rightarrow ((\forall i \in iota,\; \sum_{l: iota} Q\left(i, l\right) = c) \Rightarrow (\forall i \in iota,\; \sum_{l: iota} \operatorname {Inv.inv}\left(Q\right)\left(i, l\right) = \operatorname {Inv.inv}\left(c\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverse_row_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If Q maps the constant vector one to c times that vector, its inverse maps one to c inverse times one.

**Theorem 1.74 (Constant column sums of the inverse).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall Q \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall c \in \mathbb {C},\; (c \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(Q\right) \ne 0) \Rightarrow ((\forall j \in iota,\; \sum_{l: iota} Q\left(l, j\right) = c) \Rightarrow (\forall j \in iota,\; \sum_{l: iota} \operatorname {Inv.inv}\left(Q\right)\left(l, j\right) = \operatorname {Inv.inv}\left(c\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverse_col_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the row-sum identity to the transpose gives the corresponding column sums of the inverse.

**Theorem 1.75 (The resolvent expression has sums minus one).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall Q \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall c \in \mathbb {C},\; (c \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(Q\right) \ne 0) \Rightarrow ((\forall i \in iota,\; \sum_{l: iota} Q\left(i, l\right) = c) \Rightarrow ((\forall j \in iota,\; \sum_{l: iota} Q\left(l, j\right) = c) \Rightarrow ((\forall i \in iota,\; \sum_{l: iota} \left(1 - c\cdot (\operatorname {Inv.inv}\left(Q\right) + \operatorname {Matrix.transpose}\left(\operatorname {Inv.inv}\left(Q\right)\right))\right)\left(i, l\right) = 0 - 1) \land (\forall j \in iota,\; \sum_{l: iota} \left(1 - c\cdot (\operatorname {Inv.inv}\left(Q\right) + \operatorname {Matrix.transpose}\left(\operatorname {Inv.inv}\left(Q\right)\right))\right)\left(l, j\right) = 0 - 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.resolvent_row_col_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two inverse sums each contribute c inverse. Subtracting c times their sum from the identity leaves row and column sums equal to minus one.

**Theorem 1.76 (The determinant quotient for the difference minor).**

$$\forall n \in \mathbb {N},\; \forall S \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n + 1\right), \operatorname {Fin}\left(n + 1\right), \mathbb {C}\right),\; \forall c \in \mathbb {C},\; (c \ne 0) \Rightarrow ((\operatorname {Matrix.transpose}\left(S\right) = 0 - S) \Rightarrow ((\operatorname {Odd}\left(n + 1\right)) \Rightarrow ((\operatorname {Matrix.det}\left(c\cdot (1) - S\right) \ne 0) \Rightarrow ((\forall i \in \operatorname {Fin}\left(n + 1\right),\; \sum_{l: \operatorname {Fin}\left(n + 1\right)} S\left(i, l\right) = 0) \Rightarrow (\operatorname {Matrix.det}\left(\operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(n\right)\mapsto (k: \operatorname {Fin}\left(n\right)\mapsto \left(1 - c\cdot (\operatorname {Inv.inv}\left(c\cdot (1) - S\right) + \operatorname {Matrix.transpose}\left(\operatorname {Inv.inv}\left(c\cdot (1) - S\right)\right))\right)\left(\operatorname {Fin.castSucc}\left(i\right), \operatorname {Fin.castSucc}\left(k\right)\right) - \left(1 - c\cdot (\operatorname {Inv.inv}\left(c\cdot (1) - S\right) + \operatorname {Matrix.transpose}\left(\operatorname {Inv.inv}\left(c\cdot (1) - S\right)\right))\right)\left(\operatorname {Fin.castSucc}\left(i\right), \operatorname {Fin.last}\left(n\right)\right) - \left(1 - c\cdot (\operatorname {Inv.inv}\left(c\cdot (1) - S\right) + \operatorname {Matrix.transpose}\left(\operatorname {Inv.inv}\left(c\cdot (1) - S\right)\right))\right)\left(\operatorname {Fin.last}\left(n\right), \operatorname {Fin.castSucc}\left(k\right)\right) + \left(1 - c\cdot (\operatorname {Inv.inv}\left(c\cdot (1) - S\right) + \operatorname {Matrix.transpose}\left(\operatorname {Inv.inv}\left(c\cdot (1) - S\right)\right))\right)\left(\operatorname {Fin.last}\left(n\right), \operatorname {Fin.last}\left(n\right)\right)))\right)\right) = \frac{\left(\operatorname {Nat.cast}\left(n\right) + 1\right) \cdot \operatorname {Matrix.det}\left(c^{2}\cdot (1) + S \cdot S\right)}{\operatorname {Matrix.det}\left(c^{2}\cdot (1) - S \cdot S\right)})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.skew_difference_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero row sums of a skew matrix also give zero column sums. The resolvent expression therefore has sums minus one, and its difference-minor determinant is (n+1)det(c²I+S²)/det(c²I−S²).

**Theorem 1.77 (Differentiating matrix inversion).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall Q \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; (\operatorname {Matrix.det}\left(Q\right) \ne 0) \Rightarrow (\operatorname {HasFDerivAt}\left(\mathbb {C}, (M: \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right)\mapsto \operatorname {Inv.inv}\left(M\right)), 0 - \operatorname {ContinuousLinearMap.mulLeftRight}\left(\mathbb {C}, \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right), \operatorname {Inv.inv}\left(Q\right), \operatorname {Inv.inv}\left(Q\right)\right), Q\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.matrixInverse_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an invertible complex matrix Q, the derivative of inversion maps H to −Q inverse H Q inverse. The matrix operator norm permits direct application of the normed-algebra inverse theorem.

**Theorem 1.78 (Differentiating the diagonal resolvent).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow (\operatorname {HasFDerivAt}\left(\mathbb {C}, \operatorname {inverseQ}\left(S\right), \operatorname {inverseQDeriv}\left(y\right), y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverseQ_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each diagonal entry 2/y_j has derivative −2v_j/y_j². The off-diagonal skew matrix is constant.

**Theorem 1.79 (Differentiating the inverse resolvent).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\operatorname {HasFDerivAt}\left(\mathbb {C}, (u: iota \to \mathbb {C}\mapsto \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, u\right)\right)), \operatorname {ContinuousLinearMap.comp}\left(0 - \operatorname {ContinuousLinearMap.mulLeftRight}\left(\mathbb {C}, \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right), \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right), \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\right), \operatorname {inverseQDeriv}\left(y\right)\right), y\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverse_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chain rule composes the diagonal resolvent derivative with the derivative of matrix inversion.

**Theorem 1.80 (Differentiating the inverse-entry sum).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\operatorname {HasFDerivAt}\left(\mathbb {C}, \operatorname {alpha}\left(S\right), \operatorname {ContinuousLinearMap.comp}\left(\operatorname {sumEntriesCLM}, \operatorname {ContinuousLinearMap.comp}\left(0 - \operatorname {ContinuousLinearMap.mulLeftRight}\left(\mathbb {C}, \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right), \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right), \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\right), \operatorname {inverseQDeriv}\left(y\right)\right)\right), y\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.alpha_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing all matrix entries is a continuous linear functional, so its composition with the inverse resolvent has the indicated derivative.

**Theorem 1.81 (Smoothness of the diagonal resolvent).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, \operatorname {inverseQ}\left(S\right), y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverseQ_contDiffAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonzero coordinate hypothesis makes each reciprocal coordinate complex C2. Diagonal embedding and subtraction preserve this regularity.

**Theorem 1.82 (Smoothness of the inverse resolvent).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, (u: iota \to \mathbb {C}\mapsto \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, u\right)\right)), y\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverse_contDiffAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inversion is analytic on the units of a complex normed algebra. The nonzero determinant hypothesis allows composition with the C2 diagonal resolvent.

**Theorem 1.83 (Smoothness of the scalar inverse-entry equation).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, \operatorname {alpha}\left(S\right), y\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.alpha_contDiffAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of inverse entries is complex C2 wherever all coordinates and the resolvent determinant are nonzero.

**Theorem 1.84 (A single-coordinate diagonal derivative).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall y \in iota \to \mathbb {C},\; \forall j \in iota,\; \operatorname {inverseQDeriv}\left(y\right)\left(\operatorname {Pi.single}\left(j, 1\right)\right) = \frac{0 - 2}{y\left(j\right)^{2}}\cdot (\operatorname {Matrix.diagonal}\left(\operatorname {Pi.single}\left(j, 1\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverseQDeriv_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the diagonal resolvent derivative on a coordinate vector gives a diagonal matrix supported at that coordinate.

**Theorem 1.85 (A single-coordinate inverse derivative).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\forall j \in iota,\; \operatorname {fderiv}\left(\mathbb {C}, (u: iota \to \mathbb {C}\mapsto \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, u\right)\right)), y, \operatorname {Pi.single}\left(j, 1\right)\right) = \frac{2}{y\left(j\right)^{2}}\cdot (\operatorname {Matrix.of}\left((i: iota\mapsto (k: iota\mapsto \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(i, j\right) \cdot \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(j, k\right)))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverse_fderiv_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The jth partial derivative of the inverse matrix is 2/y_j² times the outer product of its jth column and jth row.

**Theorem 1.86 (Differentiating an inverse row sum).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\forall j \in iota,\; \forall k \in iota,\; \operatorname {fderiv}\left(\mathbb {C}, (u: iota \to \mathbb {C}\mapsto \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, u\right)\right)\left(j, l\right)), y, \operatorname {Pi.single}\left(k, 1\right)\right) = \frac{2}{y\left(k\right)^{2}} \cdot \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(j, k\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(k, l\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.row_fderiv_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the single-coordinate inverse derivative across a row gives 2V_jk/y_k² times the kth inverse row sum.

**Theorem 1.87 (Differentiating an inverse column sum).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\forall j \in iota,\; \forall k \in iota,\; \operatorname {fderiv}\left(\mathbb {C}, (u: iota \to \mathbb {C}\mapsto \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, u\right)\right)\left(l, j\right)), y, \operatorname {Pi.single}\left(k, 1\right)\right) = \frac{2}{y\left(k\right)^{2}} \cdot \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(k, j\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(l, k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.col_fderiv_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the single-coordinate inverse derivative down a column gives 2V_kj/y_k² times the kth inverse column sum.

**Theorem 1.88 (First partials of the scalar inverse-entry equation).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\forall j \in iota,\; \operatorname {fderiv}\left(\mathbb {C}, \operatorname {alpha}\left(S\right), y, \operatorname {Pi.single}\left(j, 1\right)\right) = \frac{2}{y\left(j\right)^{2}} \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(j, l\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(l, j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.alpha_fderiv_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first partial is 2/y_j² times the product of the jth inverse row and column sums.

**Theorem 1.89 (The derivative of a reciprocal square).**

$$\forall t \in \mathbb {C},\; (t \ne 0) \Rightarrow (\operatorname {HasDerivAt}\left(\mathbb {C}, (u: \mathbb {C}\mapsto \frac{2}{u^{2}}), \frac{0 - 4}{t^{3}}, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverse_square_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scalar function 2/t² has derivative −4/t³ at every nonzero complex number.

**Theorem 1.90 (Second partials of the scalar inverse-entry equation).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\forall j \in iota,\; \forall k \in iota,\; \operatorname {fderiv}\left(\mathbb {C}, (u: iota \to \mathbb {C}\mapsto \operatorname {fderiv}\left(\mathbb {C}, \operatorname {alpha}\left(S\right), u, \operatorname {Pi.single}\left(j, 1\right)\right)), y, \operatorname {Pi.single}\left(k, 1\right)\right) = \frac{0 - 4}{y\left(j\right)^{3}} \cdot \operatorname {ite}\left(k = j, 1, 0\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(j, l\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(l, j\right) + \frac{4}{y\left(j\right)^{2} \cdot y\left(k\right)^{2}} \cdot \left(\operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(j, k\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(k, l\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(l, j\right) + \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(k, j\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(j, l\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(l, k\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.alpha_second_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first-partial formula holds on a neighbourhood where coordinates and determinant remain nonzero. Differentiating that equality uses the reciprocal-square derivative and the inverse row and column derivatives, producing the displayed second partial.

**Theorem 1.91 (Equal first partials at a balanced constant point).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall b \in \mathbb {C},\; (b \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right) \ne 0) \Rightarrow ((\forall i \in iota,\; \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right)\left(i, l\right) = \frac{b}{2}) \Rightarrow ((\forall j \in iota,\; \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right)\left(l, j\right) = \frac{b}{2}) \Rightarrow (\forall j \in iota,\; \operatorname {fderiv}\left(\mathbb {C}, \operatorname {alpha}\left(S\right), \operatorname {Function.const}\left(iota, b\right), \operatorname {Pi.single}\left(j, 1\right)\right) = \frac{1}{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.alpha_first_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When all coordinates equal b and every inverse row and column sums to b/2, every first partial equals one half.

**Theorem 1.92 (The second-partial matrix at a balanced constant point).**

$$\forall iota \in Type,\; \forall finite \in \operatorname {Fintype}\left(iota\right),\; \forall decidable \in \operatorname {DecidableEq}\left(iota\right),\; \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall b \in \mathbb {C},\; (b \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right) \ne 0) \Rightarrow ((\forall i \in iota,\; \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right)\left(i, l\right) = \frac{b}{2}) \Rightarrow ((\forall j \in iota,\; \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right)\left(l, j\right) = \frac{b}{2}) \Rightarrow (\forall j \in iota,\; \forall k \in iota,\; \operatorname {fderiv}\left(\mathbb {C}, (u: iota \to \mathbb {C}\mapsto \operatorname {fderiv}\left(\mathbb {C}, \operatorname {alpha}\left(S\right), u, \operatorname {Pi.single}\left(j, 1\right)\right)), \operatorname {Function.const}\left(iota, b\right), \operatorname {Pi.single}\left(k, 1\right)\right) = \operatorname {Inv.inv}\left(b^{2}\right) \cdot \left(\operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right)\left(j, k\right) + \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right)\left(k, j\right)\right) - \operatorname {ite}\left(j = k, \operatorname {Inv.inv}\left(b\right), 0\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.alpha_second_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the balanced constant point, the second-partial matrix is b inverse squared times V plus its transpose, minus b inverse times the identity.

## The Hessian closed form and rational square

**Theorem 1.93 (The closed form for the analytic Hessian determinant).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; (\operatorname {IsLocalSolution}\left(A, h\right)) \Rightarrow (\operatorname {calH}\left(h\right) = \frac{\operatorname {Nat.cast}\left(d\right) \cdot \operatorname {Matrix.det}\left(\operatorname {Nat.cast}\left(d\right)^{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) \cdot \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)}{\operatorname {Matrix.det}\left(\operatorname {Nat.cast}\left(d\right)^{2}\cdot (1) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) \cdot \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.calH_closedForm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every regular tournament of order d at least three and every complex C2 local solution h, the actual real angular Hessian determinant is d times det(d²I+S²) divided by det(d²I−S²). The Hessian is defined by two real Frechet derivatives of the logarithmic phase.

**Theorem 1.94 (The rational-square conjecture).**

$$\forall d \in \mathbb {N},\; (3 \le d) \Rightarrow (\forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow ((\exists h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \operatorname {IsLocalSolution}\left(A, h\right)) \land (\forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; (\operatorname {IsLocalSolution}\left(A, h\right)) \Rightarrow ((\operatorname {calH}\left(h\right) \ne 0) \land (\exists q \in \mathbb {Q},\; \frac{d}{\operatorname {calH}\left(h\right)} = \operatorname {Rat.cast}\left(q\right)^{2})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/wormald-2026-tournament-hessian-square` (proved) by `D5/S3/Combinatorics/WormaldTournamentHessian/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wormald-2026-tournament-hessian-square","declaration_gid":"D5/S3/Combinatorics/WormaldTournamentHessian/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

Write C=½I+A and let J have every entry equal to one. Tournament completeness gives 2C=J+S. For nonzero coordinates y and nonsingular Q(y)=diag(2/y)−S, the matrix determinant lemma factors K(y) as det Q(y), the product of the coordinates y_j/2, and one minus the sum of all entries of Q(y) inverse. Call that inverse-entry sum alpha. At the constant point z=2/d, the resolvent is dI−S. Strict diagonal dominance makes it nonsingular, and regularity gives row and column sums 1/d for its inverse.

The resolvent inverse and alpha are complex C2 near the constant point. Every first coordinate derivative of alpha there is 1/2. Its second derivative in coordinates j and k is z to the power minus two times V_jk+V_kj, minus z inverse when j=k, where V=(dI−S) inverse. The equation alpha(y,h(y))=1 holds on a neighbourhood for every local solution. Its first derivative gives each coordinate derivative of h equal to minus one; its second derivative gives the corresponding difference of four alpha second derivatives.

The exponential coordinate chart and the principal logarithm are C2 at the base point because h takes the positive value z there. Applying the second Frechet chain rule and then substituting imaginary angular coordinates identifies the actual angular Hessian with minus R transpose T R. Here the columns of R are e_j−e_d and T=I−d(V+V transpose). Both row and column sums of T are minus one. The matrix whose columns are R followed by the all-ones vector has determinant d; conjugating T by this matrix gives diagonal blocks R transpose T R and minus d. Consequently det(R transpose T R)=−d det T.

The resolvent identity gives T=−(d²I+S²)(d²I−S²) inverse. All required inverses follow from the nonzero shifted determinants. The order d is odd, so its determinant contributes one minus sign, while the angular Hessian has the even size d−1 and its overall minus sign does not change its determinant. This proves the displayed closed form for calH.

Transposition identifies det(dI−S) with det(dI+S). Factoring the quadratic matrices therefore makes det(d²I−S²) the square of an integer. In odd dimension, det(S+idI) is a purely imaginary Gaussian integer; dividing it by i gives a nonzero integer, and det(d²I+S²) is its square. The quotient of these two quadratic determinants is thus the square of a nonzero rational. The closed form identifies this quotient with d divided by calH, and also gives nonvanishing of calH.

Finally, every first coordinate derivative of K at the constant point equals −det(dI−S)/(2d^d), which is nonzero. The complex implicit function theorem supplies a C2 local solution with value z and the required equation germ. Together with the Hessian calculation for every such solution, this proves both clauses of the conjecture.

## References

- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.IsLocalSolution`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.IsRegularTournament`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.K`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.K_coordinate_deriv`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.K_eq_zero_iff_resolvent_sum`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.K_resolvent_factorization`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.actual_hessian`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.adjacency`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.algebraicRatioRational`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.algebraicSquareIdentity`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.alpha_contDiffAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.alpha_fderiv_single`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.alpha_first_const`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.alpha_hasFDerivAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.alpha_second_const`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.alpha_second_single`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.appendLast`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.appendLastLinearApply`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.appendLast_update`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.bridgeU_congr`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.bridgeU_det`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.bridgeU_entry_left`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.bridgeU_entry_right`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.bridge_det`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.calH`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.calH_closedForm`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.claim`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.cofactor_eq_of_zero_sums`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.col_fderiv_single`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.det_const_perturb`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.det_doubly_stochastic_cofactor`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.det_projection_update`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.det_rank_one_sub`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.determinantAtBase`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.determinant_column_deriv`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.differenceMinor_det`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.fderiv_exponentialChart`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.hessian`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.hessian_of_implicit_coordinates`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.hessian_of_implicit_scalar`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.imaginaryShiftIntegral`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.implicit_first_graph`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.implicit_first_scalar`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.implicit_second_graph`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.implicit_second_scalar`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverseQDeriv_single`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverseQ_contDiffAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverseQ_hasFDerivAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverse_col_sum`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverse_contDiffAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverse_fderiv_single`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverse_hasFDerivAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverse_row_sum`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.inverse_square_hasDerivAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.localSolutionOfInvertible`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.localSolution_resolvent_eq`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.logarithmicPhase_second`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.logarithmicPhase_smooth`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.matrixInverse_hasFDerivAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.phase`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.polynomialSmooth`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularAlgebraicSquare`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularColumnSlopeValue`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularDegree`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularLocalSolution`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularOdd`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularSkewColSum`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularSkewRowSum`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.resolvent_row_col_sum`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.result`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.row_fderiv_single`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.scalar_map_invertible`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.scalar_partial_invertible`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_angular_substitution`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_clog`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_comp`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_comp_clm`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_complex_to_real`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_eq_derivative`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_eq_zero_of_eventually`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_exponentialChart`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_graph`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_sub_const`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.second_sub_sub`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.shiftedDetNeZero`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.shiftedDetPureImaginary`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.shiftedNegativeDetNeZero`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.skewAdjacency`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.skewDiag`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.skewNormLe`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.skew_difference_det`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.skew_resolvent_det`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.tournamentCoefficientIdentity`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.z`
