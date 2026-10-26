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

The supplied source excerpt does not identify a printed page number. The formula includes existence of a complex C2 local solution and the same conclusion for every such solution. The rational is embedded into ℂ before squaring. This document states the conjecture; it does not assert a settling theorem.

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

Transposition identifies the determinants of dI+S and dI−S. Factoring d²I−S² gives the square of the first determinant. Factoring d²I+S² and using odd dimension gives the square of det(S+idI)/i. Thus the quotient is the square of the previously constructed rational. This algebraic identity does not identify the quotient with d divided by the analytic Hessian determinant.

**Theorem 1.21 (The algebraic square for regular tournaments).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\exists q \in \mathbb {Q},\; (q \ne 0) \land (\frac{\operatorname {Matrix.det}\left(d^{2}\cdot (1) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) \cdot \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)}{\operatorname {Matrix.det}\left(d^{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) \cdot \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)} = \operatorname {Rat.cast}\left(q\right)^{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularAlgebraicSquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Oddness of a regular tournament supplies the hypothesis of the quadratic determinant identity. The existence of a local solution and the identification with its angular Hessian remain separate assertions.

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

## References

- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.IsLocalSolution`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.IsRegularTournament`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.K`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.adjacency`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.algebraicRatioRational`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.algebraicSquareIdentity`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.appendLast`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.calH`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.claim`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.determinantAtBase`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.hessian`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.imaginaryShiftIntegral`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.localSolutionOfInvertible`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.phase`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.polynomialSmooth`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularAlgebraicSquare`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularDegree`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.regularOdd`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.shiftedDetNeZero`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.shiftedDetPureImaginary`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.skewAdjacency`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.skewDiag`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.skewNormLe`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Result.z`
