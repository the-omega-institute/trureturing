# Tournament Hessian: defs

## Abstract

Regular tournament Hessians: defs.

**Definition 1.1 (Regular tournaments).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \operatorname {IsRegularTournament}\left(A\right) = \left((\forall i \in \operatorname {Fin}\left(d\right),\; A\left(i, i\right) = false) \land ((\forall i \in \operatorname {Fin}\left(d\right),\; \forall j \in \operatorname {Fin}\left(d\right),\; (i \ne j) \Rightarrow ((A\left(i, j\right) = true) \Leftrightarrow (A\left(j, i\right) = false))) \land (\exists r \in \mathbb {N},\; \forall i \in \operatorname {Fin}\left(d\right),\; \sum_{j: \operatorname {Fin}\left(d\right)} \operatorname {ite}\left(A\left(i, j\right) = true, 1, 0\right) = r))\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.IsRegularTournament` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

The adjacency is Boolean. Each diagonal entry is false, and for distinct vertices exactly one direction is true. The out-degree is the same natural number at every vertex. No oddness hypothesis is added.

**Definition 1.2 (The integral adjacency matrix).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall i \in \operatorname {Fin}\left(d\right),\; \forall j \in \operatorname {Fin}\left(d\right),\; \operatorname {adjacency}\left(A, i, j\right) = \operatorname {ite}\left(A\left(i, j\right) = true, 1, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.adjacency` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

True edges have integral entry one and false edges have integral entry zero.

**Definition 1.3 (The skew adjacency matrix).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \operatorname {skewAdjacency}\left(A\right) = \operatorname {adjacency}\left(A\right) - \operatorname {Matrix.transpose}\left(\operatorname {adjacency}\left(A\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.skewAdjacency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integral matrix S is A minus its transpose. It has zero diagonal and entries in {−1,0,1}.

**Definition 1.4 (The expansion point).**

$$\forall d \in \mathbb {N},\; \operatorname {z}\left(d\right) = \frac{2}{d}$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.z` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

The source defines z=2/d and the constant vector with this coordinate. Only d at least three enters the conjecture.

**Definition 1.5 (The determinant polynomial).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall y \in \operatorname {Fin}\left(d\right) \to \mathbb {C},\; \operatorname {K}\left(A, y\right) = \operatorname {Matrix.det}\left(1 - \left(\frac{1}{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {adjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right) \cdot \operatorname {Matrix.diagonal}\left(y\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.K` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

§1, equation (1.2) and its defining paragraph: “Define $B$ to be the matrix whose $(i,j)$ entry $B_{ij}$ is $-y_{j}$ if $A_{ij} = 1$ and 0 otherwise, except for diagonal entries $B_{ii} = 1 - \frac{1}{2} \cdot y_{i}$. That is, $B = I_{d} - (\frac{1}{2} \cdot I_{d} + A) \cdot D_{y}$ where $D_{y} = \operatorname {diag}\left(y_{1}, ..., y_{d}\right)$. Let $K=K\left(\mathbf {y}\right)=\operatorname {det}\left(B\right)$. Set $z = \frac{2}{d}$ and $\mathbf {z} = (z,z,...,z)$.”

The map Int.castRingHom embeds the integral adjacency into the complex numbers. Matrix multiplication retains the source's column scaling by y.

**Definition 1.6 (The final implicit coordinate).**

$$\forall d \in \mathbb {N},\; \forall y \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C},\; \forall t \in \mathbb {C},\; \forall i \in \operatorname {Fin}\left(d\right),\; \operatorname {appendLast}\left(y, t, i\right) = \operatorname {Fin.snoc}\left(y, t, \operatorname {Fin.ofNat}\left(\operatorname {Nat.sub}\left(d, 1\right) + 1, \operatorname {Fin.val}\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.appendLast` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fin.snoc appends the scalar after the first d−1 coordinates. The index is lifted by its natural value to Fin((d−1)+1); for d positive this is the order-preserving identification with Fin d. The case d=0 has no indices.

**Definition 1.7 (A complex C2 local solution).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \operatorname {IsLocalSolution}\left(A, h\right) = \left((h\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right)\right) = \operatorname {z}\left(d\right)) \land ((\operatorname {ContDiffAt}\left(\mathbb {C}, 2, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right)\right)) \land (\operatorname {Filter.Eventually}\left((y: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\mapsto \operatorname {K}\left(A, \operatorname {appendLast}\left(y, h\left(y\right)\right)\right) = 0), \operatorname {nhds}\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right)\right)\right)))\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.IsLocalSolution` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

§1, defining paragraphs immediately preceding Theorem 4: “Writing $K_{j}$ for the partial derivative of $K$ with respect to $y_{j}$, it will be shown that $\left(K_{d}\right)\left(\mathbf {z}\right) \ne 0$ and $K\left(\mathbf {z}\right) = 0$, so (e.g. by observing that $K$ is linear in $y_{d}$) one may solve $K\left(\mathbf {y}\right) = 0$ in the neighbourhood of $\mathbf {z}$ and obtain $y_{d} = h\left(y_{1}, ..., y_{d - 1}\right)$ for an analytic function $h$.”

The source uses an analytic function h. The encoding requires complex C2 regularity at the base point, which suffices for the Hessian: h(z′)=z, ContDiffAt over the complex scalar field of order two, and an equation holding eventually in the neighbourhood filter at z′. It imposes no global equation on h.

**Definition 1.8 (Real angular coordinates).**

$$\forall d \in \mathbb {N},\; \forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall theta \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {R},\; \operatorname {phase}\left(h, theta\right) = \operatorname {Complex.log}\left(h\left((j: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right)\mapsto \operatorname {z}\left(d\right) \cdot \operatorname {Complex.exp}\left(\operatorname {Complex.I} \cdot theta\left(j\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.phase` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

§1, defining paragraphs immediately preceding Theorem 4: “Define a function $\widetilde {f}$ in the neighbourhood of $(0,0,...,0)$ (the $(d - 1)$-dimensional vector) by $\widetilde {f}\left(\theta_{1}, ..., \theta_{d - 1}\right) = \operatorname {log}\left(h\left(z \cdot e^{i \cdot \theta_{1}}, ..., z \cdot e^{i \cdot \theta_{d - 1}}\right)\right)$.”

Complex.log is the principal logarithm. Its argument at zero is the positive real number z when h is a local solution and d is at least three.

**Definition 1.9 (The real angular Hessian).**

$$\forall d \in \mathbb {N},\; \forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall j \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \forall k \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \operatorname {hessian}\left(h, j, k\right) = \operatorname {fderiv}\left(\mathbb {R}, (theta: \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {R}\mapsto \operatorname {fderiv}\left(\mathbb {R}, \operatorname {phase}\left(h\right), theta, \operatorname {Pi.single}\left(j, 1\right)\right)), 0, \operatorname {Pi.single}\left(k, 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.hessian` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

The entry in row j and column k differentiates θ↦fderiv ℝ (phase h) θ (Pi.single j 1) once more over ℝ in the direction Pi.single k 1, at θ=0. Thus the definition uses fderiv of fderiv and keeps the complex-valued output.

**Definition 1.10 (The Hessian determinant).**

$$\forall d \in \mathbb {N},\; \forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \operatorname {calH}\left(h\right) = \operatorname {Matrix.det}\left(\operatorname {hessian}\left(h\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.calH` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

§1, defining paragraphs immediately preceding Theorem 4: “Let $\mathcal {H}$ denote the determinant of the Hessian (matrix of second order partials) of $\widetilde {f}$ at $\theta_{j} = 0$ for $j=1,...,d - 1$.”

The determinant has d−1 rows and columns.

**Definition 1.11 (Conjecture 6 with local existence).**

$$claim = \left(\forall d \in \mathbb {N},\; (3 \le d) \Rightarrow (\forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow ((\exists h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; \operatorname {IsLocalSolution}\left(A, h\right)) \land (\forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; (\operatorname {IsLocalSolution}\left(A, h\right)) \Rightarrow ((\operatorname {calH}\left(h\right) \ne 0) \land (\exists q \in \mathbb {Q},\; \frac{d}{\operatorname {calH}\left(h\right)} = \operatorname {Rat.cast}\left(q\right)^{2})))))\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.claim` (`✓ std3`).

*Citation.* N. C. Wormald (2026). *Tournaments with many Hamilton cycles*. URL: <https://arxiv.org/abs/2610.16245>.

*Commentary.*

The supplied source excerpt does not identify a printed page number. The formula includes existence of a complex C2 local solution and the same conclusion for every such solution. The rational is embedded into ℂ before squaring. The theorem result proves this full statement with the stated analytic definitions.

**Theorem 1.12 (The degree and order identity).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\exists r \in \mathbb {N},\; (d = 2 \cdot r + 1) \land (\forall i \in \operatorname {Fin}\left(d\right),\; \sum_{j: \operatorname {Fin}\left(d\right)} \operatorname {adjacency}\left(A, i, j\right) = \operatorname {Nat.cast}\left(r\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.regularDegree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the common out-degree is r, counting both orientations gives 2dr=d(d−1). Positivity of d gives d=2r+1, and every integral adjacency row sums to r.

**Theorem 1.13 (Regular tournaments have odd order).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\operatorname {Odd}\left(d\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.regularOdd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every out-degree is r, summing the two orientations of each off-diagonal pair gives 2dr=d(d−1). Since d is positive, d=2r+1.

**Theorem 1.14 (The determinant vanishes at the expansion point).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\operatorname {K}\left(A, \operatorname {Function.const}\left(\operatorname {Fin}\left(d\right), \operatorname {z}\left(d\right)\right)\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.determinantAtBase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant vector one is in the kernel of I−(½I+A)D_z: each row of ½I+A sums to d/2. Hence its determinant is zero.

## Second variations

**Theorem 1.15 (The second derivative of a composition).**

$$\forall kappa \in Type,\; [\operatorname {NontriviallyNormedField}\left(kappa\right)] \forall E \in Type,\; [\operatorname {NormedAddCommGroup}\left(E\right)] [\operatorname {NormedSpace}\left(kappa, E\right)] \forall F \in Type,\; [\operatorname {NormedAddCommGroup}\left(F\right)] [\operatorname {NormedSpace}\left(kappa, F\right)] \forall G \in Type,\; [\operatorname {NormedAddCommGroup}\left(G\right)] [\operatorname {NormedSpace}\left(kappa, G\right)] \forall f \in E \to F,\; \forall g \in F \to G,\; \forall x \in E,\; \forall v \in E,\; \forall w \in E,\; (\operatorname {ContDiffAt}\left(kappa, 2, f, x\right)) \Rightarrow ((\operatorname {ContDiffAt}\left(kappa, 2, g, f\left(x\right)\right)) \Rightarrow (\operatorname {second}\left(kappa, \operatorname {Function.comp}\left(g, f\right), x, v, w\right) = \operatorname {second}\left(kappa, g, f\left(x\right), \operatorname {fderiv}\left(kappa, f, x, v\right), \operatorname {fderiv}\left(kappa, f, x, w\right)\right) + \operatorname {fderiv}\left(kappa, g, f\left(x\right), \operatorname {second}\left(kappa, f, x, v, w\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write second(f,x,v,w) for the derivative in direction w of y mapped to Df(y)v. The chain rule gives the outer second derivative on the two inner velocities, plus the outer first derivative on the inner acceleration.

**Theorem 1.16 (A zero germ has zero second derivative).**

$$\forall kappa \in Type,\; [\operatorname {NontriviallyNormedField}\left(kappa\right)] \forall E \in Type,\; [\operatorname {NormedAddCommGroup}\left(E\right)] [\operatorname {NormedSpace}\left(kappa, E\right)] \forall F \in Type,\; [\operatorname {NormedAddCommGroup}\left(F\right)] [\operatorname {NormedSpace}\left(kappa, F\right)] \forall f \in E \to F,\; \forall x \in E,\; \forall v \in E,\; \forall w \in E,\; (\operatorname {Filter.EventuallyEq}\left(\operatorname {nhds}\left(x\right), f, (y: E\mapsto 0)\right)) \Rightarrow (\operatorname {second}\left(kappa, f, x, v, w\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_eq_zero_of_eventually` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A function agreeing with zero on a neighbourhood has the same first and second Frechet derivatives as zero. No separate smoothness hypothesis is needed for this germ equality.

**Theorem 1.17 (The second derivative of a graph).**

$$\forall kappa \in Type,\; [\operatorname {NontriviallyNormedField}\left(kappa\right)] \forall E \in Type,\; [\operatorname {NormedAddCommGroup}\left(E\right)] [\operatorname {NormedSpace}\left(kappa, E\right)] \forall F \in Type,\; [\operatorname {NormedAddCommGroup}\left(F\right)] [\operatorname {NormedSpace}\left(kappa, F\right)] \forall h \in E \to F,\; \forall x \in E,\; \forall v \in E,\; \forall w \in E,\; (\operatorname {ContDiffAt}\left(kappa, 2, h, x\right)) \Rightarrow (\operatorname {second}\left(kappa, (y: E\mapsto \operatorname {Prod.mk}\left(y, h\left(y\right)\right)), x, v, w\right) = \operatorname {Prod.mk}\left(0, \operatorname {second}\left(kappa, h, x, v, w\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity coordinate has zero acceleration, while the final coordinate has the second derivative of h.

**Theorem 1.18 (First differentiation of an implicit equation).**

$$\forall kappa \in Type,\; [\operatorname {NontriviallyNormedField}\left(kappa\right)] \forall E \in Type,\; [\operatorname {NormedAddCommGroup}\left(E\right)] [\operatorname {NormedSpace}\left(kappa, E\right)] \forall F \in Type,\; [\operatorname {NormedAddCommGroup}\left(F\right)] [\operatorname {NormedSpace}\left(kappa, F\right)] \forall G \in Type,\; [\operatorname {NormedAddCommGroup}\left(G\right)] [\operatorname {NormedSpace}\left(kappa, G\right)] \forall h \in E \to F,\; \forall F0 \in \operatorname {Prod}\left(E, F\right) \to G,\; \forall x \in E,\; (\operatorname {ContDiffAt}\left(kappa, 2, h, x\right)) \Rightarrow ((\operatorname {ContDiffAt}\left(kappa, 2, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right)\right)) \Rightarrow ((\operatorname {Filter.EventuallyEq}\left(\operatorname {nhds}\left(x\right), \operatorname {Function.comp}\left(F0, (y: E\mapsto \operatorname {Prod.mk}\left(y, h\left(y\right)\right))\right), (y: E\mapsto 0)\right)) \Rightarrow (\forall v \in E,\; \operatorname {fderiv}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(v, \operatorname {fderiv}\left(kappa, h, x, v\right)\right)\right) = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.implicit_first_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative of a constant zero germ vanishes. Applying the chain rule to the graph y mapped to (y,h(y)) gives the first implicit derivative equation.

**Theorem 1.19 (Second differentiation of an implicit equation).**

$$\forall kappa \in Type,\; [\operatorname {NontriviallyNormedField}\left(kappa\right)] \forall E \in Type,\; [\operatorname {NormedAddCommGroup}\left(E\right)] [\operatorname {NormedSpace}\left(kappa, E\right)] \forall F \in Type,\; [\operatorname {NormedAddCommGroup}\left(F\right)] [\operatorname {NormedSpace}\left(kappa, F\right)] \forall G \in Type,\; [\operatorname {NormedAddCommGroup}\left(G\right)] [\operatorname {NormedSpace}\left(kappa, G\right)] \forall h \in E \to F,\; \forall F0 \in \operatorname {Prod}\left(E, F\right) \to G,\; \forall x \in E,\; (\operatorname {ContDiffAt}\left(kappa, 2, h, x\right)) \Rightarrow ((\operatorname {ContDiffAt}\left(kappa, 2, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right)\right)) \Rightarrow ((\operatorname {Filter.EventuallyEq}\left(\operatorname {nhds}\left(x\right), \operatorname {Function.comp}\left(F0, (y: E\mapsto \operatorname {Prod.mk}\left(y, h\left(y\right)\right))\right), (y: E\mapsto 0)\right)) \Rightarrow (\forall v \in E,\; \forall w \in E,\; \operatorname {second}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(v, \operatorname {fderiv}\left(kappa, h, x, v\right)\right), \operatorname {Prod.mk}\left(w, \operatorname {fderiv}\left(kappa, h, x, w\right)\right)\right) + \operatorname {fderiv}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(0, \operatorname {second}\left(kappa, h, x, v, w\right)\right)\right) = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.implicit_second_graph` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiating the zero germ twice gives the outer second derivative on graph tangent vectors, plus the final-coordinate derivative applied to the acceleration of h.

**Theorem 1.20 (Solving the first implicit derivative equation).**

$$\forall kappa \in Type,\; [\operatorname {NontriviallyNormedField}\left(kappa\right)] \forall E \in Type,\; [\operatorname {NormedAddCommGroup}\left(E\right)] [\operatorname {NormedSpace}\left(kappa, E\right)] \forall h \in E \to kappa,\; \forall F0 \in \operatorname {Prod}\left(E, kappa\right) \to kappa,\; \forall x \in E,\; (\operatorname {ContDiffAt}\left(kappa, 2, h, x\right)) \Rightarrow ((\operatorname {ContDiffAt}\left(kappa, 2, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right)\right)) \Rightarrow ((\operatorname {Filter.EventuallyEq}\left(\operatorname {nhds}\left(x\right), \operatorname {Function.comp}\left(F0, (y: E\mapsto \operatorname {Prod.mk}\left(y, h\left(y\right)\right))\right), (y: E\mapsto 0)\right)) \Rightarrow ((\operatorname {fderiv}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(0, 1\right)\right) \ne 0) \Rightarrow (\forall v \in E,\; \operatorname {fderiv}\left(kappa, h, x, v\right) = \frac{0 - \operatorname {fderiv}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(v, 0\right)\right)}{\operatorname {fderiv}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(0, 1\right)\right)}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.implicit_first_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a scalar final coordinate, a nonzero final partial derivative permits division. The derivative of h is the negative ratio of the two partial derivatives.

**Theorem 1.21 (Solving the second implicit derivative equation).**

$$\forall kappa \in Type,\; [\operatorname {NontriviallyNormedField}\left(kappa\right)] \forall E \in Type,\; [\operatorname {NormedAddCommGroup}\left(E\right)] [\operatorname {NormedSpace}\left(kappa, E\right)] \forall h \in E \to kappa,\; \forall F0 \in \operatorname {Prod}\left(E, kappa\right) \to kappa,\; \forall x \in E,\; (\operatorname {ContDiffAt}\left(kappa, 2, h, x\right)) \Rightarrow ((\operatorname {ContDiffAt}\left(kappa, 2, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right)\right)) \Rightarrow ((\operatorname {Filter.EventuallyEq}\left(\operatorname {nhds}\left(x\right), \operatorname {Function.comp}\left(F0, (y: E\mapsto \operatorname {Prod.mk}\left(y, h\left(y\right)\right))\right), (y: E\mapsto 0)\right)) \Rightarrow ((\operatorname {fderiv}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(0, 1\right)\right) \ne 0) \Rightarrow (\forall v \in E,\; \forall w \in E,\; \operatorname {second}\left(kappa, h, x, v, w\right) = \frac{0 - \operatorname {second}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(v, \operatorname {fderiv}\left(kappa, h, x, v\right)\right), \operatorname {Prod.mk}\left(w, \operatorname {fderiv}\left(kappa, h, x, w\right)\right)\right)}{\operatorname {fderiv}\left(kappa, F0, \operatorname {Prod.mk}\left(x, h\left(x\right)\right), \operatorname {Prod.mk}\left(0, 1\right)\right)}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.implicit_second_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second derivative of h is the negative outer second derivative on graph tangent vectors divided by the final partial derivative.

**Theorem 1.22 (Constants do not affect second derivatives).**

$$\forall kappa \in Type,\; [\operatorname {NontriviallyNormedField}\left(kappa\right)] \forall E \in Type,\; [\operatorname {NormedAddCommGroup}\left(E\right)] [\operatorname {NormedSpace}\left(kappa, E\right)] \forall F \in Type,\; [\operatorname {NormedAddCommGroup}\left(F\right)] [\operatorname {NormedSpace}\left(kappa, F\right)] \forall f \in E \to F,\; \forall c \in F,\; \forall x \in E,\; \forall v \in E,\; \forall w \in E,\; \operatorname {second}\left(kappa, (y: E\mapsto f\left(y\right) - c), x, v, w\right) = \operatorname {second}\left(kappa, f, x, v, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_sub_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting a constant leaves both derivatives unchanged.

**Theorem 1.23 (Second derivatives under a linear change of variables).**

$$\forall kappa \in Type,\; [\operatorname {NontriviallyNormedField}\left(kappa\right)] \forall E \in Type,\; [\operatorname {NormedAddCommGroup}\left(E\right)] [\operatorname {NormedSpace}\left(kappa, E\right)] \forall F \in Type,\; [\operatorname {NormedAddCommGroup}\left(F\right)] [\operatorname {NormedSpace}\left(kappa, F\right)] \forall G \in Type,\; [\operatorname {NormedAddCommGroup}\left(G\right)] [\operatorname {NormedSpace}\left(kappa, G\right)] \forall L \in \operatorname {ContinuousLinearMap}\left(kappa, E, F\right),\; \forall f \in F \to G,\; \forall x \in E,\; \forall v \in E,\; \forall w \in E,\; (\operatorname {ContDiffAt}\left(kappa, 2, f, L\left(x\right)\right)) \Rightarrow (\operatorname {second}\left(kappa, \operatorname {Function.comp}\left(f, L\right), x, v, w\right) = \operatorname {second}\left(kappa, f, L\left(x\right), L\left(v\right), L\left(w\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_comp_clm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A continuous linear inner map has zero second derivative. Its two images are the directions supplied to the outer second derivative.

**Theorem 1.24 (The bilinear second derivative).**

$$\forall n \in \mathbb {N},\; \forall f \in \left(\operatorname {Fin}\left(n\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall x \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, f, x\right)) \Rightarrow (\forall v \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall w \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \operatorname {second}\left(\mathbb {C}, f, x, v, w\right) = \operatorname {fderiv}\left(\mathbb {C}, \operatorname {fderiv}\left(\mathbb {C}, f\right), x, w, v\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_eq_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex C2 function, differentiating its derivative and then evaluating in v gives the same directional second derivative. This expression is complex bilinear in v and w.

**Theorem 1.25 (Bilinearity on difference directions).**

$$\forall n \in \mathbb {N},\; \forall f \in \left(\operatorname {Fin}\left(n\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall x \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, f, x\right)) \Rightarrow (\forall a \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall b \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall c \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall d0 \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \operatorname {second}\left(\mathbb {C}, f, x, a - b, c - d0\right) = \operatorname {second}\left(\mathbb {C}, f, x, a, c\right) - \operatorname {second}\left(\mathbb {C}, f, x, a, d0\right) - \operatorname {second}\left(\mathbb {C}, f, x, b, c\right) + \operatorname {second}\left(\mathbb {C}, f, x, b, d0\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_sub_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding both difference directions gives the four terms of a two-coordinate minor.

**Theorem 1.26 (Restriction from complex to real derivatives).**

$$\forall n \in \mathbb {N},\; \forall f \in \left(\operatorname {Fin}\left(n\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall x \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, f, x\right)) \Rightarrow (\forall v \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall w \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \operatorname {second}\left(\mathbb {R}, f, x, v, w\right) = \operatorname {second}\left(\mathbb {C}, f, x, v, w\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_complex_to_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real derivative of a complex differentiable function is the scalar restriction of its complex derivative. Applying the same fact to the first derivative proves equality of the two second directional derivatives on complex vectors regarded as real vectors.

**Theorem 1.27 (The angular substitution negates the Hessian).**

$$\forall n \in \mathbb {N},\; \forall f \in \left(\operatorname {Fin}\left(n\right) \to \mathbb {C}\right) \to \mathbb {C},\; (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, f, 0\right)) \Rightarrow (\forall j \in \operatorname {Fin}\left(n\right),\; \forall k \in \operatorname {Fin}\left(n\right),\; \operatorname {second}\left(\mathbb {R}, (theta: \operatorname {Fin}\left(n\right) \to \mathbb {R}\mapsto f\left(\operatorname {angularMap}\left(theta\right)\right)), 0, \operatorname {Pi.single}\left(j, 1\right), \operatorname {Pi.single}\left(k, 1\right)\right) = 0 - \operatorname {second}\left(\mathbb {C}, f, 0, \operatorname {Pi.single}\left(j, 1\right), \operatorname {Pi.single}\left(k, 1\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_angular_substitution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real angular map sends each coordinate vector to i times the corresponding complex vector. Complex bilinearity contributes i squared, hence a factor of minus one.

**Theorem 1.28 (Smoothness in logarithmic coordinates).**

$$\forall n \in \mathbb {N},\; \forall a \in \mathbb {C},\; \forall h \in \left(\operatorname {Fin}\left(n\right) \to \mathbb {C}\right) \to \mathbb {C},\; (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right)\right)) \Rightarrow ((\operatorname {Membership.mem}\left(\operatorname {Complex.slitPlane}, h\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right)\right)\right)) \Rightarrow (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, \operatorname {logarithmicPhase}\left(a, h\right), 0\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.logarithmicPhase_smooth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential coordinate map is entire. If h is complex C2 at the constant point and its value lies in the slit plane, composition with the principal logarithm is complex C2 at zero.

**Theorem 1.29 (The first derivative of exponential coordinates).**

$$\forall n \in \mathbb {N},\; \forall a \in \mathbb {C},\; \forall u \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall v \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \operatorname {fderiv}\left(\mathbb {C}, \operatorname {exponentialChart}\left(a\right), u, v\right) = (j: \operatorname {Fin}\left(n\right)\mapsto a \cdot \operatorname {Complex.exp}\left(u\left(j\right)\right) \cdot v\left(j\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.fderiv_exponentialChart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate map u_j mapped to a exp(u_j) has derivative a exp(u_j) v_j in direction v.

**Theorem 1.30 (The second derivative of exponential coordinates).**

$$\forall n \in \mathbb {N},\; \forall a \in \mathbb {C},\; \forall v \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall w \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \operatorname {second}\left(\mathbb {C}, \operatorname {exponentialChart}\left(a\right), 0, v, w\right) = (j: \operatorname {Fin}\left(n\right)\mapsto a \cdot v\left(j\right) \cdot w\left(j\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_exponentialChart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero, the second derivative in directions v and w has coordinate a v_j w_j.

**Theorem 1.31 (The second derivative of a logarithm).**

$$\forall n \in \mathbb {N},\; \forall g \in \left(\operatorname {Fin}\left(n\right) \to \mathbb {C}\right) \to \mathbb {C},\; \forall x \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, g, x\right)) \Rightarrow ((\operatorname {Membership.mem}\left(\operatorname {Complex.slitPlane}, g\left(x\right)\right)) \Rightarrow (\forall v \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \forall w \in \operatorname {Fin}\left(n\right) \to \mathbb {C},\; \operatorname {second}\left(\mathbb {C}, (y: \operatorname {Fin}\left(n\right) \to \mathbb {C}\mapsto \operatorname {Complex.log}\left(g\left(y\right)\right)), x, v, w\right) = \left(0 - \operatorname {Inv.inv}\left(g\left(x\right)^{2}\right)\right) \cdot \operatorname {fderiv}\left(\mathbb {C}, g, x, w\right) \cdot \operatorname {fderiv}\left(\mathbb {C}, g, x, v\right) + \operatorname {Inv.inv}\left(g\left(x\right)\right) \cdot \operatorname {second}\left(\mathbb {C}, g, x, v, w\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_clog` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative of log(g) is g inverse times Dg. The product rule gives g inverse times the second derivative, minus the product of the two first derivatives divided by g squared.

**Theorem 1.32 (The logarithmic-coordinate Hessian).**

$$\forall n \in \mathbb {N},\; \forall a \in \mathbb {C},\; \forall h \in \left(\operatorname {Fin}\left(n\right) \to \mathbb {C}\right) \to \mathbb {C},\; (a \ne 0) \Rightarrow ((\operatorname {ContDiffAt}\left(\mathbb {C}, 2, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right)\right)) \Rightarrow ((h\left(\operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right)\right) = a) \Rightarrow ((\operatorname {Membership.mem}\left(\operatorname {Complex.slitPlane}, a\right)) \Rightarrow (\forall j \in \operatorname {Fin}\left(n\right),\; \forall k \in \operatorname {Fin}\left(n\right),\; \operatorname {second}\left(\mathbb {C}, \operatorname {logarithmicPhase}\left(a, h\right), 0, \operatorname {Pi.single}\left(j, 1\right), \operatorname {Pi.single}\left(k, 1\right)\right) = a \cdot \operatorname {second}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right), \operatorname {Pi.single}\left(j, 1\right), \operatorname {Pi.single}\left(k, 1\right)\right) + \operatorname {ite}\left(j = k, \operatorname {fderiv}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right), \operatorname {Pi.single}\left(j, 1\right)\right), 0\right) - \operatorname {fderiv}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right), \operatorname {Pi.single}\left(j, 1\right)\right) \cdot \operatorname {fderiv}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(n\right), a\right), \operatorname {Pi.single}\left(k, 1\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.logarithmicPhase_second` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At h(a,...,a)=a, the exponential and logarithm chain rules give a times the second derivative of h, the diagonal first-derivative term, and minus the product of first derivatives.

**Theorem 1.33 (The angular Hessian in derivatives of the local solution).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall h \in \left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right) \to \mathbb {C}\right) \to \mathbb {C},\; (3 \le d) \Rightarrow ((\operatorname {IsLocalSolution}\left(A, h\right)) \Rightarrow (\forall j \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \forall k \in \operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right),\; \operatorname {hessian}\left(h, j, k\right) = \operatorname {fderiv}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {Pi.single}\left(j, 1\right)\right) \cdot \operatorname {fderiv}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {Pi.single}\left(k, 1\right)\right) - \operatorname {z}\left(d\right) \cdot \operatorname {second}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {Pi.single}\left(j, 1\right), \operatorname {Pi.single}\left(k, 1\right)\right) - \operatorname {ite}\left(j = k, \operatorname {fderiv}\left(\mathbb {C}, h, \operatorname {Function.const}\left(\operatorname {Fin}\left(\operatorname {Nat.sub}\left(d, 1\right)\right), \operatorname {z}\left(d\right)\right), \operatorname {Pi.single}\left(j, 1\right)\right), 0\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.actual_hessian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local solution takes the positive real value z at the base point, so the principal logarithm is smooth there. Combining logarithmic coordinates with the angular substitution gives H_jk=h_j h_k-z h_jk-delta_jk h_j, with all derivatives of h taken over the complex numbers at the base point.

**Definition 1.34 (Directional second derivatives).**

$$\forall kappa \in Type,\; [\operatorname {NontriviallyNormedField}\left(kappa\right)] \forall E \in Type,\; [\operatorname {NormedAddCommGroup}\left(E\right)] [\operatorname {NormedSpace}\left(kappa, E\right)] \forall F \in Type,\; [\operatorname {NormedAddCommGroup}\left(F\right)] [\operatorname {NormedSpace}\left(kappa, F\right)] \forall f \in E \to F,\; \forall x \in E,\; \forall v \in E,\; \forall w \in E,\; \operatorname {second}\left(kappa, f, x, v, w\right) = \operatorname {fderiv}\left(kappa, (y: E\mapsto \operatorname {fderiv}\left(kappa, f, y, v\right)), x, w\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first direction is held fixed while the first derivative is differentiated in the second direction.

## References

- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.IsLocalSolution`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.IsRegularTournament`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.K`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.actual_hessian`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.adjacency`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.appendLast`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.calH`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.claim`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.determinantAtBase`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.fderiv_exponentialChart`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.hessian`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.implicit_first_graph`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.implicit_first_scalar`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.implicit_second_graph`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.implicit_second_scalar`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.logarithmicPhase_second`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.logarithmicPhase_smooth`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.phase`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.regularDegree`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.regularOdd`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_angular_substitution`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_clog`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_comp`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_comp_clm`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_complex_to_real`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_eq_derivative`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_eq_zero_of_eventually`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_exponentialChart`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_graph`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_sub_const`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.second_sub_sub`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.skewAdjacency`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Defs.z`
