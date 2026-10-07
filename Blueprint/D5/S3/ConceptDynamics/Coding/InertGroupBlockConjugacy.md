# Inert group block conjugacy

## Abstract

Actual stationary actions and rational splitting give every original positive-threshold block construction.

**Theorem 1.1 (One common annihilation stage).**

$$\forall R \in Type, commRingR \in \operatorname{CommRing}\left(R\right), M \in Type, addGroupM \in \operatorname{AddCommGroup}\left(M\right), moduleM \in \operatorname{Module}\left(R, M\right), I \in Type, finiteI \in \operatorname{Fintype}\left(I\right), Gamma \in Type, finiteGamma \in \operatorname{Fintype}\left(Gamma\right), basis \in \operatorname{Basis}\left(I, R, M\right), T \in \operatorname{ModuleEnd}\left(R, M\right), P \in \operatorname{Function}\left(Gamma, \operatorname{ModuleEnd}\left(R, M\right)\right), commutes \in \left(\forall g \in Gamma,\; \operatorname{Commute}\left(\operatorname{apply}\left(P, g\right), T\right)\right),\; \left(\left(\forall g \in Gamma,\; \operatorname{induced}\left(T, \operatorname{apply}\left(P, g\right), \operatorname{apply}\left(commutes, g\right)\right) = \operatorname{linearIdentity}\left(\operatorname{StationaryModule}\left(T\right)\right)\right) \Rightarrow \left(\exists N \in Nat,\; \forall g \in Gamma,\; \operatorname{compose}\left(\operatorname{power}\left(T, N\right), \operatorname{apply}\left(P, g\right)\right) = \operatorname{power}\left(T, N\right)\right)\right) \land \left(\left(\exists N \in Nat,\; \forall g \in Gamma,\; \operatorname{compose}\left(\operatorname{power}\left(T, N\right), \operatorname{apply}\left(P, g\right)\right) = \operatorname{power}\left(T, N\right)\right) \Rightarrow \left(\forall g \in Gamma,\; \operatorname{induced}\left(T, \operatorname{apply}\left(P, g\right), \operatorname{apply}\left(commutes, g\right)\right) = \operatorname{linearIdentity}\left(\operatorname{StationaryModule}\left(T\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.finite_family_inert_iff_eventual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

StationaryModule(T) is the actual module direct limit with transition from stage i to stage j equal to T raised to j minus i. The commuting endomorphism P(g) induces the displayed map on this direct limit. Powers of endomorphisms use composition, so the finite-stage equation is T^N composed with P(g) equals T^N.

Equality of two stage-zero classes is witnessed at a later stage by direct-limit exactness. There are finitely many basis vectors and finitely many family members; taking finite maxima gives one N for all of them. Conversely the same finite-stage equation holds after every starting stage, so it forces identity on the entire colimit. The exponent N may be zero, the basis may be empty, and the family need not be a group action.

**Theorem 1.2 (Every admissible exponent).**

$$\forall H \in Type, groupH \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), k \in Nat,\; \left(\operatorname{tau}\left(A\right) \le \operatorname{finiteWithTop}\left(k\right) \Rightarrow \left(\operatorname{NatPositive}\left(k\right) \land \operatorname{UniformMatrix}\left(\operatorname{matrixPower}\left(A, k\right)\right)\right)\right) \land \left(\left(\operatorname{NatPositive}\left(k\right) \land \operatorname{UniformMatrix}\left(\operatorname{matrixPower}\left(A, k\right)\right)\right) \Rightarrow \operatorname{tau}\left(A\right) \le \operatorname{finiteWithTop}\left(k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.tau_le_iff_uniform_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

GroupMat(H,n,n) is the matrix semiring over the natural group algebra. UniformMatrix means every actual group coefficient in each entry equals its coefficient at the identity, including zero coefficients. The value tau lies in the natural numbers with a top element: it is the least positive uniform exponent when one exists and infinity otherwise. Ordered convolution preserves uniformity under right multiplication, without assuming the finite group H is commutative.

**Theorem 1.3 (The positive convention includes zero).**

$$\forall H \in Type, groupH \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right),\; \left(\operatorname{tau}\left(A\right) = \operatorname{finiteWithTop}\left(1\right) \Rightarrow \operatorname{UniformMatrix}\left(A\right)\right) \land \left(\operatorname{UniformMatrix}\left(A\right) \Rightarrow \operatorname{tau}\left(A\right) = \operatorname{finiteWithTop}\left(1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.tau_eq_one_iff_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence includes the zero matrix, whose least positive exponent is one even though its zeroth power behaves differently. If H is trivial, every entry is uniform and every matrix has tau one. It also includes n=0; no positivity of the matrix order is needed for the natural threshold theorem.

**Theorem 1.4 (Equal augmentation gives equal natural powers).**

$$\forall H \in Type, groupH \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, n, n\right), sameAugmentation \in \operatorname{matrixAugmentation}\left(A\right) = \operatorname{matrixAugmentation}\left(B\right), k \in Nat, threshold \in \operatorname{max}\left(\operatorname{tau}\left(A\right), \operatorname{tau}\left(B\right)\right) \le \operatorname{finiteWithTop}\left(k\right),\; \operatorname{NatPositive}\left(k\right) \land \operatorname{matrixPower}\left(A, k\right) = \operatorname{matrixPower}\left(B, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.equal_power_of_tau_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Augmentation sums the actual natural coefficients entry by entry and is a ring homomorphism. At every k at least both tau values, both powers are uniform. A uniform natural entry is determined by its augmentation because its coefficient sum is |H| times any coefficient and |H| is positive. Thus A^k=B^k in the original natural group-matrix semiring. Positivity of k is a conclusion; k=1 is retained.

**Theorem 1.5 (The exact kernel of the nontrivial tail).**

$$\forall H \in Type, groupH \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), S \in Type, ringS \in \operatorname{Ring}\left(S\right), algebraS \in \operatorname{Algebra}\left(Rat, S\right), phi \in \operatorname{AlgEquiv}\left(Rat, \operatorname{MonoidAlgebra}\left(Rat, H\right), \operatorname{Product}\left(Rat, S\right)\right), augmentationFirst \in \left(\forall z \in \operatorname{MonoidAlgebra}\left(Rat, H\right),\; \operatorname{first}\left(\operatorname{apply}\left(phi, z\right)\right) = \operatorname{augmentation}\left(z\right)\right), x \in \operatorname{MonoidAlgebra}\left(Rat, H\right),\; \left(\operatorname{UniformRational}\left(x\right) \Rightarrow \operatorname{second}\left(\operatorname{apply}\left(phi, x\right)\right) = 0\right) \land \left(\operatorname{second}\left(\operatorname{apply}\left(phi, x\right)\right) = 0 \Rightarrow \operatorname{UniformRational}\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.uniform_iff_tail_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

UniformRational means equality of every coefficient with the identity coefficient. Augmentation is their rational sum. The normalized element average(H), denoted e_H, has every coefficient 1/|H|. The theorem applies to any actual rational algebra equivalence phi whose first coordinate is literally augmentation; S may be noncommutative. A uniform element satisfies x*y=augmentation(y) times x. Conversely, vanishing tail makes every left group translation fix x and hence makes every coefficient equal.

**Theorem 1.6 (All nontrivial rational simple factors).**

$$\forall H \in Type, groupH \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), nontrivialH \in \operatorname{Nontrivial}\left(H\right),\; \operatorname{Nonempty}\left(\operatorname{RationalDecomposition}\left(H\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.nonempty_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RationalDecomposition(H) consists of a positive count m, a division algebra D_l over the rationals of finite rational dimension for each l in Fin(m), positive natural matrix orders r_l, and an actual rational algebra equivalence Q[H] with Q times the product of Mat(r_l,D_l). Its first coordinate equals augmentation on every element. No complex splitting or change of coefficient field occurs.

Uniform elements form a two-sided ideal J. The map x to (augmentation(x),[x]) is bijective: its kernel is zero because a uniform augmentation-zero element is zero, and a preimage of (a,[x]) is x+(a-augmentation(x))*e_H. For nontrivial H the quotient Q[H]/J is nontrivial. Maschke supplies semisimplicity and the finite rational Wedderburn theorem supplies the division-ring factors of this quotient. The quotient's nontriviality makes the factor count positive; no empty maximum is assigned to a trivial group.

**Theorem 1.7 (The exact normalized expression).**

$$\forall H \in Type, groupH \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), x \in \operatorname{MonoidAlgebra}\left(Rat, H\right), uniform \in \operatorname{UniformRational}\left(x\right),\; x = \operatorname{scalarMultiply}\left(\operatorname{augmentation}\left(x\right), \operatorname{average}\left(H\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.uniform_eq_augmentation_smul_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every uniform rational element is its actual augmentation times e_H. This includes zero and preserves the factor 1/|H| exactly.

**Theorem 1.8 (Actual uniformity and faithful blocks).**

$$\forall H \in Type, groupH \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), n \in Nat, W \in \operatorname{RationalDecomposition}\left(H\right), C \in \operatorname{GroupMat}\left(H, n, n\right),\; \left(\operatorname{UniformMatrix}\left(C\right) \Rightarrow \left(\forall l \in \operatorname{Fin}\left(\operatorname{count}\left(W\right)\right),\; \operatorname{block}\left(W, l, C\right) = 0\right)\right) \land \left(\left(\forall l \in \operatorname{Fin}\left(\operatorname{count}\left(W\right)\right),\; \operatorname{block}\left(W, l, C\right) = 0\right) \Rightarrow \operatorname{UniformMatrix}\left(C\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.uniform_iff_blocks_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

W is an actual augmentation-first rational decomposition with positive factor count, positive matrix orders r_l and finite rational division algebras D_l. The map block(W,l,C) casts natural coefficients to rational coefficients, applies the l-th tail factor entrywise, then flattens Mat(n,Mat(r_l,D_l)) to Mat(Fin(n) times Fin(r_l),D_l). Faithfulness and augmentation-firstness identify its simultaneous zero kernel with uniform coefficients. This is a theorem about every C, not an assumed bridge for selected powers.

**Theorem 1.9 (The exact bound n*b_H).**

$$\forall H \in Type, groupH \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), n \in Nat, W \in \operatorname{RationalDecomposition}\left(H\right), positiveN \in \operatorname{NatPositive}\left(n\right), A \in \operatorname{GroupMat}\left(H, n, n\right), uniformizes \in \operatorname{Uniformizes}\left(A\right),\; \operatorname{tau}\left(A\right) \le \operatorname{finiteWithTop}\left(\operatorname{multiply}\left(n, \operatorname{bH}\left(W\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.tau_le_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural number bH(W) is the maximum of W's original nontrivial rational matrix orders r_l. A positive uniform power makes every tail block nilpotent. Right multiplication on row vectors is linear over the same division ring and reverses products, but preserves powers of one matrix. Kernel stabilization therefore kills an n*r_l dimensional block by exponent n*r_l, and hence all blocks vanish by n*bH(W).

The dimension is measured over D_l, not over the rationals; there is no factor dim_Q(D_l). The hypotheses n>0, positive factor count and positive r_l ensure that n*bH(W) is a positive exponent, as required by the least-positive convention. The trivial group uses the separate tau=1 boundary and has no artificial b_H.

**Theorem 1.10 (Rational expression of a natural uniform matrix).**

$$\forall H \in Type, groupH \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), n \in Nat, C \in \operatorname{GroupMat}\left(H, n, n\right), uniform \in \operatorname{UniformMatrix}\left(C\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{rationalEntry}\left(C, i, j\right) = \operatorname{scalarMultiply}\left(\operatorname{castRat}\left(\operatorname{augmentationEntry}\left(C, i, j\right)\right), \operatorname{average}\left(H\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.uniform_rational_expression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

rationalEntry(C,i,j) is the natural entry C[i,j] with its coefficients cast to the rationals; augmentationEntry is the natural augmentation entry. The equality is entrywise equality in Q[H]. It divides only after casting to the rationals and does not assert divisibility by introducing an operation in the natural semiring.

**Theorem 1.11 (Ordered vertex coordinates).**

$$\forall H \in Type, groupH \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), h \in H, t \in H,\; \operatorname{coefficient}\left(\operatorname{vertexCoordinate}\left(\operatorname{apply}\left(\operatorname{transition}\left(A\right), \operatorname{vertex}\left(i, h\right)\right), j\right), t\right) = \operatorname{castInt}\left(\operatorname{coefficient}\left(\operatorname{entry}\left(A, i, j\right), \operatorname{multiply}\left(\operatorname{inverse}\left(h\right), t\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.actual_expansion_adjacency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

VertexModule is Fin(n) to Z[H], the free abelian group on vertices (i,h). The vector vertex(i,h) has coefficient one at that vertex and zero elsewhere. The transition sends a row vector v to v times the coefficientwise integer cast of A. The displayed coefficient is exactly the number of actual expanded edges from (i,h) to (j,t): an edge labelled s ends at h*s, so s=h inverse times t. The order is retained for noncommutative H.

**Theorem 1.12 (Identity on the actual stationary group).**

$$\forall H \in Type, groupH \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right),\; \left(\operatorname{Inert}\left(A\right) \Rightarrow \operatorname{Uniformizes}\left(A\right)\right) \land \left(\operatorname{Uniformizes}\left(A\right) \Rightarrow \operatorname{Inert}\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.inert_iff_uniformizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

DimensionGroup(A) is the actual stationary module colimit of this integer transition. The original left H-action sends each vertex (i,h) to (i,g*h), commutes with adjacency, and therefore induces groupAction(A,g) on that colimit. Inert(A) means groupAction(A,g) equals the identity for every g; uniformization is not part of this definition. Uniformizes(A) means that some positive natural exponent has all actual group coefficients constant in each matrix entry.

The finite vertex basis and finite group give a common stage N at which T_A^N composed with every left translation equals T_A^N. Reading basis coefficients equates every coefficient of A^N; conversely uniform coefficients imply those stage equations on the basis. Advancing from N to N+1 supplies a positive exponent even when the common stage was zero. Inertness is identity on the underlying stationary group; the argument does not require a separately constructed ordered-group API or an order-unit normalization.

**Theorem 1.13 (The full threshold and unchanged construction).**

$$\forall H \in Type, groupH \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), n \in Nat, topologyH \in \operatorname{TopologicalSpace}\left(H\right), discreteH \in \operatorname{DiscreteTopology}\left(H\right), A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, n, n\right), essentialA \in \operatorname{Essential}\left(\operatorname{baseGraph}\left(A\right)\right), essentialB \in \operatorname{Essential}\left(\operatorname{baseGraph}\left(B\right)\right), inertA \in \operatorname{Inert}\left(A\right), inertB \in \operatorname{Inert}\left(B\right), sameAugmentation \in \operatorname{matrixAugmentation}\left(A\right) = \operatorname{matrixAugmentation}\left(B\right),\; \left(\left(\operatorname{Subsingleton}\left(H\right) \Rightarrow \left(\operatorname{tau}\left(A\right) = \operatorname{finiteWithTop}\left(1\right) \land \left(\operatorname{tau}\left(B\right) = \operatorname{finiteWithTop}\left(1\right) \land A = B\right)\right)\right) \land \left(\left(\forall W \in \operatorname{RationalDecomposition}\left(H\right), positiveN \in \operatorname{NatPositive}\left(n\right),\; \operatorname{max}\left(\operatorname{tau}\left(A\right), \operatorname{tau}\left(B\right)\right) \le \operatorname{finiteWithTop}\left(\operatorname{multiply}\left(n, \operatorname{bH}\left(W\right)\right)\right)\right) \land \left(\forall k \in Nat, threshold \in \operatorname{max}\left(\operatorname{tau}\left(A\right), \operatorname{tau}\left(B\right)\right) \le \operatorname{finiteWithTop}\left(k\right),\; \exists hk \in \operatorname{NatPositive}\left(k\right),\; \exists hpower \in \operatorname{matrixPower}\left(A, k\right) = \operatorname{matrixPower}\left(B, k\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{rationalEntry}\left(\operatorname{matrixPower}\left(A, k\right), i, j\right) = \operatorname{scalarMultiply}\left(\operatorname{castRat}\left(\operatorname{entry}\left(\operatorname{matrixPower}\left(\operatorname{matrixAugmentation}\left(A\right), k\right), i, j\right)\right), \operatorname{average}\left(H\right)\right)\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{rationalEntry}\left(\operatorname{matrixPower}\left(B, k\right), i, j\right) = \operatorname{scalarMultiply}\left(\operatorname{castRat}\left(\operatorname{entry}\left(\operatorname{matrixPower}\left(\operatorname{matrixAugmentation}\left(A\right), k\right), i, j\right)\right), \operatorname{average}\left(H\right)\right)\right) \land \left(\left(\forall x \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right),\; \operatorname{original181History}\left(A, B, hk, \operatorname{equalPowerFiberCounts}\left(A, B, hk, hpower\right), x\right) = \operatorname{apply}\left(\operatorname{equalPowerHomeomorph}\left(A, B, hk, hpower\right), x\right)\right) \land \left(\left(\forall a \in H, x \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right),\; \operatorname{apply}\left(\operatorname{equalPowerHomeomorph}\left(A, B, hk, hpower\right), \operatorname{groupHistory}\left(A, a, x\right)\right) = \operatorname{groupHistory}\left(B, a, \operatorname{apply}\left(\operatorname{equalPowerHomeomorph}\left(A, B, hk, hpower\right), x\right)\right)\right) \land \left(\left(\forall x \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right),\; \operatorname{apply}\left(\operatorname{equalPowerHomeomorph}\left(A, B, hk, hpower\right), \operatorname{iterate}\left(\operatorname{shift}\left(\operatorname{expandedGraph}\left(A\right)\right), k, x\right)\right) = \operatorname{iterate}\left(\operatorname{shift}\left(\operatorname{expandedGraph}\left(B\right)\right), k, \operatorname{apply}\left(\operatorname{equalPowerHomeomorph}\left(A, B, hk, hpower\right), x\right)\right)\right) \land \left(\left(\forall x \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right),\; \operatorname{apply}\left(\operatorname{equalPowerHomeomorph}\left(A, B, hk, hpower\right), \operatorname{shift}\left(\operatorname{expandedGraph}\left(A\right), x\right)\right) = \operatorname{shift}\left(\operatorname{expandedGraph}\left(B\right), \operatorname{apply}\left(\operatorname{equalPowerHomeomorph}\left(A, B, hk, hpower\right), x\right)\right)\right) \Rightarrow A = B\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\operatorname{Nontrivial}\left(H\right) \Rightarrow \left(\operatorname{NatPositive}\left(n\right) \Rightarrow \left(\exists W \in \operatorname{RationalDecomposition}\left(H\right),\; \operatorname{max}\left(\operatorname{tau}\left(A\right), \operatorname{tau}\left(B\right)\right) \le \operatorname{finiteWithTop}\left(\operatorname{multiply}\left(n, \operatorname{bH}\left(W\right)\right)\right) \land \left(\forall k \in Nat, threshold \in \operatorname{finiteWithTop}\left(\operatorname{multiply}\left(n, \operatorname{bH}\left(W\right)\right)\right) \le \operatorname{finiteWithTop}\left(k\right),\; \exists hk \in \operatorname{NatPositive}\left(k\right),\; \exists hpower \in \operatorname{matrixPower}\left(A, k\right) = \operatorname{matrixPower}\left(B, k\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{rationalEntry}\left(\operatorname{matrixPower}\left(A, k\right), i, j\right) = \operatorname{scalarMultiply}\left(\operatorname{castRat}\left(\operatorname{entry}\left(\operatorname{matrixPower}\left(\operatorname{matrixAugmentation}\left(A\right), k\right), i, j\right)\right), \operatorname{average}\left(H\right)\right)\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right),\; \operatorname{rationalEntry}\left(\operatorname{matrixPower}\left(B, k\right), i, j\right) = \operatorname{scalarMultiply}\left(\operatorname{castRat}\left(\operatorname{entry}\left(\operatorname{matrixPower}\left(\operatorname{matrixAugmentation}\left(A\right), k\right), i, j\right)\right), \operatorname{average}\left(H\right)\right)\right) \land \left(\left(\forall x \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right),\; \operatorname{original181History}\left(A, B, hk, \operatorname{equalPowerFiberCounts}\left(A, B, hk, hpower\right), x\right) = \operatorname{apply}\left(\operatorname{equalPowerHomeomorph}\left(A, B, hk, hpower\right), x\right)\right) \land \left(\left(\forall a \in H, x \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right),\; \operatorname{apply}\left(\operatorname{equalPowerHomeomorph}\left(A, B, hk, hpower\right), \operatorname{groupHistory}\left(A, a, x\right)\right) = \operatorname{groupHistory}\left(B, a, \operatorname{apply}\left(\operatorname{equalPowerHomeomorph}\left(A, B, hk, hpower\right), x\right)\right)\right) \land \left(\left(\forall x \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right),\; \operatorname{apply}\left(\operatorname{equalPowerHomeomorph}\left(A, B, hk, hpower\right), \operatorname{iterate}\left(\operatorname{shift}\left(\operatorname{expandedGraph}\left(A\right)\right), k, x\right)\right) = \operatorname{iterate}\left(\operatorname{shift}\left(\operatorname{expandedGraph}\left(B\right)\right), k, \operatorname{apply}\left(\operatorname{equalPowerHomeomorph}\left(A, B, hk, hpower\right), x\right)\right)\right) \land \left(\left(\forall x \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right),\; \operatorname{apply}\left(\operatorname{equalPowerHomeomorph}\left(A, B, hk, hpower\right), \operatorname{shift}\left(\operatorname{expandedGraph}\left(A\right), x\right)\right) = \operatorname{shift}\left(\operatorname{expandedGraph}\left(B\right), \operatorname{apply}\left(\operatorname{equalPowerHomeomorph}\left(A, B, hk, hpower\right), x\right)\right)\right) \Rightarrow A = B\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.original18_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A and B are natural group-ring matrices with the same actual augmentation matrix. Their finite base graphs are essential, and their original left H-actions are inert on the stationary dimension groups of the actual integer free-expansion adjacencies. NatPositive means strictly positive. The displayed equalPowerFiberCounts denotes the existing fiber_counts_of_equal_power proof on the same A, B, hk and hpower. Tau is the least positive uniform exponent, or infinity if no such exponent exists. The displayed existential proofs hk and hpower express conclusions 0<k and A^k=B^k; neither is an additional premise.

The final conjunct supplies an actual single decomposition W when H is nontrivial and n is positive. Its own original block orders give the displayed cutoff, and this same W controls the constructed map for every k at least that cutoff. No decomposition or cutoff is an extra premise. The preceding clauses still cover every supplied W and every k at least max tau, including smaller admissible exponents. For nontrivial H, an augmentation-first RationalDecomposition is supplied by the rational splitting theorem. The cutoff clause holds for every such decomposition W and every positive n. It retains W's original nontrivial rational block orders r_l, with bH(W)=max_l r_l, giving max(tau(A),tau(B)) at most n*bH(W). Therefore every k at least n*bH(W) satisfies the final clause, while all smaller k at least the original max-tau threshold remain included. For trivial H both tau values are one and equal augmentation already gives A=B. Zero matrices have tau one by the positive convention; no empty b_H is assigned.

The rational equations are equalities in Q[H] at each entry: both A^k and B^k equal the corresponding entry of the k-th power of their common augmentation matrix times e_H, whose actual coefficients are 1/|H|. The equality A^k=B^k itself is in the natural group-matrix semiring. No commutativity of H or replacement by complex irreducible degrees is used.

For each admissible k, the exact equalPowerHomeomorph uses the existing ordered-label fiber bijections and the same fixed nonoverlapping integer blocks [jk,(j+1)k-1]. Operational equality identifies original181History with this homeomorphism; the next equations give the original left H-equivariance and the k-step shift law for this same map. Positive and negative positions use the same quotient-and-remainder construction, and k=1 is included. Different k may give different maps.

If this exact fixed-block map also commutes with the original one-step shift, essentiality and fixed-block rigidity force A=B. The conclusion does not forbid other overlapping codes, other state presentations or other original-time conjugacies. No unit-time conjugacy is claimed from inertness alone.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.actual_expansion_adjacency`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.equal_power_of_tau_le`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.finite_family_inert_iff_eventual`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.inert_iff_uniformizes`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.nonempty_decomposition`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.original18_1`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.tau_eq_one_iff_uniform`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.tau_le_cutoff`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.tau_le_iff_uniform_power`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.uniform_eq_augmentation_smul_average`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.uniform_iff_blocks_zero`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.uniform_iff_tail_zero`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy.uniform_rational_expression`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedGroupOverlap](CountedGroupOverlap.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FixedBlockRigidity](FixedBlockRigidity.md)
