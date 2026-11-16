# Circuit balance and least confirmation

## Abstract

On the original closed finite dimensional real cone with a strictly positive unit, full finite pure-mixture comparison, all-reference circuit balance and reciprocal whole-cone least confirmation are equivalent.

Let A be a finite dimensional real normed vector space, C a closed cone containing zero and closed under addition and nonnegative scaling, with real span all of A. The original linear unit u is strictly positive at every nonzero point of C. Strict positivity also excludes nonzero lines in C. The chosen compatible norm gives the usual finite dimensional topology on this same A; its numerical values enter no comparison or effect definition. All effects act on the original A. No pure-generation equality, finite pure-decomposition supplier, relation preservation, reciprocity or least confirmation is a premise. The theorem includes the zero carrier as well as every original nonzero carrier.

**Theorem 1.1 (Compactness of the entire base).**

$$\forall A \in Type,\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, A\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, A\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, A\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, A, \mathbb{R}\right),\; \operatorname{IsClosed}\left(C\right) \Rightarrow \left(\left(\forall x \in A,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \operatorname{IsCompact}\left(\operatorname{base}\left(C, u\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.base_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Closedness and strict positivity make the entire normalized base compact, including the empty base. A positive minimum of the unit on the cone's unit-sphere section bounds the norm of normalized points.

**Theorem 1.2 (Extend pure nonnegativity to the entire cone).**

$$\forall A \in Type,\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, A\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, A\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, A\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, A, \mathbb{R}\right),\; \forall f \in \operatorname{LinearMap}\left(\mathbb{R}, A, \mathbb{R}\right),\; \operatorname{IsCompact}\left(\operatorname{base}\left(C, u\right)\right) \Rightarrow \left(\left(\forall x \in A,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; 0\leq \operatorname{apply}\left(f, p\right)\right) \Rightarrow \left(\forall x \in A,\; x\in C \Rightarrow 0\leq \operatorname{apply}\left(f, x\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.nonneg_on_cone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original linear functional f, nonnegativity on all extreme points extends first to their closed convex hull, the entire compact base, and then by positive rescaling to every cone vector. The zero vector is handled directly.

**Theorem 1.3 (Extend pure bounds to the full proper interval).**

$$\forall A \in Type,\; [\operatorname{NormedAddCommGroup}\left(A\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, A\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, A\right)] \forall C \in \operatorname{PointedCone}\left(\mathbb{R}, A\right),\; \forall u \in \operatorname{LinearMap}\left(\mathbb{R}, A, \mathbb{R}\right),\; \forall f \in \operatorname{LinearMap}\left(\mathbb{R}, A, \mathbb{R}\right),\; \operatorname{IsCompact}\left(\operatorname{base}\left(C, u\right)\right) \Rightarrow \left(\left(\forall x \in A,\; x\in C \Rightarrow \left(x\neq 0 \Rightarrow 0< \operatorname{apply}\left(u, x\right)\right)\right) \Rightarrow \left(\left(\forall p \in \operatorname{pure}\left(C, u\right),\; 0\leq \operatorname{apply}\left(f, p\right) \land \operatorname{apply}\left(f, p\right)\leq 1\right) \Rightarrow \operatorname{proper}\left(C, u, f\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.cone_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bounds between zero and one at every global pure point imply 0<=f<=u on the entire original cone. Apply pure nonnegativity extension to f and to u-f. No finite pure-decomposition premise is required.

**Definition 1.4 (The entire normalized base).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.base`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.base` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the specified C and u, base(C,u) consists of all x in C with u(x)=1. No selected preparations replace this base.

**Definition 1.5 (All pure points).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pure set P is exactly the set of extreme points of base(C,u), with extremality over the real scalars. It is not an independently chosen list and need not be finite or consist of exposed points.

**Theorem 1.6 (Affine images preserve extreme points).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.affine_extreme_image`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.affine_extreme_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For additive real module carriers E and F, a convex set S, an affine map f that is injective on S, and an extreme point x of S, the image f(x) is an extreme point of the image f '' S. This is the shared generic transport used by both the Bell-polytope supplier and the whole-pair ball consumer.

**Definition 1.7 (The full proper interval).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.proper`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.proper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real linear functional f on A is proper precisely when 0 <= f(x) <= u(x) for every x in the original C. Every such f is available in this mathematical interval.

**Definition 1.8 (All confirming proper effects).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.confirms`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.confirms` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate confirms(C,u,p,f) requires f to be proper on all of C and f(p)=1. In particular the original u confirms each pure point.

**Definition 1.9 (The original comparison lower envelope).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.comparison`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.comparison` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a pure reference p, the value T_p(x) is the real infimum of f(x) over all original proper effects f confirming p. For each x in C this set of readings is nonempty and bounded below by zero. The theorem proves that its infimum is attained by the constructed effect; it does not assume attainment.

**Definition 1.10 (Actual minimal signed relations).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.circuit`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.circuit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a finite subset s of P, a coefficient function c on s is a circuit when c is nonzero, its weighted sum of the original pure vectors is zero, and any nonzero signed relation w supported inside the support of c has exactly that support. The finite ambient subset may contain unused labels; the actual support is the circuit. Subtype labels are distinct original pure points. No preservation of signs is imposed on competitors.

**Definition 1.11 (Balance on every circuit).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.balanced`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.balanced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A scalar assignment v on P is balanced when, for every finite subset s and every circuit c on s, the sum of c(i)v(i) is zero. Applied at reference p, the assignment is v(q)=T_q(p); reciprocity is absent from this definition.

**Definition 1.12 (Every finite pure mixture).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.fullMixture`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.fullMixture` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Full S requires, for every pure reference p, every natural n, every list q indexed by Fin n of original pure points and every nonnegative real weight list summing to one, T_p(sum_i w_i q_i)=sum_i w_i T_{q_i}(p). Zero weights, unequal positive weights and repeated labels remain included. An empty normalized weight list is impossible, rather than excluded by a supplier.

**Definition 1.13 (Reciprocal least confirming effects).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.reciprocalLeast`

*Formalization.* `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.reciprocalLeast` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is a family of real linear effects e_p on A, one for each original pure p, with e_p proper and confirming p, e_p(x)<=f(x) for every x in the entire original cone and every original proper confirmer f of p, and e_p(q)=e_q(p) for every pair of pure points. Leastness is required on the whole cone, including nonnormalized positive vectors.

**Theorem 1.14 (Constructing reciprocal least confirmation).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.circuit_balance_least_confirmation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.circuit_balance_least_confirmation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the original closed generating C and strictly positive u, all-reference circuit balance yields real linear effects e_p satisfying six conclusions: e_p is proper and confirms p; e_p(q)=T_q(p); T_p(q)=T_q(p); e_p is least among every original proper confirmer on all of C; T_p(x)=e_p(x) for every x in C; and full S holds for every finite pure list. The identity with the lower envelope is asserted only on C, not on signed vectors outside it.

The normalized base is closed. On the compact intersection of C with the unit sphere, the continuous unit has a positive minimum; rescaling bounds the norm of every normalized positive vector. The empty-base case is handled directly. Thus the base is compact and convex. Krein–Milman gives that it is the closed convex hull of all its extreme points. The span of those points is closed in finite dimensions, so contains the base; strict-unit rescaling and generatingness give their span equal to A. Closed linear halfspaces similarly extend pure nonnegativity to the base and then to all of C. This proves exactly the spanning and inequality-extension facts needed here without a finite decomposition premise.

In real coordinates, apply the existing support-contained circuit decomposition to each finite original relation. Balance annihilates every circuit summand, hence every relation, and the existing linear quotient construction descends q maps to T_q(p) to e_p on A. Pure bounds extend through the closed halfspaces, giving 0<=e_p<=u on C and e_p(p)=1. Since the full proper interval includes e_p, T_p(q)<=e_p(q)=T_q(p). Interchanging references supplies the reverse inequality. Pure domination against every confirmer then extends to all of C. Leastness and attainment identify T_p with e_p there, and linearity gives full S.

**Theorem 1.15 (Full comparison is equivalent to circuit balance).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.full_mixture_iff_circuit_balance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.full_mixture_iff_circuit_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same C and u, full S is equivalent to all-reference circuit balance. That balance is equivalent to its conjunction with pure reciprocity, and to reciprocal least confirming effects on the entire cone. These are the four conditions of Quantum Origin V Theorem 77.16, on the unchanged full state and full proper-effect carrier.

For the converse, take any finite signed relation sum_i c_i q_i=0 on the original pure points. Applying u gives sum_i c_i=0. Write a_i=max(c_i,0) and b_i=max(-c_i,0); their masses and weighted original vectors agree. Add the same reference p with unit weight to both sides, and divide by the positive common mass 1+sum_i a_i. These are two nonnegative normalized pure preparations of exactly the same vector. Full S evaluates them equally. Cancelling the common reference contribution and common mass proves sum_i c_i T_{q_i}(p)=0, including the zero relation. Reindexing finite types by Fin n introduces no new preparation assumption. Conversely, reciprocal least effects attain the original infimum at every positive vector; their linearity and pure reciprocity give full S.

**Theorem 1.16 (Descent of balanced assignments).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.descends`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.descends` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every set P spanning A and every scalar assignment balanced on all its finite circuits, there exists an original real linear functional taking those assigned values on every p in P.

**Theorem 1.17 (Pure points are normalized positive vectors).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every pure point belongs to the original cone and has original unit value one.

**Theorem 1.18 (Convexity of the normalized base).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.base_convex`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.base_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entire normalized base of the original cone and linear unit is convex.

**Theorem 1.19 (Normalization of nonzero positive vectors).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.normalized_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.normalized_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a unit strictly positive on every nonzero cone vector, multiplying any nonzero vector x in the cone by the inverse of u(x) places it in the entire normalized base. The same theorem applies to native face cones by restricting strict positivity along their inclusion.

**Theorem 1.20 (Pure spanning of the original carrier).**

Lean statement: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure_span`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the compact original base, strictly positive unit and generating original cone, all pure points together linearly span the original carrier.

The circuit-size and two-points-per-sign clauses of Lemma 77.15, the mixed-remainder equivalence of Theorem 77.19, and the EJA, PRE, reset, H13/C13 and static or operational consumers remain outside this result. The proof needs neither a finite Minkowski theorem nor an assumption supplying pure decompositions. Mathematical effects and mixtures do not supply actual preparation programs, menus, histories, references or operations.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.affine_extreme_image`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.balanced`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.base`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.base_compact`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.base_convex`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.circuit`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.circuit_balance_least_confirmation`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.comparison`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.cone_bound`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.confirms`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.descends`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.fullMixture`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.full_mixture_iff_circuit_balance`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.nonneg_on_cone`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.normalized_mem`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.proper`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure_mem`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.pure_span`
- Truth anchor: `D5/S3/Quantum/Foundation/CircuitBalancedConfirmation.reciprocalLeast`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit](../Entanglement/AbsolutePPT/NonnegativeKernelCircuit.md)
