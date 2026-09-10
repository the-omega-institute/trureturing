# Prime Infinity and the Witnessed Core Limit

## Abstract

Admissible chains: unique core limit; strict binding with exhaustion: infinite primes.

**Remark 1.1 (Total admissible transformations).**

Lean statement: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.GeneratedChain`

*Formalization.* `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.GeneratedChain` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix a proof system s and a sequence L of legal finite snapshots. A transformation is a total function on all legal ledgers. It is admissible when every input is extended, with every old witness retained. GeneratedChain(L) requires each successor L(t+1) to equal T(L(t)) for some such globally admissible T. The frozen sets grow monotonically, and witnesses on overlapping stages agree by comparison at max(i,j). Stuttering is allowed, and a dependent and its prerequisites may enter in the same stage.

**Theorem 1.2 (Extensions are exactly attainable admissible steps).**

$$\forall s: ProofSystem, M, N: \operatorname{LegalLedger}\left(s\right),\\{}\operatorname{Extends}\left(M, N\right) \iff \exists T: \operatorname{LegalLedger}\left(s\right) \to \operatorname{LegalLedger}\left(s\right), \operatorname{Admissible}\left(T\right) \land N = \operatorname{T}\left(M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.extends_iff_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an extension from one snapshot to another, define a total transformation sending that particular input to the extension and fixing every other input. It is globally admissible. The reverse implication evaluates admissibility at the given input. Together with core extension, this identifies the attainability preorder and its antisymmetric frozen-core projection.

**Remark 1.3 (The raw union witness).**

Lean statement: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.limit_witness_agrees`

*Formalization.* `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.limit_witness_agrees` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write unionNodes(L) for the union over all natural-number stages of N(L(t)). Glue the coherent witnesses on these sets by Set.iUnionLift. For a proposition in N(L(t)), the resulting witness equals its stored witness at t. Define the raw union edge from the references of this glued witness. Its incoming edges at an old target agree exactly with the old incoming edges. Reference closure keeps all those predecessors in the old stage.

**Theorem 1.4 (Old targets have no new ancestors).**

$$\forall s: ProofSystem, L: Nat \to \operatorname{LegalLedger}\left(s\right),\\{}\operatorname{GeneratedChain}\left(L\right) \Rightarrow\\{}\forall t: Nat, a, b: \operatorname{P}\left(s\right), b \in \operatorname{N}\left(\operatorname{L}\left(t\right)\right) \Rightarrow\\{}(\operatorname{StrictReachable}\left(\operatorname{limitEdge}\left(L\right), a, b\right) \iff \operatorname{StrictReachable}\left(\operatorname{E}\left(\operatorname{core}\left(\operatorname{L}\left(t\right)\right)\right), a, b\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.limit_path_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every old frozen stage is predecessor-closed for the raw union relation, giving a dependency filtration. The least predecessor-closed set containing a target contains each vertex on a path into it. Induction backward from an old target then reflects every path into its old snapshot, using the incoming-edge equality. The forward implication does not assume that the union is already acyclic.

**Remark 1.5 (The lawful core).**

Lean statement: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.limitCore`

*Formalization.* `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.limitCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Acceptance, permitted axioms, and reference closure of the union witness follow from any stage containing its target. A cycle in the raw union would reflect into such a stage and contradict its acyclicity. This constructs a witnessed core with frozen set unionNodes(L); its edges are exactly the union of the stage edges. For every p already present at t, Anc(limitCore(L),p) equals Anc(core(L(t)),p), so each present node has finitely many ancestors.

**Theorem 1.6 (The core is the least upper bound).**

$$\forall s: ProofSystem, L: Nat \to \operatorname{LegalLedger}\left(s\right),\\{}\operatorname{GeneratedChain}\left(L\right) \Rightarrow\\{}\forall Q: \operatorname{WitnessedCore}\left(s\right),\\{}\operatorname{CoreExtends}\left(\operatorname{limitCore}\left(L\right), Q\right) \iff \forall t: Nat, \operatorname{CoreExtends}\left(\operatorname{core}\left(\operatorname{L}\left(t\right)\right), Q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.limit_isLeastUpperBound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every stage extends into the union core. If another core Q extends all stages, it contains every union node and agrees with its witness at a containing stage. Thus the union core extends into Q. CoreLimit(L,U) denotes precisely these upper-bound and leastness clauses. Antisymmetry of core extension gives uniqueness on (N,E,w). No order or limit is imposed on registered frontiers.

**Theorem 1.7 (Exhaustion is equality with the theorem set).**

$$\forall s: ProofSystem, L: Nat \to \operatorname{LegalLedger}\left(s\right),\\{}\operatorname{Exhausts}\left(L\right) \iff \operatorname{unionNodes}\left(L\right) = \operatorname{Thm}\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.exhausts_iff_iUnion_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exhausts(L) means that each p in Thm(s) occurs in N(L(t)) at some natural-number stage t. Every frozen node already belongs to Thm(s), by its accepted permitted witness, which proves the reverse inclusion. For a generated exhaustive chain, the same finite growing sets form a Set.FiniteExhaustion of Thm(s). Existence of an exhaustive chain for an arbitrary proof system is not asserted.

**Theorem 1.8 (The finite-total-prime contradiction).**

$$\forall s: ProofSystem, L: Nat \to \operatorname{LegalLedger}\left(s\right),\\{}\forall B: \operatorname{ClosureOperator}\left(\operatorname{Set}\left(\operatorname{P}\left(s\right)\right)\right),\\{}(\forall R: \operatorname{Set}\left(\operatorname{P}\left(s\right)\right), \operatorname{Finite}\left(R\right) \land R \subseteq \operatorname{Thm}\left(s\right) \Rightarrow \operatorname{inter}\left(\operatorname{B}\left(R\right), \operatorname{Thm}\left(s\right)\right) \subset \operatorname{Thm}\left(s\right)) \land \operatorname{Finite}\left(\operatorname{PrimeUnion}\left(B, L\right)\right) \Rightarrow\\{}\operatorname{PrimeUnion}\left(B, L\right) \subseteq \operatorname{Thm}\left(s\right) \land (\forall t: Nat, \operatorname{N}\left(\operatorname{L}\left(t\right)\right) \subseteq \operatorname{B}\left(\operatorname{PrimeUnion}\left(B, L\right)\right)) \land \\{}\operatorname{unionNodes}\left(L\right) \subseteq \operatorname{inter}\left(\operatorname{B}\left(\operatorname{PrimeUnion}\left(B, L\right)\right), \operatorname{Thm}\left(s\right)\right) \land \operatorname{inter}\left(\operatorname{B}\left(\operatorname{PrimeUnion}\left(B, L\right)\right), \operatorname{Thm}\left(s\right)\right) \subset \operatorname{Thm}\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.finite_total_primes_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write PrimeUnion(B,L) for the union over all stages of Prime(B,core(L(t))), and call this set R. Suppose R is finite. Each of its members has an accepted permitted witness, so R is contained in Thm(s). Finite prime generation and monotonicity of B put every N(L(t)) in B(R). Their union therefore lies in B(R) intersect Thm(s). Strict binding makes that intersection a proper subset of Thm(s), contradicting exhaustion. These inclusions hold for any family of legal finite snapshots.

**Theorem 1.9 (The limit primes are exactly the union of the stage primes).**

$$\forall s: ProofSystem, L: Nat \to \operatorname{LegalLedger}\left(s\right),\\{}\forall B: \operatorname{ClosureOperator}\left(\operatorname{Set}\left(\operatorname{P}\left(s\right)\right)\right),\\{}\operatorname{GeneratedChain}\left(L\right) \Rightarrow\\{}\operatorname{Prime}\left(B, \operatorname{limitCore}\left(L\right)\right) = \operatorname{PrimeUnion}\left(B, L\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.limit_prime_eq_iUnion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a proposition in an old stage, the ancestor set is exactly unchanged in the limit, hence so is membership in B of that ancestor set. Every limit node occurs at some stage. These two facts give both inclusions without any continuity or finitarity assumption on B.

**Theorem 1.10 (Prime infinity with the unique exhaustive core).**

$$\forall s: ProofSystem, L: Nat \to \operatorname{LegalLedger}\left(s\right),\\{}\forall B: \operatorname{ClosureOperator}\left(\operatorname{Set}\left(\operatorname{P}\left(s\right)\right)\right),\\{}\operatorname{GeneratedChain}\left(L\right) \land (\forall R: \operatorname{Set}\left(\operatorname{P}\left(s\right)\right), \operatorname{Finite}\left(R\right) \land R \subseteq \operatorname{Thm}\left(s\right) \Rightarrow \operatorname{inter}\left(\operatorname{B}\left(R\right), \operatorname{Thm}\left(s\right)\right) \subset \operatorname{Thm}\left(s\right)) \land \operatorname{Exhausts}\left(L\right) \Rightarrow\\{}\operatorname{Infinite}\left(\operatorname{PrimeUnion}\left(B, L\right)\right) \land \exists! U: \operatorname{WitnessedCore}\left(s\right),\\{}\operatorname{CoreLimit}\left(L, U\right) \land \operatorname{N}\left(U\right) = \operatorname{Thm}\left(s\right) \land \operatorname{Prime}\left(B, U\right) = \operatorname{PrimeUnion}\left(B, L\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.prime_infinity_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every proof system, every closure operator B, and every globally admissible exhaustive chain satisfying strict binding, the union of the stage primes is infinite. There is exactly one witnessed core U satisfying CoreLimit(L,U), N(U)=Thm(s), and Prime(B,U)=PrimeUnion(B,L). The finite-total-prime contradiction proves infinitude; witness gluing and the least-upper-bound property give the core, while ancestor stability gives its prime set.

**Theorem 1.11 (Infinitely many primes in the limit).**

$$\forall s: ProofSystem, L: Nat \to \operatorname{LegalLedger}\left(s\right),\\{}\forall B: \operatorname{ClosureOperator}\left(\operatorname{Set}\left(\operatorname{P}\left(s\right)\right)\right),\\{}\operatorname{GeneratedChain}\left(L\right) \land (\forall R: \operatorname{Set}\left(\operatorname{P}\left(s\right)\right), \operatorname{Finite}\left(R\right) \land R \subseteq \operatorname{Thm}\left(s\right) \Rightarrow \operatorname{inter}\left(\operatorname{B}\left(R\right), \operatorname{Thm}\left(s\right)\right) \subset \operatorname{Thm}\left(s\right)) \land \operatorname{Exhausts}\left(L\right) \Rightarrow\\{}\operatorname{Infinite}\left(\operatorname{Prime}\left(B, \operatorname{limitCore}\left(L\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.limit_prime_infinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prime-set equality transfers infinitude to the limit. Since primes belong to the frozen set, this exhaustive limit cannot be a finite snapshot. Any disjoint frontier can be attached to its core, including the empty set, without changing ancestry or primes; this does not select a limit of the frontiers.

**Remark 1.12 (The structural reading).**

Lean statement: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.prime_infinity_complete`

*Formalization.* `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.prime_infinity_complete` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Euclid and Godel analogy concerns the obstruction that a finite collection of generators cannot cover every theorem by binding closure. It supplies neither a formal equivalence between those classical arguments nor a theorem about a particular collection of actual proof-assistant declarations. The result is conditional on the displayed structural hypotheses. It adds no global countability, kernel soundness, semantic consistency, universal certificate availability, or convergence assumption.

## References

- Truth anchor: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.GeneratedChain`
- Truth anchor: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.exhausts_iff_iUnion_eq`
- Truth anchor: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.extends_iff_admissible`
- Truth anchor: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.finite_total_primes_bound`
- Truth anchor: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.limitCore`
- Truth anchor: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.limit_isLeastUpperBound`
- Truth anchor: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.limit_path_iff`
- Truth anchor: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.limit_prime_eq_iUnion`
- Truth anchor: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.limit_prime_infinite`
- Truth anchor: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.limit_witness_agrees`
- Truth anchor: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.prime_infinity_complete`
- Truth anchor: `D5/S3/ConceptDynamics/FixedPointPhilosophy/PrimeInfinity.prime_infinity_complete`
- Dependency: [D5/S3/ConceptDynamics/DagCompletion/DependencyClosedFiltration](../DagCompletion/DependencyClosedFiltration.md)
- Dependency: [D5/S3/ConceptDynamics/FixedPointPhilosophy/WitnessedLedger](WitnessedLedger.md)
