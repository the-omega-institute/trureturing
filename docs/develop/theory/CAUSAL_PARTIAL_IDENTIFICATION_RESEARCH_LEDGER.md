# Causal Partial Identification Research Ledger

## 1. Purpose

This ledger records the research and formalization work carried by pull request #5029. It separates reusable libraries, concrete causal truth sources, literature-facing interfaces, semantic boundaries, and remaining proof obligations.

The governing proof pipeline is:

```text
causal and statistical assumptions
  -> admissible structural response models
  -> feasible coupling or response-type set
  -> primal query optimization
  -> replayable dual validity certificate
  -> attaining primal witness
  -> Lean sharpness theorem
```

For convex finite models, exact endpoint witnesses and affine interpolation fill the complete interval. Polynomial cross-world restrictions and unions over graph completions can produce nonconvex or disconnected identified ranges.

## 2. Reused library layer

The causal lane reuses the following repository truth sources.

- `D5/S0/Certificates/RationalFarkas` checks exact rational infeasibility certificates.
- `D5/S0/Certificates/LinearObjectiveDual` checks exact rational lower and upper objective certificates and matching primal witnesses.
- `D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification` separates universal validity, endpoint attainment, convexity, and interval sharpness.
- `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification` separates exact endpoints from full range sharpness and transports valid bounds from outer relaxations.
- `D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification` packages finite causal LP rows with data, structural, and sensitivity provenance.
- `D5/S3/ConceptDynamics/Causal/StructuralEvaluationSemantics` supplies the canonical finite order semantics used by causal evaluation.

The library audit found no pre-existing exact compiler from required edges, forbidden edges, and query-order admissibility to a finite support polytope.

## 3. Finite sharp-bounds layer

The first layer proves:

1. exact rational primal-dual certificates for finite linear objectives;
2. a generic convex sharp-interval theorem;
3. an explicit four-cell Frechet coupling with an exact feasible-target theorem;
4. a disagreement-cap tightening with replayable slack identities;
5. a ternary-treatment, ternary-outcome response-type instance;
6. a nonconvex identification core;
7. a polynomial cross-world independence example with a sharp singleton query and a globally nonconvex independence family.

The common mathematical object is a feasible counterfactual coupling set and a scalar projection of that set.

## 4. Covariate aggregation and shared parameters

`CovariateSharpAggregation` proves that independently combinable stratum intervals

```text
Q_c in [L_c, U_c]
```

aggregate sharply to

```text
[sum_c w_c L_c, sum_c w_c U_c]
```

under nonnegative weights and an explicit joint-selection premise.

`CovariateSharedParameterObstruction` proves that stratum projections alone do not justify that conclusion. Two complementary strata can each project to `[0, 1]`, while one shared parameter fixes the equal-weight global query at the singleton `{1 / 2}`.

`ComplementSymmetryProjection` isolates the underlying affine involution. The value one half is the fixed point of `x -> 1 - x` and the invariant component retained by equal-weight averaging. This observation has no established implication for the Riemann hypothesis.

## 5. Partial-graph information order and completion ranges

`PartialGraphInformationOrder` represents partial diagrams by required and forbidden directed edges. Refinement preserves every previous assertion and may add more. It proves:

```text
stronger diagram information
  -> fewer compatible complete graphs
  -> fewer compatible structural models
  -> a smaller attainable query set.
```

Valid weaker-family bounds survive refinement. Exact lower endpoints can only rise, and exact upper endpoints can only fall.

`PartialGraphCompletionRange` records a second semantic fact. When one complete graph is a single unknown global object, the partial-graph identified range is the union of completion-specific ranges. Its lower and upper envelope may be exact while the interval between them contains unattainable gaps.

## 6. Query-implied causal order

`QueryImpliedCausalOrder` extracts intervention-to-outcome precedence obligations from counterfactual atoms. Reciprocal obligations are inconsistent with a strict causal order.

`QueryOrderLinearExtension` embeds certified query requirements into a partial order and uses the Szpilrajn theorem to obtain a linear extension preserving every requirement.

`CanonicalResponseSignature` stores one deterministic predecessor-response table at each position of a total order. Finite value spaces give a finite signature carrier, and every Boolean signature event is an exact zero-one linear objective in signature masses.

`CausalOrderLinearProgram` joins those signatures to the finite causal LP interface. `AttainingStructuralModel` realizes every normalized signature law by a finite shared-exogenous structural model whose exogenous states index complete response signatures.

## 7. Conditional extension invariance

`AdjacentIncomparableSwapInvariance` proves that adjacent parent-independent structural updates commute.

`SwapClosureExtensionInvariance` propagates one local swap through a finite certified swap chain. `SwapInvariantEventMass` then transports pointwise structural equality to equality of finite event masses and linear event queries.

`ExtensionInvariantQueryBound` gives the LP-level interface. A signature equivalence preserving every constraint row, right-hand side, and query event preserves the entire attainable query set.

A remaining combinatorial obligation is to construct a certified adjacent-incomparable swap path between arbitrary finite linear extensions of the same partial order. A remaining compiler obligation is to show that each concrete row and query event is equivariant under those swaps.

## 8. Partial-diagram constraint compiler soundness

`PartialDiagramConstraintCompilerSoundness` is the next concrete compiler truth source.

A finite candidate completion supplies:

```text
a directed-edge table
+ a query-order compatibility judgment.
```

The compiler generates:

```text
one nonnegativity row per completion
+ upper and lower normalization rows
+ one zero-support row per required-edge violation
+ one zero-support row per forbidden-edge violation
+ one zero-support row per query-order violation.
```

For a completion mass vector `mu`, the central theorem is:

```text
mu satisfies every generated rational row
iff
mu is normalized, nonnegative, and supported only on admissible completions.
```

This gives both compiler soundness and compiler completeness. The point-mass theorem proves that a deterministic completion witness is feasible exactly when it is admissible. The nonemptiness theorem proves that the support polytope is inhabited exactly when at least one admissible completion exists.

The refinement theorem reuses partial-graph antitonicity. A mass feasible for a stronger diagram remains feasible for every weaker diagram with the same candidate completions and query-order predicate. Rational lower and upper certificates proved on the weaker feasible family therefore remain valid after adding graph information.

## 9. Semantic boundary: mixture versus one global graph

The support compiler has latent-completion mixture semantics. Different units may receive mass from different admissible completions.

That object must be distinguished from epistemic uncertainty about one fixed complete graph. For one global unknown graph, the correct range is:

```text
union over admissible completions of completion-specific identified ranges.
```

Convexifying that union silently changes the causal model by introducing a latent graph index. Future compilers must expose this choice in their type and certificate payload.

## 10. Interfaces to 2026 research

The current literature interface is organized as follows.

- Partial causal diagrams: Xie and Li, arXiv:2602.14503. Structural and auxiliary statistical information is represented as constraints on counterfactual distributions.
- Causal orders: Rossetto and Antonucci, arXiv:2608.24427. Counterfactual queries induce precedence constraints, compatible total orders support canonical response-function programs, and tightness is tied to constructing attaining structural models.
- Covariates and mediators: Shu, Lei, and Li, arXiv:2608.12657. Additional causal knowledge can tighten multivalued probabilities of causation. Mediator factorization may leave the polyhedral lane and enter polynomial feasibility.
- Continuous outcomes: Chaoge et al., arXiv:2605.01883. Copula restrictions constrain infinite-dimensional counterfactual coupling families.

The repository claim boundary is narrower than these papers. The PR proves reusable logical kernels and finite concrete instances. It does not claim a complete reproduction of any paper's general algorithm or theorem family.

## 11. Verification ledger

Required protected-branch checks are:

```text
Candidate harness engineering checks
Canonical Lean report production
Content-addressed dev baseline admission
```

A truth source is considered machine-verified only after the current PR head passes the protected workflow. Scribe freshness is likewise determined by the repository renderer rather than by hand-edited Markdown.

## 12. Next formal research sequence

The partial-diagram lane now advances to:

```text
PartialDiagramConstraintCompilerSoundness
  -> graphical ancestry and non-ancestry semantics
  -> observational and interventional event-row compiler
  -> compiler soundness against finite SCM evaluation
  -> rational primal-dual payload
  -> completion-specific sharp endpoints
  -> exact interval-union normalization across global graph completions.
```

The causal-order lane continues in parallel:

```text
finite linear-extension swap connectivity
  -> row and query equivariance under one adjacent swap
  -> extension-independent compiled LP
  -> permutation transport of primal-dual certificates.
```

The nonlinear lane remains separate for mediator cross-world factorization and continuous copula restrictions.
