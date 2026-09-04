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

For convex finite models, exact endpoint witnesses and affine interpolation fill the complete interval. Polynomial cross-world restrictions, Markovian product families, and unions over graph completions can produce nonconvex or disconnected identified ranges.

## 2. Reused library layer

The causal lane reuses the following repository truth sources.

- `D5/S0/Certificates/RationalFarkas` checks exact rational infeasibility certificates.
- `D5/S0/Certificates/LinearObjectiveDual` checks exact rational lower and upper objective certificates and matching primal witnesses.
- `D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification` separates universal validity, endpoint attainment, convexity, and interval sharpness.
- `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification` separates exact endpoints from full range sharpness and transports valid bounds from outer relaxations.
- `D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification` packages finite causal LP rows with data, structural, and sensitivity provenance.
- `D5/S3/ConceptDynamics/Causal/StructuralEvaluationSemantics` supplies the canonical finite order semantics used by causal evaluation.
- `D5/S3/Entropy/Submodularity/MarkovDataProcessing` supplies finite single-world Markov factorization and mutual-information data processing.
- `D5/S3/ConceptDynamics/Completion/PositivePriorConditionalIndependence` relates positive-prior kernel descent to conditional independence.
- `D5/S3/Estimation/DecisionRisk/StochasticDescentEquivalence` identifies quotient-kernel descent, strong lumpability, and observed transition factorization.

The library audit found no pre-existing exact compiler from required edges, forbidden edges, query-order admissibility, and finite causal-event marginals to one joint completion-signature polytope. It also found no cross-world theorem proving that independent exogenous components remain product-factorized after deterministic response pushforward, or that a counterfactual event becomes a certified LP objective after all but one component law are fixed.

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

## 8. Partial-diagram support compiler

`PartialDiagramConstraintCompilerSoundness` compiles a finite candidate-completion carrier with a directed-edge table and query-order compatibility judgment.

It generates:

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

The point-mass theorem proves that a deterministic completion witness is feasible exactly when it is admissible. The nonemptiness theorem proves that the support polytope is inhabited exactly when at least one admissible completion exists.

The refinement theorem reuses partial-graph antitonicity. A mass feasible for a stronger diagram remains feasible for every weaker diagram with the same candidate completions and query-order predicate. Rational lower and upper certificates proved on the weaker feasible family therefore remain valid after adding graph information.

## 9. Partial-diagram event-row compiler

`PartialDiagramEventRowCompilerSoundness` lifts the completion carrier to joint atoms:

```text
candidate graph completion x deterministic response signature.
```

This is the first truth source in the lane that places graph uncertainty and response-event probabilities in one exact rational program.

Each supplied event has two independent audit labels:

```text
semantic kind: observational | interventional | counterfactual
provenance layer: data | structural | sensitivity.
```

The distinction is substantive. An interventional event may be supplied as experimental data, derived structurally in a special model, or imposed as a sensitivity condition. Event meaning and justification must therefore remain separate fields.

The compiler emits:

```text
one nonnegativity row per completion-signature atom
+ paired normalization rows
+ atomwise zero-support rows for every graph or query-order violation
+ paired upper and lower rows for every supplied causal-event probability.
```

For event `e`, the two statistical rows are exactly

```text
sum_atom 1[e holds on atom] mu_atom <= target_e
-sum_atom 1[e holds on atom] mu_atom <= -target_e.
```

Together they enforce equality. The central theorem is:

```text
mu is feasible for every generated row
iff
mu is a normalized nonnegative joint law,
its support uses only admissible graph completions,
and every supplied event mass equals its exact rational target.
```

The theorem gives compiler soundness and completeness. It applies uniformly to observational, interventional, and counterfactual events because all three become finite Boolean predicates on completion-signature atoms after semantic evaluation.

The module also proves a finite exogenous pushforward identity. Mapping each exogenous state to its graph completion and response signature preserves total mass, nonnegativity, and every Boolean event probability. Conversely, the joint atom carrier itself gives a canonical identity exogenous realization of every feasible event law.

Diagram refinement preserves all event rows and removes admissible support. Consequently, every mass feasible under stronger graph information is feasible under the weaker event compiler, and rational lower or upper certificates for the weaker problem remain valid on the refined problem.

## 10. Markovian response-law factorization

`MarkovianResponseLawFactorization` moves the Markov assumption to the level that directly constrains counterfactual couplings.

A normalized local response law is a nonnegative rational mass vector with total mass one. Two independent components combine as

```text
mu(left, right) = mu_left(left) * mu_right(right).
```

The module proves nonnegativity, normalization, and recovery of both component marginals. More importantly, it proves the deterministic pushforward identity

```text
(f x g)_*(mu_left x mu_right)
  = f_*(mu_left) x g_*(mu_right).
```

Thus independent finite exogenous components induce a product-factorized response law after componentwise deterministic structural maps. The displayed components can represent individual disturbances in a Markovian SCM or whole confounded blocks in a quasi-Markovian SCM. Dependence inside each block remains unrestricted.

For a Boolean counterfactual event `E(left, right)`, the product-law probability is

```text
sum_left sum_right
  1[E(left, right)] * mu_left(left) * mu_right(right).
```

This is bilinear when both component laws are unknown. After fixing `mu_right`, the exact left coefficient becomes

```text
c(left) = sum_right 1[E(left, right)] * mu_right(right),
```

and the event probability is exactly the rational linear objective

```text
sum_left c(left) * mu_left(left).
```

The module connects this fixed-component slice directly to `LinearObjectiveDual`. Exact rational lower and upper certificates for the remaining component law replay as valid bounds on the original Markovian counterfactual event probability.

The product-law family is globally nonconvex. Two degenerate independent Boolean response laws have a midpoint supported on the two diagonal response states. That midpoint violates the two-by-two determinant identity and therefore cannot be product-factorized. Exact endpoint witnesses cannot be interpolated inside the Markovian family without an additional inner witness construction.

This formalizes the main optimization boundary reported in recent quasi-Markovian work:

```text
several unknown component laws -> multilinear program
all but one component law fixed -> linear program.
```

The module does not infer confounded components from a graph, compile observational distributions to component-law constraints, or solve the general multilinear optimization problem.

## 11. Markovian benefit identification boundary

`MarkovianBenefitIdentificationBoundary` separates two assumptions that are often conflated in probability-of-causation arguments.

A standard Markovian treatment-outcome SCM separates the treatment-assignment disturbance from the outcome-mechanism disturbance. The two potential outcomes remain coordinates of one outcome response type. Markovianity therefore permits an arbitrary joint law on

```text
(Y0, Y1).
```

The module constructs, for every target `b` satisfying

```text
max(0, p1 - p0) <= b <= min(p1, 1 - p0),
```

an explicit normalized four-cell outcome-response law with control success `p0`, treated success `p1`, and benefit mass `b`. Pairing this law with a normalized independent assignment law gives a Markovian assignment-outcome response model. Conversely, every such model obeys the same bounds. The ordinary Boolean Frechet interval remains exactly sharp under assignment-outcome exogenous independence.

The concrete theorem with `p0 = p1 = 1 / 2` constructs two Markovian models. One has benefit probability zero and the other has benefit probability one half. Their observed interventional marginals agree. Standard Markovianity therefore does not point identify probability of benefit.

The module then imposes the stronger response-coordinate factorization

```text
P(Y0 = y0, Y1 = y1)
  = P(Y0 = y0) P(Y1 = y1).
```

Under this extra cross-world restriction, benefit is point identified as

```text
P(Y0 = false, Y1 = true)
  = (1 - p0) * p1.
```

This restriction is not derived from the standard Markovian SCM definition. It splits two coordinates produced by one structural disturbance into separate independent components. The distinction supplies a formal claim boundary for future PoC analyses.

## 12. Semantic boundary: mixture versus one global graph

The support and event-row compilers have latent-completion mixture semantics. Different units may receive mass from different admissible completions.

That object must be distinguished from epistemic uncertainty about one fixed complete graph. For one global unknown graph, the correct range is:

```text
union over admissible completions of completion-specific identified ranges.
```

Convexifying that union silently changes the causal model by introducing a latent graph index. Future compilers must expose this choice in their type and certificate payload.

A similar warning applies to Markovian response laws. Mixing two product-factorized laws can create dependence between components. A latent mixture index must therefore be represented explicitly and cannot be silently absorbed into a claim of exogenous independence.

## 13. Interfaces to current research

The current literature interface is organized as follows.

- Partial causal diagrams: Xie and Li, arXiv:2602.14503. Structural and auxiliary statistical information is represented as constraints on counterfactual distributions. The event-row compiler formalizes the finite zero-one-row kernel of those statistical constraints, without claiming completeness for the paper's full language.
- Causal orders: Rossetto and Antonucci, arXiv:2608.24427. Counterfactual queries induce precedence constraints, compatible total orders support canonical response-function programs, and tightness is tied to constructing attaining structural models.
- Markovian canonical counterfactual models: de Lara, arXiv:2507.16370. Canonical counterfactual representations separate interventional restrictions from additional counterfactual choices in Markovian SCMs.
- Quasi-Markovian partial identification: Arroyo et al., arXiv:2509.03548. General bounds are formulated as multilinear programs, while a single intervened confounded component admits a linear-program route and column-generation reduction.
- Probabilities of causation in quasi-Markovian models: Laurentino et al., arXiv:2509.02535. Latent confounding and component structure are used to obtain tighter PoC bounds and root-cause scores.
- Canonical domain reduction: Choe et al., UAI 2026. Counterfactual states indistinguishable to every objective and constraint row are quotiented without changing sharp LP bounds.
- Covariates and mediators: Shu, Lei, and Li, arXiv:2608.12657. Additional causal knowledge can tighten multivalued probabilities of causation. Mediator factorization may leave the polyhedral lane and enter polynomial feasibility.
- Continuous outcomes: Chaoge et al., arXiv:2605.01883. Copula restrictions constrain infinite-dimensional counterfactual coupling families.

The repository claim boundary is narrower than these papers. The PR proves reusable logical kernels and finite concrete instances. It does not claim a complete reproduction of any paper's general algorithm or theorem family.

## 14. Verification ledger

Required protected-branch checks are:

```text
Candidate harness engineering checks
Canonical Lean report production
Content-addressed dev baseline admission
```

A truth source is considered machine-verified only after the current PR head passes the protected workflow. Scribe freshness is likewise determined by the repository renderer rather than by hand-edited Markdown.

## 15. Next formal research sequence

The Markovian lane now advances through:

```text
MarkovianResponseLawFactorization
  -> MarkovianBenefitIdentificationBoundary
  -> finite component decomposition from a causal graph
  -> componentwise observational and interventional likelihood rows
  -> multilinear event polynomial semantics
  -> fixed-component linear slices
  -> branch or alternating certificate payloads
  -> attaining Markovian structural models
  -> sharp PoC bounds.
```

The next high-value instance should use a small quasi-Markovian graph with two confounded components and one probability-of-causation query. It should compare:

```text
unrestricted response-law coupling bound
versus
component-factorized Markovian or quasi-Markovian bound,
```

and provide either a closed-form sharp interval or a finite exact branch certificate.

A second target is to characterize which additional assumptions on the outcome response component genuinely reduce the Boolean benefit interval. Candidate restrictions include monotonicity, response-coordinate independence, bounded disagreement, and shared latent-rank models. Each restriction must be stated separately from standard Markovian assignment-outcome independence.

The partial-diagram lane continues with:

```text
PartialDiagramEventRowCompilerSoundness
  -> event-language interpretation against finite SCM evaluation
  -> observational consistency rows
  -> intervention consistency rows
  -> counterfactual conjunction and nesting rows
  -> rational primal-dual payload
  -> completion-specific sharp endpoints
  -> exact interval-union normalization across one-global-graph completions.
```

The causal-order lane continues in parallel:

```text
finite linear-extension swap connectivity
  -> row and query equivariance under one adjacent swap
  -> extension-independent compiled LP
  -> permutation transport of primal-dual certificates.
```

Continuous copula restrictions remain in the measure-coupling lane, while mediator and multi-component Markovian factorization remain in the polynomial or multilinear lane.
