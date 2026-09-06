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

## 12. Sharp joint benefit across independent mechanisms

`MarkovianJointMechanismBenefitSharpBounds` gives the first concrete query in this lane for which standard Markovian separation between two outcome mechanisms genuinely tightens a probability-of-causation range.

Each mechanism has its own complete response pair

```text
(Y0_first, Y1_first)
(Y0_second, Y1_second).
```

The internal coupling between control and treated potential outcomes remains arbitrary inside each mechanism. Define one Boolean benefit indicator per mechanism by the response cell `(false, true)`.

If the two benefit indicators are allowed an unrestricted coupling with marginal probabilities `b1` and `b2`, simultaneous benefit has the exact identified interval

```text
[max(0, b1 + b2 - 1), min(b1, b2)].
```

The module proves necessity from the four cell masses and supplies an explicit normalized coupling for every point in the interval.

A Markovian two-mechanism model instead factorizes the complete first and second mechanism response laws. Deterministic projection to benefit status preserves that factorization. Consequently,

```text
P(first mechanism benefits and second mechanism benefits)
  = P(first mechanism benefits) * P(second mechanism benefits).
```

The resulting identified set is the sharp singleton `{b1 * b2}`. Explicit complete mechanism laws attain the value while retaining arbitrary within-mechanism interpretation outside the nominated benefit cell.

At `b1 = b2 = 1 / 2`, unrestricted coupling gives the full interval `[0, 1 / 2]`. Independent Markovian mechanisms give the singleton `{1 / 4}`. The formal theorem exhibits zero as an unrestricted feasible target and proves one quarter for every Markovian model with the same marginal benefit probabilities.

This comparison clarifies where Markovianity has identifying power. Separating assignment noise from one outcome mechanism leaves the within-mechanism cross-world coupling free. Separating two complete outcome mechanisms constrains queries that jointly cross those mechanisms.

## 13. Semantic boundary: mixture versus one global graph

The support and event-row compilers have latent-completion mixture semantics. Different units may receive mass from different admissible completions.

That object must be distinguished from epistemic uncertainty about one fixed complete graph. For one global unknown graph, the correct range is:

```text
union over admissible completions of completion-specific identified ranges.
```

Convexifying that union silently changes the causal model by introducing a latent graph index. Future compilers must expose this choice in their type and certificate payload.

A similar warning applies to Markovian response laws. Mixing two product-factorized laws can create dependence between components. A latent mixture index must therefore be represented explicitly and cannot be silently absorbed into a claim of exogenous independence.

## 14. Interfaces to current research

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

## 15. Verification ledger

Required protected-branch checks are:

```text
Candidate harness engineering checks
Canonical Lean report production
Content-addressed dev baseline admission
```

A truth source is considered machine-verified only after the current PR head passes the protected workflow. Scribe freshness is likewise determined by the repository renderer rather than by hand-edited Markdown.

## 16. Next formal research sequence

The Markovian lane now advances through:

```text
MarkovianResponseLawFactorization
  -> MarkovianBenefitIdentificationBoundary
  -> MarkovianJointMechanismBenefitSharpBounds
  -> finite component decomposition from a causal graph
  -> componentwise observational and interventional likelihood rows
  -> multilinear event polynomial semantics
  -> fixed-component linear slices
  -> branch or alternating certificate payloads
  -> attaining Markovian structural models
  -> sharp PoC bounds.
```

The next high-value compiler theorem should derive the independent response components from a finite causal graph or an explicit confounded-component partition. It must prove that every generated event polynomial has one factor per independent component and that fixing all but one component produces exactly the linear slice already accepted by `LinearObjectiveDual`.

A second target is an exact finite certificate for a two-component bilinear problem. Candidate payloads are a finite branch decomposition with one rational dual certificate per branch, or a verified alternating bound whose global validity is discharged by a separate envelope theorem. Local stationary-point evidence alone is insufficient for a sharpness claim.

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

## 17. Four-marginal joint-benefit sharpness, 2026-09-05

The remote audit at commit `41009328ecfb110c8e429522552d5329ec912fb8` found that the fixed-benefit singleton theorem in Section 12 was already present. This continuation reuses that module and its complete model carrier rather than recreating it.

New authored Lean source:

```text
D5/S3/ConceptDynamics/Causal/PartialIdentification/
  MarkovianJointBenefitMarginalSharpBounds.lean
```

Its Scribe source is under the matching `Blueprint` path. Compilation status for this continuation is stated explicitly in Section 19.

Let the four interventional success probabilities be `p10,p11,p20,p21`. Define

```text
L1 = max(0, p11 - p10), U1 = min(p11, 1 - p10)
L2 = max(0, p21 - p20), U2 = min(p21, 1 - p20).
```

Assume `L1 <= U1` and `L2 <= U2`. For independent complete mechanism response laws, the exact rational target range is

```text
[L1 * L2, U1 * U2] intersect Q.
```

The main authored theorem is `four_marginal_joint_benefit_sharp_iff`. Its existential witness fixes all four interventional marginals, rather than fixing the two cross-world benefit probabilities as Section 12 does. Each within-mechanism coupling remains free subject to its own marginals.

The arithmetic core `nonnegative_product_interval_iff` constructs rational factors for every rational target `q` in that interval. If `q <= U1 * L2` and `L2 > 0`, choose `(b1,b2) = (q/L2,L2)`. If that edge has `L2 = 0`, the target is zero. Otherwise `U1 > 0` and choose `(b1,b2) = (U1,q/U1)`. This path follows two edges of the parameter rectangle. It does not interpolate joint product distributions and does not rely on square roots or a real intermediate-value theorem.

For each chosen benefit value, `benefitResponseLaw` supplies the existing four-cell attaining response law. Their product realizes the desired simultaneous-benefit target. Necessity reuses `markovian_benefit_target_feasible_iff` through `outcomeLaw_benefit_bounds`.

For four success marginals equal to one half, the resulting interval is `[0,1/4]`, as stated by `balanced_four_marginal_sharp_interval`. This must be distinguished from the singleton `{1/4}` obtained when the two benefit probabilities themselves are both fixed at one half.

## 18. Conditional factorization and the shared-ancestor boundary

New authored Lean source:

```text
D5/S3/ConceptDynamics/Causal/PartialIdentification/
  ConditionalMarkovianBenefitBoundary.lean
```

The phrase "independent outcome mechanisms" in Section 12 means that the evaluated complete response laws actually factorize. Distinct local disturbances or distinct c-components alone do not establish this property for arbitrary evaluated potential outcomes. The response maps can share a random endogenous ancestor. A graph compiler must certify the exogenous dependencies of the queried events after intervention, not merely the local disturbance partition.

The concrete counterexample has three independent exogenous variables: a fair Boolean root `U_C` and two degenerate Boolean local disturbances. Let `C = U_C` and let the two outcome equations be

```text
Y_i(a,c,u_i) = a AND c.
```

Both complete response pairs are `(false,C)`, so both benefit indicators equal `C`. Therefore both marginal benefits and their intersection have probability one half. Their marginal product is one quarter. The module gives an explicit product source law, a deterministic shared-root response map, a finite pushforward calculation, and an obstruction to factorizing the resulting response law. No causal graph compiler is claimed by this construction.

The existing `product_pushforward_factorizes` theorem remains valid: it requires componentwise response maps on separate source coordinates, and the shared-root response map does not meet that premise.

For a finite covariate and conditionally product-factorized mechanism laws, `conditional_joint_benefit_eq_weighted_products` states

```text
J = sum_c w(c) * b1(c) * b2(c).
```

For two strata with weight `w` on the second stratum, the exact certificate is

```text
J - ((1-w)*x0+w*x1) * ((1-w)*y0+w*y1)
  = w*(1-w)*(x1-x0)*(y1-y0).
```

`binary_mixture_covariance_certificate` is the polynomial identity. With `0 < w < 1`, `binary_mixture_factorizes_iff` states that equality with the product of population means holds exactly when `x1=x0` or `y1=y0`. This criterion is specifically for two positive strata; with more strata, zero covariance may result from cancellation.

Conditional sharp aggregation still requires jointly attainable stratum witnesses, as Section 4 already records. This continuation does not add a rational-to-real bridge to `CovariateSharpAggregation`, nor does it establish a general fixed-noise realization for arbitrary conditional kernel families.

## 19. Intrinsic-information interpretation and continuation verification status

The governing reference read for this continuation is version 4.3 of

```text
docs/develop/spec/lean_single_compile_intrinsic_information_escape_theory_and_spec.md
```

The new `fourMarginalReadout` acts on the existing full `MarkovianJointMechanismModel` carrier. The authored theorem `joint_benefit_strictly_refines_four_marginal_kernel` constructs two models with the same four-marginal readout and joint-benefit values zero and one quarter. Thus the mathematical witness certifies strict refinement of the observation kernel when the joint-benefit query is added. `no_joint_benefit_reconstruction_from_four_marginals` states the corresponding impossibility of a reconstruction function.

This full rational model space is infinite. No uniform finite escape rate, sampled model arena, novelty score, or external Python admission judge is introduced. A two-model strict-refinement witness is not a proof of positive leave-one-out capture against all peers in a designated maximal catalog. The non-reconstruction corollary is not registered as an extra independently informative occurrence.

Still outstanding for the new sources are their kernel-checked primitive realizations, canonical arena occurrence/disposition registration where applicable, designated-root maximal-catalog sealing, and protected build acceptance. The historical workflow name containing "baseline" in Section 15 is an engineering label; it is not an authorization to use historical deltas or scoring in the version 4.3 information theory.

At the time of this writeback:

- Both Lean sources and both authored Scribe documents have been pushed to the existing PR #5029 branch.
- No Lean compiler or Lake executable was available in the local runtime. No local Lean build, `#print axioms` output, Scribe rendering, or information-theory seal was obtained. The new scripts therefore remain unverified formal proof candidates until a pinned build accepts them.
- Supplementary exact `fractions.Fraction` regression checks passed 18,225 interval-product cases, 59,049 four-marginal attaining-law cases, 59,049 binary covariance cases, and the explicit shared-root counterexample. These are finite arithmetic checks, not proofs or admission certificates.
- The initial remote PR snapshot was open, draft, and unmergeable. A passing protected workflow for the new head has not been established. The convenience workflow lookup restricted to `pull_request` cannot adjudicate this repository's `pull_request_target` workflow.
- No merge, auto-merge, workflow bypass, or modification of protected admission machinery was performed.

The next compiler obligation is now more precise:

```text
intervened event semantics
  -> certified exogenous dependency sets
  -> disjoint independent source blocks, or explicit conditioning context
  -> componentwise pushforward factorization
  -> event polynomial and sharp attaining models.
```

This dependency-locality obligation prevents the shared-ancestor counterexample from being incorrectly admitted as an unconditional product query.

## 20. Intervention-specific exogenous locality, 2026-09-05

`InterventionExogenousLocality.lean` supplies the dependency-locality interface identified in Section 19. It reuses the existing parent-indexed `ParentOrderedStructuralEvaluationSemantics.StructuralModel`, its `EvaluationWitness`, and its unique evaluation theorem. The equation input has type `model.parents v -> Value`, so the parent boundary is enforced by the source type itself. The module introduces no competing structural evaluator.

Let a complete exogenous assignment be `u : Source -> Noise`. For each node `v`, declare a finite set `N(v)` of direct exogenous coordinates. `ExogenousLocality` requires that, for every fixed parent assignment, the equation satisfies Mathlib's existing `DependsOn` predicate on `N(v)`. Agreement of two sources on those coordinates therefore forces equal equation values when parent values agree.

The compiled transfer at an evaluation step is

```text
D'(v) = empty                              if v is intervened
D'(v) = N(v) union union_{p in parents(v)} D(p) otherwise
D'(w) = D(w)                               for w != v.
```

Every initial node support is the full source set. This accounts for arbitrary source dependence in `model.initial`; soundness does not assume a constant or source-independent initialization. The transfer follows the same finite list as the canonical evaluation trace.

The main statement `evaluatedResponse_dependsOn` says that the evaluated intervention response at `v` depends only on `compiledSupport model direct intervention v`. Its proof is a trace induction. Agreement on a nonintervened node's compiled union yields agreement of the direct source coordinates and all parent values. Locality then gives agreement of the equation output. A constant intervention gives agreement immediately, and all untouched coordinates retain their prior locality certificates.

The support compiler also proves `compiledSupport_antitone_intervention`:

```text
I subset J  ->  compiledSupport(J,v) subset compiledSupport(I,v).
```

This theorem applies to constant interventions whose assigned values do not depend on `u`. Source-dependent policies would need an additional support contribution for their assignment functions.

For a finite family of counterfactual queries, `counterfactualReadout` evaluates every queried world at the same original exogenous assignment. `counterfactualSupport` unions the relevant intervention-specific supports. `counterfactualReadout_dependsOn` and `counterfactualEvent_factorsThrough` certify locality of the full vector and of every Boolean event applied to that vector. The formal query family is unnested and uses fixed intervention assignments. It does not create fresh independent disturbances for different worlds.

The compiled sets are conservative dependency bounds. Their disjointness is useful evidence for separation; their overlap alone does not establish that the evaluated events are probabilistically dependent.

All fourteen public definitions and theorems have matching declaration handles in `Blueprint/D5/S3/ConceptDynamics/Causal/PartialIdentification/InterventionExogenousLocality.scribe.cs`.

## 21. From source separation to counterfactual product laws

`SeparatedCounterfactualSourceFactorization.lean` joins the locality compiler to the existing finite product-pushforward library.

Suppose two readouts `F` and `G` depend on finite source sets `S` and `T`, with `S` disjoint from `T`. The formal probability premise supplies independent normalized rational laws on the entire `S` block and its complement:

```text
mu = mu_S x mu_complement.
```

Dependence inside either block remains unrestricted. The source split uses Mathlib's standard equivalence

```text
(Source -> Noise)
  equivalent to
({i // i in S} -> Noise) x ({i // i not in S} -> Noise).
```

It covers every full source assignment. Coordinates unused by either readout remain in the complement block; they are not removed by selecting a smaller test carrier.

`DependsOn` supplies reduced maps through the corresponding coordinate restrictions. Disjointness places the right readout entirely inside the complement block. Under the standard equivalence, the original full-source maps are therefore coordinatewise maps. Reusing `independent_exogenous_components_induce_markovian_response_law` yields `separated_readouts_factorize`.

The associated cell formula is

```text
P(F = f, G = g) = P(F = f) * P(G = g),
```

where both factors are the actual marginals of the generated response law. `separated_readouts_cell_eq_product` states this equality for every pair of response values. For Boolean benefit readouts, its `(true,true)` cell gives simultaneous benefit.

The end-to-end statement `compiled_counterfactual_events_factorize` combines:

```text
parent-indexed structural evaluation
  + direct exogenous locality
  + finite counterfactual support compilation
  + disjoint compiled supports
  + an independent S/complement source law
  -> a product-factorized Boolean counterfactual event law.
```

The independence premise is explicit. This module does not yet derive the S/complement law from a separately represented family of elementary independent disturbance laws. It also does not assert that c-component labels alone establish independence of arbitrary evaluated potential outcomes.

The structural distinction agrees with the quasi-Markovian formulation in Arroyo et al., arXiv:2509.03548, Section 2: local mechanisms still read endogenous parents, while exogenous laws have their own factorization. General counterfactual identification remains a broader problem, as in Shpitser and Pearl, *What Counterfactuals Can Be Tested*, UAI 2007, arXiv:1206.5294. The present source-separation certificate supplies a sufficient condition; no completeness claim for a counterfactual identification algorithm is made.

All four public declarations have matching handles in `Blueprint/D5/S3/ConceptDynamics/Causal/PartialIdentification/SeparatedCounterfactualSourceFactorization.scribe.cs`.

## 22. A shared-root intervention cut and its limits

The closed support calculation `fork_support_cut_certificate` uses four nodes:

```text
0 = C, 1 = A, 2 = first outcome, 3 = second outcome
parents(0) = parents(1) = empty
parents(2) = parents(3) = {0,1}
N(v) = {v}
order = [0,1,2,3].
```

The exact compiled supports are

```text
under do(A = a):
  D(first outcome)  = {U_C, U_first}
  D(second outcome) = {U_C, U_second}

under do(C = c, A = a):
  D(first outcome)  = {U_first}
  D(second outcome) = {U_second}.
```

The support calculation is independent of the fixed assigned values. Consequently, taking the union across treatment values preserves these sets for complete treatment-response pairs and their benefit events. The shared-root example in Section 18 fails the disjoint-support premise under treatment-only intervention. Fixing the common root removes that shared coordinate and makes the source-separation route available under an appropriate independent block law.

Three distinctions matter for interpretation.

First, shrinking dependency supports concerns the source coordinates a query may read. Adding an intervention generally changes the estimand. No ordering of the old and new probabilities, or nesting of their identified intervals, follows from support antitonicity alone.

Second, `do(C=c)` and conditioning on an endogenous event `C=c` require different arguments. Conditioning can change dependence between residual source blocks. The new modules prove the constant-intervention route and do not infer general conditional independence from it.

Third, the interval in Section 17 is sharp over a family allowing all compatible complete within-mechanism response laws. A fixed set of structural equations can restrict that family further. The new source-separation theorem establishes factorization for a given structural model, while transferring the full sharp interval to a more restricted structural family still requires attaining models inside that family.

## 23. Query-preserving kernels and the next mathematical interface

For a fixed structural model, let `r_S` restrict a full exogenous assignment to the compiled source set of a query `Q`. `counterfactualEvent_factorsThrough` gives

```text
Q = reduced_Q composed with r_S
ker(r_S) subset ker(Q).
```

Thus all distinctions relevant to the query survive source restriction. This is a semantic kernel-descent statement on the original source-assignment carrier, using the existing Mathlib `FactorsThrough` interface.

The carrier here differs from the space of entire probability models used by `fourMarginalReadout` in Section 19. Source restriction studies evaluation inside a fixed model; the earlier nonidentifiability witness compares different models with the same data. Their kernels are not interchangeable and no scalar information measure is transported between these carriers. The standard partition equivalence recoordinates the full source space, and the probability-cell corollary does not assert an extra independent information occurrence. No maximal-catalog irredundancy or information-escape score is claimed by these local semantic results.

The mathematical chain now has authored Lean and Scribe sources through

```text
intervened structural trace
  -> conservative exogenous dependency support
  -> query-preserving source restriction
  -> certified disjoint support
  -> coordinatewise evaluation of independent source blocks
  -> exact counterfactual product law.
```

The proof scripts have undergone logical review and exact finite regression checks; kernel compilation has not been performed in this round. The regression cases exercise response constancy on support fibers, support monotonicity under nested interventions, and joint-cell factorization with arbitrary within-block dependence. They are supplementary checks rather than substitutes for the general Lean statements.

The next mathematical interface is to group a finite family of elementary independent disturbance laws into the S/complement law used above, preserving the full assignment carrier and its pushforward. This would remove the remaining manually supplied block-law premise for a canonical finite Markovian source representation. Conditional fixed-noise realization and simultaneous attainment across strata remain separate obligations, as recorded in Sections 4 and 18.

## 24. Elementary independent source grouping, 2026-09-06

The source-grouping obligation in Section 23 is addressed by `FiniteIndependentSourceGrouping.lean`. The current module location is `D5/S3/ConceptDynamics/PartialIdentification/`, following the repository's relocation of the partial-identification lane. The authored Scribe source follows the same path under `Blueprint`.

Each elementary disturbance has a finite carrier `Noise i` and a normalized nonnegative rational law `mu_i`. The carriers may differ between source indices. Define one full law before choosing any partition:

```text
State = (i : Source) -> Noise i
mu(u) = product_i mu_i(u_i).
```

`independentSourceLaw` constructs this law. Normalization reuses the pinned Mathlib identity `Fintype.prod_sum`:

```text
sum_u product_i mu_i(u_i) = product_i sum_a mu_i(a) = 1.
```

For any finite source set `S`, the standard `Equiv.piEquivPiSubtypeProd` splits the full assignment into its restriction to `S` and to its complement. `independentSource_mass_split` reuses `Fintype.prod_subtype_mul_prod_subtype` to prove the pointwise mass identity. `independentSource_split_law` then identifies the actual block distribution:

```text
split_*(mu) = mu_S x mu_complement,
mu_S(s) = product_{i in S} mu_i(s_i).
```

Both block laws come from the same elementary law family. Their independence is derived for the original product law; it is not a replacement assumption about an unrelated block model. Empty blocks carry the unit law on the unique empty assignment. Zero-probability assignments remain part of the full carrier, and no positivity or division is needed for regrouping.

`independentSource_pushforward_regroup` proves equality of every finite readout distribution before and after this change of coordinates. It reindexes the full source sum through the standard equivalence and applies the pointwise mass identity. Thus it also covers joint readouts that do not factorize.

The elementary premise is mutual independence, represented by the full product law. Pairwise independence is insufficient for arbitrary block grouping. For example, fair independent bits A and B together with C = A XOR B have pairwise-independent coordinates, while the readouts A XOR B and C coincide and are nonconstant. Each independent index may itself encode an entire multivariate response type; no independence of coordinates inside that type is imposed.

## 25. Exact query elimination and data-safe parameter projection

Suppose a fixed readout factors through source restriction:

```text
F(u) = reduced_F(u restricted to S).
```

`independentSource_pushforward_restrict` proves the exact distributional identity

```text
F_*(mu) = reduced_F_*(mu_S).
```

After regrouping, the complementary product law sums to one. `independentSource_restriction_marginal` identifies `mu_S` with the actual restriction marginal. `independentSource_readout_law_invariant` further proves that two elementary law families agreeing on S give the same complete readout distribution, irrespective of changes outside S. The readout and structural equations are fixed in this statement.

This distributional invariance does not authorize deletion of statistical constraints involving other sources. Consider independent Bernoulli variables with parameters x and z, a target x, and supplied joint-event probability c. The data impose x*z = c. For nonnegative rational c, `joint_event_constraint_projection_iff` states the exact parameter projection:

```text
c <= x <= 1
iff
0 <= x <= 1 and there exists 0 <= z <= 1 with x*z = c.
```

For x > 0 the witness is z = c/x. For x = 0, feasibility forces c = 0 and z = 0 is a witness. Necessity follows from c = x*z <= x. The formal statement is at the probability-parameter level. When 0 <= c <= 1, its attainable target set is `[c,1] intersect Q`; if c > 1, it is empty.

At c = 1/4, a target that does not read the second disturbance is still restricted to `[1/4,1]`. Deleting the joint-event data row would incorrectly expand the range to `[0,1]`. Consequently, exact optimization reduction must use the projection of the complete feasible parameter set:

```text
full feasible set C
  -> projected set {theta_S | exists theta_complement, (theta_S,theta_complement) in C}
  -> reduced query on theta_S.
```

Elementary independence is a within-model distributional property. It does not imply that the sets of admissible elementary parameters are independently selectable after all observational and interventional constraints are imposed.

## 26. Counterfactual factorization under the original elementary source law

`IndependentSourceCounterfactualFactorization.lean` connects the new source construction to the existing locality compiler and source-separation theorem. Its Scribe source covers all four public bridge theorems.

`independentSource_pair_readout_eq_partitioned` proves that evaluating two original full-source readouts under `independentSourceLaw` gives exactly the existing `partitionedReadoutLaw`, with both block laws derived from the elementary family. `independentSource_separated_readouts_factorize` therefore obtains a product response law from disjoint semantic supports. Its joint-cell corollary uses the actual marginals of the original full-source pushforward.

The end-to-end theorem is `compiled_counterfactual_events_independent_sources`. Its inputs are elementary normalized laws, the existing parent-indexed structural model and topological certificate, direct exogenous locality, two finite counterfactual query families, and disjoint compiled supports. Its conclusion concerns the direct pushforward of the original source law:

```text
mutually independent elementary disturbances
  -> derived S/complement source product law
  -> certified intervention-specific query locality
  -> source-separated response maps
  -> product-factorized Boolean counterfactual event law.
```

No separate block-law witness is supplied by the caller. No new structural evaluator or independent noise copy per counterfactual world is introduced. For two benefit indicators the `(true,true)` cell is the product of their marginal benefit probabilities. The previous block-level theorem remains more general about dependence inside each supplied source block; this continuation supplies its canonical elementary-independent specialization.

These results are sufficient separation statements. Shared ancestors may still make compiled supports overlap, conditioning can change source dependence, and fixed structural equations can restrict the attainable response laws. The earlier obligations concerning same-mechanism coupling and simultaneous sharp attainment remain distinct.

## 27. Literature interface and conditional realization target

Arroyo et al., *Multilinear and Linear Programs for Partially Identifiable Queries in Quasi-Markovian Structural Causal Models*, arXiv:2509.03548v1, Section 2, explicitly assumes independent exogenous nodes and writes their full mass as a product. Its Sections 3 and 4 use additional causal and data identities to simplify probability programs. The present regrouping and query-elimination theorems certify finite rational probability identities underlying such manipulations. The constraint-projection example explains why readout locality alone cannot replace those additional data arguments.

Zhang, Tian, and Bareinboim, *Partial Counterfactual Identification from Observational and Experimental Data*, arXiv:2110.05690, connects finite canonical structural models to polynomial optimization of counterfactual bounds. The present modules retain the same finite-source perspective while adding exact compatibility between source regrouping, the existing structural evaluator, and query distributions. They do not reproduce a general counterfactual optimizer or finite-domain completeness theorem.

For the intrinsic-information interpretation, regrouping uses a bijection on the complete source carrier. Source elimination is justified by the already established kernel descent together with an exact marginalization theorem. No sampled arena, finite information score, or maximal-catalog irredundancy claim is introduced. Equality of pushforward laws and kernel descent remain separate statements with explicit carriers.

The next constructive target is simultaneous fixed-noise realization for a finite covariate C. Given finite conditional response laws q_c, a candidate common disturbance is a full table W = (W_c)_c with product law over the q_c, independent of C, and evaluation W_C. For two mechanisms, use independent full tables W1 and W2 together with the common covariate. This construction preserves arbitrary coupling inside each response pair at a fixed c and offers a route to realizing all strata in one structural model.

The remaining formal obligations are the joint pushforward identity for (C,W_C), its two-mechanism conditional version, and attaining witnesses for the aggregate sharp interval. Product grouping alone does not discharge those obligations. Additional restrictions tying response tables across covariate values must remain explicit when present.

## 28. Simultaneous finite conditional response tables, 2026-09-06

`FiniteConditionalResponseTable.lean` addresses the common-noise realization target in Section 27. For a finite covariate carrier C and finite response carrier R, take a normalized rational kernel q_c on R for each c. A complete table has type C -> R. The previously constructed independentSourceLaw supplies

```text
nu(w) = product_c q_c(w(c)).
```

`tableEvaluationLaw_independentSource` proves that evaluating this one table at c has mass q_c. The proof reuses exact source restriction to the singleton {c}, then identifies a singleton-indexed assignment with its response value. `finite_conditional_table_realization` therefore realizes all rows in the same disturbance space.

For two mechanisms, `FixedNoisePairModel` stores laws nu_1 and nu_2 on complete tables. The general model class permits arbitrary dependence between different rows inside each table. Its source law is

```text
P(U_C=c, W_1=w_1, W_2=w_2) = weight(c) * nu_1(w_1) * nu_2(w_2),
C = U_C,
R_1 = W_1(C), R_2 = W_2(C).
```

Thus the covariate root and both complete mechanism disturbances are mutually independent. `selectedPairLaw` is the actual pushforward of this full source law. For arbitrary table laws, `selectedPairLaw_mass` proves

```text
P(C=c, R_1=r_1, R_2=r_2)
  = weight(c) * rowLaw_1(c,r_1) * rowLaw_2(c,r_2).
```

No conditional-probability division is used. The equality covers null strata; an interpretation as a conditional probability obtained by division requires weight(c) > 0.

`canonicalFixedNoisePair` chooses the product table law for each prescribed row-kernel family. `simultaneous_conditional_product_realization` proves that one such model reproduces every specified conditional product cell simultaneously. Independent rows are a constructive choice of witness. They are not an additional assumption in the model class used for necessity.

If R is Bool x Bool, dependence of the two potential-outcome coordinates inside each row remains unrestricted. Neither table construction nor mechanism independence implies Y_0 independent of Y_1.

## 29. Sharp covariate joint benefit in one fixed-noise model

`FixedNoiseCovariateBenefitSharpBounds.lean` combines simultaneous table realization with the existing four-marginal sharpness theorem. The deterministic treatment equation is

```text
Y_i(a,c,W_i) = first coordinate of W_i(c)  if a=false,
Y_i(a,c,W_i) = second coordinate of W_i(c) if a=true.
```

`fixedNoiseOutcome_response` identifies the complete treatment response with W_i(c). Both treatment interventions use the same table disturbance. `fixedNoiseStratumModel` records the actual row marginals of an arbitrary fixed table model, and `HasConditionalFourMarginals` fixes their four intervention-success kernels p10(c), p11(c), p20(c), p21(c).

Define

```text
L_i(c) = max(0, p_i1(c) - p_i0(c)),
U_i(c) = min(p_i1(c), 1 - p_i0(c)),
l(c) = L_1(c)*L_2(c), u(c) = U_1(c)*U_2(c),
L = sum_c weight(c)*l(c), U = sum_c weight(c)*u(c).
```

For compatible local marginals, the main theorem `fixedNoise_covariate_joint_benefit_sharp_iff` states

```text
L <= target <= U
iff
there exists one FixedNoisePairModel with all four prescribed kernels
and actual population simultaneous-benefit probability target.
```

All quantities and attaining laws are rational. The identified set is `[L,U] intersect Q`. `fixedNoiseJointBenefit` is defined by summing the relevant cells of the actual common-source pushforward, rather than by stipulating a weighted objective. `fixedNoiseJointBenefit_eq_weighted` derives the weighted product formula from that law.

Necessity covers every admitted table law, including correlated rows. Its row marginals satisfy the existing local joint-benefit interval. Nonnegative covariate weights preserve these bounds under summation.

For sufficiency, if L=U, select every lower endpoint. Otherwise set

```text
t = (target-L)/(U-L),
q_c = l(c) + t*(u(c)-l(c)).
```

Then 0<=t<=1, each q_c belongs to its local sharp interval, and the weighted sum of the q_c equals target. The existing local theorem constructs two response laws attaining q_c with the specified four marginals. `fixedNoiseStrata_simultaneously_realized` assembles all those laws into one pair of full-table disturbances.

Only the scalar target values are interpolated. The construction does not mix two product distributions, which could break mechanism independence. A private rational specialization of the weighted interpolation argument avoids converting real witnesses back into rational source laws. The former joint-selection premise has now been discharged for this explicit fixed-noise model family.

## 30. Scope, shared covariates, and cross-stratum restrictions

The covariate in this model is an independent root whose value is shared by both outcome equations. Arbitrary conditioning on a mediator, collider, or variable affected by treatment is not justified by this construction. An embedding of these particular equations into the parent-ordered graph evaluator has not been added here; the common-source distributions, table equations, and response-pair identities are explicit in the new modules.

For zero-weight strata, the four marginal values are prescribed kernels, not conditional probabilities learned from an event of probability zero. Their compatibility is assumed, and they do not contribute to the population endpoints.

No restrictions linking different rows of the same table are supplied beyond being a valid full-table law. Rank preservation, cross-covariate monotonicity, a fixed small disturbance support, and extra statistical constraints may restrict the jointly attainable row family. In those cases the newly constructed product-row witness may be inadmissible. The shared-parameter obstruction from Section 4 and the data-projection obligation from Section 25 remain applicable.

A shared covariate can induce population dependence even when both table disturbances are independent. For example, with two equally weighted strata, let both mechanisms never benefit in the first stratum and always benefit in the second. The local intervals are {0} and {1}. The new formula gives the sharp population singleton {1/2}, whereas the product of population marginal benefits is 1/4. This is consistent with the earlier binary-mixture covariance certificate.

If all four success kernels equal 1/2 in every stratum, all local joint-benefit intervals are [0,1/4]. Normalized weights give the same population interval [0,1/4]. These examples illustrate distinct patterns of conditional heterogeneity; the theorem does not replace a weighted product by a product of averages.

## 31. Literature connection and remaining representation work

The independent-noise representation is a finite rational instance of the functional representation principle. Li and El Gamal, *Strong Functional Representation Lemma and Applications to Coding Theorems*, IEEE Transactions on Information Theory 64(11):6967-6978 (2018), arXiv:1701.02827v4, studies a much stronger representation with information-theoretic guarantees. The present modules do not formalize that stronger bound or claim novelty for the representation principle.

Zhang, Tian, and Bareinboim, *Partial Counterfactual Identification from Observational and Experimental Data*, ICML 2022, PMLR 162:26548-26558, develops canonical finite causal representations for counterfactual bounds. Arroyo et al., arXiv:2509.03548v1, relates quasi-Markovian source factorization to multilinear and linear probability programs. The concrete addition here is an exact common-table witness together with a rational sharp-interval theorem for conditional joint benefit, integrated with the repository's existing response-law and local sharpness results.

The source carrier is the entire table space. For k covariate values and a four-state response pair, one table has 4^k possible rows-of-responses assignments. This finite construction proves existence but does not provide an efficient minimal-support representation. A natural remaining obligation is exact rational support reduction preserving every row marginal and the required query cells, followed by transport of attaining models through that reduction. Cross-stratum restrictions must be retained when defining the constraints to preserve.

The new table model space is not identified with an information-escape arena. The finite regression suite supplies no novelty score, maximal-catalog irredundancy certificate, or proof of root admission. The authored sources contain complete proof scripts and matching Scribe declaration coverage; their Lean kernel compilation has not been performed in this continuation.
