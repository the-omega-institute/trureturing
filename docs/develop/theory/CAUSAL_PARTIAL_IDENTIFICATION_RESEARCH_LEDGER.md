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

The next high-value compiler theorem should derive the independent response components from a finite causal graph or an explicit confounded-component partition. It must prove that every generated event polynomial has one factor per independent component and that fixing all but one component law produces exactly the linear slice already accepted by `LinearObjectiveDual`.

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

## 32. Exact quaternary capacity bridge to the golden base-four lane, 2026-09-06

`QuaternaryResponseTableCoding.lean` formalizes the exact part of the numerical coincidence between the causal response-table construction and the golden-ratio base-four DFAO problem.

One Boolean complete response pair has four possibilities:

```text
(false,false), (false,true), (true,false), (true,true).
```

`responsePairDigitEquiv` identifies these with the quaternary digits `0,1,2,3`. Coordinatewise application gives

```text
(Fin k -> Bool x Bool)  equivalent to  (Fin k -> Fin 4).
```

Mathlib's existing `finFunctionFinEquiv` then gives the explicit finite radix equivalence

```text
(Fin k -> Bool x Bool)  equivalent to  Fin (4^k).
```

The theorem `responseTable_card_eq_four_pow` records the corresponding cardinality. Thus the `4^k` in the fixed-noise causal construction is exactly the size of the unrestricted length-k word space over the same four-symbol alphabet that appears as the output alphabet of the golden base-four digit problem.

The number `4^k` is a capacity boundary. Every actual k-row table is coded by an integer strictly smaller than `4^k`, as stated by `responseTableCode_lt_capacity`. It is therefore important not to identify `4^k` with one particular table code.

The existing golden oracle defines

```text
base4PowerWord k = zeckendorfMSDWord (4^k).
```

Combining this unchanged definition with the response-table cardinality gives the new theorem

```text
golden_base4_power_word_is_response_table_capacity:
  base4PowerWord k
    = zeckendorfMSDWord (Fintype.card (Fin k -> Bool x Bool)).
```

This is an exact structural identity. The k-th sparse input of the golden DFAO is the Zeckendorf representation of the cardinality of the unrestricted k-row Boolean response-table carrier.

## 33. The four-ary tree interpretation and the distinguished golden path

The unrestricted response tables form a rooted four-ary tree by prefix extension. Level k consists of all k-row tables and has `4^k` nodes. The existing golden base-four digit `base4GoldenDigit k : Fin 4` supplies one branch symbol at depth k.

`goldenResponsePrefix k` decodes the first k golden digits into one distinguished causal-style response table. `goldenResponsePrefix_castSucc` proves prefix consistency:

```text
goldenResponsePrefix (k+1) restricted to Fin k
  = goldenResponsePrefix k.
```

Hence the golden digit sequence selects one nested path through the same four-ary table tree whose full level size is `4^k`. `goldenResponsePrefixCode k` places the chosen node in `Fin (4^k)`.

The combined picture is therefore

```text
all level-k response prefixes:  A^k, |A|=4, |A^k|=4^k
capacity input to golden DFAO:  Zeckendorf(4^k)
returned branch symbol:         d_k in A
golden prefix recursion:        g_(k+1) extends g_k by d_k.
```

The last line is a prefix statement about the coordinate family. Mathlib's integer radix equivalence fixes its own least-significant-coordinate convention for `goldenResponsePrefixCode`; no claim about textual big-endian concatenation is needed.

This yields a useful level-size/branch-symbol duality. The automaton is queried at the arithmetic size of the whole unrestricted prefix level and returns the next symbol of one highly structured path through that level hierarchy.

## 34. Support complexity and automaton complexity are different quantities

`StructuredResponseTableSupport.lean` formalizes the boundary needed to prevent an invalid compression argument.

Let a deterministic latent generator map a finite state carrier `S` into all k-row response tables. If it is surjective, then

```text
4^k <= Fintype.card S.
```

This is `surjective_response_table_generator_requires_four_pow`, obtained directly from finite cardinality. Its contrapositive `small_generator_not_universal` says that every smaller latent family omits at least one unrestricted table.

The probabilistic statement is stronger for the canonical independent-row witness. If every stratum response kernel gives strictly positive mass to all four response types, then `independentResponseTable_full_support` proves that every one of the `4^k` full tables has positive mass. Therefore any deterministic latent generator that exactly covers the positive-mass support needs at least `4^k` states. This is stated by `positive_independent_table_law_generator_lower_bound` and its small-generator impossibility corollary.

Consequently, the exponential carrier in Section 31 is not merely an inefficient naming scheme when the product table law has full support. Exact atom-by-atom latent enumeration really has exponential support complexity.

This does not conflict with the small DFAO in the golden-ratio lane. A DFAO state is a computational state used to evaluate a coordinate oracle. It need not correspond to one latent response table atom. A finite automaton can describe one infinite structured quaternary sequence with a small transition system while the unrestricted set of length-k quaternary sequences still has `4^k` members. Algorithmic description complexity and probability-support complexity are different invariants.

In particular, the 21-state upper construction currently developed in draft PR #5405 cannot be read as a 21-atom representation of every causal response table. The bridge source deliberately imports only the stable `GoldenBase4AutomataOracle` definitions and does not depend on the unmerged 21-state candidate.

## 35. Relation to the current Zeckendorf/Fibonacci DFAO research and next formal target

Barnoff, Bright, and Shallit, *Computing the base-b representation of quadratic irrationals using automata*, Theoretical Computer Science 1071 (2026), 115843, proves that the n-th base-b digit of a quadratic irrational is a finite-state function of the corresponding Ostrowski representation of `b^n`. In the golden-ratio, base-four case this is exactly the Zeckendorf representation of `4^n`. The bridge above uses the same repository input definition, rather than introducing a second power or Zeckendorf encoder.

Moradi, Rampersad, and Shallit, arXiv:2603.21645v1, studies complexity of arithmetic relations and linear subsequences in Fibonacci-automatic systems. Its linear-subsequence results do not automatically imply a finite-state recurrence in the exponent k for the exponentially sparse restriction `4^k`. The bridge established here therefore stops at the exact capacity/input identity and the existing DFAO coordinate oracle.

Earp-Lynch, Earp-Lynch, Kihel, and Tiebekabe, arXiv:2608.04445, studies powers represented as sparse sums of Fibonacci numbers. That number-theoretic sparsity can constrain the shapes of some Zeckendorf power inputs, but it supplies no support-reduction theorem for arbitrary causal response tables.

A genuine causal use of automata would require an explicit cross-stratum structural hypothesis. For ordered strata, one could restrict admissible complete response tables to a regular, automatic, or sofic family. Such a restriction can reduce support and can tighten partial-identification bounds, but it changes the feasible causal model and therefore needs scientific justification. The unrestricted sharpness theorems must remain available as the outer model.

There is also a separate compression mechanism that should be studied before attributing support reduction to automata. If only finitely many row marginals and query moments must be preserved, convex support-reduction results such as Caratheodory-type representations can potentially replace a `4^k` ambient carrier by a support whose size is controlled by the number of retained moment coordinates. That would preserve a specified finite observation/query map without imposing an automatic cross-stratum law. Formalizing this exact rational moment-preserving support reduction is the next high-value representation target.

The two new Lean sources and their Scribe companions establish the radix bridge and the exact full-support obstruction. They do not claim that the golden sequence is a scientifically justified causal response mechanism, that the powers-only DFAO minimum has been resolved, or that automaton state count is an information-escape score.

## 36. Exact finite moment support reduction, 2026-09-06

`FiniteMomentSupportReduction.lean` discharges the representation target left open in Section 35. The theorem is stated for the repository's existing `FiniteResponseLaw`, `LinearFeasible`, and `linearObjective`; it introduces no second probability or LP semantics.

For a finite atom carrier `A`, a finite feature carrier `J`, and feature map

```text
phi : A -> (J -> Q),
```

a normalized nonnegative law `mu` has retained moment vector

```text
M(mu) = sum_a mu(a) * phi(a).
```

`lawMomentVector_mem_convexHull` proves that `M(mu)` belongs to the rational convex hull of the atom profiles `phi(a)`. Mathlib's existing Caratheodory construction then supplies an affinely independent finite family of original profiles with nonnegative weights summing to one and exactly the same moment vector. The resulting `MomentCompression` records the selected profiles, source certification, normalized weights, exact moment equality, and affine independence.

The ambient theorem `exists_momentCompression` gives

```text
selected atoms <= |J| + 1.
```

This support depends on the particular law and retained moment point. It is therefore a witness reduction for one feasible probability law, rather than a universal generator for all atoms.

## 37. Affine profile rank is the sharper complexity parameter

The raw number of retained coordinates can overcount information. `profileAffineRank` is defined as

```text
r(phi) = finrank_Q vectorSpan(range(phi)).
```

`MomentCompression.card_le_profileAffineRank` proves the sharper bound

```text
selected atoms <= r(phi) + 1.
```

Thus duplicate feature profiles and affine dependencies among the retained rows reduce the support bound automatically. For an LP with constraint rows `A_c` and objective `q`, `linearRowQueryFeature` packages the joint profile of one atom as

```text
atom |-> (q(atom), A_1(atom), ..., A_m(atom)).
```

and `linearProblemProfileRank` is the affine rank of this joint profile family. The formal chain is

```text
selected atoms
  <= linearProblemProfileRank(A,q) + 1
  <= number_of_constraint_rows + 2.
```

The second inequality is only an ambient bound. The rank-aware statement is the mathematically informative one when constraints are repeated, linearly dependent, or unable to distinguish large groups of canonical atoms.

This gives a direct geometric connection to canonical-domain reduction. Choe, Kwon, Park, and Lee, UAI 2026, quotient canonical counterfactual states that are indistinguishable to every LP row and the objective. The range of `linearRowQueryFeature` already collapses exactly such duplicate profiles. Caratheodory then performs a second, law-specific reduction inside the convex hull of the distinct profile family. Exact profile equality and affine redundancy are separate reductions and both can decrease the witness size.

## 38. Feasibility and query value survive on the original causal carrier

A small latent witness alone would leave open whether the original causal LP semantics were preserved after reparameterization. `FiniteMomentSparseLaw.lean` closes that gap.

`pushforward_linearObjective` proves for every deterministic map `g : S -> A` and every rational atom coefficient `f` that

```text
E_{g_* nu}[f] = E_nu[f o g].
```

A `MomentCompression` therefore pushes its latent law through the selected original atoms to `sparseLaw`, a normalized law on the unchanged original atom carrier.

For the joint LP row/query profile, the source proves

```text
original law feasible for (A,b)
  -> sparseLaw feasible for the same (A,b),

linearObjective q sparseLaw
  = linearObjective q originalLaw.
```

The endpoint `finite_linear_problem_sparse_original_witness` gives, for every feasible law, a sparse law on the same original response carrier whose generating latent support is at most

```text
linearProblemProfileRank(A,q) + 1
```

and which has the identical query value. The coarser endpoint replaces the rank by `number_of_rows + 1`, giving `number_of_rows + 2` atoms.

Consequently, for a finite linear partial-identification problem, every attainable query value has a sparse attaining representative without changing the original feasible family or the query map. This is pointwise preservation of the identified query image. It is stronger than merely constructing an alternative latent parameterization.

## 39. Why this does not contradict the 4^k support lower bound

Sections 34 and 38 concern different quantifiers.

The full-support theorem says that one deterministic latent generator which must cover every positive-mass table of a strictly positive independent-row law needs all `4^k` table atoms. The new Caratheodory theorem says that, once a finite observation/query map is fixed, each particular attainable moment point has some sparse law with the same retained moments and query value.

The sparse support is allowed to depend on the original law and on the retained query. There is no single set of `r+1` atoms asserted to represent every law or every future query. Therefore

```text
universal atom-by-atom support complexity = 4^k
```

can coexist with

```text
law-specific support needed for one finite LP/query profile <= r + 1.
```

This distinction is important for causal interpretation. The sparse law preserves exactly the finite rows and query supplied to the theorem. A later query outside that feature family may distinguish it from the original law.

## 40. Specialization to k Boolean response-pair strata and next reduction

For the response-table carrier

```text
Fin k -> Bool x Bool
```

there are `4^k` possible complete tables. `responseTableCellQueryFeature` retains all four one-stratum response-cell indicators for every stratum together with one scalar query. `exists_responseTableCellQueryCompression` proves a positive atomic witness with

```text
support <= 4*k + 2,
```

while `responseTableCellMoment_eq` and `responseTableQueryMoment_eq` prove exact preservation of every retained cell probability and the query.

The displayed `4*k+2` is deliberately conservative. Within each stratum the four cell indicators sum to one, while every admitted law is already normalized. Hence only three independent cell coordinates per stratum are required to reconstruct the fourth. A direct three-cell specialization should therefore target the explicit ambient bound

```text
3*k + 2.
```

The rank theorem may reduce the support further when the query or data induce additional affine dependencies. The exact rank, rather than `3*k+1` or `4*k+1`, is the reusable final complexity parameter.

For multilinear Markovian families, the present theorem applies directly to already linearized fixed-component slices. Applying it to the whole nonlinear feasible family would require retaining sufficient polynomial features and proving that the reduced witness still satisfies the structural factorization constraints. A linear moment projection alone does not preserve a nonconvex product-law model class.

The resulting representation hierarchy is now:

```text
4^k unrestricted response atoms
  -> quotient exact row/query duplicate profiles
  -> affine profile rank r
  -> law-specific Caratheodory witness of size <= r+1
  -> pushforward to a sparse law on the original response carrier.
```

This is a lossless reduction for the nominated finite linear identification problem. An automatic or sofic cross-stratum restriction remains a separate scientifically substantive assumption that can shrink the causal model family itself. The next formal target is the explicit `3*k+2` response-marginal specialization and then an executable rational support-reduction certificate that can be replayed alongside the existing primal-dual LP certificates.

## 41. Three-cell reconstruction and actual support bounds, 2026-09-06

`ReducedResponseTableMoments.lean` closes the explicit bound proposed in Section 40. For each Boolean response row, retain the cells with quaternary digits 0, 1, and 2. The omitted digit-3 probability is one minus their sum. `boolean_pair_law_eq_of_first_three` proves equality of the complete normalized response laws from equality of these three cells. The existing `responsePairDigitEquiv` fixes the encoding; no second response alphabet is introduced.

`reducedTableFeature` has exactly `3*k` coordinates for k covariate values. Its moments are the actual cells of `tableEvaluationLaw`. Applying the existing rational moment compression and recovering the omitted cells gives

```text
exists_three_cell_table_compression:
  every table law has a replacement with all row laws unchanged
  and at most 3*k+1 nonzero original-table atoms.

exists_three_cell_query_compression:
  all row laws and one additional rational table-query expectation
  are preserved with at most 3*k+2 nonzero original-table atoms.
```

`finiteLawSupport` counts nonzero masses on the original finite carrier. `momentCompression_sparse_support_card_le` proves that this support lies in the image of the compressed latent carrier. Consequently these are actual support bounds, in addition to the earlier latent-presentation bounds. The bounds also admit the independent trivial cap `4^k`; no claim that `3*k+2` is the exact minimum for every instance is made.

No cross-row coupling is held fixed unless it is represented among the retained query or constraint moments. The replacement law is selected for each original moment vector. A universally fixed small list of table atoms is not obtained.

## 42. Sparse witnesses inside the same fixed-noise Markovian family

`SparseFixedNoiseBenefitRealization.lean` resolves the independence issue that a direct compression of the two-mechanism joint law would leave open. Apply the row-only theorem separately to each complete mechanism table law and then use the unchanged `FixedNoisePairModel` product semantics.

For every original model, `exists_fixedNoise_sparse_equivalent` constructs a replacement such that

```text
support(left table law) <= 3*k+1,
support(right table law) <= 3*k+1,
all left and right response-row laws are equal to the originals,
selectedPairLaw(replacement).mass = selectedPairLaw(original).mass.
```

Thus the full distribution of `(C, W1(C), W2(C))` is preserved, not merely its simultaneous-benefit cell. The covariate root and the two complete mechanism disturbances remain independent because the source law is still their product. Cross-row dependence inside an individual table is allowed to change. No independence of Y0 and Y1 inside a response row is introduced.

`fixedNoise_pair_support_card_le` uses the exact Cartesian-product support identity to bound the support of the two table disturbances together by `(3*k+1)^2`. Including the separate covariate root multiplies this bound by its support size, which is at most k.

`fixedNoise_sparse_attainment_iff` proves equality of the unrestricted and support-bounded attainable benefit images for the existing four-conditional-marginal model class. Its composition with the previous sharpness theorem is `fixedNoise_sparse_joint_benefit_sharp_iff`:

```text
sum_c w(c)*L1(c)*L2(c) <= target <= sum_c w(c)*U1(c)*U2(c)
iff
one fixed-noise model attains target with the specified four kernels
and at most 3*k+1 support points in each independent mechanism.
```

The interval and estimand are unchanged. Any additional cross-row condition or extra statistical moment must be preserved separately before this result can be used for a more restricted family. In particular, full-table-law equality and preservation of queries that intervene on the covariate in several worlds are not inferred from equality of the selected same-stratum response law.

## 43. Sequential sparsification of arbitrary product-law moments

`ProductLawMomentSparsification.lean` goes beyond the same-stratum example. Let mu and nu be normalized rational laws on finite carriers A and B, and let f_j(a,b), j in J, be any finite family of rational coefficients. The retained vector is

```text
M_j(mu,nu) = sum_a sum_b mu(a)*nu(b)*f_j(a,b).
```

Fix nu and form `g_j(a) = sum_b nu(b)*f_j(a,b)`. Compress mu while preserving every g_j expectation. Call the replacement mu'. Then form the second, updated feature family `h_j(b) = sum_a mu'(a)*f_j(a,b)` and compress nu while preserving every h_j expectation. The resulting nu' satisfies

```text
M_j(mu',nu') = M_j(mu',nu) = M_j(mu,nu)  for every j.
```

The Lean theorem `productLaw_moment_sparse_replacements` implements these two exact steps and proves that each new factor has support at most `|J|+1`. Both factors stay on their original carriers, and the resulting law remains their product. The argument needs neither convexity of the product family nor independent selectability of factor parameters after data constraints are imposed.

For m supplied linear data rows and one target coefficient, `product_linear_problem_sparse_witness` retains all m+1 values and gives at most m+2 support points in each factor. The original `LinearFeasible` predicate and `linearObjective` are evaluated on the new product law itself. Any equalities or inequalities determined by the preserved moment vector therefore remain valid. Restrictions not determined by that vector still need their own preservation argument.

Recomputing the second feature family matters. For two initially independent fair bits, the equality event has probability 1/2. Holding either original fair factor fixed makes the equality probability insensitive to the other factor, so each factor separately admits replacement by a point mass at zero. Replacing both using those stale slices gives equality probability 1. The ordered construction recomputes the second slice after the first change and excludes this failure.

The same mathematical proof extends by finite induction to s independent components: retain the entire d-dimensional moment vector at each step, fix all other current factors, and replace only the current factor. Each final component needs at most d+1 atoms. This multi-component induction is a paper derivation here; the authored Lean endpoint covers two components. The small-support result is an existence statement and does not make the general multilinear optimization problem convex or polynomial-time solvable.

## 44. When the extra query really costs one dimension

The following exact rank classification is a mathematical derivation, not an additional Lean theorem in this continuation. On the unrestricted table carrier `{0,1,2,3}^k`, let b(t) be the 3k retained cell indicators. The all-3 table maps to zero. Changing only row c to a in {0,1,2} gives the standard basis vector e_(c,a). Therefore the affine rank of the row-profile family is exactly 3k.

For one extra scalar query q, the augmented profile `(b(t),q(t))` has affine rank 3k precisely when

```text
q(t) = alpha + sum_c beta_c(t(c)), with beta_c(3)=0.
```

One implication is immediate from the displayed affine representation. For the other, subtract the augmented all-3 profile. The 3k single-row changes are independent. If any table has a query residual not explained by their linear combination, subtracting that combination produces a nonzero vector whose first 3k coordinates vanish. This adds exactly one independent direction. Hence the augmented rank is 3k+1 whenever q has such a residual.

Thus an additive row query needs no new moment coordinate and admits the `3k+1` bound. A genuinely interacting query gives the ambient `3k+2` bound. At k=0 or k=1, every table query is additive in this sense, so an extra dimension cannot occur. Equivalently, a nonzero mixed rectangular difference across two distinct rows certifies an interaction; vanishing of every such difference gives the additive representation by successive row replacement.

These rank bounds are worst-case support guarantees, not pointwise lower bounds. For a finite profile family of affine rank r, the union of convex hulls of all subsets of at most r profiles is contained in a finite union of proper affine subspaces. It cannot cover the relative interior of the full profile polytope. Rational points outside that union exist because all profiles are rational and a rational simplex in the polytope has dense rational barycentric points. Such moment points require r+1 atoms. Special points can require fewer. The exact rank classification and this worst-case lower-bound argument have not yet been implemented as Lean declarations.

## 45. A direct rational construction and a replayable elimination identity

The row-only `3k+1` bound also has a direct construction that avoids enumerating `4^k` table atoms. Given four-cell row laws q_c, form the three internal cumulative sums per row, add 0 and 1, and sort their distinct values

```text
0 = a_0 < a_1 < ... < a_M = 1.
```

There are at most 3k internal cut points, so M <= 3k+1. On every interval `[a_j,a_(j+1))`, each row's inverse cumulative distribution is constant. Record the resulting complete table t_j and give it mass `a_(j+1)-a_j`. The masses are nonnegative rational numbers and telescope to one. Summing interval lengths assigned to any row cell recovers exactly q_c. Empty or repeated cumulative intervals cause no problem after distinct cut points are used.

Taking two independent copies of this finite interval-index disturbance realizes the two mechanisms with unchanged row laws. This is a choice of cross-row coupling for a witness, not an assumption imposed on all models. The construction preserves row marginals but need not preserve an arbitrary interacting query. Sorting uses O(k log k) rational comparisons and explicitly listing the at-most-3k+1 tables uses O(k^2) response entries; no rational bit-complexity bound is claimed here.

For a general moment vector, exact support elimination instead starts from a supplied finite law. For supported atom profiles v_i, augment them with the normalization coordinate 1. A rational nonzero dependence z satisfying

```text
sum_i z_i = 0,
sum_i z_i*v_i = 0
```

has both positive and negative coordinates. Define

```text
theta = min_{z_i>0} weight_i/z_i,
weight'_i = weight_i - theta*z_i.
```

Positive-z coordinates remain nonnegative by the ratio minimum; negative-z coordinates increase; at least one positive weight becomes zero. Normalization and all moments are unchanged by the two zero-sum identities. Iterating removes support until the augmented profiles are linearly independent. Every arithmetic operation is rational. This is the certificate identity underlying the regression implementation; a data-only Lean checker and a termination/correctness proof for an executable eliminator remain separate implementation obligations.

## 46. Source status and literature placement

The three new Lean modules have matching Scribe sources covering all 17 explicitly named public declarations. Mathematical self-review and exact rational regression were performed. Lean elaboration, kernel checking, Scribe emission, and executed axiom-closure reports were not obtained in this runtime. Existing declarations used by the new proof scripts retain their own verification status. No new axiom, sorry, admit, or native_decide occurs in the authored source.

The independent Python regression uses seed 20260906. It passed 1,252 omitted-cell identities, 60 table compression cases, 1,190 exact support-elimination steps, 36 sequential product cases with 90 preserved joint coordinates, 384 selected-pair cell comparisons, 12 population-benefit comparisons, and six direct cumulative-table constructions. It also checked the stale-parallel-slice counterexample and exact row/additive/interaction ranks for k=0 through k=4. A ten-stratum cumulative example has 31 table atoms instead of an ambient 1,048,576; two such mechanism laws have support 961. These are finite diagnostics, not universal proof-kernel evidence.

Bayer and Teichmann, *The proof of Tchakaloff's Theorem*, arXiv:math/0502473, places positive finite moment representation in its classical cubature context. Zhang, Tian, and Bareinboim, ICML 2022, PMLR 162:26548-26558, establishes canonical finite causal representations and polynomial counterfactual optimization. Arroyo et al., arXiv:2509.03548, exploits quasi-Markovian component structure and fixed-component linear slices, including a column-generation route. The present work uses these established representation principles; it makes no novelty or priority claim for Caratheodory, inverse-CDF coupling, or the support lemma.

The concrete repository additions are original-carrier three-cell reconstruction, sparse attainment of the existing covariate benefit interval within independent mechanisms, and a two-component exact moment-preserving sparsification theorem. None of these bounds is a DFAO state bound. The law space carrying the moment readout, the table atom space, and the computational states of the Zeckendorf oracle remain different typed objects. No finite information-escape score or maximal-catalog irredundancy assertion is inferred from their cardinalities.

## 47. Data-only rational elimination certificates, 2026-09-06

`D5/S0/Certificates/RationalMomentElimination.lean` turns the identity in Section 45 into a finite exact certificate consumer. The raw carrier is `Fin n`, the retained feature array has type `Fin n -> Fin d -> Q`, and the proposed `EliminationStep` contains only a rational direction z and a pivot index p. The payload contains no proof fields. Feature moments reuse the existing `linearObjective`.

`checkStep` decides seven finite conditions: nonnegative current weights; positive pivot weight; positive pivot direction; zero direction at every zero-weight atom; zero total direction; zero direction for each retained moment; and the cross-multiplied ratio inequalities

```text
weight(p)*z(i) <= weight(i)*z(p) whenever z(i)>0.
```

The validator does not divide by unverified denominators. Once accepted, it performs

```text
theta = weight(p)/z(p),
weight'(i) = weight(i) - theta*z(i).
```

`validStep_nonnegative`, `validStep_total`, and `validStep_moment` prove nonnegative output, exact mass conservation, and exact preservation of all nominated linear moments. `validStep_pivot_zero` proves cancellation of the positive pivot. `validStep_zero_stays_zero` prohibits reactivation of any zero atom. Together these imply the strict support theorem `validStep_support`: support is contained in the old support and its cardinality strictly decreases. Ratio ties may remove several atoms in one step.

`validStep_maximal_rate` proves that no larger move along the same oriented direction keeps every weight nonnegative, because its pivot would become negative. This is maximality along one feasible direction; it is not objective optimality or minimum-support optimality.

The inactive-coordinate condition matters independently of moment preservation. On atoms 0,1,2, the law `(1/2,0,1/2)` and direction `(1,-2,1)` would move to `(0,1,0)`, preserving total mass and mean while introducing the previously absent atom 1. The checker rejects this move. As a result, arbitrary hard support admissibility inherited from the initial law survives replay without needing a separate linear feature for every excluded atom.

## 48. Exact trace replay and a finite descent bound

`D5/S0/Certificates/RationalMomentReplay.lean` defines `replaySteps` by structural recursion on a finite list of proposed elimination steps. Every step is checked against the current weight vector. Failure returns `none`; success computes the exact rational update and checks the remaining trace. The recursion terminates on every finite input, including invalid traces.

`replaySteps_sound` proves the stronger quantitative invariant

```text
trace_length + final_support_size <= initial_support_size,
```

together with nonnegativity, conserved mass, equality of all retained moments, and support containment. A normalized vector cannot have empty support, so every successful trace from N active atoms has length at most N-1. This bounds accepted elimination steps, not rational arithmetic bit complexity or the runtime of an external search procedure.

`checkCompression` first checks normalization and nonnegative input, then replays the trace and requires the final support count to be at most d+1. It recomputes the output; a producer-supplied terminal vector is not trusted. `checkCompression_sound` certifies all these properties for any accepted output. `checkCompression_preserves_support_predicate` additionally transports every predicate holding on all initially active atoms, even if that predicate is not decidable or expressible as one of the retained moments.

Two closed examples are included as ordinary `decide` proof scripts: an accepted mean-preserving compression from the uniform law on 0,1,2 to the middle atom, and rejection of the zero-atom revival above. These Lean computations have not been executed in the current runtime.

## 49. Completeness of the certificate language

`CertifiedSparseCausalWitness.lean` separates a valid certificate language from a verified discovery algorithm. `exists_supported_moment_replacement` first restricts the existing rational Caratheodory construction to the original positive-support subtype. Its small latent law is pushed back to the same `Fin n` carrier. The result has at most d+1 active atoms, the same feature moments, and support contained in the original support.

This yields the stronger existence theorem `exists_accepted_moment_certificate`: every finite rational probability law has an accepted certificate, and existentially zero or one step suffices. An already small law uses an empty trace. Otherwise let v be the support-contained small replacement and define

```text
z = weight - v.
```

Both laws have equal totals and feature moments, so z has zero total and zero feature moments. Some initially positive pivot p has v(p)=0, since the replacement has strictly fewer active atoms. Therefore z(p)=weight(p)>0 and the pivot ratio is exactly one. For every z(i)>0, nonnegativity of v gives z(i)<=weight(i), which proves the cross-multiplied ratio condition. Zero initial coordinates also have v(i)=0. The checked update is exactly v.

Thus the data-only checker is not limited to a few hand-selected examples. Every required rational moment point admits a certificate in its language. The existence proof uses classical selection through the previously established Caratheodory theorem; it does not discover v in one arithmetic step. A Gaussian-elimination producer can still provide a longer trace with small local dependencies, while a solver that has already found v can provide the single difference direction.

## 50. Preserve the original causal LP and reuse its dual witness

The `rowQueryArray` adapter places the original scalar query at coordinate zero and the original m data rows at the successor coordinates. No coefficients are changed, and probability normalization remains a separate checker condition.

`checked_causal_problem_witness` packages an accepted result as the existing `FiniteResponseLaw` on the original carrier. It proves

```text
support(result) subset support(original),
support_size(result) <= m+2,
LinearFeasible A b result,
linearObjective query result = linearObjective query original.
```

The bound follows from retaining m+1 moment coordinates. Additional linear equalities or inequalities are preserved when their coefficients are among the retained rows, and any condition determined by the preserved moment vector remains true. Other nonlinear restrictions are not inferred automatically.

`checked_lower_endpoint_witness` combines the checked sparse primal law with an unchanged `LowerBoundCertificate`, using the existing `exact_lower_bound_of_certificate_and_witness`. The resulting exact lower endpoint and sparse attaining witness belong to the same original inequality system. The corresponding upper-bound interface already exists in `LinearObjectiveDual`; a separate checked upper-endpoint wrapper has not been added here.

For Markovian product families, apply the checker to a single current component using the fixed-component features from Section 43, recompute the features for the next component, and retain the product representation. The present new bridge formally covers one finite linear problem. An end-to-end executable multi-component replay driver remains to be implemented; a direct joint-law compression must not be treated as preserving independence.

## 51. Exact validation, remaining algorithms, and literature placement

The three new Lean modules have matching Scribe sources covering 27 named public declarations. The S0 validators and replay functions are written entirely with computable finite rational operations; classical choices are confined to S3 existence proofs. No new proof placeholders or axioms were introduced. Logical review and an independent exact-rational Python regression were performed. No Lean compiler or Lake executable was available, so elaboration, actual kernel execution of the closed examples, Scribe emission, and executed axiom-closure checks remain unverified in this session.

The Python producer uses rational Gaussian elimination to propose null directions and exact ratio minimization to propose pivots. A separate checker mirrors the finite acceptance conditions. With seed 20260906, it passed 192 trace cases, 192 zero-or-one-step certificate constructions, 480 preserved moment-coordinate checks, 1,187 checked elimination steps, and nine causal row/query cases. Six malformed step cases and four invalid compression cases were rejected. The exported example reduces eight active atoms to three in five checked steps and also has a one-step difference certificate. Python is not extracted Lean and supplies no proof-kernel evidence.

Piazzon, Sommariva, and Vianello, *Caratheodory-Tchakaloff Subsampling*, arXiv:1611.02065, studies compression of discrete measures and numerical construction through linear or quadratic programming. That established representation principle supplies context, not a novelty claim. The contribution to this repository is a data-only exact certificate format, proved support-monotone replay invariants, certificate existence over the same rational source semantics, and transport to the existing primal-dual causal certificates.

The next computational obligation is verified direction discovery, including row-operation invariants, a nonzero null-vector witness when active augmented columns are dependent, and the connection from verified Gaussian elimination to the existing checker. The direct sorted cumulative-table algorithm from Section 45 and rank-adaptive terminal certificates also remain separate targets. The current checker enforces the ambient d+1 bound; it does not compute a minimal support or an affine rank certificate.

All moment comparisons here occur on a fixed finite coefficient array and its original probability-law carrier. The integer N in the descent bound counts active probability atoms. It is unrelated to DFAO computational-state counts, and no information-escape score or maximal-catalog admission statement is asserted by the new certificate theorems.

## 52. Cross-author source audit and the preservation question, 2026-09-06

This continuation examined recent repository work across authors before selecting a mathematical interface. Three source-level connections were retained.

- loning, PR #5326, `RH_OFFLINE_ZERO_LEE_YANG_INSTANTANEOUS_PHASE_TRANSITION_THEORY.md`, pinned at `3beb435bf9ca8aa35aa6079ea4033a9c2e6c9007`: the solenoid/Schur/Rouche appendix explicitly separates Hankel behavioral minimality from determinant preservation. Its proposed low-dimensional transfer still needs a determinant-preserving identification. The reusable lesson here is that preserving nominated observations does not establish preservation of every later invariant.
- AlyciaBHZ, draft PR #5750, pinned at `dff43c8fe8cf16fa83bfacdda22090fd682acc61`: `SymmetricGaussianCompensation` retains the actual unequal-half phase before specializing, and `BernoulliIntervalThreshold` selects a common test before quantifying over unknown acquisition probabilities. The transferable quantifier pattern is one fixed construction with a guarantee for an entire parameter family.
- PR #5803, `QuquintCertificateAssembly.lean`, pinned at `dfab12155e5f5d7a8524862a8d1ee0353b0bc6c3`: branch definiteness is connected to the actual matrices by explicit LDL identities. Its coefficient identities are a stronger interface than a numerical proxy. No ququint or spectral claim is imported into the causal lane.

The new modules reuse only the causal lane's current `linearObjective`, support-monotone replay, `FiniteResponseLaw`, and primal-dual interfaces. The cross-author connections motivate the statements and their boundaries; they are not asserted to identify the different mathematical carriers or transfer physical conclusions. Searches for a matching affine presentation/replay or residual-envelope owner in the current lane did not produce a reusable exact owner. This is a scoped audit, not an exhaustive novelty claim.

## 53. Checked support-local affine coordinate reduction

`D5/S0/Certificates/RationalAffineMomentCompression.lean` upgrades the ambient-coordinate replay using a data-only `AffinePresentation`. For an original feature array phi with d coordinates, the payload selects r original coordinates and supplies offsets a_j and coefficients B_js. It checks the identity

```text
phi_j(i) = a_j + sum_s B_js * phi_selected(s)(i)
```

at every atom with nonzero original weight. An averaged identity is insufficient. The check need not cover zero-weight atoms because the existing accepted replay cannot introduce those atoms.

`checkAffineCompression` validates this presentation and invokes the unchanged `checkCompression` on the selected coordinates. `checkAffineCompression_sound` proves normalized nonnegative output, support contained in the original support, support size at most r+1, and equality of every original feature expectation. Thus rows are omitted only after their reconstruction has been checked against actual original coefficients.

The parameter r is the number of selected coordinates. The certificate proves an affine dimension upper bound on the original support, not equality with the minimal affine rank. Repeated or redundant selected coordinates do not invalidate the theorem, but can give a looser budget. Computing a minimal presentation or its independence certificate remains separate from checking a proposed presentation.

The closed example uses features i, 3+2i and 5-i on four atoms. The uniform input is replayed to weights `(1/2,0,0,1/2)`. One selected coordinate preserves all three expectations, with values `(3/2,6,7/2)`, and the output has two atoms. The same principle recovers the fourth response-cell indicator from normalization and three selected cell indicators.

## 54. One compressed law for a whole affine query family

`checkAffineCompression_preserves_affine_family` fixes the accepted compression and then quantifies over all rational offsets and coefficient vectors. For any

```text
q_theta(i) = alpha_theta + sum_j beta_theta,j * phi_j(i),
```

the same output law preserves the query expectation. The law and trace are not reselected for each theta. This accommodates families with infinitely many parameter values while keeping a finite spanning feature family.

The source gives this universal statement for affine queries of the retained full feature vector. It does not claim that every later nonlinear statistic, determinant, chronological functional, or intervention query belongs to that span. Additional readouts require a reconstruction or an error certificate. This is the causal counterpart of the preservation boundary identified in loning's theory, with distinct carriers kept explicit.

## 55. Certified residual enclosures for queries outside the retained span

`D5/S0/Certificates/RationalMomentQueryEnvelope.lean` supplies a data-only affine predictor and residual interval for a nominated query q. Write

```text
e(i) = q(i) - alpha - sum_j beta_j*phi_j(i).
```

`checkQueryEnvelope` verifies `lower <= e(i) <= upper` at every original active atom. For any accepted compression w -> v, nonnegativity and normalization give the same expectation enclosure for both laws:

```text
center + lower <= E_w[q], E_v[q] <= center + upper,
center = alpha + sum_j beta_j*E_w[phi_j].
```

`checked_query_error_bound` therefore proves

```text
abs(E_v[q] - E_w[q]) <= upper - lower.
```

A symmetric pointwise residual bound epsilon gives the general bound 2*epsilon. `checked_uniform_query_family` fixes one compressed law before quantifying over an arbitrary query-family parameter, with a verified support-local envelope for each parameter. This is a deterministic model-approximation guarantee. It is not a sampling confidence statement and does not by itself preserve the exact identified set of an omitted query.

`residual_energy_zero_iff` proves, for nonnegative weights,

```text
sum_i w(i)*e(i)^2 = 0
iff
all active atoms have e(i)=0.
```

Consequently `checked_query_exact_of_zero_residual_energy` turns an exact zero weighted square residual into exact query preservation. The signed residual has no analogous zero-mean criterion. In the closed counterexample, the uniform law on 0,1,2 is compressed to its middle atom while its mean is retained. The omitted event has coefficients `(1,0,1)` and changes from 2/3 to zero. Subtracting its original mean gives signed residual mean zero but residual square expectation 2/9.

Small positive square error is also insufficient for a uniform claim without additional weight control. The exact diagnostic takes w=(9999/10000,1/10000), q=(0,1), and no retained nonconstant features. A valid support-contained compression can choose the rare second atom with mass one. Its original square residual is 1/10000, while the query changes by 9999/10000. The finite pointwise envelope remains valid. This example is a Python-checked paper boundary, not an additional Lean declaration in this continuation.

## 56. Return to original causal feasibility and endpoint certificates

`RankAdaptiveSparseCausalWitness.lean` consumes `rowQueryArray`, so the reconstructed features are exactly the original LP data rows and target coefficient. `checked_affine_causal_witness` packages the actual checker output as `FiniteResponseLaw` on the original atom carrier, preserving every original `LinearFeasible` constraint and the exact query value with support at most r+1.

`checked_affine_lower_endpoint` reuses the original lower dual certificate with the new sparse primal witness. It does not alter the inequality system or claim that a support-local affine presentation holds outside the original support. The original dual certificate supplies the global bound; the compressed law supplies the attaining point.

For an omitted query, `checked_compressed_query_decision` proves that a compressed value exceeding a threshold by more than the residual width certifies that the original value exceeds the same threshold. This transports a strict decision under a verified error margin, analogous in quantifier structure to the common-envelope reasoning in #5750. No new concentration or physical measurement theorem is asserted.

## 57. Paper derivation: optimal residual width equals universal moment ambiguity

This section is a finite linear-programming derivation; the strong-duality equality has not yet been added as a Lean theorem. Fix a nonempty finite allowed carrier S, rational feature columns phi(i), and a rational query q(i). Consider the worst query difference between probability laws on S sharing the same feature moments:

```text
Delta_S(phi,q) = max { abs(E_u[q]-E_v[q]) : u,v in simplex(S), E_u[phi]=E_v[phi] }.
```

Swapping u and v shows that the absolute-value maximum equals the maximum of the signed difference. The primal linear program has objective `q.u - q.v`, constraints `1.u=1`, `1.v=1`, `Phi.u-Phi.v=0`, and nonnegative u,v. Its dual minimizes alpha+gamma subject to

```text
alpha + beta.phi(i) >= q(i),
gamma - beta.phi(i) >= -q(i)  for every i in S.
```

For fixed beta, the least alpha is the maximum of q-beta.phi and the least gamma is minus its minimum. Finite LP strong duality therefore gives

```text
Delta_S(phi,q) = min_beta [ max_i(q(i)-beta.phi(i)) - min_i(q(i)-beta.phi(i)) ]
              = 2 * min_{alpha,beta} max_i abs(q(i)-alpha-beta.phi(i)).
```

The primal is nonempty and bounded. Since its data are rational, optimal rational primal and dual witnesses exist, so the same equality applies to rational probability laws. The residual center alpha does not affect oscillation; the centered best uniform approximation splits the optimal width in half.

Thus universal zero ambiguity is equivalent to affine reconstruction on S. This is a statement about all laws on the allowed carrier and their moment fibers. It is distinct from the width for one fixed observed moment vector, which can be smaller, and from preservation by one particular compression map. Nonconvex Markovian restrictions on the probability-law family require their own analysis; the displayed duality uses the full pair of simplices.

For the Boolean benefit query q=1[(Y0,Y1)=(0,1)] and retained features (Y0,Y1), choose beta=(-1/2,1/2). The residual is `(0,1/2,1/2,0)` in the established four-cell ordering, so its oscillation is 1/2. The equal-weight diagonal and anti-diagonal laws have identical marginals (1/2,1/2) and benefit values zero and 1/2. These witnesses match the residual certificate, giving universal ambiguity exactly 1/2. This supplies a consistency bridge to the original benefit nonidentification example without replacing its sharper data-dependent Frechet interval.

## 58. Validation, scope and next source obligations

The three new Lean modules contain 29 named public declarations and have matching Scribe sources. The proof scripts received mathematical and source review. There is no Lean or Lake executable in this runtime; no new elaboration receipt, kernel evaluation of the closed examples, Scribe rendering, or executed axiom report was obtained. The authored source contains no sorry, admit, native_decide, or new axiom declaration. These facts do not replace kernel verification.

An independent Fraction regression with seed 20260906 reused the prior elimination producer and checker mirror. It passed 100 adaptive-coordinate cases, 500 full-feature moment comparisons, 658 elimination steps, 700 common affine-family query checks, 700 residual-envelope and strict-margin checks, and 700 zero-energy exactness cases. It rejected 100 corrupted affine presentations and 700 invalid envelopes. Zero-mass atoms with deliberately invalid reconstruction coefficients were included to test the support-local boundary. The exported diagnostics also verify signed cancellation, the rare-atom small-energy obstruction, and the matching Boolean-benefit ambiguity witnesses.

The external representation context remains Piazzon, Sommariva and Vianello, *Caratheodory-Tchakaloff Subsampling*, arXiv:1611.02065, and Zhang, Tian and Bareinboim, *Partial Counterfactual Identification from Observational and Experimental Data*, ICML 2022, PMLR 162:26548-26558. No novelty claim is made for finite moment compression, affine expectation transport, positivity of square residuals, or finite LP duality. The contribution in this lane is their exact integration with support-monotone replay and original causal witness semantics.

The direction-discovery obligation from Section 51 remains open in the authored source. This continuation closes a separate load-bearing interface: a proposed dimension reduction is now checked against actual coefficients before the smaller support budget is used, and additional query families have explicit exactness or error conditions. Further work can connect verified rational elimination to presentation discovery, prove the optimal residual-width duality using the existing certificate framework, and lift the checks into the ordered multi-component replay without weakening independence.

## 59. Fresh source audit and the finite-duality dependency, 2026-09-06

The continuation first reread PR #5029 at `60fbadcbca587ef4becfa3d8c99168812b8eea14`, compared it with the previous `976eef8d23501fb388398c03d141d207eb00096c`, and inspected dev at `d1aef59802e5c5be8302018ef0b2d47f7f87b9d0`. The intervening branch commit changes only the two earlier moment-support Scribe files; those concurrent edits are preserved. The cross-author scan included loning's updated PRs, including #5867, and the recent causal, moment and duality work across authors. No finite LP strong-duality implementation was inferred from an engineering closure argument or from a PR title.

The actual source of `D5/S3/Observer/Budget/ProjectiveStrongDuality.lean` assumes the finite strong-duality premise before transporting an infimum through a projective limit. The actual `LinearObjectiveDual.lean` proves weak duality and exactness given a matching primal witness. Neither provides the missing finite optimizer-existence theorem for Section 57.

A direct external owner was located: Martin Dvorak and Vladimir Kolmogorov, *Duality theory in linear optimization and its extensions: formally verified*, Annals of Formalized Mathematics, published 13 March 2026, DOI `10.46298/afm.14253`, arXiv:2409.08119v3. Its released code is `madvorak/duality` tag `v3.2.0`; `Duality/LinearProgrammingB.lean` contains `StandardLP.strongDuality` and imports the extended LP development. Both that tag and the checked default branch use Lean 4.18.0. This lane uses Lean 4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. No uninstalled import, toolchain change, external axiom or unreviewed compatibility port was introduced.

The approximation/moment-matching duality is an established principle, also explicitly described by Wu and Yang in their work on Chebyshev approximation and estimation of the unseen. Choe, Kwon, Park and Lee, *Canonical Domain Reduction for Partial Counterfactual Identification*, UAI 2026, PMLR 337:1302-1326, emphasizes preserving every objective and constraint functional during canonical reduction. These sources support the choice to verify the actual query coefficients and the whole allowed carrier. They do not supply an attribution of the specific certificate implementation or Boolean tolerance construction below. The present audit does not establish global mathematical novelty.

## 60. A robust ambiguity modulus for approximate moment agreement

Fix a nonempty finite allowed carrier S, rational feature map phi with d coordinates, a rational query q, and nonnegative coordinate tolerances eta. Define the pairwise ambiguity

```text
Delta_eta(phi,q) = max { abs(E_u[q]-E_v[q]) :
  u,v in simplex(S), abs(E_u[phi_j]-E_v[phi_j]) <= eta_j for every j }.
```

The errors compare two models directly. If each model is within epsilon_j of one observed center, triangle inequality only gives eta_j=2*epsilon_j; the common-center restrictions can make the actual range smaller than this global pairwise modulus.

For e(i)=q(i)-alpha-beta.phi(i) in [lower,upper] on every allowed atom, define

```text
B_eta = upper-lower + sum_j abs(beta_j)*eta_j.
```

`query_gap_le_residualBudget` reuses the earlier expectation enclosure for each law and proves `abs(E_u[q]-E_v[q]) <= B_eta`. The proof bounds the change of the two affine predictor centers, rather than assuming those centers are still equal. The full-array check is essential: a certificate verified only on the proposed optimizing supports cannot bound other admissible laws.

At paper level, the finite LP dual extends Section 57 to

```text
Delta_eta(phi,q) = min_beta [osc_S(q-beta.phi) + sum_j abs(beta_j)*eta_j].
```

Indeed, the primal has two simplex normalizations and the inequalities `-eta <= Phi*u-Phi*v <= eta`. Splitting the dual moment multiplier into its positive and negative parts gives the weighted absolute-value cost. This generic existence-and-equality statement still awaits a compatible connection to the external strong-duality owner. The Lean source below proves an exact certificate theorem and constructs a full parameter family of such certificates; it does not assume generic optimizer existence.

## 61. Exact contact certificates and the three-part optimality gap

`D5/S0/Certificates/RationalMomentAmbiguityCertificate.lean` introduces a raw payload containing only two rational weight vectors and the existing `QueryEnvelope`. Its finite checker validates normalization, nonnegativity, moment tolerances, the global residual envelope, support contacts, and signed moment alignment.

Write delta_j=E_u[phi_j]-E_v[phi_j]. The new `primal_dual_gap_identity` proves the exact equality

```text
B_eta - (E_u[q]-E_v[q])
 = sum_i u_i*(upper-e(i))
 + sum_i v_i*(e(i)-lower)
 + sum_j (abs(beta_j)*eta_j-beta_j*delta_j).
```

Under the checked feasibility conditions all three sums are nonnegative. Therefore a sufficient equality certificate is

```text
u_i != 0 -> e(i)=upper,
v_i != 0 -> e(i)=lower,
beta_j*delta_j = abs(beta_j)*eta_j for every j.
```

These are coefficient-level conditions checked from the supplied numbers. `contact_gap_eq_budget` uses the displayed identity to prove attainment. `checkContactCertificate_sound` then proves both `IsGreatest` of the actual attainable query-difference set and `IsLeast` of the actual valid residual-budget set, at that same rational value. Any competing affine residual envelope must have budget at least the query difference of the supplied pair. Thus acceptance proves optimality on both sides, rather than merely validating an upper bound.

With eta=0, the signed-alignment condition follows from exact moment matching. Geometrically, the upper-contact profiles and lower-contact profiles must admit convex combinations with the same feature mean. Their intersection is a useful way to search for certificate witnesses. This geometric interpretation is a paper explanation here; the source checks the explicit rational combinations.

## 62. A complete Boolean benefit tolerance family

`D5/S3/ConceptDynamics/PartialIdentification/BenefitMarginalToleranceSharp.lean` constructs a certificate for every eta0,eta1 >= 0. It retains the existing `FiniteResponseLaw (Bool x Bool)`, `controlSuccessMarginal`, `treatmentSuccessMarginal`, and `benefitResponseMass`. The Fin 4 array is only their encoding in order 00,01,10,11, with explicit expectation and probability-law transport in the proof.

The main theorem gives the universal bound, an attaining pair of actual response laws, and the least affine residual budget:

```text
max abs(Benefit(u)-Benefit(v)) = min(1, (1+eta0+eta1)/2),
```

where the two control marginals differ by at most eta0 and the two treated marginals by at most eta1. There is no fixed marginal location, primal optimizer, numerical threshold table or strong-duality hypothesis in this theorem. Dependence between the two potential outcomes within one outcome mechanism remains unrestricted.

For eta0+eta1 <= 1, put

```text
t=(1+eta0+eta1)/2,  s=(1+eta0-eta1)/2,
u=(0,t,1-t,0),     v=(1-s,0,0,s).
```

Nonnegative tolerances and their sum bound give 0<=t,s<=1. The control discrepancy is -eta0, the treatment discrepancy eta1, and the benefit gap t. The predictor beta=(-1/2,1/2) has residual `(0,1/2,1/2,0)`, so both support contacts and both signed alignments hold. Its budget is exactly t.

For eta0+eta1 > 1, take

```text
s=min(1,eta0),
u=(0,1,0,0),  v=(1-s,0,0,s).
```

The marginal discrepancies are -s and 1-s. The second is at most eta1, including eta0>=1. Choosing beta=0 and residual interval [0,1] gives budget one and both contacts. The source includes the joining boundary in the first branch; both constructions have the same optimum there.

For example, eta0=1/10 and eta1=1/5 give `u=(0,13/20,7/20,0)` and `v=(11/20,0,0,9/20)`, with benefit difference 13/20. At zero tolerances the earlier diagonal/anti-diagonal ambiguity 1/2 is recovered. This global modulus does not replace the narrower Frechet interval at a particular observed pair of marginals.

## 63. Optimal contact supports remove the extra query coordinate

`contact_certificate_preserved_by_compression` connects the new optimality witness to the existing support-monotone replay. Starting from a valid contact certificate, run `checkCompression` separately on its high and low laws, retaining only the d original feature coordinates. The output of each run has at most d+1 active atoms.

Support containment keeps the high output on the old upper-contact set and the low output on the old lower-contact set. Their individually preserved feature means keep both the tolerance inequalities and signed alignment. The resulting pair is therefore another valid contact certificate with the unchanged envelope and exact query gap.

The query is not added as a d+1st feature. On the upper contact support it already equals `alpha+beta.phi+upper`; on the lower contact support it equals `alpha+beta.phi+lower`. This is an exact support-local reconstruction, even when q is not affine on the whole original carrier. The result improves the general row-plus-query replay budget d+2 to d+1 per endpoint after an optimal contact certificate has been established.

The theorem supplies preservation and size bounds for accepted traces. Existing certificate-language completeness can supply traces existentially; it does not turn the current rational Gaussian-elimination producer into a kernel-verified discovery algorithm. Nor does the result claim a pointwise minimum number of atoms.

## 64. Paper continuation: a joint colored replay targets d+2 total atoms

There is a sharper construction that treats the pair jointly. On the disjoint union of the upper and lower contact carriers, give atom (plus,i) mass u_i/2 and atom (minus,i) mass v_i/2. This is one normalized rational law. Retain only the following d+1 coordinates:

```text
psi(plus,i)  = (1,  phi(i)),
psi(minus,i) = (0, -phi(i)).
```

The retained moments are `(1/2, delta/2)`. Apply support-contained moment compression to this single colored law. Its support has at most d+2 atoms. Preservation of the first coordinate gives mass 1/2 on each color. Multiplying the two color restrictions by two recovers two probability laws. Preservation of the signed features gives the same moment difference delta, and support containment retains the two residual contact levels. Consequently their query gap still equals the same optimal budget.

Thus, at paper level, every existing contact certificate has another one with at most d+2 total active atoms across both endpoints. This can be sharper than separately bounding each endpoint by d+1. The argument holds for nonzero tolerances because it preserves the realized signed moment difference, not merely an error bound. The explicit Fin-index packing/unpacking adapter and joint replay theorem have not yet been added to Lean. The new formal source in Section 63 covers the separate two-trace construction only.

## 65. Executed checks, source status and the next dependency boundary

The two new Lean sources contain 601 lines and 22 named public declarations, with two source-owned Scribe counterparts. Every named declaration has a Describe handle; theorem formulas and the two-branch coefficient data are authored in the Scribe sources. There is no Lean, Lake or dotnet executable in this runtime. No new Lean elaboration, executed axiom report, Scribe compilation or canonical emission is claimed. The scripts contain no new axiom declaration, sorry, admit or native_decide. Source/logic review and finite exact regression are distinct from kernel verification.

The reproducible Fraction diagnostic uses seed 20260906. It passed 3,721 Boolean tolerance-grid certificates, including zero, the exact boundary and tolerances above one; 400 general rational three-part gap identities and error bounds; and 120 independent numerical LP proposals reconstructed into rational primal and dual data. Every reconstructed proposal passed the complete exact contact checker without a numerical acceptance tolerance.

For those 120 certified problems, each allowed atom was duplicated four times and its weight divided equally among its copies. The resulting larger contact laws were separately compressed using only their original feature coordinates. All 120 resulting pairs retained certificate validity, individual query values and the optimum, with 834 checked elimination steps and the d+1 bound on each endpoint. Eight malformed certificates, targeting probability validity, moment feasibility, global bounds, contacts and slope direction, were rejected. These implementations are independent Python mirrors, not code extracted from Lean.

The formalized certificate language now has a substantive consumer with an explicit certificate for every nonnegative Boolean tolerance pair. The remaining general existence theorem should consume a compatible port or upstream integration of the identified Dvorak--Kolmogorov strong-duality owner, with exact maps between its standard LP coefficients and this lane's original feature/query arrays. Joint colored replay is the next source-local compression target. Statistical confidence statements would additionally require a simultaneous data-error event and an explicit conversion between individual confidence radii and pairwise moment tolerances; none is supplied by a deterministic residual certificate alone.
