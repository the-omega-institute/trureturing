# Causal Partial Identification Research Ledger

## 1. Purpose

This ledger records the research and formalization work carried by pull request #5029. It separates verified repository state, reusable library interfaces, new truth sources, literature-facing claims, and remaining proof obligations.

The governing proof pipeline is:

```text
causal or statistical assumptions
  -> admissible structural response models
  -> feasible coupling or response-type set
  -> primal query optimization
  -> replayable dual validity certificate
  -> attaining primal witness
  -> Lean sharpness theorem
```

For convex finite models, exact endpoint witnesses and affine interpolation fill the entire interval. For polynomial cross-world restrictions, endpoint attainment alone does not imply interval filling.

## 2. Baseline repair

The PR branch began at commit `2326aeaeeb898d256ac2843a1ccca6622e0ba8e8` and had diverged from the protected `dev` branch. The repair merge rebases the research tree semantically onto `dev` commit `a5ebe0428d12d75a2e29587909df910fe44f2808` while preserving all fifteen existing PR files.

Seven existing Scribe definitions had no committed Markdown projections. Their generated projections, together with the three new projections introduced below, are required before the narrative layer is fresh under `make emit --check`. The Scribe files remain the canonical narrative sources. Generated Markdown is a projection and must not be edited independently.

## 3. Library audit

The audit reused the following truth sources.

- `D5/S0/Certificates/RationalFarkas` supplies exact rational infeasibility certificates.
- `D5/S0/Certificates/LinearObjectiveDual` extends this pattern to nonzero linear objectives with primal and dual endpoint witnesses.
- `D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification` separates universal validity, endpoint attainment, convexity, and interval sharpness.
- `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification` supplies outer-relaxation transport and records why endpoints do not determine a disconnected range.
- `D5/S3/ConceptDynamics/Causal/StructuralEvaluationSemantics` supplies the canonical finite list-level `Before` relation.

Repository searches found no existing theorem for independently combinable covariate-stratum sharp intervals, no required/forbidden-edge partial-diagram refinement object, and no counterfactual-query-to-order compiler layer.

## 4. Existing PR truth sources

The first research layer establishes:

1. exact rational weak-duality certificates for finite linear objectives;
2. a generic convex sharp-interval theorem;
3. an explicit four-cell Fréchet coupling with an exact projection theorem;
4. a disagreement-cap tightening with a replayable slack certificate;
5. a ternary-treatment, ternary-outcome structural-response instance;
6. a finite causal LP semantic adapter with data, structural, and sensitivity constraint provenance;
7. a nonconvex identification core;
8. a polynomial cross-world independence example whose query is point identified while the global independence family is nonconvex.

## 5. New concrete truth source: covariate aggregation

`CovariateSharpAggregation` treats a finite covariate set. Stratum `c` has a sharp scalar interval `[L_c, U_c]`, and the global query uses fixed nonnegative weights `w_c`.

Under the explicit joint-selection assumption that one admissible query value may be chosen in every stratum, the global identified set is exactly

```text
[ sum_c w_c L_c, sum_c w_c U_c ].
```

Validity follows from pointwise order and nonnegative weighted summation. Sharpness uses one common interpolation parameter across all strata. This assumption fails when strata share unidentified structural parameters or are coupled by transport, smoothness, or other cross-stratum restrictions.

## 6. New concrete truth source: partial graph information order

`PartialGraphInformationOrder` represents a partial causal diagram by required and forbidden directed edges. A stronger diagram retains all assertions of a weaker diagram and may add more.

The central order reversal is:

```text
stronger graph information
  -> fewer compatible complete graphs
  -> fewer compatible structural models
  -> a smaller identified query set.
```

The module proves compatible-set and identified-set antitonicity. It then reuses the generic nonconvex outer-relaxation theorems to show that valid weaker-family bounds survive refinement, attained lower endpoints can only rise, and attained upper endpoints can only fall.

This is an information-order theorem. It does not yet compile arbitrary graphical separation statements into response-type probability constraints.

## 7. New concrete truth source: query-implied causal order

`QueryImpliedCausalOrder` formalizes one query-compiler obligation motivated by causal-order partial identification.

A counterfactual atom contains an outcome coordinate and an intervention set. Every nontrivial intervention coordinate generates the strict precedence requirement

```text
intervened coordinate < counterfactual outcome.
```

A query is compatible with a strict causal order when all generated requirements hold. Reciprocal requirements are inconsistent by asymmetry. The module also provides an adapter to the existing finite structural-model `Before` relation.

The following claims remain outside this truth source:

- completeness of the extracted order constraints;
- construction of every compatible total extension;
- canonical response signatures for a selected extension;
- linearization of all observational and counterfactual query terms;
- invariance of optimal endpoints across compatible extensions;
- construction of an attaining SCM from every optimal response-signature mass.

These are the next theorem-sized research targets.

## 8. Interfaces to 2026 research

The current literature interface is organized as follows.

- Partial causal diagrams: Xie and Li, arXiv:2602.14503. Structural and statistical partial knowledge is represented as constraints on counterfactual distributions.
- Causal orders: Rossetto and Antonucci, arXiv:2608.24427. Counterfactual queries induce precedence constraints, compatible total extensions support canonical response-function LPs, and sharpness is tied to constructing attaining SCMs.
- Covariates and mediators: Shu, Lei, and Li, arXiv:2608.12657. Additional causal knowledge can tighten multivalued probabilities of causation. Mediator factorization can leave the polyhedral lane and enter polynomial feasibility.
- Continuous outcomes: Chaoge et al., arXiv:2605.01883. Copula restrictions constrain infinite-dimensional counterfactual coupling families.

The repository claim boundary is narrower than the cited papers. This PR proves reusable logical kernels and finite concrete instances. It does not claim full reproduction of any paper's general algorithm or theorem family.

## 9. Verification ledger

The required machine checks after branch update are:

```text
Candidate harness engineering checks
Canonical Lean report production
Content-addressed dev baseline admission
```

A truth source is considered repaired only after its current commit is checked by the protected-branch workflow. Scribe freshness additionally requires generated Markdown to equal the current render exactly.

## 10. Next formal research sequence

The next sequence is deliberately compiler-centered:

```text
QueryOrderLinearExtension
  -> CanonicalResponseSignature
  -> CausalOrderLinearProgram
  -> ExtensionInvariantQueryBound
  -> AttainingStructuralModel
```

In parallel, the partial-diagram lane should add:

```text
PartialDiagramConstraintCompiler
  -> compiler soundness
  -> information-refinement row inclusion
  -> rational primal-dual payload
  -> sharp endpoint witnesses.
```

The covariate lane should next distinguish freely combinable strata from shared-parameter strata and prove a strict counterexample to naive weighted sharpness under cross-stratum coupling.
