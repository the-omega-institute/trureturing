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

The PR branch began at commit `2326aeaeeb898d256ac2843a1ccca6622e0ba8e8` and had diverged from the protected `dev` branch. The repair merge places the research tree on `dev` commit `a5ebe0428d12d75a2e29587909df910fe44f2808` while preserving all existing research files.

Scribe files remain the canonical narrative sources. Generated Markdown must be produced and judged by the repository renderer rather than edited independently. Projection freshness is therefore recorded only from the protected workflow result.

## 3. Library audit

The audit reused the following truth sources.

- `D5/S0/Certificates/RationalFarkas` supplies exact rational infeasibility certificates.
- `D5/S0/Certificates/LinearObjectiveDual` extends this pattern to nonzero linear objectives with primal and dual endpoint witnesses.
- `D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification` separates universal validity, endpoint attainment, convexity, and interval sharpness.
- `D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification` supplies outer-relaxation transport and records why endpoints do not determine a disconnected range.
- `D5/S3/ConceptDynamics/Causal/StructuralEvaluationSemantics` supplies the canonical finite list-level `Before` relation.
- Mathlib's `extend_partialOrder` supplies the Szpilrajn linear-extension theorem already used elsewhere in the repository.

Repository searches found no existing theorem for independently combinable covariate-stratum sharp intervals, no shared-parameter counterexample to naive aggregation, no required/forbidden-edge partial-diagram refinement object, no counterfactual-query-to-order compiler, no finite canonical response-signature carrier, and no identified-set transport theorem across order-indexed signature equivalences.

## 4. First sharp-bounds layer

The first research layer establishes:

1. exact rational weak-duality certificates for finite linear objectives;
2. a generic convex sharp-interval theorem;
3. an explicit four-cell Fréchet coupling with an exact projection theorem;
4. a disagreement-cap tightening with a replayable slack certificate;
5. a ternary-treatment, ternary-outcome structural-response instance;
6. a finite causal LP semantic adapter with data, structural, and sensitivity constraint provenance;
7. a nonconvex identification core;
8. a polynomial cross-world independence example whose query is point identified while the global independence family is nonconvex.

## 5. Covariate sharp aggregation

`CovariateSharpAggregation` treats a finite covariate set. Stratum `c` has a sharp scalar interval `[L_c, U_c]`, and the global query uses fixed nonnegative weights `w_c`.

Under the explicit joint-selection assumption that one admissible query value may be chosen in every stratum, the global identified set is exactly

```text
[ sum_c w_c L_c, sum_c w_c U_c ].
```

Validity follows from pointwise order and nonnegative weighted summation. Sharpness uses one common interpolation parameter across all strata. This assumption fails when strata share unidentified structural parameters or are coupled by transport, smoothness, or other cross-stratum restrictions.

## 6. Shared-parameter obstruction and the value one half

`CovariateSharedParameterObstruction` proves that sharp projected stratum intervals do not suffice for sharp weighted aggregation.

Two Boolean strata use complementary responses to one parameter:

```text
q_false(theta) = theta
q_true(theta)  = 1 - theta.
```

If the parameter may be chosen separately for each stratum, both projected identified sets are exactly `[0, 1]`, and the independent product family can realize global value zero. If both strata must share one parameter and receive equal weights, the actual global query is

```text
(1 / 2) q_false(theta) + (1 / 2) q_true(theta) = 1 / 2
```

for every admissible `theta`. The shared-parameter identified set is therefore the singleton `{1 / 2}`.

The module now isolates the algebraic mechanism:

```text
x = 1 - x  ->  x = 1 / 2,
left + right = 1  ->  (left + right) / 2 = 1 / 2.
```

This is an affine complement symmetry. It has no established analytic-number-theoretic content.

The Riemann zeta critical line also contains the coordinate `1 / 2`, but for a different reason. The completed zeta function satisfies the reflection equation `xi(s) = xi(1 - s)`, whose real-coordinate reflection has fixed set `Re(s) = 1 / 2`. The shared abstract pattern is a reflection with midpoint one half. No map in this causal construction preserves the zeta function, its Euler product, analytic continuation, or nontrivial zero set. Therefore the causal singleton does not currently yield an RH implication, criterion, or reformulation.

## 7. Partial graph information order

`PartialGraphInformationOrder` represents a partial causal diagram by required and forbidden directed edges. A stronger diagram retains all assertions of a weaker diagram and may add more.

The central order reversal is:

```text
stronger graph information
  -> fewer compatible complete graphs
  -> fewer compatible structural models
  -> a smaller identified query set.
```

The module proves compatible-set and identified-set antitonicity. It then reuses the generic nonconvex outer-relaxation theorems to show that valid weaker-family bounds survive refinement, attained lower endpoints can only rise, and attained upper endpoints can only fall.

This is an information-order theorem. It does not yet compile graphical path, ancestry, or separation assertions into response-type probability rows.

## 8. Query-implied causal order

`QueryImpliedCausalOrder` formalizes the first compiler obligation motivated by causal-order partial identification.

A counterfactual atom contains an outcome coordinate and an intervention set. Every nontrivial intervention coordinate generates the strict precedence requirement

```text
intervened coordinate < counterfactual outcome.
```

A query is compatible with a strict causal order when all generated requirements hold. Reciprocal requirements are inconsistent by asymmetry. The module also provides an adapter to the existing finite structural-model `Before` relation.

## 9. Linear extension of the query order

`QueryOrderLinearExtension` packages an embedding of all query-generated precedence requirements into a partial order. It applies the Szpilrajn extension theorem and proves the existence of a linear relation that:

1. is a linear order;
2. preserves every relation in the certified partial order;
3. preserves every query-generated intervention-to-outcome obligation;
4. retains source-target disequality for each nontrivial obligation.

This closes the first missing step in the 2026 causal-order pipeline. It does not claim that an arbitrary cyclic query admits such a certificate.

## 10. Canonical response signatures

`CanonicalResponseSignature` formalizes the response representation induced by a chosen total order.

For position `j`, the structural response table has type

```text
(assignments to the j predecessor positions) -> current value.
```

A complete signature stores one such table at every position. Finite value spaces give a finite signature carrier. Every Boolean observational or counterfactual event is then represented by a zero-one coefficient, and its probability is exactly a rational linear objective in signature masses.

The module also defines deterministic pushforward from finite exogenous states to signatures and proves preservation of total mass, nonnegativity, and identity realization.

## 11. Causal-order linear program

`CausalOrderLinearProgram` joins canonical signatures to `FiniteLinearCausalIdentification`.

```text
layered constraint rows
+ response-signature mass vector
+ Boolean event indicator
= finite rational causal LP.
```

The compiled query equals the original signature event probability. Rational lower and upper dual certificates therefore bound the causal event itself. A finite-sum pushforward theorem proves that evaluating an event directly on exogenous states agrees with evaluating it after mapping those states to deterministic signatures.

## 12. Extension-invariant identified sets

`ExtensionInvariantQueryBound` isolates the exact proof payload required to justify the paper's total-order invariance claim.

For two order-indexed signature programs, a carrier equivalence must preserve:

1. every compiled observational or statistical row;
2. every row right-hand side;
3. the Boolean query evaluation.

Under those conditions, relabeling a mass vector preserves feasibility and event value in both directions. The complete attainable query sets are therefore equal.

This theorem deliberately refuses the shortcut

```text
both total orders extend the same partial order
  -> automatically equal LP bounds.
```

The missing implication is precisely the construction of a row- and query-equivariant signature equivalence for the two concrete order extensions.

## 13. Attaining structural model

`AttainingStructuralModel` formalizes the canonical tightness construction.

A normalized nonnegative law on complete response signatures is realized by taking the signature carrier itself as one shared exogenous state space. Each exogenous state selects itself, and its structural equations are exactly the predecessor-response tables stored in that signature.

Consequently:

```text
feasible signature mass
  -> finite shared-exogenous structural model
  -> identical induced signature law
  -> identical Boolean counterfactual event probability.
```

This closes the abstract primal-attainment bridge. A concrete paper-level tightness theorem must additionally prove that the compiled observational rows are exactly the observed distribution constraints and that the structural model is compatible with the chosen query order.

## 14. Interface to 2026 research

The current literature interface is organized as follows.

- Partial causal diagrams: Xie and Li, arXiv:2602.14503. Structural and auxiliary statistical information are inserted as constraints on counterfactual distributions. The paper also emphasizes multivalued variables, covariate information, and mediator information.
- Causal orders: Rossetto and Antonucci, arXiv:2608.24427. Counterfactual queries induce precedence constraints. A compatible total order defines a canonical PSCM and response signature. Query and observational probabilities become linear expressions. The LP is claimed tight by an attaining SCM construction, and the optimal bound is claimed invariant across compatible total orders and after marginalizing unqueried variables.
- Covariates and mediators: Shu, Lei, and Li, arXiv:2608.12657. Additional causal knowledge can tighten multivalued probabilities of causation. Mediator factorization can leave the polyhedral lane and enter polynomial feasibility.
- Continuous outcomes: Chaoge et al., arXiv:2605.01883. Copula restrictions constrain infinite-dimensional counterfactual coupling families.

The repository claim boundary is narrower than the cited papers. This PR proves reusable logical kernels, compiler interfaces, and finite concrete instances. It does not claim full reproduction of any paper's general algorithm or theorem family.

## 15. Verification ledger

The required machine checks after branch updates are:

```text
Candidate harness engineering checks
Canonical Lean report production
Content-addressed dev baseline admission
```

A truth source is considered repaired only after its current commit is checked by the protected-branch workflow. Scribe freshness additionally requires the renderer's generated projection to agree exactly with the checked source.

## 16. Next formal research sequence

The causal-order sequence has advanced through:

```text
QueryImpliedCausalOrder
  -> QueryOrderLinearExtension
  -> CanonicalResponseSignature
  -> CausalOrderLinearProgram
  -> ExtensionInvariantQueryBound
  -> AttainingStructuralModel.
```

The next nontrivial theorem is a concrete adjacent-swap construction for two incomparable variables. It should build the signature equivalence explicitly and prove preservation of all observation and query evaluations. Adjacent swaps can then generate invariance between arbitrary linear extensions of the same finite partial order.

In parallel, the partial-diagram lane should add:

```text
PartialDiagramConstraintCompiler
  -> ancestry and non-ancestry row semantics
  -> compiler soundness
  -> information-refinement row inclusion
  -> rational primal-dual payload
  -> sharp endpoint witnesses.
```

The covariate lane should characterize shared-parameter aggregation as the image of a joint feasible set and identify sufficient conditions weaker than a full product decomposition under which weighted endpoints remain sharp.
