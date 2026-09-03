# Causal Partial Identification and Sharp Bounds

## 1. Scope

This note develops the logical layer behind the causal sharp-bounds lane. The aim is to separate four questions that are often conflated:

1. what causal or statistical assumptions define the admissible counterfactual worlds;
2. how those worlds become a feasible coupling set;
3. how a query is bounded over that set;
4. what is required to call the resulting bounds sharp.

The key point is that the reusable object is not a particular probability-of-causation formula. It is an identified set obtained by projecting a feasible set of counterfactual laws through a query functional.

The finite polyhedral case is the first formal target because response-function models turn many discrete counterfactual problems into linear optimization over a simplex. The continuous case has the same logical shape but generally becomes an infinite-dimensional coupling problem.

## 2. Counterfactual semantics as a response-type law

Let `R` be a finite set of deterministic response types. A response type contains enough information to evaluate every counterfactual term relevant to the query. A population is represented by a probability vector

\[
\pi \in \Delta(R),
\qquad
\pi_r \ge 0,
\qquad
\sum_{r\in R}\pi_r=1.
\]

For a discrete structural causal model, `R` may be taken as a set of deterministic structural response functions. A full Cartesian response-type representation can be very large, but causal order and graph structure can factor it into local response functions.

Every event probability whose truth value is determined by a response type is linear in `\pi`. If `g(r)\in\{0,1\}` records whether response type `r` satisfies a counterfactual event, then

\[
Q(\pi)=\sum_{r\in R} g(r)\pi_r.
\]

More general finite counterfactual expectations are also linear whenever the response-type value of the estimand is fixed.

This gives the first abstraction:

\[
\boxed{
\text{counterfactual semantics}
\to
\text{response types}
\to
\text{law on response types}
\to
\text{linear query}.
}
\]

## 3. Three sources of constraints must remain distinct

A feasible model is obtained by intersecting the response-type simplex with constraints. The provenance of a constraint matters.

### 3.1 Data-identified constraints

Observed and interventional distributions usually become affine marginal equations. For example,

\[
P(Y_a=y)=\sum_{r:\,Y_a(r)=y}\pi_r.
\]

When the right-hand side probability is known, this is a linear equality in `\pi`.

These constraints are justified by the observation or intervention regime plus whatever identification assumptions are needed to connect that regime to the counterfactual marginal.

### 3.2 Structural causal assumptions

A causal graph, a partial graph, or merely a causal order restricts which response functions are admissible and how they may depend on parent variables. In a response-type encoding this can appear as:

- removal of impossible response types;
- equality constraints tying response coordinates together;
- a factorized local response representation;
- consistency restrictions between nested counterfactuals.

The 2026 causal-order result is especially important conceptually: a complete graph is not always required. The query itself can imply enough topological order to parameterize an admissible finite SCM family and optimize the query over it.

### 3.3 Sensitivity or cross-world restrictions

A condition such as

\[
P(A\neq B)\le \kappa
\]

may restrict the unknown dependence between potential outcomes while not being identified from their marginals. Such a condition must be represented as an additional assumption or sensitivity parameter.

This distinction prevents a common logical error: treating a cross-world dependence restriction as though it were observed data.

The correct pipeline is therefore

\[
\boxed{
\text{data constraints}
\cap
\text{structural constraints}
\cap
\text{sensitivity constraints}
=
\mathcal F.
}
\]

## 4. The identified set is a projection

Let `\mathcal F` be the set of admissible response-type laws and let `Q` be the causal query. The identified set is

\[
\mathcal I_Q
=
\{Q(\pi):\pi\in\mathcal F\}.
\]

For a scalar query, partial identification asks for this set. Reporting only two valid inequalities is logically weaker than identifying the set.

Four notions should be distinguished.

### 4.1 Valid lower and upper bounds

`L` and `U` are valid when

\[
\forall \pi\in\mathcal F,
\qquad
L\le Q(\pi)\le U.
\]

### 4.2 Endpoint optimality

The lower endpoint is optimal when some admissible model attains it:

\[
\exists \pi_L\in\mathcal F,
\qquad Q(\pi_L)=L.
\]

Likewise for `U`.

### 4.3 Interval sharpness

The interval is sharp when

\[
\mathcal I_Q=[L,U].
\]

This requires every interior target to be attainable, not only validity of the two inequalities.

### 4.4 Point identification

Point identification is the degenerate case

\[
L=U.
\]

It is therefore best treated as collapse of a sharp identified interval rather than as a logically separate framework.

## 5. Convexity gives the central sharpness theorem

The most useful general observation is elementary but powerful.

Assume:

1. `\mathcal F` is convex;
2. `Q` is affine on `\mathcal F`;
3. `L` and `U` are valid bounds;
4. there are admissible endpoint witnesses `\pi_L,\pi_U` with query values `L,U`.

For every `t\in[0,1]`, convexity gives

\[
\pi_t=(1-t)\pi_L+t\pi_U\in\mathcal F.
\]

Affinity gives

\[
Q(\pi_t)
=(1-t)L+tU.
\]

As `t` ranges over `[0,1]`, the right-hand side ranges over the whole interval `[L,U]`. Hence

\[
\boxed{
\mathcal I_Q=[L,U].
}
\]

This theorem changes how sharpness proofs should be organized. One need not construct a new SCM independently for every interior target. It is enough to prove endpoint attainment and convex closure, provided mixing admissible laws preserves all assumptions.

For finite linear constraints this convexity is automatic. It may fail after imposing nonlinear or nonconvex dependence restrictions.

## 6. Primal and dual certificates have different jobs

Suppose the finite problem is written as a linear program over `x=\pi`:

\[
Ax=b,
\qquad
Cx\le d,
\qquad
x\ge0,
\]

with query

\[
Q(x)=c^\top x.
\]

A dual or Farkas-style certificate can prove a bound by expressing the target inequality as a nonnegative combination of feasible constraints. Its logical role is universal:

\[
\boxed{
\text{dual certificate}
\Rightarrow
\text{every feasible model obeys the bound}.
}
\]

A primal witness has an existential role:

\[
\boxed{
\text{primal witness at value }L
\Rightarrow
L\text{ is attainable}.
}
\]

When a valid dual bound and a primal witness have the same objective value, the endpoint is optimal. If both endpoints are certified and the feasible set is convex with affine query, the complete interval is sharp.

Thus the preferred proof architecture is

\[
\boxed{
\begin{aligned}
\text{causal assumptions}
&\to \mathcal F,\\
\text{dual certificate}
&\to \text{valid endpoint},\\
\text{primal witness}
&\to \text{attained endpoint},\\
\text{convexity + affinity}
&\to \text{sharp interval}.
\end{aligned}
}
\]

This is stronger and more modular than asking an optimizer for a decimal optimum and calling it sharp.

## 7. Stronger assumptions form an information order

Let `\mathcal F_2\subseteq\mathcal F_1`. The second model contains at least as much valid restriction as the first. Then

\[
\inf_{\pi\in\mathcal F_1}Q(\pi)
\le
\inf_{\pi\in\mathcal F_2}Q(\pi)
\le
\sup_{\pi\in\mathcal F_2}Q(\pi)
\le
\sup_{\pi\in\mathcal F_1}Q(\pi),
\]

whenever the extrema are defined.

So adding valid information can only shrink the identified interval. This provides a precise interpretation of covariates, mediators, partial graph knowledge, or dependence restrictions as information operators on the feasible set.

This also gives a useful diagnostic. If a purported additional assumption produces a wider exact identified interval under the same query and data, then either the feasible-set relation was encoded incorrectly or the reported intervals are not exact.

## 8. Empty feasible sets represent falsification, not extreme bounds

If

\[
\mathcal F=\varnothing,
\]

the data and assumptions are mutually inconsistent. The correct conclusion is incompatibility of the model specification, not a causal bound.

This is important for machine workflows. A solver should first distinguish:

```text
feasible
infeasible
unbounded/improper query encoding
```

before interpreting numerical objectives causally.

A formal API should therefore carry feasibility evidence explicitly.

## 9. Partial causal diagrams and causal orders

The 2026 work on partial causal diagrams shows that incomplete graphical knowledge can still tighten probabilities of causation by translating available causal and statistical knowledge into optimization constraints. The newer causal-order formulation goes further: arbitrary and nested counterfactual queries can induce a partial topological order that is sufficient to construct a query-specific LP, with tightness proved by attaining SCMs.

The conceptual lesson is that graph completion is not the primitive object for partial identification. The primitive object is the set of structural models compatible with the information actually needed by the query.

For formalization this suggests:

```text
Query
  -> required counterfactual variables
  -> query-implied causal order
  -> admissible local response functions
  -> finite response-type carrier
  -> linear observational/interventional constraints
  -> query LP.
```

A future compiler should therefore target a constraint system rather than insist on reconstructing a unique full DAG.

## 10. Multivalued treatment and outcome

If treatment takes `k` values and outcome takes `m` values, a naive potential-outcome response type is a function

\[
r:\{1,\dots,k\}\to\{1,\dots,m\}.
\]

There are `m^k` such response types before additional structure is used. A joint counterfactual event is simply a subset of this finite carrier, so its probability is linear in the response-type law.

Therefore multivaluedness changes the dimension of the polytope, but not the basic logic:

\[
\boxed{
\text{finite multivalued PoC}
=
\text{linear projection of a finite response polytope}.
}
\]

The main mathematical difficulty is combinatorial growth and the structure of useful additional constraints, rather than a new notion of sharpness.

## 11. Covariates

Let a discrete covariate be `C`. Conditional response laws `\pi^{(c)}` can be used within each stratum. If the stratum weights `w_c=P(C=c)` are known and there are no additional cross-stratum restrictions, then

\[
Q=\sum_c w_c Q_c.
\]

If each stratum has a sharp interval

\[
Q_c\in[L_c,U_c],
\]

and the strata can be varied independently, then

\[
\boxed{
Q\in
\left[
\sum_c w_cL_c,
\sum_c w_cU_c
\right]
}
\]

is sharp. Endpoint witnesses are obtained by choosing all stratum lower witnesses or all stratum upper witnesses.

This explains why covariate information can tighten bounds: conditioning replaces one coarse coupling problem by smaller constrained coupling problems before the results are recombined.

The independence qualification matters. If response laws across strata share parameters or obey global structural restrictions, simple endpoint-wise summation may cease to be sharp.

## 12. Mediators

Mediators require more care because different assumptions have different algebraic forms.

Finite mediator response types can still be encoded in a larger response-function carrier. Marginal experimental information about `M_a` or `Y_{a,m}` remains linear in the response-type law.

However, cross-world independence assumptions can impose factorization conditions such as products of probabilities. These are generally polynomial rather than linear constraints. The feasible set may cease to be polyhedral and may even cease to be convex.

Therefore the correct hierarchy is:

```text
linear mediator information
    -> polyhedral sharp-bounds lane

nonlinear cross-world factorization
    -> semialgebraic/nonconvex lane
```

The second case should not be silently passed to an LP abstraction.

## 13. Continuous outcomes and copulas

For continuous potential outcomes, the unknown object is a coupling measure `\gamma` with identified or partially identified marginals. The Fréchet-Hoeffding problem becomes an infinite-dimensional analogue of the finite transportation polytope.

The same high-level objects remain:

\[
\text{marginal constraints}
\to
\Gamma
\to
Q(\gamma)
\to
\inf/\sup.
\]

If `\Gamma` is convex and `Q` is affine in the coupling measure, the convex sharpness theorem still applies abstractly.

Copula information changes the admissible coupling family. A fixed parametric copula can identify a particular dependence model. A range of copula parameters acts as a sensitivity family. Such a family need not be convex as a set of couplings, so interval filling cannot be assumed from endpoint attainment alone.

This gives a clean boundary between the finite LP theory and the future measure-theoretic theory.

## 14. A proposed formal hierarchy

The reusable formal objects should be layered as follows.

### Layer A. Convex partial identification

```text
FeasibleModel
Query
ValidLowerBound
ValidUpperBound
LowerWitness
UpperWitness
ConvexFeasible
AffineQuery
SharpIdentifiedInterval
```

This layer does not know anything about causality or LPs.

### Layer B. Finite polyhedral identification

```text
FiniteResponseType
ProbabilityMass
LinearEqualityConstraint
LinearInequalityConstraint
LinearCausalQuery
PrimalFeasibleWitness
DualBoundCertificate
```

This layer proves that the feasible family is convex and the query affine, then invokes Layer A.

### Layer C. Causal compilation

```text
PotentialOutcomeQuery
PartialCausalOrder
StructuralResponseType
ObservedMarginalConstraint
InterventionalMarginalConstraint
CovariateConstraint
MediatorConstraint
SensitivityConstraint
```

This layer proves that a causal problem is faithfully represented by Layer B.

### Layer D. Exact certificate replay

External solvers may discover candidate rational primal and dual solutions. The trusted proof boundary should remain:

```text
untrusted solver search
    -> rational witness/certificate
    -> Lean replay
    -> theorem.
```

The existing `D5/S0/Certificates/RationalFarkas` module is a natural target for the dual side.

## 15. The next formal theorems

The first generic theorem should state:

> If a feasible family of real-valued masses is closed under convex blending, the query respects the same blend, every feasible model has query value in `[L,U]`, and feasible witnesses attain `L` and `U`, then a target is feasible exactly when it lies in `[L,U]`.

The second should state the information-order rule:

> If every model satisfying stronger assumptions also satisfies weaker assumptions, every valid lower bound for the weaker family remains a lower bound for the stronger family, and every valid upper bound remains an upper bound. With optimal endpoint witnesses, the stronger identified interval is nested inside the weaker one.

The third should package primal-dual endpoint optimality:

> A replayable universal certificate for `Q>=L`, together with a feasible model satisfying `Q=L`, proves that `L` is the exact lower endpoint. The analogous statement holds for `U`.

These results are the logical bridge from the current four-cell examples to arbitrary finite causal LPs.

## 16. Research claim boundary

The theory above supports a broad architecture but does not by itself prove that every causal problem yields a convex polytope.

In particular:

- arbitrary partial causal diagrams require a correctness theorem for the compiler from structural semantics to constraints;
- latent-variable restrictions may require careful response-function parameterization;
- mediator cross-world independence can be nonlinear;
- a restricted copula family can be nonconvex;
- continuous outcomes require probability measures and existence results for extrema;
- estimated constraints introduce statistical uncertainty distinct from identification uncertainty.

The formal program should preserve these boundaries rather than hide them behind a single optimization interface.

## 17. Research direction

The strongest reusable target is therefore not one more isolated closed-form bound. It is a certified partial-identification compiler whose output consists of:

```text
1. an explicit feasible-model semantics;
2. a finite rational constraint system when the problem is polyhedral;
3. a linear causal query;
4. a primal endpoint witness;
5. a replayable rational dual certificate;
6. a convexity/affinity bridge;
7. a Lean theorem stating the exact sharp identified interval.
```

This would turn causal sharp bounds from solver output into machine-checkable mathematical objects.
