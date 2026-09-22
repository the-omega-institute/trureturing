[Index](../../marked_head_profile.md) · [Exact continuation state](411-exact-continuation-state-is-a-joint-residue-histogram.md) · [Task extension](436-self-observation-refines-a-count-sufficient-clique-state.md) · [Actual lifting](439-actual-residual-lifting-and-exact-free-coordinate-cost.md)

# Joint test profiles as composable boundaries

A scalar upper bound on a complete layout game is a sufficient answer
to one maximization task. It need not be a state on which subsequent
operations descend. An exact mod-35 example below shows this failure
even when the coarse marginal is also retained. For the finite lifting
task of report 439, the supported cost profile gives a precise boundary
that can be contracted through successive actual projection fibres.

These are repo-derived ordinary deductions using finite minimax and
closed-convex separation. No new Lean certification or literature
priority is claimed. The existing task-completion interfaces are reused
as described in report 436, without adding binding declarations.

## 1. A scalar game value fails under the same subsequent mixture

On Z/35, keep all independent phases for the original numerical labels
`1,5,7,35`. For a probability nu write

    Gamma_35(nu) = max_(a5,a7,a35)
        E_nu [1 + 1_(x=a5 mod5) + 1_(x=a7 mod7)
                + 1_(x=a35 mod35)]^2.

Take nu0=delta_0 and nu5=delta_5. Both project to delta_0 modulo five,
and both have Gamma_35=16, attained by centering every test at their
support point. They are probabilities on the same actual full carrier;
there are no original excluded classes in this control.

Apply the same fixed operation to either law:

    A(nu) = (nu + delta_0)/2.

Then

    Gamma_35(A(nu0)) = 16,
    Gamma_35(A(nu5)) = 10.                                  (JB1)

Indeed, the modulus-five indicator can hit both zero and five. Each
of the modulus-seven and modulus-35 indicators can hit at most one.
Putting both at the same point gives squared loads 16 and 4, hence
average ten. Putting them at different points gives nine at each.
Missing either point, or choosing a modulus-five phase other than
zero, cannot increase the load. This proves the second equality.

Thus the kernel of the summary `(coarse marginal, Gamma)` is not
preserved by A. No update rule on that summary can reproduce Gamma
after every such operation. The second input law is fixed; no phases
or probability supports are chosen after observing a test.

This is a counterexample about a task interface, not a source-law
counterexample or a realization of a hypothetical minimum odd cover.
In particular it does not refute the exact free-coordinate completion
formula of report 439, whose particular extension operation has a
scalar formula under its additional freedom and coprimality hypotheses.

## 2. The exact boundary for the fixed-marginal lifting task

Let R be a finite nonempty allowed fine support, let pi:R->S be a
surjection, and let Lambda be the finite complete family of declared
fine layouts. The labels and their phases retain their original
arithmetic meaning. Put

    c(x) = (L_lambda(x)^2)_(lambda in Lambda),
    P_s = conv {c(x): x in R, pi(x)=s}.

A conditional probability in the fibre R_s realizes exactly one
vector in P_s, and every vector in P_s is realizable. If the task asks
which coordinatewise upper budgets are attainable, its exact boundary is

    U_s = P_s + R_(nonnegative)^Lambda.                        (JB2)

Thus b belongs to U_s precisely when some SINGLE conditional law
has every layout moment at most the corresponding coordinate of b.
It is not permissible to choose a different law for each coordinate.

For one probability theta on the whole layout family, define

    f_theta(x) = sum_lambda theta(lambda)c_lambda(x),
    K_s(theta) = min_(x in R_s) f_theta(x).

Finite minimax, as already established in report 439, gives for a
fixed coarse probability mu

    min_(nu on R, pi_*nu=mu) Gamma(nu)
      = max_theta sum_s mu(s) K_s(theta).                     (JB3)

Theta is shared by every fibre. Its occurrence before the inner
minimum is a dual formula for the common-law problem, not permission
to implement a different primal probability after learning the layout.

For nonnegative layout prices, K_s identifies U_s exactly. One
direction follows from minimizing a linear functional over a convex
hull and then its nonnegative upper closure. Conversely, if two such
closed convex upper sets differ, strictly separate a point of one from
the other. The separating functional pointing toward a lower bound
must have nonnegative coefficients, since the set is upward closed.
It is nonzero, so normalize its coefficient sum to one. The resulting
theta distinguishes the two K profiles. The sets are closed because
P_s is compact and the nonnegative orthant is closed.

Nonnegative prices need not reconstruct P_s itself. For example,
`{(1,1)}` and `conv{(1,1),(2,2)}` have the same upper closure and the
same K on nonnegative prices. All signed linear directions would
recover the full convex set. These abstract vectors illustrate the
scope of the convex statement; they are not claimed as an E7 source.

There are three different task scopes. For every coarse mu and every
theta, the fibrewise profile can be recovered by taking mu=delta_s.
For one fixed mu only the aggregate `sum_s mu(s)K_s(theta)` is needed.
If only its minimax value is queried, the maximum of that aggregate is
an even coarser readout. A restricted family of mu, such as report
439's K_C, does not automatically permit testing individual fibres.

## 3. Contraction composes when the whole price profile is retained

For finite surjective projections R --rho--> T --pi--> S, define

    D_rho f(t) = min_(x:rho(x)=t) f(x).

Then for every real-valued terminal price f,

    D_(pi composed with rho) f = D_pi(D_rho f).               (JB4)

For each s, its fine fibre is the union of the rho-fibres indexed by
t with pi(t)=s. Minimizing over this union equals the iterated minimum.
All relevant fibres are nonempty; an extension to partial relations
can instead use positive infinity for an empty continuation set.

This is the composable boundary operator for this specified finite
task. First form f_theta using ONE shared theta, and then contract
through the actual intermediate fibres. A change of finite coordinates
transports the fibre relation and the terminal price together; the
minimum is unchanged because the indexing map is a bijection.

The mixture cannot generally be moved through the minimum:

    D_rho(sum_lambda theta(lambda)c_lambda)
      >= sum_lambda theta(lambda)D_rho(c_lambda),             (JB5)

and equality can fail. On the two support points zero and five from
section 1, the two coherent layouts centered at them have cost vectors
`(16,4)` and `(4,16)`. Their equal mixture has cost ten at either
point, whereas averaging the two separate minima gives four.
The same two-layout dual proves a minimax lower bound ten on this
two-point support. The balanced law in JB1 attains it, even against
the full independent-phase inventory.

Consequently a boundary containing only separately minimized layout
values loses the common-law constraint. This failure already occurs
on two finite points and does not require an infinite tail or an
uncomputable operation.

## 4. Static budget sufficiency is not unrestricted behavioral sufficiency

JB2--JB4 concern a fixed support relation, declared layout family,
and projection task. They do not assert that U_s alone remains
sufficient after arbitrary deletions, newly authorized record reads,
or changes to the original constraints. Such operations can distinguish
points with identical current cost vectors or change which fine
continuations remain possible.

Nor does fibre contraction make squared loads additive across code
blocks. If a layout has inherited load l_lambda and later load r_lambda,
the terminal price is `(l_lambda+r_lambda)^2`, including the cross term
`2*l_lambda*r_lambda`. Contracting that full price is legitimate;
adding two independently summarized squared-load costs discards the
cross term. A dynamic block interface must retain enough inherited
load and common-label information to evaluate it.

[Report 411](411-exact-continuation-state-is-a-joint-residue-histogram.md)
retains the joint residue histogram needed for exact future deletions.
[Report 416](416-exact-independent-layout-tree-separation-and-actual-laws.md)
retains inherited loads and remaining numerical labels in its exact
layout DP. Report 436 supplies the archive distinction and cites
`controlled_completion_is_least_stable_refinement`: dynamic sufficiency
requires closure under all declared action words, not just agreement
of today's outputs. These are direct reuse boundaries, not new Lean
wrappers or a claim that a generic finite profile solves unrestricted E7.

For E7 the remaining problem is a bound on the actual profiles in JB3,
using the original arithmetic incidence and the correct inventory
budget. Report 439's full-inventory floor still applies. Compressing
to an interface cannot supply the missing bound by itself.

The [exact arithmetic control](../../frontier/cover-geometry/joint_test_boundary.py)
checks all 1,225 original layouts for each of the four before/after
laws, reconstructs the maximizing phases, and checks the two-layout
dual and the strict gap in JB5. Run:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/joint_test_boundary.py

The general statements are supported by the ordinary proofs above;
the finite control does not replace them or establish an odd covering.

## 5. Internal selectors must preserve observable successors

Let a controller select an action pi(x), with joint update
`F(x)=T_(pi(x))(x)`. If each action descends through a summary sigma,
and the selected action can be recovered from sigma, then F also
descends. Recovering the action label is sufficient, not necessary:
different actions may have the same observable effect. The exact
condition, taking the summary carrier to be the realized image of
sigma, is

    sigma(x)=sigma(y) implies sigma(F(x))=sigma(F(y)).

This is the existing
[`dynamics_descends_iff`](../../../../../D5/S0/Rewriting/Quotients/DynamicsDescent.lean)
criterion. If recording the action itself is part of the task, that
record must be included in the successor summary.

For a random selector with transition law
`Q_x=sum_a p_a(x) delta_(T_a(x))`, the corresponding condition is that
`sigma_*Q_x` is constant on every sigma fibre. Probabilities of actions
with the same summarized successor may be aggregated. The existing
[`strong_lumpability_descent_tfae`](../../../../../D5/S3/Observer/ProbabilisticClosure/StrongLumpabilityDescent.lean)
and
[`stochastic_descent_equivalence`](../../../../../D5/S3/Estimation/DecisionRisk/StochasticDescentEquivalence.lean)
supply this stochastic descent interface. These are reuse references,
not newly compiled specializations or new Lean declarations.

For the actual lifting problem, choose a coarse law mu and a conditional
kernel kappa_(R,mu)(s,.) supported on R_s. It may depend on the fixed
source, its original constraints, and mu. The single resulting law is
`nu(x)=mu(s) kappa_(R,mu)(s,x)` for x in R_s. Every declared layout must
be tested against this same nu; the kernel cannot be replaced after
learning the tested layout. Selecting a best response to a common
dual mixture theta in JB3 is a minimax argument for existence of a
common primal law, not a recipe for using different primal laws on
different tests.

Fixed deletion is linear on unnormalized mass. Conditioning on the
survivors additionally divides by their mass, needs a positive
denominator, and may change the coarse marginal. Neither selector
closure nor linearity of the unnormalized deletion supplies the
missing quantitative survivor bound.
