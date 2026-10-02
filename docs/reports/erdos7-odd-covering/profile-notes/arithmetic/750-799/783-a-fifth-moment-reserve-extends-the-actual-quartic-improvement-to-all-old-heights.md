# A fifth-moment reserve extends the actual quartic improvement to all old heights

For the explicitly labelled family below, one change to an actual kernel strictly decreases the physical and survivor-restricted complete fourth-query suprema, uniformly over every finite old and current prime-power height. It preserves the old marginal, all actual bad mass, the survivor mass, and the global conditional density cap. The allowed complete query domain includes every numerical divisor of the full period, with independent phases.

The new estimate keeps the missing quartic terms involving one pure-current test and three other tests. Those terms control a cubic recipient load; a complete fifth moment then pays the remaining tail. This removes the twelve-old-slot restriction in [781](781-an-actual-mass-preserving-redistribution-lowers-the-complete-fourth-query-bound.md). The construction extends the actual family of [17, FI2](../../001-064/17-higher-moments-retain-the-full-old-inventory-in-a-law-changing-perturbation.md), whose earlier improvement was for the square objective.

This is ordinary mathematics with exact checks, not a new Lean verification. The original forbidden residues are specified hypotheses, not arbitrary choices. The result supplies no uniform gain for the different source in [779](779-the-original-capped-source-lowers-the-general-eight-prime-tail-cutoff.md), and does not settle unrestricted Erdős #7.

## One actual source with all numerical labels

Let

\[
M=3^{N_3+2}5^{N_5+1}7^{N_7+1}11^{A_{11}}13^{A_{13}},
\qquad N_3,N_5,N_7\ge0,\quad A_{11},A_{13}\ge1.
\]

Use the pinned PG1 old law on the 75 actual survivors modulo 315 and the eleven original PG1 forbidden phases. Its masses at 314 and 2 are respectively

\[
\mu_*={16622259\over1000000007},\qquad
\mu_2={13119398\over1000000007}.
\]

Add the pure originals 0 modulo 11 and 13. Complete to one original for every nonunit divisor of M exactly as in FI2: a remaining label divisible by 11 or 13 receives phase zero; otherwise it receives the PG1 phase at its gcd with 315. Each added class lies in an already forbidden class. The supported old probability nu is PG1 times independent uniform extra 3/5/7 digits and uniform nonzero first 11/13 digits with uniform suffixes.

At 17 keep the exact CS2 pure and eleven low-cofactor originals of 781 at every depth up to H, for any finite H>=1. Every remaining numerical label d*17^e receives phase zero and is already contained in the pure forbidden root. Thus all numerical divisors greater than one of M*17^H occur exactly once as original labels; complete tests retain that entire inventory. The actual current bad masks still depend only on the low 315 point.

Use the same normalized BB kernel q0, with delta=7/15. On every row in E={x=314 mod315}, transfer

\[
t=2^{-37}
\]

from the globally clean roots R_H, equally, to the whole good root 2. Here R_1={12,13,14,15,16} and R_H={12,13,14,16} for H>=2. Call the result qt. The source and feasibility facts from 781 apply separately on every row of E. In particular t<41/952 and t/4<1/17; the transfer stays within the common cap, changes only survivor points, and preserves every bad atom. Both laws have the same survivor mass rho>=|R_H|/17.

For a full independent-phase query T let L_T be its complete numerical-divisor load. Let V4(q) be max_T integral L_T^4 against the physical law nu*q; let W4(q) be the analogous unnormalized maximum after restricting to actual survivors. Then

\[
\begin{split}
V_4(q_t)&\le V_4(q_0)-\epsilon,\\
W_4(q_t)&\le W_4(q_0)-\epsilon,\\
\epsilon&={3\mu_*t\over2}
={49866777\over274877908868145348608}>0.
\end{split}
\tag{1}
\]

The normalized supported fourth-query bound therefore decreases by at least epsilon/rho. The gain is independent of every displayed finite height.

## Complete old-height moments

Let G_p be independent geometric variables with Pr(G_p>=j)=p^-j. For p=11,13 also let B_p have probability 1/(p-1), independently. Conditional on any fixed low 315 point, with the current coordinate uniform in a fixed first root, every complete query moment of order k is bounded by

\[
Y=\left[
(3+G_3)(2+G_5)(2+G_7)
(1+B_{11}(1+G_{11}))(1+B_{13}(1+G_{13}))(2+G_{17})
\right],\qquad K_k=\mathbb E[Y^k].
\tag{2}
\]

Expand the kth power into ordered numerical-label tuples. Compatible prefixes intersect at maximum depth and incompatible prefixes have zero mass. The conditional prefix caps factor over the independent suffix coordinates. The geometric comparison bounds their sum with every full exponent vector still present. Enlarging finite suffix inventories adds nonnegative terms. Neither the forbidden phases nor the actual law are replaced by the comparison variables.

The needed exact values are

\[
K_4={1516272071872640407789\over28665446400000},\qquad
K_5={2490869562060881363619599867\over104367705292800000}.
\tag{3}
\]

The verification also reproduces FI3's second and third moments. All geometric tails are evaluated as rational sums, rather than truncated at a physical height.

## A cubic missing-term reserve in the quartic expansion

Fix any complete query T. Keep all its old phases, separately at each current exponent. As in 781, move all positive-current query prefixes to one nested path inside a globally clean root. The resulting single legal query simultaneously attains the tuple cap upper value U(T) for the physical law and U_S(T) for the killed law. The zero-current tuple uses the unchanged old fourth power, and after killing uses its actual surviving-row multiplier. No separate optimization of tuple phases is used.

Let P be T's pure17 test and let z be its first root. If z is outside R_H, the same fifteen pure/unit terms as in 781 give one of the gaps

\[
15\mu_2\,{14\over187},\qquad {15\over17},\qquad {15\over289}.
\tag{4}
\]

The extra old coordinates do not change their masses. The positive perturbation is at most mu_* t K4 by (2). Exact arithmetic gives G>mu_* t K4+epsilon for each gap in (4), so (1) holds for all these queries.

Suppose instead z is clean. Average from now on over nu conditioned on E and the uniform current root2. Let A be the old-only query load, let Z be the sum of its positive-current labels starting in root2, and put X=A+Z. Thus A>=1 and X>=A; every such positive label differs from P and is disjoint from it.

Consider the ordered quartic terms containing exactly one P and three labels chosen from the old-only and root2 inventories, with at least one root2 label. There are four choices for the position of P. Every such actual intersection is empty. Its cap term in U(T) is at least c_H(x)/17 times the corresponding triple intersection probability conditional on root2: a nonempty triple at positive maximum depth e has root-conditional probability 17^(1-e), while its cap is c_H(x)17^-e. For incompatible triples the conditional probability is zero. Since c_H>=1, these DISTINCT quartic terms supply a total cap deficit at least

\[
{4\mu_*\over17}\,\mathbb E(X^3-A^3).
\tag{5}
\]

This counts repeated old labels as ordered slots, preserves every full numerical label, and uses the same fixed T throughout. None of the counted terms is an old-only term. The physical and killed caps coincide on their positive-current maximum-depth terms.

At donor root z, the pure17 test contributes one everywhere. After cancellation of the unchanged old-only term, its fourth-power increment is at least (A+1)^4-A^4>=15. There are at most five equal donor roots, so subtraction decreases the integral by at least 3 mu_* t. All other donor contributions after this cancellation are nonnegative.

The positive recipient increment is mu_* t E(X^4-A^4). For any 0<=A<=X,

\[
X^4-A^4\le {4X\over3}(X^3-A^3).
\]

Consequently, using the threshold X=3/(17t),

\[
t(X^4-A^4)-{4\over17}(X^3-A^3)
\le tX^4\mathbf1_{X>3/(17t)}
\le {17\over3}t^2X^5.
\tag{6}
\]

For the selected t, the exact complete moment gives

\[
{17\over3}tK_5<{3\over2}.
\tag{7}
\]

Combine the donor decrease, (5), (6), and (7). Every perturbed query is at most its own attainable baseline cap minus 3 mu_* t/2. Taking maxima establishes (1). This argument uses no pointwise bound on the old load and no alignment of the depth-one query prefixes.

## Actual families with no globally clean root

The fourth-query improvement survives a specified rare change to the actual forbidden masks. Keep nu, all pure17 originals and the full numerical inventory. Change mixed phases only on old event F, in the sense that the resulting current bad masks equal the base masks outside F. Write q=nu(F). Use the new family's actual BB kernel q0_tilde and apply the same transfer only on E minus F to obtain qt_tilde. The pair still have equal old marginals, actual bad mass and survivor mass rho_tilde>=4(1-q)/17.

All four base and modified physical kernels, and their killed restrictions, have density at most 2 relative to current Haar. Each new-versus-base difference vanishes outside F and has absolute density at most 2. Under nu times current Haar, replace the last factor of (2) by 1+G17. Its complete eighth moment is

\[
K_8^{\rm Haar}=
{898948498268780406789760549378803375337181\over60867245726760960000000}.
\]

Cauchy--Schwarz bounds each fourth-cost change by 2 sqrt(q K8_Haar), uniformly over every full query. Comparing both the baseline and perturbed maxima with their base-family versions gives a remaining improvement of at least epsilon-4 sqrt(q K8_Haar). The exact inequality

\[
64K_8^{\rm Haar}<3^{98}\epsilon^2
\tag{8}
\]

therefore proves a positive gain at least epsilon/2 whenever q<=3^-98.

To realize this condition with no globally clean first17 root, take N3>=98, Q=3^100 and F={x=314 mod Q}. Then q<=3^-98. At depth one replace only the five originally redundant labels with old cofactors Q,5Q,7Q,35Q,11Q by old phase314 and respective17 roots12,13,14,15,16. These are distinct existing numerical labels, each old cylinder lies in F, and each has positive nu-mass. The removed zero phases lay in the pure forbidden root. Root0 remains pure forbidden, every spoke1 through11 is bad on the positive low row2, and the five new classes affect all other roots on positive old mass. No root is globally clean. Equation (8) applies for every permitted higher finite height; it does not assume that the modified family's cap is attained by a clean query.

## Verification and continuation scope

The standalone [consumer](../../../frontier/cover-geometry/pg1-quartic-gain/fullheight_quartic_gain.py) and [retained exact result](../../../frontier/cover-geometry/pg1-quartic-gain/fullheight_quartic_gain.json) evaluate (2), (3), (7), and (8), the source capacities and all exceptional reserves using rational arithmetic. A second geometric-moment calculation and finite complete-label examples check the cubic deficit mechanism. These checks support the implementation; the proof above supplies the arbitrary-height and arbitrary-query quantifiers.

This gives a complete order-four interface to the [quartic continuation of734](../700-749/734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md) on this specified six-prime family: every finite future old cofactor can be included before construction, and Holder bounds four different query loads by the same improved fourth maximum. It does not replace the first six primes with an arbitrary head source or remove the stated original phase conditions. The no-clean-root variant has the same mass, so its strictly smaller fourth bound improves any otherwise applicable mass-minus-tail estimate without combining different source laws.

Run from the repository root:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/pg1-quartic-gain/fullheight_quartic_gain.py
```
