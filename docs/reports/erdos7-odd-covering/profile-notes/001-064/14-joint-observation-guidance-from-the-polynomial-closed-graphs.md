[Index](../../marked_head_profile.md) · [Previous](13-probability-capped-deletion-and-a-joint-observation-beyond-this-boundary.md) · [Next](15-a-clean-cylinder-makes-all-current-prime-pair-caps-exact.md)

<a id="joint-observation-guidance-from-the-polynomial-closed-graphs"></a>
### Joint-observation guidance from the polynomial closed graphs

[RRO section43 at dev34c829dfb0](https://github.com/the-omega-institute/trureturing/blob/34c829dfb0791b4a40bbf98c232db6f2d49efba4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#43-增补乘法满闭图与有限多项式联合闭图的定向判据)
gives a concrete boundary for assembling observations. Under its stated
phase assumptions, theorem43.11 characterizes joint polynomial limits by
a common phase preimage and one error vector satisfying every required
strict sign. Theorem43.13 exhibits two full marginal nonlinear graphs
whose joint circuit still obeys the relation \(a(b+1)=ab+a\); even all
linear phase identities can leave an impossible combination of boundary
directions. The ordinary polynomial equidistribution input is Weyl's
theorem, in the scalar form stated in
[Tao's Corollary6](https://terrytao.wordpress.com/2010/03/28/254b-notes-1-equidistribution-of-polynomial-sequences-in-torii/).

For the covering problem this motivates retaining the actual joint
configuration before maximizing, as in (ZD2), and retaining one deletion
event and probability when combining costs. Separate maxima remain valid
upper bounds but need not have a simultaneous actual maximizer. The
Zeckendorf phase and directional-cone theorems do not themselves provide
a CRT survivor probability, a charge estimate, or a uniform positive
residual for arbitrary prime support. No quantitative #7 bridge or Lean
formalization of the new RRO section is claimed here.

<a id="exact-weighted-geometry-at-the-first-nonzero-auxiliary-depth"></a>
### Exact weighted geometry at the first nonzero auxiliary depth

Keep the PG1 probability, the actual higher357 survival event \(F\), and
the original3/original9 roots from (ZD1)--(ZD4). At auxiliary depth
\(z=(1,0,0)\), retain the old load in the form

\[
 A=1+\mathbf1_{C(i,3)}+\mathbf1_{C(j,9)}
   +\mathbf1_{C_5}+\mathbf1_{C_{15}}
   +2\mathbf1_{C_{45}}+\mathbf1_{C_{\mathrm{higher}9}}.       \tag{WD1}
\]

The original mod9 residue \(j\) stays fixed. The higher9 cylinder is
independently free. The six seven-label cofactors \((1,3,5,9,15,45)\)
have weights \((1,1,1,2,1,2)\) and independent seven digits.
Equal-cofactor free cylinders can be pooled for this pure square maximum:
for \(r\ge0\), convexity gives

\[
 (H+\mathbf1_C+r\mathbf1_D)^2
 \le\frac{(H+(1+r)\mathbf1_C)^2
          +r(H+(1+r)\mathbf1_D)^2}{1+r}.                    \tag{WD2}
\]

Each term on the right is a permitted pooled choice; conversely the
pooled choice is realized by \(C=D\). Thus the maxima agree. This
argument only pools free labels. It neither identifies fixed original9
with higher9 nor applies to an arbitrary signed score.

The exact weighted optimizer checks 3972 old-load vectors for each of
the ten root pairs, hence 39720 rooted layouts. It retains all 3024
labeled subset states, empty classes and digit zero, with maximum load
15 or16 according to root compatibility. It strictly improves the
inherited depth100 square bound at every root. Let \(h^{(1)}_{ij}\) be
the new maximum and \(H_{ij}(1,0,0)\) the inherited minimum of the
pure7 and fixed-old estimates. Since this depth has probability
\(16/105\), replace

\[
 U''_{ij}=U'_{ij}-s_{ij},\qquad
 s_{ij}=\frac{16}{105}
          \bigl(H_{ij}(1,0,0)-h^{(1)}_{ij}\bigr)>0.          \tag{WD3}
\]

Keep the exact zero-depth value, the other268 inside-box observations,
the complete outside coefficients and the root-specific deletion costs.
The same actual source law consequently satisfies

\[
 \boxed{\displaystyle
 \Gamma\le
 \frac{491316187201313799169931}{14604022456869186140625}
 <33.642525.}                                               \tag{WD4}
\]

The worst roots remain \((2,2)\). This is an improvement of
\(4255298304/177996524699\) over the source bound in (ZD1).

For the common-source continuation (JF1)--(JF7), every one of the10000
root combinations decreases its unconditional source cost by at least

\[
 \eta=\frac{1403}{630}\min_{i,j}s_{ij}
      =\frac{65098504112}{11025000077175}>0.                 \tag{WD5}
\]

Subtract \(\eta\) from both \(\delta\) and \(B_*\) in (JF6).
The actual \(Q\), its interval, and the crossing are unchanged.
Checking the same two endpoints and crossing yields

\[
 \boxed{\displaystyle
 \Gamma_{13}\le
 \frac{3452717513949582813397269113208403}
      {23265022838471110091964891311550}
 <148.408087.}                                              \tag{WD6}
\]

`verify_pg1_exact_depth100.py` and
`pg1_exact_depth100_certificate.json` retain these exact comparisons.
`pg1_weighted_score_oracle.py` and its C++ implementation support signed,
nonmonotone score tables in the weighted total load. The verifier
independently reconstructs every old domain and subset load from raw
residues, checks each rooted winner by all \(7^6\) digit assignments,
and evaluates its literal75-point realization. Signed comparisons
include a case where independent digits strictly beat a common digit,
a necessary digit-zero choice, and overflow/domain rejection checks.
The common-digit maximum happens to agree for (WD1)'s square; it is
not imposed on other objectives.

The sufficient target35 mass-loss budget also increases to
\(2478074848638464468993/117162648257638532062500\), with integer
lost-weight limit21150724 at denominator1000000007. No new complete
carrier count is inferred from this enlarged scalar budget. The
arbitrary-prime continuation remains open; these are ordinary exact
certificates, with no new Lean declaration.

<a id="joint-low-and-high-deletion-enlarges-the-transported-support-domain"></a>
### Joint low and high deletion enlarges the transported support domain

Let \(\mu\) be the same PG1 low probability, \(\lambda\) its uniform
lift to arbitrary finite3/5/7 heights, and \(F\) any admissible actual
higher357 survivor event. The unchanged bound is
\(\lambda(F)\ge q_0=25428074957/48000000336\). Fix a low loss set
\(S\), put \(t=\mu(S)\), and condition on \(A=F\cap S^c\).
Then \(\rho=\lambda(A)\ge q_0-t\). For each original test root pair,
write \(b_{ij}=1+\mathbf1_{C(i,3)}+\mathbf1_{C(j,9)}\) and
\(f_{ij}=35-b_{ij}^2>0\). The complete grouped-deletion bound \(R\)
applies to any nonnegative, possibly unnormalized low weight. Using
the exact-zero-depth source bounds \(U'_{ij}\) gives

\[
 \boxed{\displaystyle
 \rho\bigl(\mathbb E[L^2\mid A]-35\bigr)
 \le U'_{ij}-35
       +\mu(f_{ij}\mathbf1_S)
       +R(f_{ij}\mu\mathbf1_{S^c}).}                        \tag{JT1}
\]

Indeed, the removed set is the disjoint union
\(S\sqcup(S^c\cap F^c)\). Subtract its actual square energy from
\(\lambda(L^2)\), bound that energy below by \(b_{ij}^2\), and apply
the weighted grouped-deletion bound only on \(S^c\). The intersection
\(S\cap F^c\) is charged once. Every term uses the same physical
law and event. All higher deletion coefficients and the full auxiliary
square tail remain present. Empty test-root branches are dominated by
the same nonempty-root extensions as in the source estimate.

Four fixed low losses pass (JT1) strictly at every one of the ten roots:

| Lost source points \(S\) | Lost weight numerator | Retained support | Maximum right side of (JT1) |
| --- | ---: | ---: | ---: |
| \(88,208,313\) | 24940311 | 72 | \(<-0.21149\) |
| \(43,88,253\) | 25521977 | 72 | \(<-0.19666\) |
| \(2,128\) | 25865521 | 73 | \(<-0.19738\) |
| \(38,143\) | 26142429 | 73 | \(<-0.14937\) |

The weight denominator is1000000007. All four lost-weight numerators
exceed both scalar limits20778236 and21150724, while each lost mass
\(t\) is below \(q_0\). Therefore each
conditioned law has positive survival and \(\Gamma\le35\).
One original target family is
\((3,0),(5,0),(7,0),(9,4),(15,11),(21,5),(35,18),(45,37),
(63,50),(105,94),(315,79)\); its low carrier has76 points and contains
the mapped72-point support. The certificate specifies all four actual
families, their full coordinate maps, and exact rational criteria.

More generally, let \(T\) be a permitted CRT coordinate permutation
and let a target carrier contain \(T(\operatorname{supp}\mu\setminus S)\).
Transport \(\mu|_{S^c}/(1-t)\) to that carrier. The low maps preserve
the mod3 parent of each mod9 child. Extending them by leaving subsequent
prime-adic digits unchanged preserves every original residue class at
every height. Thus any target high event pulls back to an admissible
source \(F\), with target high survival at least
\((q_0-t)/(1-t)>0\), and (JT1) still applies. The target need only
contain the retained support, not the entire initial target carrier.
Source and target forbidden families are never merged.

The four supports have48 distinct old-coordinate images. Reconstructing
all34160 same-shape target orbits and checking inclusion gives701 orbits,
21 inclusion-minimal orbits, and4892 normalized digit-union states.
For these701 targets, exact matching over12 old maps and720 seven-digit
permutations determines their overlap with the previously published
scalar threshold19730787. The disjoint addition is242 orbits,9 minimal
orbits, and1782 states. Thus the PG1-shape union is1414 orbits,62 minimal
orbits, and8855 states. Including the unchanged other-shape results, the
combined supported \(\Gamma\le35\) region is

\[
 \boxed{2643\text{ carrier orbits},\quad
        72\text{ minimal orbits},\quad
        16153\text{ normalized states}.}                  \tag{JT2}
\]

There remain56894 of the56966 minimal orbits outside this certified
region. `verify_pg1_joint_carrier_transfer.py` and
`pg1_joint_carrier_transfer_certificate.json` check all40 criteria,
literal transport, support containment, minimality, and exact old overlap.
The inherited complete weighted count is hash-bound; matching is newly
computed only for included targets. The enlarged scalar budgets are not
silently substituted into that old count. An independent coordinate
enumeration and bipartite matching calculation agrees on the covered
sets. These are all-height moment bounds on the specified region, not
noncoverage for arbitrary prime support or a resolution of #7.

<a id="arithmetic-admission-requires-a-common-numerical-witness"></a>
### Arithmetic admission requires a common numerical witness

[RRO section44 at devc33851543c](https://github.com/the-omega-institute/trureturing/blob/c33851543ce6ef8cc2e821a1d4fda7a49159b4f5/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#44-arithmetic-admission-order-and-euclidean-division-in-zeckendorf-observation)
sharpens the preceding guidance. Under its phase assumptions44.1,
theorem44.5 gives a full closed graph for variable-divisor Euclidean
division. Theorem44.11 exhibits two locally dense success constraints
whose conjunction is empty: one requires \(r<b\), the other \(b<r\).
Each separate finite-prefix image is full. Requiring one common
numerical witness before projecting detects the incompatibility.

For a literally fixed divisor \(c\), theorem44.8 retains the remainder,
the equation \(H(x)=cH(y)+[r\phi]\), and compatible approach sides.
Theorems44.9 and44.13 show, under those assumptions, why a finite
Zeckendorf prefix cannot serve as the exact residue observation needed
for #7: each completed dividend admits every remainder, and for
\(c\ge2\) no nonconstant finite-discrete output observer descends
continuously. The existing CRT observations retain those distinctions.
This is an obstruction to replacing them with a fixed digit prefix;
it is not an obstruction to exact finite integer conversion.

The dev increment contains theoretical text and digestion atoms, with
no new D5 theorem. Its topological closures and equidistribution along
one polynomial curve supply neither the finite CRT probability used
here nor a quantitative positive residual. In (WD1)--(WD6) and
(JT1)--(JT2), the useful implementation of the common-witness principle
is to keep the actual labeled layout and one source event throughout
the calculation. A uniform extension over the remaining carriers and
arbitrary later primes is still required.

<a id="complete-integer-hinges-on-the-unchanged-pg1-survivor-law"></a>
### Complete integer hinges on the unchanged PG1 survivor law

Keep the PG1 probability, the actual higher357 event \(F\), and its
positive lower bound \(q_0=25428074957/48000000336\). For a complete
original test load \(L\), let \(H_t=\sup_L\mathbb E[(L-t)_+]\) on
this one conditional law. The following simultaneous bounds improve
the previously supplied interpolation or threshold4/6 estimates:

| Threshold \(t\) | Exact upper bound for \(H_t\) | Decimal upper bound |
| ---: | --- | ---: |
| 3 | \(10162026053915069246357/4868007485623062046875\) | 2.087512414 |
| 4 | \(1433737384346892410897/973601497124612409375\) | 1.472612141 |
| 6 | \(4033254968714385651877/4868007485623062046875\) | 0.828522755 |
| 7 | \(9648458629766273805119/14604022456869186140625\) | 0.660671309 |
| 8 | \(212159150814634558117/417257784481976746875\) | 0.508460618 |

The existing direct unweighted \(n=1\) cost already supplies
\(H_5\le1093534028247938362241/973601497124612409375\).
It is reused, not a new threshold5 calculation. The earlier
\(H_2\le3\), \(\mathbb E L\le5\), and square bound (WD4)
hold on this same probability.

For each of the ten fixed original3/original9 root pairs, evaluate the
convex row bound at thresholds3,7,8 on all270 auxiliary depths in
\([0,8]\times[0,5]\times[0,4]\). Threshold4/6 reuse their existing
complete arrays. Write \(h_{t,ij}(z)\) for these bounds,
\(\beta=\Pr(Z\text{ in the box})\), and \(h^*_{t,ij}(0)\) for
the exact zero-depth maximum over the actual twelve original labels.
Original-root realizations are retained before identical old loads
are deduplicated. The six seven-divisible labels have independent
digits; their maximizers need not use a common digit.

The true fixed-root hinge maximum obeys (M9C2), by its one-Lipschitz
increment bound. Thus replacing both the inside zero term and the
outside anchor in (M9C3) gives

\[
 U^{\rm new}_{t,ij}=U^{\rm old}_{t,ij}
 -\left(\Pr(Z=0)+1-\beta\right)
       \left(h_{t,ij}(0)-h^*_{t,ij}(0)\right),\qquad
 \Pr(Z=0)+1-\beta=\frac{12507116753}{27348890625}.       \tag{IH1}
\]

The other269 depth terms and the entire first-moment remainder
\(2330295100792072343/3063075771441530250000\) remain included.
Since the hinge is nonnegative and
\((1+I_3+I_9-t)_+=0\) for these thresholds,
\(H_t\le\max_{i,j}U^{\rm new}_{t,ij}/q_0\).
This comparison covers every original finite3/5/7 height. It changes
the observation bounds, not the actual probability or forbidden event.

`verify_pg1_integer_hinges.py` reconstructs the new depth arrays and
full tail, reuses hash-bound threshold4/6 data, and checks all50 rooted
zero maxima with the integer oracle. Each maximizing load is replayed
by the Python digit optimizer and literal twelve-label evaluation on
the75 source points. Selected nonlinear row values are also checked
by complete old-layout enumeration. The exact results are retained in
`pg1_integer_hinges_certificate.json`.

<a id="a-complete-scalar-schedule-consumer-and-its-remaining-gap"></a>
### A complete scalar schedule consumer and its remaining gap

Insert (IH1), the reused \(H_5\), \(H_2\le3\), mean5 and
\(G=491316187201313799169931/14604022456869186140625\)
into the existing actual-kernel criterion (SH28). Fix11/4 and13/5,
and consider all255 pairs \(1\le T_{17}\le15\),
\(1\le T_{19}\le17\). For any required integer \(j>8\), use
\(H_j\le\min(H_8,G/(4j))\); the second inequality follows from
\((L-j)_+\le L^2/(4j)\). Also \(H_1\le4\) since \(L\ge1\).

For each prime, the auxiliary multiplier distribution below \(T_p\)
is calculated exactly by divisor convolution. Its remaining mass and
first moment account for all \(N\ge T_p\), where the entire combined
cost is \(W(NL-T_p)/d_p\). No exponent or auxiliary tail is discarded.
The integer hinge expansion of (SH27) has nonnegative coefficients at
the final \(W\); its constant may be negative and is retained exactly.

The existing direct13/5 observation for \((2L-5)_+\) improves the
\(n=2\) charge term, but cannot simply be subtracted from an arbitrary
signed expansion. Put \(W_0=f_{13}a_{13}c_{13}\), the convexity
threshold. The valid decomposition is

\[
 h_W(2L)=h_{W_0}(2L)
       +\frac{W-W_0}{d_{13}}(2L-5)_+ .                 \tag{IH2}
\]

Bound the first summand by its nonnegative integer hinge coefficients,
and the second by the smaller of the direct cost and \(H_2+H_3\).
Both coefficients have the required sign because \(W\ge W_0\).
The resulting total cost has the form \(AW+B\). With
\(P=\prod_p(1+a_pc_p)\), (SH28) becomes
\(PG-1+B\le(1-A)W\). The final value must also satisfy every
prime's convexity condition.

Of these255 schedules,83 give a finite sufficient bound with the
supplied features. The best is11/4,13/5,17/8,19/8, giving

\[
 \Gamma_{19}\le
 \frac{4328407686313602732003920846923406469670769}
      {3525794087392122703309813353800433137280}
 <1227.640520.                                         \tag{IH3}
\]

Here \(P=7367153/1814400\), \(A<0.889741\), and equality holds
in (SH28). At the fixed17/7,19/8 thresholds the bound is
\(<1248.112850\). The remaining172 schedules have \(A\ge1\)
and strictly fail the affine criterion already at their smallest
convexity-admissible \(W\); increasing \(W\) cannot repair them.
None of these supplied-feature bounds is below484, the necessary
input threshold for the scalar23 continuation. This is a limitation
of this explicitly evaluated upper-bound criterion, not a lower bound
on actual moments and not an obstruction to other head laws or joint
observations.

`verify_pg1_scalar_schedule.py` and
`pg1_scalar_schedule_certificate.json` retain the complete255-case
calculation. Every successful row is checked at its final \(W\),
including the discrete feature identity, coefficient signs, full tail
and (SH28); each unsuccessful row retains its positive affine defect.
An independent rational convolution and convex-base decomposition
agrees on all255 outcomes. These are ordinary all-height estimates
and exact experimental certificates, not new Lean theorems or a
resolution of unrestricted #7.

<a id="what-the-latest-finite-quotient-and-observer-results-contribute"></a>
### What the latest finite-quotient and observer results contribute

[RRO section45 at devd3774401e0](https://github.com/the-omega-institute/trureturing/blob/d3774401e080a6c4dfc7b73b86e94d4ad782166b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#45-稠密自然数紧半环的有限商强制性与阈值超自然周期分类)
assumes a compact Hausdorff unital semiring, jointly continuous
addition and multiplication, and a dense natural core. Under these
hypotheses it classifies finite natural quotients by a threshold and
period. Their common refinement takes the maximum threshold and the
least common multiple of the periods. In particular, the CRT residue
observations used here belong to a family closed under the required
arithmetic and finite intersections. The classification does not
give a uniform finite period sufficient for arbitrary input moduli,
nor does it attach survivor probabilities to these observations.
Section45.18 explicitly distinguishes existence of suitable finite
quotients from sufficiency of an arbitrary chosen finite observation.

[The ML observation companion section44](https://github.com/the-omega-institute/trureturing/blob/d3774401e080a6c4dfc7b73b86e94d4ad782166b/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML_OBSERVATION.md#44-精度切换后的严格区间捕获与可重复双轨观察)
proves finite capture of a valid new interval for its specified binary
hidden-state model. Its proof uses the same future reports, contraction
between two exact trajectories, and a strictly positive inward margin;
output accuracy alone does not supply interval membership. For #7,
no corresponding contraction or uniform inward survivor margin is
established. The useful design requirement is to prove that an
improved observation supports the next actual update, including its
positivity premise. The new dev increment contains no D5 declaration.
Neither result supplies the missing quantitative correlation between
the current test and the actual mixed bad union.

<a id="equal-row-charges-do-not-determine-the-actual-test-update"></a>
### Equal row charges do not determine the actual test update

For a row's pure-power survivor probability \(m\), mixed bad union
\(B\), \(\alpha=m(B)\), and clipping parameter \(0\le\delta<1\),
the actual distortion kernel has density \(g-h\mathbf1_B\), where

\[
 g=\frac1{1-\min(\alpha,\delta)},\qquad
 h=\begin{cases}
 \dfrac{\min(\alpha,\delta)}{\alpha(1-\min(\alpha,\delta))},
       &\alpha>0,\\
 0,&\alpha=0.
 \end{cases}
\]

In particular, \(g-h\alpha=1\), the old marginal is preserved, and
the assigned bad mass is \((\alpha-\delta)_+/(1-\delta)\).
For every fixed test cost \(Z\), the exact update is

\[
 \mathbb E_{\rm new}Z
 =g\mathbb E_mZ-h\mathbb E_m[Z\mathbf1_B].             \tag{PO1}
\]

This is the actual kernel from
[BBMST, section2](https://arxiv.org/abs/1811.03547), with its bad-set
term retained. The following two original arithmetic families show
why that term cannot be recovered from row charges and test marginals.

Use the existing PG1 low family and source probability \(\mu\),
and put \(x_0=2\), whose weight is
\(13119398/1000000007>0\). Add the pure class \(0\bmod17\),
so \(m\) is uniform on the16 roots \(1,\ldots,16\).
Index the nine distinct low divisors

\[
 (d_1,\ldots,d_9)=(3,5,7,9,15,21,35,45,315).
\]

Family A adds one class for each original modulus \(17d_i\), with
CRT coordinates \(x\equiv2\pmod{d_i}\), \(y\equiv i\pmod{17}\).
Family B instead uses \(y\equiv i+1\pmod{17}\), keeping the same
low residues. Each family has21 distinct odd moduli greater than one
and full period5355. Because the nine high roots are distinct in each
family, every low row has the same \(\alpha(x)\), natural cap, and
assigned charge in both families. Set \(T_{17}=8\), so the (SH26)
convention is \(\delta=7/15\).

Keep one fixed complete24-label test: for every \(d\mid315\), its
old class is \(2\bmod d\), and its \(17d\) class has the same low
residue and high root10. With
\(A(x)=\sum_{d\mid315}\mathbf1_{x\equiv2\bmod d}\), its load is

\[
 L(x,y)=A(x)(1+\mathbf1_{y=10}),\qquad
 Z=L^2-A^2=3A(x)^2\mathbf1_{y=10}.                    \tag{PO2}
\]

The source probability, all pre-kernel test moments, and the complete
old test load are identical. In Family A, however, \(B_x\) uses
only roots1 through9, so \(Z\mathbf1_{B_x}=0\) in every row.
In Family B, root10 is bad exactly when \(x\equiv2\pmod{315}\),
namely at \(x=x_0\). At that point,

\[
 A(x_0)=12,\quad \alpha=\frac9{16},\quad
 g=\frac{15}{8},\quad h=\frac{14}{9},\quad
 \text{charge}=\frac{23}{128},\quad c_{\rm actual}=2=c_{17}.
\]

Applying each family's own kernel to the same test gives row square
expectations \(1557/8\) and \(1221/8\), respectively. Hence the
global fixed-test square expectations differ by exactly

\[
 42\mu(2)=\frac{551014716}{1000000007}>0.               \tag{PO3}
\]

Thus row bad densities, natural caps, charges and pre-kernel test
marginals do not determine the test update. The natural-cap deficit
also vanishes at the distinguished row. The literal height-one
good-cylinder multiplier relative to \(17^{-1}\) is \(255/128\),
not2; the latter is the all-height natural upper cap. This small
pure-coordinate relaxation is separate from the overlap distinction.

Family A also rules out a universally strictly positive bad-overlap
bound for the new-coordinate increment \(Z\) without additional
residue-coupling hypotheses. It does not make the full-square overlap
zero: the old baseline \(A^2\) still overlaps the bad union. Neither
family is asserted to cover, and this example does not refute an
overlap bound with additional global-cover assumptions. It gives no
lower bound on the supremal \(\Gamma_{19}\).

An exact joint observation sufficient for (PO1) retains both
\(\mathbb E_mZ\) and \(\mathbb E_m[Z\mathbf1_B]\), along with
\(\alpha\), on one common CRT refinement. For a fixed finite
original family and test this is a finite computation. A bound usable
in the unrestricted continuation still requires uniform control over
all allowed tests and all heights. In particular, a test-specific
deficit cannot be subtracted from a uniform supremum unless its
infimum over the stated test domain is bounded, or that same test is
retained through the entire expansion. Formula (SH26) uses the valid
universal floor \(A_eA_f\ge1\) and is unaffected by this distinction.

`verify_pg1_physical_overlap.py` reconstructs both original families,
their common test and all literal residues modulo5355. It compares
direct row integration with (PO1), checks normalization and preserved
old marginals, and records (PO2)--(PO3) in
`pg1_physical_overlap_certificate.json`. This is a counterexample to
the specified compressed observation, with an ordinary proof and
exact arithmetic replay; no new Lean declaration is claimed.

For a finite next-step optimization, the full joint observation can be
written as a pair matrix. Fix the actual forbidden family and old law
\(\nu\). For original labels \(\ell,k\), retain their old test
cylinders \(C_\ell,C_k\) and current-prime test prefixes \(u,v\),
using the full current cylinder for an exponent-zero label.
With the actual row base laws \(m_x\), define

\[
 \begin{aligned}
 K_{\ell k}(u,v)=\mathbb E_{x\sim\nu}\bigl[
 \mathbf1_{C_\ell\cap C_k}(x)\bigl(&g_xm_x([u]\cap[v])\\
                  &-h_xm_x(B_x\cap[u]\cap[v])\bigr)\bigr].
 \end{aligned}                                         \tag{PO4}
\]

This is precisely the post-kernel intersection mass, hence nonnegative.
For one fixed complete test \(\mathcal T\), summing (PO4) over its
ordered original-label pairs gives \(\mathbb E_{\rm new}L_{\mathcal T}^2\).
Compatible current-prime prefixes intersect in their deeper prefix;
incompatible prefixes have empty intersection. A finite forbidden
family therefore permits exact evaluation from its actual finite
prefix antichain and a common old CRT refinement.

For a downstream factor \(f\ge0\) and charge weight \(W\ge0\),
the finite support function to estimate is
\(\max_{\mathcal T}\{f\mathbb E_{\rm new}L_{\mathcal T}^2+
W\mathbb E_\nu\operatorname{charge}(x)\}\), with one globally
legal test retained in every row and every matrix entry. If forbidden
families are also optimized, each family's kernel, charge and test
cost must remain together. Separate maximization of the positive
part and minimization of the subtracted overlap loses that constraint.
The pair matrix is an exact representation, not a proved compression
or a newly evaluated upper bound. Physical antichain depth is
unbounded across input families. The bounds below control complete
test tails for a fixed actual family and, separately, both forbidden
and test tails when the entire old cofactor inventory is small.

<a id="latest-dev-finite-solutions-and-a-common-actual-witness"></a>
### Latest dev: finite solutions and a common actual witness

[RRO section46 at devdbbe3c44b8](https://github.com/the-omega-institute/trureturing/blob/dbbe3c44b82a352d5d1380cdd10e7b8d7ef491e7/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#46-增补有限算术解共同自然见证与有效性边界)
distinguishes the actual image of simultaneous natural solutions,
the intersection of separately attained images, and solutions of
the quotient equations. These sets need not agree. Its system
\(x^2=x,\ x=z+2\) has compatible solutions in every stated finite
arithmetic quotient, but no natural solution. Sections46.7--46.8
identify a uniform bound on the natural witnesses as a sufficient
way to recover an actual witness from those approximations.

For the present optimization, this requires every pair entry, row
charge and test load to come from one actual original-label layout.
Separately attainable extrema cannot be assembled into a fictitious
joint witness. Conversely, an explicit finite CRT construction does
supply the needed actual witness; the comb below provides one.
Section46's H10 statements concern uniformly arbitrary polynomial
systems. They give no undecidability conclusion for #7 or for checking
one finite covering family: the latter is exactly decidable on its
finite least-common-multiple period. The inspected increment after
devd3774401e0 adds305 theory lines and digestion records, with no D5
change. It supplies neither a new survivor probability nor the missing
quantitative bound for unrestricted #7.

The subsequent [RRO section47 at dev947f585f61](https://github.com/the-omega-institute/trureturing/blob/947f585f613318920f48aa35859b360649e22409/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#47-全阈值周期完成中的自然锚边界环与判定边界)
identifies its completion as natural anchors together with a closed
profinite-integer boundary, with different internal and ambient zero
and unit elements. It separates logical definability of natural anchors
from continuous finite observation and effective membership decisions.
For any fixed finite covering family, however, all congruence conditions
factor through its one full period \(M\). A surviving profinite point
projects to a residue modulo \(M\), whose integer representative in
\([0,M-1]\) survives the same family. This finite CRT lifting has no
natural-anchor obstruction. Section47.10 adopts a published decision
theorem for the common first-order theory of all finite residue rings;
it does not supply a quantitative bound for the varying original-label
inventories here. This later increment adds407 theory lines and45 new
atom/residual pairs, with no D5 change or new #7 probability estimate.

There is an exact fixed-cardinality connection to the decision theorem
adopted in section47.10. In the language of rings put
\(D(u,v)\iff\exists t\ (v=ut)\), and let \(\Phi_N\) say

\[
 \exists u,d_1,\ldots,d_N,a_1,\ldots,a_N\quad
 2u=1\ \land\ \bigwedge_i\neg D(d_i,1)
 \ \land\ \bigwedge_{i<j}\neg(D(d_i,d_j)\land D(d_j,d_i))
 \ \land\ \forall x\ \bigvee_i D(d_i,x-a_i).
\]

For each fixed \(N\ge1\), some \(\mathbb Z/m\mathbb Z\),
\(m>1\), satisfies \(\Phi_N\) if and only if there exists an
\(N\)-class distinct odd-modulus cover. Forward, take integer
representatives and \(n_i=\gcd(d_i,m)\). The unit condition makes
\(m\) odd; proper, pairwise different principal ideals give distinct
odd \(n_i>1\). Ideal membership is exactly congruence modulo
\(n_i\), so the last clause covers every integer. Reverse, use
\(m=\operatorname{lcm}(n_1,\ldots,n_N)\) and \(d_i=n_i\)
as ring elements. Thus, conditional on the external common-theory
decision theorem adopted there, applying it to \(\neg\Phi_N\)
decides existence at that fixed class count, uniformly in \(N\).
This exact reduction does not decide the unrestricted quantifier over
all \(N\) in one call, give a bound on \(N\), or improve the
survivor estimates. The cited Cambridge primary text returned HTTP503
in this source check; the external algorithm is not independently
implemented or formally replayed here. No new Lean wrapper is added.

<a id="finite-recoding-and-the-arithmetic-resolution-boundary"></a>
### Finite recoding and the arithmetic-resolution boundary

All conclusions below concern ordinary mathematics and the accompanying finite exact diagnostic. They do not resolve unrestricted Erdős–Selfridge noncoverage. Numerical moduli remain pairwise distinct odd integers greater than one in the intended problem, and residues are fixed once for each original label.

#### 1. Canonical finite words

Fix k>=2 and G_j=2^j for j<k, followed by G_j=sum_(i=1)^k G_(j-i). A legal word has digits0,1 and no run1^k. Digits are stored least significant first. Zero has the empty canonical word; every nonzero canonical word has highest digit1. Padded words of a specified length retain their padding.

Legal words of length n, decoded by sum_(j<n) d_j G_j, give each integer in [0,G_n) exactly once. Here is an interval induction, not an inference from counts alone. For n<k, this is binary expansion. For n>=k, partition the word from the highest position into r leading ones followed by a zero, 0<=r<k. The remaining n-r-1 lower digits decode to [0,G_(n-r-1)). The block with r leading ones starts at S_r=sum_(q=1)^r G_(n-q), and its endpoint is S_r+G_(n-r-1)=S_(r+1). Thus the blocks concatenate without gaps or overlap from0 to S_k=G_n. Lower-word uniqueness gives block uniqueness. Removing highest zero padding supplies the canonical encoding E_k of every natural number. The powers2 initial conditions and positive recurrence make G_n unbounded.

Existing project material supplies the count in [DBonacci/Names](../../../../../D5/S0/Tower/DBonacci/Names.lean) (`dbonacci_name_card`, with dbonacci k(n+2)=G_n), and the integer-value bijection for k=3 in [Tribonacci/Representation](../../../../../D5/S0/Tower/Tribonacci/Representation.lean) (`decode_bijective`). [DBonacci/Values](../../../../../D5/S0/Tower/DBonacci/Values.lean) uses real beta-values in several declarations: those are not silently identified with these integer weighted sums. [CanonicalInterchangeability](../../../../../D5/S0/Conventions/CanonicalInterchangeability.lean) already states decoded-predicate preservation for arbitrary faithful encodings. No new Lean wrapper is needed.

For fixed finite covering family let L be its LCM and choose representatives0<=s<L. The encoded survivor is {E_k(s): s mod m_i !=a_i for every i}. Consequently its cardinality and emptiness agree with the arithmetic survivor. Transporting the uniform law on these L representatives gives exactly |H|/L in every encoding. Choosing a fresh uniform law on all legal words at a padded length is a different probability law: the interval [0,G_n) need not have size divisible by L.

For L|L', the encoded reduction is defined by

    E_k(s) -> E_k(s mod L),  0<=s<L'.

These reductions commute with cross-encoding translation because both orders decode, reduce modulo L and encode. Literal word-prefix truncation is not the same operation.

#### 2. The exact automaton needs weight phase

At a known digit layer j, the pair (run,s) suffices for the recurrence

    (run,s) --d--> (run',s+dG_j mod L),

where d=1 requires run<k-1, and run'=0 for d=0, run+1 for d=1. Without the external layer, include the phase vector

    v_j=(G_j,...,G_(j+k-1)) mod L.

Its update F(v)=(v_1,...,v_(k-1),sum v) has inverse

    F^(-1)(w)=(w_(k-1)-sum_(i<k-1)w_i,w_0,...,w_(k-2)).

It permutes a finite set, so the orbit of v_0 is purely periodic. The autonomous state (run,s,v) is finite, with at most k L T states on its weight orbit of period T. This is an upper bound for this representation, not the minimum number of states of a residue recognizer. The existing [ZeckendorfResidueTransducer](../../../../../D5/S1/Digit/ZeckendorfResidueTransducer.lean) stores precisely the accumulated residue and two consecutive Fibonacci weights and proves the prime-modulus evaluation invariant.

Acceptance is tested when a word terminates. Prefix coverage does not imply coverage of every extension: in binary,1 belongs to1 mod3 while its extension11 represents3 and does not. A covered-prefix subgraph deletion can therefore erase a valid survivor. A safe deletion needs a statement about all permitted continuations. Termination and leading-padding conventions must be retained as well.

A forced0 contributes no choice conditioned on its state, but consumes a position. For Zeckendorf,101 represents4 whereas deleting its forced middle0 gives11, an illegal word whose raw weighted value is3. A contracted edge must carry the consumed length/phase and any termination or cost information. Shannon information increment can only be discussed after fixing a law; language capacity log(lambda_k) is not arbitrary-source entropy.

The program also checks a common LSB example for every tested k: prefix(0) is covered by0 mod3, while its legal extension(0,1) has value2 and survives. This avoids confusing the binary11 example with Zeckendorf legality.

#### 3. Finite recoding does not identify the two completions

Give X_k={infinite0/1 sequences avoiding1^k} its digit-prefix topology, reading positions0,1,... from the least significant end. Let e_j be the sequence with its sole1 at position j. It is legal and e_j tends to the all-zero sequence. Its finite integer value is G_j.

For every m>1 there is no continuous f:X_k -> Z/mZ agreeing with finite integer values modulo m. Indeed, continuity at zero would force f(e_j)=0 for all sufficiently large j, so G_j=0 mod m eventually. The invertible recurrence above implies that k consecutive zeros force the entire preceding recurrence vector to be zero. Iterating backwards would give G_0=0 mod m, contradicting G_0=1. Equivalently every block of k successive weights contains a nonzero residue. Thus every low-digit prefix neighborhood of zero contains a finite legal word with a different residue modulo m.

For binary the corresponding extension exists exactly when m divides some2^N: then the first N digits determine the residue. If m has a nontrivial odd factor,2^j is never0 modulo that factor, and the same single-one argument forbids a continuous extension. The modulus1 case is trivial.

This is an obstruction to extending the particular finite-value identification, not a claim that the underlying compact spaces admit no abstract homeomorphism. It concerns least-significant-first prefix topology, not every possible encoding topology. Finite residue automata do not contradict it: they evaluate a word with an end, and their accumulated residues need not converge on an infinite word.

Therefore one may re-encode each arithmetic layer Z/LZ and transport its bonding maps, or independently study an infinite digit shift. One cannot identify the latter with the arithmetic inverse limit just because every finite integer can be translated. The project's [NoContinuousAdditionExtension](../../../../../D5/S1/Digit/Infinite/NoContinuousAdditionExtension.lean) already records a related k=2 obstruction for separately continuous addition; it is not this mod-m statement. [RRO §96](../../../../develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#96-有界游程并集的有限覆盖与零测性) separately distinguishes finite-view stabilization as k grows from the union of the fixed-k infinite languages: the latter is a proper, dense null subset of the full binary shift.

#### 4. Bounded diagnostic and research consequence

The accompanying program fixes k=2,3,4,5,binary and L=3,9,15,27,45,105,315. For each L, it uses each divisor m>1 exactly once, with fixed original phase a_m=(floor(m/3)+1) mod m. It checks full legal-word value intervals, direct residue histograms against layered DP, an autonomous vector-phase evaluator, canonical representatives, and cross-encoding arithmetic reductions. Separate controls include the14/27 survivor example and a known even whole cover; neither is an odd-distinct covering counterexample.

At L=315 the common survivor has96 representatives, with uniform mass32/105. Maximum canonical lengths are12,10,9,9,9 in the specified encoding order. Layered widths and padded-language counts are recorded separately; no minimal-state or runtime superiority is claimed. All20 finite-k weight periods in the specified modulus matrix returned before the fixed100000-step cap. In particular k=5 modulo15 has period81224, versus40 for k=2. These are exact orbit periods, not bounds on every possible implementation.

For fixed k, the standard no1^k language growth gives capacity h_k=log(lambda_k); the minimum padded depth to represent all0<=s<L satisfies N_k log(lambda_k)=log L+O_k(1). This is an asymptotic capacity identity, not an exact energy law. Finite recoding preserves |H|, emptiness and a transported law; automaton cycles, branching, code lengths and raw-digit entropy have no automatic equality across k. A coordinate-specific lemma remains useful if its arithmetic consequence transports soundly.

The remaining research obligation is a uniform arithmetic restriction using oddness and original-label distinctness. Changing encoding alone supplies no positive lower bound for |H|. A future encoding-based proof must supply such a restriction, or a verified computational improvement, while preserving the fixed phases and the same probability law.

#### 5. Finite translation resolution and the logical boundary

Write Q_(k,n)(x) for the first n low-order digits of the canonical k-code of x, padded by zeros, and R_m(x)=x mod m. A source observation Q supports a deterministic exact translation to a target observation P if and only if

    Q(x)=Q(y) implies P(x)=P(y).

Necessity follows by applying the translator. For sufficiency define its value at an observed Q(x) to be P(x); the displayed implication makes this well defined. This is the repository's existing observation-kernel/factorization criterion, also used in [RRO §133](../../../../develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md#133-共同实现概率与演化的同步运输). It introduces no new theorem or mathematical novelty.

For finite k>=2, no n makes R_m factor through Q_(k,n) on all natural numbers when m>1: choose j>=n with G_j nonzero modulo m; x=0 and y=G_j have the same zero low prefix and distinct residues. This is already proved in section3. Thus partial recoding really has a task-dependent resolution obstruction, even though full finite words translate exactly. On a bounded domain0<=x<B, a sufficiently long word completely specifies x and every target observation; the bound is computable from the increasing weights. There is no contradiction between these two statements.

Recursive refinement and self-reference alone do not imply Gödel incompleteness. A finite run automaton has recurrent transitions, and membership of every supplied finite word is nevertheless decided by scanning it. A recursive procedure that computes every finite residue layer can likewise terminate on every layer while no single layer determines the entire completion. These are observation and algorithmic statements, not undecidability of a particular sentence in a formal theory.

The relevant incompleteness conclusion requires specifying a consistent, effectively axiomatized formal theory with enough arithmetic (for example, an extension of Robinson arithmetic). The Gödel–Rosser theorem then gives a sentence neither provable nor refutable in that theory. A numeration system by itself supplies neither such a proof predicate nor this conclusion. Primality of a given integer is also decidable; prime-indexed refinement is not automatically an undecidable operation.

The existing [ClosureUndecidable](../../../../../D5/S0/Computability/ClosureUndecidable.lean) module invokes Rice's theorem for a nontrivial extensional predicate on arbitrary partial recursive programs. Its program-universality and extensionality hypotheses have not been supplied by the k-bonacci residue automata or by the restricted odd-cover problem. Every supplied finite covering family remains exactly decidable on its LCM. No reduction from an undecidable problem to Erdős #7, and no independence of #7 from a named formal theory, is established here.

The [replay program](../../frontier/cover-geometry/cross_encoding_arithmetic_resolution.py) and [complete diagnostic result](../../frontier/cover-geometry/cross_encoding_arithmetic_resolution.json) retain every stated bounded case. Use `--base <report-base> --check` under `python3 -B -I -S -O`; arithmetic reduction is transported through the original integer value. The result records complete periods and bounded state counts, without inferring a lower bound for the unrestricted survivor set.
