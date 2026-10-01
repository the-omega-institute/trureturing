# Adaptive row-law positivity need not survive convexifying actual phases

The passage from actual phase dictionaries to their convex hull can change
whether an adaptive row law has positive margin. A two-state, two-row
example on the divisor system of315 has exact costs

\[
 \Lambda_{\rm actual}=\frac{35}{36}
 <1<\Lambda_{\rm hull}=\frac76
 <\Lambda_{\rm common}=\frac{175}{144}.
 \tag{PC1}
\]

The example uses a **seven-term subfunctional on the selected carrier
`X={0,105}`**. It does not use the current75-row source and does not refute
universal feasibility of [report758's complete372-slot functional](758-one-row-mass-law-handles-all-outside-colours.md). In fact,
adding just one omitted term makes both actual endpoints fail that full
functional. The related [integer-selector result503](../500-549/503-integer-selectors-strengthen-capped-budgets-but-axis-limits-survive.md) shows a different cap/convexification issue. The present example excludes a general vertexwise-to-hull argument;
it does not determine the75-row arithmetic problem. The following are
ordinary finite proofs and exact computations, not new Lean verification.

## Three quantifier orders and the valid comparison

Fix a finite family H of allowed actual load arrays on a common nonempty
row set R, with every relevant denominator `r_j-h_j(x)` strictly positive
throughout H. Positivity then holds throughout its convex hull. For one
row law `u>=0`, `sum u=1`, write the report758-type cost

\[
 F_h(u)=\sum_t c_t\max_{a\bmod d_t}
 \sum_{x\in R,\ x\equiv a\pmod{d_t}}
 \frac{u_x}{\prod_{j\in J_t}(r_j-h_j(x))},\qquad c_t\ge0.
 \tag{PC2}
\]

Define

\[
 \begin{aligned}
 \Lambda_{\rm actual}&=\max_{h\in H}\min_u F_h(u),\\
 \Lambda_{\rm hull}&=\max_{h\in\operatorname{conv}H}\min_u F_h(u),\\
 \Lambda_{\rm common}&=\min_u\max_{h\in H}F_h(u).
 \end{aligned}
\]

Then

\[
 \Lambda_{\rm actual}\le\Lambda_{\rm hull}
 \le\Lambda_{\rm common}.                         \tag{PC3}
\]

The first inequality is inclusion. For the second, a reciprocal product
in(PC2) is log-convex, hence convex, as a function of the load entries on
the positive-denominator domain. Nonnegative sums and finite maxima
preserve convexity. Thus if `hbar=sum_s pi_s h_s`,

\[
 F_{\bar h}(u)\le\sum_s\pi_sF_{h_s}(u).
\]

Maximize over pi after minimizing over u. Finite-dimensional convex-concave
minimax applies to the resulting expression, since it is convex and
continuous in u, affine in pi, and both simplices are compact. It yields

\[
 \max_\pi\min_u\sum_s\pi_sF_{h_s}(u)
 =\min_u\max_sF_{h_s}(u),
\]

which proves(PC3). This is a use of standard minimax, not a new general
minimax theorem. The common positive-row hypothesis matters: the general
758 problem may exclude different rows for different actual h. No fixed
nonempty admissible row set for that entire problem is inferred here.

The actual-state objective permits one u chosen after observing the
complete actual dictionary. All terms of that dictionary's cost use this
same u. The common-law objective requires one u before the dictionary is
chosen. Hull feasibility permits a different u for every fractional load
array as well as every actual array. These are different quantifiers;
convexity for fixed u does not identify them.

## Actual phase dictionaries realizing the two endpoints

Let

\[
 D=(3,5,7,9,15,21,35,45,63,105,315),\quad X=(0,105),
\]

and put `S=(3,5,7,15,21,35,105)`. Both selected rows are0 modulo every
member of S. Take outside primes11 and13, each with pure forbidden root0.
The following is a complete literal table of the mixed numerical classes;
only the residue at modulus99 changes between the two current states.

| d | 11d | State A residue | State B residue | 13d | Common residue |
| --- | --- | --- | --- | --- | --- |
| 3 | 33 | 12 | 12 | 39 | 27 |
| 5 | 55 | 35 | 35 | 65 | 15 |
| 7 | 77 | 14 | 14 | 91 | 42 |
| 9 | 99 | 63 | 96 | 117 | 99 |
| 15 | 165 | 15 | 15 | 195 | 30 |
| 21 | 231 | 126 | 126 | 273 | 252 |
| 35 | 385 | 105 | 105 | 455 | 175 |
| 45 | 495 | 316 | 316 | 585 | 360 |
| 63 | 693 | 64 | 64 | 819 | 294 |
| 105 | 1155 | 315 | 315 | 1365 | 735 |
| 315 | 3465 | 1891 | 1891 | 4095 | 2310 |

Together with `(0 mod11)` and `(0 mod13)`, either column choice gives24
pairwise distinct odd numerical moduli. Every phase is globally fixed
across all rows, not chosen separately at each row.

The OLD phases at11 equal0 for every d in S; at9 they are0 in state A
and6 in state B; at45,63,315 they equal1. Consequently their hit counts
on X are `(8,7)` and `(7,8)`. At13 the old phases on S,9,45 are0, and
those at63,315 are42,105, yielding hits `(9,9)`.

In report758, h counts **matching labels**, which in general only bounds
the number of additional deleted roots. Here the full outside phases
make them equal. At either prime the seven S labels use distinct roots
1 through7 in S order. The11-label at9 uses root8; its other three labels
are inactive on X. At13 the9,45 labels use roots8,9 over row0, while63,315
use roots8,9 over row105. No active root is the pure forbidden root0.

The actual remaining root sets are therefore

\[
 \begin{array}{c|cc}
 &x=0&x=105\\ \hline
 11,\ A&\{9,10\}&\{8,9,10\}\\
 11,\ B&\{8,9,10\}&\{9,10\}\\
 13&\{10,11,12\}&\{10,11,12\}.
 \end{array}
 \tag{PC4}
\]

Thus their actual root counts coincide with the conservative denominators
`ell=r-h`: `(2,3)` or `(3,2)` at11 and `(3,3)` at13. A core dictionary
having residue1 at every d in D retains both selected rows and has144
survivors, so X can be a supported subcarrier. It is not that full
survivor set. Both selected rows are absent from the current75-row source,
whose pure3 class has residue0.

## The strict gap concerns exactly seven terms

Retain only `d in S` and `J={11,13}`. Report758's coefficients are

\[
 \kappa(d)+1\quad(d\in S)
 =\left(1,\frac54,\frac76,\frac54,\frac76,
                  \frac{35}{24},\frac{35}{24}\right),
\]

so their sum is35/4. Both rows lie in the old phase0 cell for every such
d. For `u=(p,1-p)` the two actual-state costs are exactly

\[
 \begin{aligned}
 F_A(p)&=\frac{35}{4}\left(\frac p6+\frac{1-p}{9}\right),\\
 F_B(p)&=\frac{35}{4}\left(\frac p9+\frac{1-p}{6}\right).
 \end{aligned}                                             \tag{PC5}
\]

State A minimizes at p=0, state B at p=1, giving35/36. Here the allowed
current dictionary family H consists of these two actual states; no
claim is made that every other possible dictionary has this property.

For the convex state `h_theta=theta h_A+(1-theta)h_B`, the11 denominators
are `(3-theta,2+theta)`. Minimizing over u gives

\[
 V(h_\theta)=\frac{35}{12\max(3-\theta,2+\theta)}.
\]

The two arguments of the maximum sum to5. Their maximum is at least5/2,
with equality at theta=1/2. Hence the maximum over the **entire** hull is
7/6, not only a lower bound from testing its midpoint. The common-law
cost is minimized where the two affine functions(PC5) meet, p=1/2, and
is175/144. This proves(PC1).

The fractional midpoint is not an actual label-hit vector: its11 hits
are `(15/2,15/2)`. It is exactly a mixture of the two actual global
phase dictionaries, but evaluating reciprocal denominators at that mean
is a different operation from randomizing the actual conditional laws.

The omitted `(d=5,J=empty)` term alone has `kappa(5)=1/4` and cap1 on X.
All full-functional terms are nonnegative. Therefore at either actual
endpoint, every row law has **full-envelope** cost at least

\[
 \frac{35}{36}+\frac14=\frac{11}{9}>1.            \tag{PC6}
\]

So this example expressly cannot establish actual-state positivity for
the full372-slot functional. It also does not exhibit a cover: even the
subfunctional is a sufficient union-budget expression, not exact mass
of the forbidden union.

## What the overload dual does preserve

For a fixed actual h and its nonempty positive-denominator row set R,
write each phase-specific contribution in(PC2) as a burden vector
`v_(t,a)(x)`. Form the polytope

\[
 Q_h=\operatorname{conv}\{\sum_t v_{t,a_t}: (a_t)_t
                      \text{ is an allowed complete assignment}\}.
\]

For the written sum of independent maxima the allowed assignments are
the product of the declared term-phase sets, and `F_h(u)=max_(q in Q_h)u.q`.
If some terms share the same original numerical-label phase, those phase
coordinates must first be identified and the functional changed to the
corresponding coupled maximum.

Standard finite minimax yields

\[
 \min_{u\in\Delta(R)}F_h(u)=\max_{q\in Q_h}\min_{x\in R}q_x.
 \tag{PC7}
\]

Hence failure of every positive-margin row law is equivalent to
`Q_h intersect [1,infinity)^R` being nonempty. Caratheodory gives a witness
mixture of at most `|R|+1` complete assignments. Every assignment uses one
global phase per declared coordinate, but the certificate is allowed to
mix complete assignments; it need not contain a single deterministic
assignment overloading all rows.

This is exact for the fixed-h **cap envelope**. Report758 first bounds
actual cylinder masses by dropping outside-root membership indicators and
replacing actual root counts by `ell`. Neither minimax nor its sparse
certificate reverses those upper bounds. An overload certificate thus
refutes that sufficient envelope, not existence of an actual supported
law or noncoverage. It also keeps h fixed; it does not justify replacing
`for every actual h, there exists u` with the hull or common-law problem.

## Continuation scope

A table of joint row masses indexed by `(CRT cylinder, complete hit-load
vector)` exactly evaluates the envelope and updates when a globally
phased OLD label is added, provided the retained cylinder family is
closed under the requisite lcm intersections. The hit load changes by
one on that label's old cell. This update is valid for **label hits**.
An actual distinct-root deletion count does not always change by one:
it also depends on whether that root is already excluded. Recovering the
actual process requires root marks or equivalent joint incidence data.

Moreover the load-table update leaves row masses fixed. Discarding newly
inadmissible rows, renormalizing, or choosing new adaptive row masses
requires the corresponding additional operation. At modulus315,
singleton cylinders already separate all75 actual rows, so retaining
all such exact data provides no automatic smaller row boundary.

## Verification

The standalone exact consumer reconstructs all displayed numerical phases
by CRT and also directly tests every point above each selected row against
the literal APs. It checks distinct labels, actual live root sets, all
seven coefficients, the endpoint optima, the full-hull optimum, the
common-law optimum and(PC6). Its checks use explicit exceptions and pass
under `python3 -I -S -B -O`. The proof of the general comparison and dual
uses standard convexity and minimax; those facts are not established by
this finite program.


[Exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_phase_convexification.py)
· [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_phase_convexification.json).
The default command recomputes the finite result and compares it with the
retained data:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_phase_convexification.py
```
