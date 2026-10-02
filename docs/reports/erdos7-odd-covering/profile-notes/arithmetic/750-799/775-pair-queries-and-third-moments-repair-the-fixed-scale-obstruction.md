# Pair queries and third moments repair the fixed-scale obstruction

A240-query sufficient bound succeeds on the actual dictionary from
[774](774-fixed-single-axis-scales-fail-while-the-joint-envelope-passes.md),
where every common row law fails the fixed-scale300 bound. Keep every two-axis query exactly, and bound all interactions of order at least three using only single-axis third moments and verified positive denominator bounds. The same fixed scales $(10,12,16,18,22)$ then admit an integer common law of mass1000 with sufficient cost below999.

The reduction is in the number of scalar query caps needed for one static sufficient-cost test. It is not a count of DP states and does not establish that these caps can be updated through arbitrary fixed-phase deletions. The obstruction in
[755](755-current-query-maxima-are-not-a-closed-continuation-boundary.md)
remains relevant to any claimed continuation interface.

## 1. The sufficient condition

Use the complete actual source of
[758](758-one-row-mass-law-handles-all-outside-colours.md): the old315 core, five globally phased singleton old dictionaries, admissible old rows $X^+$, and positive guaranteed outside denominators $\ell_j(x)$. All actual numerical labels and their phases remain fixed. Choose one nonzero common law $u_x\ge0$ and numbers $m_j,s_j>0$ with

$$
u_x>0\Longrightarrow \ell_j(x)\ge m_j
\qquad\text{for every }j.
$$

Write

$$
Z_{d,J}(u)=\max_{a\bmod d}
\sum_{x=a\pmod d}\frac{u_x}{\prod_{j\in J}\ell_j(x)},
\qquad
Y_{d,j,k}(u)=\max_{a\bmod d}
\sum_{x=a\pmod d}\frac{u_x}{\ell_j(x)^k}.
$$

The empty product in $Z_{d,\varnothing}$ is1. Use the full-height core coefficient from758,

$$
\kappa(d)=
\prod_{p\in\{3:9\mid d;\,5:5\mid d;\,7:7\mid d\}}
\frac p{p-1}-1.
$$

For $3\le k\le5$, set

$$
A_{j,k}(s)=\sum_{\substack{J\subseteq\{1,\ldots,5\}\\|J|=k,\,j\in J}}
\frac{s_j^k}{k\prod_{i\in J}s_i},
\qquad
c_j(s,m)=\sum_{k=3}^5 A_{j,k}(s)m_j^{3-k}.
$$

Define

$$
\begin{aligned}
B_{s,m}(u)={}&
\sum_d\kappa(d)Z_{d,\varnothing}(u)
+\sum_{d,j}\kappa(d)Y_{d,j,1}(u)\\
&+\sum_d\bigl(\kappa(d)+1\bigr)
\sum_{i<j}Z_{d,\{i,j\}}(u)\\
&+\sum_{d,j}\bigl(\kappa(d)+1\bigr)c_j(s,m)Y_{d,j,3}(u).
\end{aligned}
$$

Then the original372 cost satisfies

$$
C(u)\le B_{s,m}(u).
$$

Consequently $B_{s,m}(u)<\sum_xu_x$ supplies the same positive-source conclusion as758. This is a sufficient condition. Failure of this bound does not exclude a successful372 law or another actual survivor construction.

### Proof

For a subset $J$ of size $k\ge3$, apply positive scaled AM–GM pointwise on every positive-weight row:

$$
\frac1{\prod_{j\in J}\ell_j(x)}
\le
\sum_{j\in J}
\frac{s_j^k}{k\prod_{i\in J}s_i}\ell_j(x)^{-k}
\le
\sum_{j\in J}
\frac{s_j^km_j^{3-k}}{k\prod_{i\in J}s_i}\ell_j(x)^{-3}.
$$

Multiply by that same $u_x$, sum in a cylinder, and take its maximum. The maximum of a nonnegative sum is bounded by the corresponding sum of maxima. Summing over every $J$ of size $k$ gives precisely $A_{j,k}(s)m_j^{3-k}$ as the coefficient of each third-moment query.

For every $k\ge2$, the original coefficient is $\kappa(d)+1$, independent of $k$. Thus orders3,4,5 collapse into $c_j(s,m)$. Empty, singleton and pair terms are retained exactly. These operations prove the claimed inequality without optimizing independent laws for different axes, subsets or divisors.

Only the lower bounds on positive-weight rows are mathematically necessary. A support-dependent choice of $m$ is lawful only when the stated support is verified to exclude every violating row. The literal below uses the minima over all75 source rows, so its coefficients are fixed before optimizing the law.

### Query count and available computation

There are ten nonzero empty queries,50 singleton queries,120 exact pair queries, and60 single-axis third-moment queries:240 in total. For fixed $s,m$ and an admissible source, $B_{s,m}$ is a positively homogeneous convex piecewise-linear function of the one common law. Its epigraph is a finite linear program; an integer or rational proposed law can instead be checked directly by evaluating240 exact maxima.

This interface retains two-axis denominator correlations and bounds the higher interactions. It uses fewer caps than the complete372 envelope but does not imply a closed update rule for those cap values. In particular, future deletions can change both the maximizing phases and the rows attaining a denominator minimum.

## 2. The same actual dictionary, a new common law

The source is the pinned
[774 input](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_single_axis_obstruction_input.json),
SHA256
`3233f1c82a405ae6018bcad76b0274f14bce7f19a2bcf3bac741657452eec630`.
It supplies the eleven core phases and all55 globally fixed singleton old phases. Its actual75 admissible rows have global denominator minima

$$
m=(3,4,8,8,15).
$$

Set $s=(10,12,16,18,22)$. The exact third-moment coefficients are

$$
c=
\left(
\frac{6425}{7776},
\frac{5833}{4400},
\frac{59656}{22275},
\frac{1016847}{281600},
\frac{13826791}{2430000}
\right).
$$

The new
[weight literal](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_pair_third_moment_input.json)
contains one integer weight for every source row, the stated scales and denominator bounds, and the source pin. Its SHA256 is
`7f36de92b6217d6f86ee3742336dc0619e490fa0e20978a68da60a35d6d7fed0`.
These weights differ from774's mass305 witness: they have total mass1000, are positive on65 rows, and are at most23.

Exact evaluation gives

$$
\frac{B_{s,m}(u)}{1000}
=
\frac{21272859590351218471954789974856121}
{21297758225879710395684864000000000}
\approx0.9988309269330404
<\frac{999}{1000}.
$$

The distorted reserve is

$$
1000-B_{s,m}(u)
=
\frac{24898635528491923730074025143879}
{21297758225879710395684864000000}.
$$

For comparison, direct recomputation of the original372 envelope on this same law gives

$$
\frac{C(u)}{1000}
=
\frac{2929812766805649097}{2956651746048000000}
\approx0.9909225091259987
<\frac{B_{s,m}(u)}{1000}.
$$

The reference372 computation is a comparison check; the240-cap sufficient certificate does not need its values. By774's exact dual, the fixed-scale300 bound still exceeds $1017/1000$ times mass for this law and every other common law on the same dictionary. The repair therefore comes from retaining pair correlations while compressing the higher-order debit, not from a different choice of those five fixed scales.

## 3. Actual-source and Haar consequences

The lower bounds $\ell_j$ are conservative counts of old-label hits. They are not asserted to equal actual distinct-root losses. The same dictionary has the actual71-original CRT realization verified in774, with actual root minima $(9,11,15,17,21)$; this note reuses that source rather than duplicating its numerical classes.

As in758, for any actual outside roots compatible with the fixed old phases, build the single conditional-product source with old marginal $u$ on the actual surviving roots. Its actual counts satisfy $r_j(x)\ge\ell_j(x)>0$. The bound just proved pays the same original joint envelope, so it supplies a positive distorted survivor mass after arbitrary shallow multioutside phases and arbitrary finite higher core3/5/7 exponents, with outside exponents at most one.

For this law,

$$
D_0=\max_x\frac{u_x}{\prod_j\ell_j(x)}=\frac3{21560}.
$$

The maximum is attained at old row23. The density comparison from758 gives

$$
\operatorname{Haar}(\text{final survivors})
\ge
\frac{1000-B_{s,m}(u)}{315\prod_jP_j\,D_0}
=
\frac{24898635528491923730074025143879}
{991706912444306952747670392576000000}
\approx0.000025106848824037212.
$$

This uses the240 bound's reserve; using the larger actual372 reserve would give a stronger number and is not needed for this certificate. The same lower bound extends to larger ordered outside primes by758's rowwise density comparison. It does not assert unrestricted higher outside powers, an arbitrary number of outside axes, or a universal source law.

## 4. Exact evidence and the remaining quantified problem

The standalone standard-library
[consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_pair_third_moment.py)
freshly reads the pinned774 source, reconstructs the75 rows and all lower denominators, verifies the new weights and the global minima, recomputes the coefficients, and evaluates every one of the240 caps. Its
[result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_pair_third_moment.json)
also includes the372 comparison maxima and the precise normalization quantities. It does not import a numerical optimizer or trust proposed cap values.

An independent implementation uses polynomial multiplication for the coefficients and common-denominator integer sums for the residue fibres. All240 coefficients, caps and least maximizing residues agree, as do the independently computed372 cost, point-mass cap and Haar conversion. Normal and optimized Python runs preserve all explicit guards; ten malformed-certificate checks reject altered source pins, bad scales or denominator bounds, invalid weights and row lists, and forged coefficient data. This is an ordinary proof plus exact finite arithmetic, not new Lean verification.

The new uniform sufficient target is explicit: for each actual complete dictionary, find one common $u$ and verified positive $m,s$ with $B_{s,m}(u)<\sum u$. It is stronger than universal372 feasibility and has not been established for every dictionary. The present witness repairs the specific dictionary obstructing the fixed-scale300 route. It motivates keeping pair correlations in a source theorem; it does not settle the all-four-small-primes source gap or replace the further interfaces required by unrestricted Erdős #7.
