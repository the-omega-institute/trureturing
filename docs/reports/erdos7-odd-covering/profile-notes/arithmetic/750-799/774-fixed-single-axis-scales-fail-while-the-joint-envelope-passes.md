# Fixed single-axis scales fail while the joint envelope passes

The fixed scales used in [769](769-single-axis-moments-certify-a-dictionary-with-two-failed-weight-rules.md) do not give a universal sufficient certificate. One actual globally phased dictionary on the old315 core has

$$
\widetilde C_S(u)\ge
\frac{302528624050627203408353}{297327183003648000000000}
\sum_xu_x
>
\frac{1017}{1000}\sum_xu_x
$$

for every nonzero nonnegative common row law, where
$S=(10,12,16,18,22)$. Yet the original joint372 envelope of
[758](758-one-row-mass-law-handles-all-outside-colours.md) has an explicit integer law of mass305 satisfying

$$
\frac{C(u)}{305}
=
\frac{3287121421692746843}{3306522202663680000}
<\frac{199}{200}<1.
$$

Thus the failure is in this fixed single-axis sufficient method, even after optimizing the common law. It is not a failure of the joint372 envelope on this dictionary, and it does not exclude different choices of scales. It is not a covering construction or a resolution of unrestricted Erdős #7.

## 1. One complete actual dictionary

Use the old numerical labels, in this order,

$$
D^+=(3,5,7,9,15,21,35,45,63,105,315),
$$

and outside lower primes $P=(11,13,17,19,23)$. The following rows assign one globally fixed old phase to each complete label; there is no independent choice of a phase at different old points.

| Dictionary | Phases in the displayed label order |
|---|---|
| Core | $(0,0,0,4,11,8,9,1,1,59,179)$ |
| 11 | $(2,3,6,8,8,20,34,8,20,104,104)$ |
| 13 | $(2,3,3,2,8,17,23,38,59,38,248)$ |
| 17 | $(2,3,4,5,8,11,4,23,32,74,284)$ |
| 19 | $(2,3,5,2,8,5,33,23,5,68,68)$ |
| 23 | $(2,3,2,1,8,2,23,28,37,23,163)$ |

Let $X$ be the surviving old residues after deleting the eleven core classes. It has75 rows. With the actual singleton old phases $b_{j,d}$ define

$$
h_j(x)=\sum_{d\in D^+}\mathbf1_{x=b_{j,d}\pmod d},
\qquad \ell_j(x)=P_j-1-h_j(x).
$$

All75 rows have strictly positive denominators, and their coordinate minima are

$$
(3,4,8,8,15).
$$

The literal is retained in
[`fibre_credit_depth_two_single_axis_obstruction_input.json`](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_single_axis_obstruction_input.json),
with SHA256
`3233f1c82a405ae6018bcad76b0274f14bce7f19a2bcf3bac741657452eec630`.

## 2. The dual criterion and its literal witness

Suppose a finite envelope is

$$
E(u)=\sum_t c_t\max_a\sum_x u_x\psi_{t,a}(x),
\qquad c_t\ge0,\quad u_x\ge0,\quad \psi_{t,a}(x)\ge0.
$$

Choose nonnegative multipliers $\lambda_{t,a}$ such that

$$
\sum_a\lambda_{t,a}\le c_t,
\qquad
\sum_{t,a}\lambda_{t,a}\psi_{t,a}(x)\ge\eta
\quad\text{for every admissible row }x.
$$

Then

$$
E(u)
\ge\sum_{t,a}\lambda_{t,a}\sum_xu_x\psi_{t,a}(x)
\ge\eta\sum_xu_x.
$$

This standard weak-duality bound is used as a certificate criterion, not claimed as a new abstract result. The first inequality uses nonnegative queries and each slot's total multiplier budget. The second uses every row inequality against the same $u$. No minimax interchange, numerical optimality assertion, or separately optimized axis laws is required. A certificate with $\eta\ge1$ excludes strict envelope cost below mass.

For the300 envelope use

$$
\kappa(d)=
\prod_{p\in\{3:9\mid d;\,5:5\mid d;\,7:7\mid d\}}
\frac p{p-1}-1
$$

and

$$
A_{j,k}(S)=\frac{S_j^{k-1}}k
 e_{k-1}\bigl((1/S_i)_{i\ne j}\bigr).
$$

There are ten empty slots with query $\mathbf1_{x=a\pmod d}$ and coefficient $\kappa(d)$; the other290 slots have query

$$
\psi_{d,j,k,a}(x)
=\frac{\mathbf1_{x=a\pmod d}}{\ell_j(x)^k}
$$

and coefficient

$$
c_{d,j,k}=A_{j,k}(S)\bigl(\kappa(d)+\mathbf1_{k\ge2}\bigr).
$$

The literal records360 nonzero multipliers, each an integer divided by $10^{10}$. The verifier rebuilds all300 coefficients, all75 actual rows, and all query incidences. Every slot budget is respected. The minimum exact row load occurs at $x=244$ and is

$$
\eta=\frac{302528624050627203408353}{297327183003648000000000}
\approx1.017493997670961.
$$

All300 coefficient budgets and75 exact row loads are retained in the result. This proves the first inequality at the start of this note for every common law, not merely for a finite set of proposed laws.

The quantifier on the scales is essential: this fixes $S=(10,12,16,18,22)$. The certificate does not bound $\inf_s\widetilde C_s(u)$ and cannot be reused as though the scales were arbitrary.

## 3. An exact joint372 primal certificate on those same phases

Assign integer weights to the75 rows as follows.

| Weight | Old rows |
|---:|---|
|0|52,83,124,142,152,187,188,232,277|
|1|32,47,97,137|
|2|38,68,88,223,241,248,268,293|
|3|104,106,107,118,128,143,151,158,173,209,278,314|
|4|53,172,233,262|
|5|23,61,62,73,82,122,167,194,208,227,263,272,284|
|6|17,89,109,214,257,299,313|
|7|2,16,19,34,37,43,74,163,169,178,199,212,242,244,286,298,304,307|

The mass is305, supported on66 rows. With

$$
Z_{d,J}(u)=\max_{a\bmod d}
\sum_{x\in X,\,x=a\pmod d}
\frac{u_x}{\prod_{j\in J}\ell_j(x)},
$$

recompute every nonzero joint slot:

$$
C(u)=\sum_{d,J}
\bigl(\kappa(d)+\mathbf1_{|J|\ge2}\bigr)Z_{d,J}(u).
$$

The372 maxima, including a maximizing residue for each, yield the ratio stated above and the strictly positive distorted reserve

$$
305-C(u)=
\frac{19400780970933157}{10841056402176000}.
$$

This uses the same actual phases as the dual and a single common row law. It shows that replacing cross-axis reciprocal products by the fixed-scale single-axis expression can remove a successful certificate.

The conservative point-mass cap for the product law in758 is

$$
\max_x\frac{u_x}{\prod_j\ell_j(x)}=\frac1{25872}.
$$

Consequently758's normalization bridge gives the positive Haar lower bound

$$
\frac{305-C(u)}{315\prod_jP_j\,(1/25872)}
=
\frac{19400780970933157}{140222772877627440000}.
$$

This is a lower bound after paying the joint envelope, not a claim that distorted mass equals Haar mass. Its downstream scope is exactly that of758: arbitrary shallow multioutside phases and arbitrary finite higher core3/5/7 exponents, with outside exponents at most one. The usual monotonic enlargement to larger ordered outside primes remains under758's hypotheses; no unrestricted all-prime tail is supplied here.

## 4. Actual numerical realization and conservative counts

The displayed old dictionaries are realizable by71 distinct odd numerical originals. Use the eleven displayed core classes, one pure class $1\pmod {P_j}$ for each outside prime, and for every old label $d$ choose the unique mixed class modulo $dP_j$ satisfying

$$
a\equiv b_{j,d}\pmod d,
\qquad a\equiv0\pmod {P_j}.
$$

The verifier retains all71 numerical classes and checks actual root membership at6225 old-row/outside-root points. In this concrete realization, every nonempty set of old-label hits deletes the same outside root0, in addition to the pure root1. Hence its actual root count is

$$
r_j(x)=P_j-1-\mathbf1_{h_j(x)>0}\ge\ell_j(x).
$$

The minimum actual counts are $(9,11,15,17,21)$;143 row-axis pairs have strict improvement over the conservative denominator. This realization verifies actual arithmetic compatibility. It must not be mistaken for a realization in which the conservative label counts are exact distinct-root losses. The primal theorem uses only $r_j\ge\ell_j$ and consequently remains valid for any actual outside roots realizing the same old phases.

## 5. Verification and remaining target

[`fibre_credit_depth_two_single_axis_obstruction.py`](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_single_axis_obstruction.py) is a standalone standard-library rational consumer. Its retained
[result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_single_axis_obstruction.json)
contains every dual budget and row load, every joint primal maximum, the full numerical realization, and the normalization quantities. Numerical optimization proposed the literal; the exact inequalities above are certified independently of the optimizer.

All guards are explicit exceptions and survive Python optimization. Normal and `-O` runs reproduce the result. Ten malformed-certificate mutations are rejected: invalid or missing phases, altered fixed scales, an invalid dual slot, a negative multiplier, duplicate queries, excess budget, a missing dual, a negative primal weight, and a duplicate primal row. These are ordinary exact finite checks and a general dual inequality, not additional Lean verification.

The universal372 target remains: every actual complete core and five singleton old dictionaries should admit one common nonnegative law with $C(u)<\sum u$, or an actual dictionary should furnish an exact dual obstruction to that specific envelope. This note eliminates the fixed-scale300 condition as a universal replacement. Varying scales or keeping selected joint queries are separate possible sufficient methods and require their own common-source bounds.
