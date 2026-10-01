# One scaled common-centre dual excludes every threshold for all retained tables

For the fixed infinite pure-comb source C, phase-31 interface, inherited head and 249 allowed K8 cells, every nonnegative retained table satisfies

$$
\frac{H_A(h;u)+H_C(h;u)}2
\ge (28-h)\left(L(u)+\frac{M(u)}{400}\right)
  +\frac{2}{401397328829}M(u)
\qquad (0\le h\le28).
$$

Here A and C are two actual, coherent global centres. Consequently no nonzero table in this fixed interface makes the raw all-layout hinge comparison positive at any admissible threshold $0\le h<28$, even when the tail coefficient is zero. This is a statement about the specified comparison model; it is not a statement about other sources, interfaces or the actual survivor restriction, and it does not resolve Erdős #7.

## Fixed objects and quantifiers

The source and cap rows are those rebuilt by the canonical [834 consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/arbitrary_profile_common_centres.py). Its source bindings preserve the selected primes, ternary leaves, phase-31 K8 exclusions and inherited head. The allowed cells are indexed by $i=0,\ldots,248$, with strictly positive source masses $m_i$. The two centres are

$$
A=(3,0,1,1,1,1,1,1),\qquad
C=(2,0,1,1,1,1,1,1).
$$

These tuples are indices in the canonical leaf and colour lists. Actual representatives use ternary leaf 5 for A and leaf 2 for C, root 0 in the 5-adic coordinate, root 3 in every other selected prime coordinate, and zero higher digits.

Let $u_i\ge0$ be arbitrary, with no upper boxes imposed. Set $M(u)=\sum_i m_i u_i$. For each of the 384 inherited cap blocks $b$, let

$$
Z_b(u)=\max_{r\in b}\sum_i f_{ri}u_i,
\qquad
L(u)=M(u)-\sum_b\ell_bZ_b(u),
$$

using the canonical nonnegative cap coefficients $f_{ri}$ and head losses $\ell_b$. There are 9,902 cap rows. For centre $X\in\{A,C\}$, define the exact cell hinge coefficient and table hinge by

$$
b_{X,i}(h)=\int_{\text{cell }i}(N_X-h)_+\,d\nu,
\qquad
H_X(h;u)=\sum_i b_{X,i}(h)u_i.
$$

The load is integer-valued. Each cell law retains its complete mass and mean, together with the exact masses at loads $1,\ldots,27$. This determines $b_{X,i}(h)$ throughout $[0,28]$; it is not a truncation of the complete mean or a claim that larger loads vanish.

## Certificate and scaling argument

The attached exact rational certificate at $h=16$ uses 516 positive cap multipliers $\alpha_r(16)$ and centre weights $\beta_A=\beta_C=1/2$. All 384 cap budgets and 633 nonnegative dual columns are checked. Its normalization multiplier satisfies

$$
-\frac{46}{1000}<\lambda(16)<-\frac{45}{1000}<-\frac1{25}.
$$

For an arbitrary real threshold $h\in[0,28]$, retain these centre weights and set

$$
\alpha_r(h)=\frac{28-h}{12}\alpha_r(16),
$$

$$
\lambda_i(h)=(28-h)-
\frac{\sum_r\alpha_r(h)f_{ri}
      +\tfrac12b_{A,i}(h)+\tfrac12b_{C,i}(h)}{m_i},
\qquad
\lambda(h)=\max_i\lambda_i(h).
$$

The $h=16$ cap budget is $\sum_{r\in b}\alpha_r(16)\le12\ell_b$. Nonnegative scaling therefore gives

$$
\sum_{r\in b}\alpha_r(h)\le(28-h)\ell_b.
$$

Multiplying the column inequalities by $u_i$ and summing yields

$$
\frac{H_A(h;u)+H_C(h;u)}2
\ge (28-h)M(u)-\lambda(h)M(u)
   -\sum_r\alpha_r(h)\sum_i f_{ri}u_i.
$$

Each cap-row value is at most its block maximum. The scaled budget then gives

$$
\frac{H_A(h;u)+H_C(h;u)}2
\ge(28-h)L(u)-\lambda(h)M(u).
$$

This is an ordinary exact dual argument for every nonnegative table. It does not infer joint feasibility from separately optimized source columns or alter the underlying source between centres.

## From 29 endpoints to every real threshold

For integer $j=0,\ldots,27$, each $b_{X,i}$ is affine on $[j,j+1]$. So each $\lambda_i$ is affine there, and their maximum $\lambda$ is convex there. The maximum on that unit interval is bounded by the larger endpoint value. Checking all 249 columns at the 29 integer thresholds therefore bounds the entire closed interval.

The exact computation gives

$$
\max_{0\le h\le28}\lambda(h)
=\lambda(28)
=-\frac{2}{401397328829}<0.
$$

The endpoint maximum has two source-column witnesses, 177 and 214; the result stores the first, corresponding to cell $(4,96)$. The $h=16$ control reproduces its exact rational certificate unchanged, with value $-0.04560372280333804\ldots$. The valid threshold interval is all of $[0,28)$, with the stronger inequality valid also at the closed endpoint 28.

The same 29 endpoint values satisfy the stronger fixed comparison

$$
\lambda(j)+\frac{28-j}{400}
\le-\frac{2}{401397328829}
\qquad(j=0,\ldots,28).
$$

Adding an affine function preserves convexity on each unit interval, so this comparison holds for every real $h\in[0,28]$. Substitution in the scaled dual inequality proves the leading bound, including its proportional $M(u)/400$ term. The 29 exact comparison slacks are nonnegative and vanish only at $j=28$. The constant $1/400$ is a verified sufficient value; no optimality of that constant is asserted.

On the original half-open domain the same value is the supremum of this fixed certificate family by continuity. The endpoint 28 is not an admissible threshold. None of these statements identifies a primal optimum or asserts that a retained table attains this bound.

Let $H_*(h;u)$ denote the supremum over all globally fixed phase tables that independently assign a phase to each numerical query label. This includes phase tables with no nested or common-centre representation. Each label has one phase across the whole source, rather than a phase chosen separately in each source cell. The common-centre phase tables A and C are two admissible witnesses in that full class, so $H_*(h;u)\ge\max(H_A,H_C)\ge(H_A+H_C)/2$. Thus

$$
(28-h)L(u)-H_*(h;u)
\le-\left(\frac{28-h}{400}+\frac{2}{401397328829}\right)M(u).
$$

A nonzero nonnegative table has $M(u)>0$, so this gate is strictly negative. Subtracting any further nonnegative tail penalty cannot make it positive.

## Reproducible evidence and remaining boundary

The portable consumer imports the pinned canonical 834 source builder and calls `rebuild(..., low_limit=27)`. It reconstructs the fixed source and cap rows, verifies the existing 834 certificate, reconstructs the two $h=16$ centre rows from those same laws, and checks the complete semantic matrix digest and new exact dual. It then checks 7,221 threshold-column values, the 29 maxima, the uniform rational bound and the 29 proportional-margin comparisons. The retained certificate contains only the needed sparse dual; no scratch matrix, embedded source table or optimizer is required.

Independent exact verification checked the $h=16$ dual and all 7,221 threshold-column values, including the uniform maximum and its two witnesses, and separately checked all 29 proportional-margin comparisons. The consumer and exact endpoint result are accompanying reproducible artifacts. These are ordinary mathematical and rational-computation results; no Lean claim is made.

The portable consumer also passed a deterministic comparison under Python `-O` from a different working directory, with spaces in its file path. From the repository root, the corresponding reproducible command is:

```sh
e7_data=docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/pure-source-realizability
python3 -I -S -B -O "$e7_data/parametric_dual_interval.py" \
  --core "$e7_data/arbitrary_profile_common_centres.py" \
  --candidate "$e7_data/retained_factorial_hinge_certificate.json" \
  --result832 "$e7_data/common_center_hinge.json" \
  --certificate "$e7_data/arbitrary_profile_common_centres_certificate.json" \
  --certificate16 "$e7_data/parametric_dual_interval_certificate.json" \
  --result834 "$e7_data/arbitrary_profile_common_centres.json" \
  --legacy-engine "$e7_data/free45_live_cell_and_comparison_obstruction.py" \
  --centre-engine "$e7_data/common_center_engine.py" \
  --result "$e7_data/parametric_dual_interval.json" \
  --timeout 300
```

The result closes threshold adjustment within this fixed raw-comparison interface, including all nonnegative retained tables. Progress toward the covering problem still requires a justified change of source, interface or comparison, or information about the actual survivor restriction sufficient to replace the raw hinge obstruction. Choosing a different threshold alone cannot repair this model.

Artifacts: [consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/parametric_dual_interval.py), [exact result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/parametric_dual_interval.json), and [sparse certificate](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/parametric_dual_interval_certificate.json).
