---
bibkey: xu2026rational
authors: Ce Xu and Jianqiang Zhao
year: 2026
title: Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers
doi: 10.48550/arXiv.2609.11072
url: https://arxiv.org/html/2609.11072v1
claim: "Equations (7)-(8) define the strict multiple polylogarithm and its depth-normalized reciprocal coefficients; Conjecture 1.3 asks for eventual coefficient signs and an admissible strict binomial lower bound."
strata_touched:
  - D5/S3/AnalyticClosure/Polylogarithm/CompositionDisk
  - D5/S3/AnalyticClosure/Polylogarithm/CompositionRecurrences
  - D5/S3/AnalyticClosure/Polylogarithm/CompositionZeroFree
  - D5/S3/AnalyticClosure/Polylogarithm/CompositionBoundary
  - D5/S3/AnalyticClosure/Polylogarithm/CompositionBanks
  - D5/S3/AnalyticClosure/Polylogarithm/CompositionContinuation
  - D5/S3/AnalyticClosure/Polylogarithm/CompositionSlit
  - D5/S3/AnalyticClosure/Polylogarithm/CompositionZeroFreeCollar
license: citation-only
triage: anchor
---

<!-- GID: D5/L/AnalyticClosure/xu2026rational -->
# Xu and Zhao's multiple-polylogarithm coefficients

## Verified locator

DOI: 10.48550/arXiv.2609.11072
Source URL: https://arxiv.org/html/2609.11072v1
Version 1, equations (7)-(8), the constant term immediately following (8),
and Conjecture 1.3. The source HTML SHA256 is
`7fb0df703ba12b20b967a7a297c2d75e8a73408fb2a43f1c134256139883055f`.

For a nonempty positive composition $k=(k_1,\ldots,k_d)$, the source uses

$$
\operatorname{Li}_k(z)=\sum_{n_1>\cdots>n_d>0}
\frac{z^{n_1}}{n_1^{k_1}\cdots n_d^{k_d}},\qquad
F_k(z)=\frac{\operatorname{Li}_k(z)}{z^d}.
$$

The quotient is extended at zero. Its positive constant term is
$\prod_{i=1}^d(d+1-i)^{-k_i}$. Equation (8) defines ordinary coefficients
$C_n^{j;k;\ell}$ of $(1-z)^{-j}F_k(z)^{-\ell}$, without a factorial.
The admissibility condition is $k_1>1$.

Conjecture 1.3 quantifies over every positive composition and every
$\ell\ge1$: $C_n^{0;k;\ell}<0$ eventually. For each fixed $j\ge1$ it asks
for $C_n^{j;k;\ell}>0$ eventually, and, when $k_1>1$, the strict bound
$C_n^{j;k;\ell}>\binom{n+j-1}{n}/\zeta(k)^\ell$ eventually.
Thresholds can depend on $k,\ell,j$. The all-one compositions follow for
every $\ell\ge1$ from the all-one identity and Theorems 1.1 and 8.2.
Theorems 9.6 and 9.9 prove the depth-one and depth-two cases, respectively,
at $\ell=1$; Corollary 9.11 additionally proves depth one at $\ell=2$.
These parameter slices do not constitute the general conjecture.

## Exact formal correspondence

`head : PNat` and `tail : List PNat` encode every nonempty positive
composition; `depth tail = tail.length + 1`. `H tail N` sums the remaining
strict indices at most $N$. The normalized coefficient is
$H_{n+d-1}(\mathrm{tail})/(n+d)^{\mathrm{head}}$.
`StrictIndices` independently chooses each positive index below its
predecessor. `source_series` identifies its sum with `li`, proves the
exact zero order $d$, and identifies the constant with the recursive
minimal-tuple product `leading`.

The result `CompositionZeroFree.result` proves absolute convergence and
analyticity of the actual normalized series on $|z|<1$, its nonvanishing,
and analyticity and positive real part of the explicit extension
$Q(0)=d$, $Q(z)=z\operatorname{Li}'_k(z)/\operatorname{Li}_k(z)$ off zero.
`source_recurrences` proves both differential recurrences, including the
origin values; it never equates a nonzero removable value with total
division by zero.

`CompositionBoundary.result` supplies the admissible boundary bridge W03.
For every positive head greater than one and every positive-entry tail,
it proves summability of the frozen coefficients and of the independent
full family indexed by `(n : Nat) × StrictIndices tail.length n`.
Here the largest positive index is $n+1$, its exponent is the head, and
the remaining indices strictly decrease below it. The total `zeta` is
defined from that full family, not from the normalized coefficients.
The theorem identifies both sums, proves their strict positivity, and
proves that the actual frozen `normalized` function tends to this total
as real $r$ approaches one from below. Its explicit source quotient
identity holds at nonzero points of the unit disk.

The nested bound is $H_N(\mathrm{tail})\le H_N^{\mathrm{length(tail)}}$,
where the right-hand $H_N$ is the ordinary harmonic number. The logarithmic
bound and logarithm-power domination give an eventual majorant
$2^{\mathrm{length(tail)}}(n+1)^{-3/2}$ for the source series grouped by
largest index. The proof treats the empty tail and the vanishing finite
prefix exactly. Summability precedes every boundary-total and limit claim.

`CompositionSlit.result` constructs the actual branch on
$\Omega=\{z:1-z\in\mathrm{Complex.slitPlane}\}$. The empty word is one;
every nonempty branch is holomorphic on the full domain, vanishes at zero,
agrees with `strictNestedSeries` on the disk, commutes with conjugation,
and has exact zero order equal to its depth. Both differential recurrences
hold on the full domain, with derivative one at zero for a singleton word
and zero for greater depth. Nested induction uses segment primitives and
the removable `dslope`; disk agreement fixes the branch normalization.

`CompositionBanks.result` supplies the complete local Banks bridge for every
positive head, positive-entry tail and positive power $\ell$. For the actual
continued branch, put
$A(z)=(z^d/\operatorname{continued}_k(z))^\ell$, where $d$ is the depth.
The theorem produces $0<\rho<1$ such that the actual branch is nonzero on
$\Omega\cap\{|z-1|\le\rho\}$. On the full slit-domain filter at one, $A$
tends to $\zeta(k)^{-\ell}$ for an admissible head and to zero for leading
head one.

For the same $\rho$, jointly chosen upper and lower functions are continuous
on the closed upper and lower half-collars, agree with $A$ on their respective
intersections with $\Omega$, take the common endpoint value at one, and obey
the conjugation identity on the lower half-collar. For every real
$0<t\le\rho$, the upper boundary value at $1+t$ has strictly negative
imaginary part. The proof uses the actual branch throughout: source-weight
induction closes the admissible and leading-one remainder alternatives;
radial and angular integral identities transport the source estimates; and
local analytic representatives retain the ordinary-head derivative needed
for the strict sign.

`CompositionZeroFreeCollar.normalizedContinuation` is the actual
depth-normalized slit branch. At zero it is `CompositionDisk.normalized`; away
from zero it is
$\operatorname{continued}_k(z)/z^d$, with $d$ the composition depth.
`CompositionZeroFreeCollar.result` proves disk agreement and
`AnalyticOnNhd` on the full source domain $\Omega$. For each positive
composition it also produces one $R_0>1$ such that this actual normalized
continuation is nonzero throughout
$\Omega\cap\{|z|<R_0\}$.

The proof obtains unit-circle nonvanishing directly from the radial squared
norm. If $F(r)=\operatorname{continued}_k(r\zeta)$ and
$H(r)=|F(r)|^2$, then on the interior radial segment

$$
H'(r)=\frac{2}{r}|F(r)|^2\operatorname{Re}Q(r\zeta)>0,
$$

using the positive-real logarithmic derivative from
`CompositionZeroFree.result`. This route avoids taking an endpoint logarithm.
The actual Banks theorem at $\ell=1$ supplies the neighborhood of the missing
boundary point one. The union of that Banks ball with the open zero-free locus
in $\Omega$ contains the closed unit disk; compact thickening then supplies
$R_0=1+\delta$. This is a source-specific, composition-dependent collar, not
global slit-domain nonvanishing and not a composition-uniform radius.

These are intermediate disk, boundary, slit, local Banks and zero-free collar
results, not a resolution of Conjecture 1.3. No general power-log asymptotic is
asserted. The full Taylor/formal-inverse coefficient correspondence,
finite-contour sign transfer and all-$j$/$\ell$ assembly remain open. The
collar therefore supplies no coefficient-sign theorem. Solved-problem credit
is zero, and this auxiliary carries no `OpenProblemResolutionClaim`, novelty
claim or worldwide-priority claim. The preregistered target is
https://github.com/the-omega-institute/trureturing/issues/9372.

## Reuse and literature boundary

The frozen `AnalyticLogarithmicContinuation.scalar_series_analytic_unit_disk`
supplies scalar-series analyticity. Pinned Mathlib supplies weighted
geometric summability, differentiation of normally convergent series,
analytic orders, compact minimization and real derivatives of complex
paths. The classical integral-preservation argument is credited to
`D5/L/AnalyticClosure/miller1978starlike` and remains local in the source
disk consumer. The slit consumer uses the minimal attributed star-shaped
primitive from `D5/L/AnalyticClosure/li2026starprimitive`, keeping its proof
local and its exact upstream license in `CompositionContinuation.lean`.
No general primitive theorem is separately delivered.

The bounded supplied search found no exact all-composition Lean supplier.
The source's stated known cases and the supplied preregistration do not
establish worldwide unresolved status or priority. Exhaustive later
literature coverage is ASSUMED-UNVERIFIED; no originality claim is made.

For W03, pinned Mathlib at `db584cd6d46c92f209a44c0f1c829460d327499d`
supplies `harmonic_le_one_add_log`, `isLittleO_log_rpow_rpow_atTop`,
`Real.summable_nat_rpow`, `summable_sigma_of_nonneg`, and
`tendsto_tsum_of_dominated_convergence`. Public GitHub Lean-code searches
for `multiple zeta`, `multipleZeta`, `multizeta`, `multiZeta summable`,
and `nested harmonic` on 2026-09-22 found no exact convergence supplier
in the searched scope. The inspected
`google-deepmind/formal-conjectures@e5f428182a3ee32dde401eceb4a94ba0382e8434`
`FormalConjectures/Paper/ZagierMZV.lean` defines a grouped MZV and contains
conjecture statements but no general summability proof. The inspected
`ImperialCollegeLondon/AnnalsChallenge@e32eb1411db0d700ca874dd695aea92f78699db8`
positive-characteristic Zagier-Hoffman file concerns a different field
and has unproved theorem statements. Neither is imported or transplanted;
no third-party dependency or A17.2 port is introduced.
