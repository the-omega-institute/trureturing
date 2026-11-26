---
bibkey: durrett2019probability
authors: Rick Durrett
year: 2019
title: "Probability: Theory and Examples, Fifth Edition"
doi: 10.1017/9781108591034
url: https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf
claim: "Exercise 3.2.9 gives uniform CDF convergence; Theorems 3.2.9 and 4.6.3 support weak tests and first-moment truncation; Section 6.2 gives almost-everywhere ergodic averages with limit equal to the mean; Section 6.4 gives stationary subadditive-array limits."
strata_touched:
  - D5/S3/Analytic/Probability/UniformCDFConvergence
  - D5/S3/Analytic/Probability/FirstMomentWeakLimit
  - D5/S3/Analytic/Probability/BirkhoffPointwise
  - D5/S3/Analytic/Probability/BirkhoffCondexp
  - D5/S3/Analytic/Probability/BirkhoffBanachCondexp
  - D5/S3/Analytic/Probability/KingmanEstimates
  - D5/S3/Analytic/Probability/KingmanPointwise
license: citation-only
triage: anchor
---

# Probability: Theory and Examples

## Verified locator

DOI: 10.1017/9781108591034

Source: https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf

## Cited result

Exercise 3.2.9, printed page 124:

> If $F_n \Rightarrow F$ and $F$ is continuous then $\sup_x |F_n(x)-F(x)| \to 0$.

The delivered uniform-CDF theorem states the monotonicity, boundedness and tail
conditions explicitly. Its proof uses a finite compact cover and the two tails.
The characteristic-function corollary combines this result with Mathlib's
Lévy continuity theorem. The proof of Theorem 2.4.9, printed page 79, also
states the pointwise-to-uniform principle for nondecreasing functions.

## First-moment truncation

Section 4.6, printed pages 244–246, defines uniform integrability using
absolute first-moment tails. The proof of Theorem 4.6.3 on printed page 245
uses the continuous clamp
$\varphi_M(x)=\max(-M,\min(M,x))$ and the inequality
$|x-\varphi_M(x)|\leq |x|\mathbf{1}_{\{|x|>M\}}$.
Theorem 3.2.9 on printed page 119 characterizes weak convergence by bounded
continuous real tests. These are the classical ingredients for the
varying-law truncation argument; Theorem 4.6.3 itself assumes convergence
in probability and is not cited as a verbatim varying-law theorem.

`FirstMomentWeakLimit.tendsto_integral_displacement` applies this method to
Borel probability measures on the real plane. Weak convergence, integrable
coordinates for every law and its limit, and uniform absolute coordinate
tails imply convergence of the integral of $(y-x)h(x)$ for each bounded
continuous real $h$. The bounded continuous approximant is
$(\varphi_M(y)-\varphi_M(x))h(x)$, with the joint law unchanged. Its
sequence error is bounded by the sum of the coordinate tails times the
bound on $h$; dominated convergence controls its limit-law error. The Lean
proof directly uses pinned Mathlib bounded-continuous weak tests, Bochner
integral inequalities and dominated convergence. No source code is copied
from the book, and no originality claim is made.

## Real ergodic time averages

Section 6.2, printed pages 335–337, Theorem 6.2.1 and Lemma 6.2.2,
give the pointwise ergodic theorem and its maximal-ergodic ingredient.
Printed page 335 identifies the ergodic limit with the mean. For an
arbitrary measurable probability space, a measure-preserving pre-ergodic
map $T$ and each integrable real observable $g$, the local statement is

$$
\frac{1}{n}\sum_{j=0}^{n-1}g(T^j x)\longrightarrow\int g\,d\mu
\quad\text{for }\mu\text{-almost every }x.
$$

The book also treats the nonergodic conditional-expectation limit and
convergence in $L^1$. The local theorem asserts only the real ergodic
almost-everywhere conclusion. It requires no pointwise measurability of
$g$: an almost-everywhere equal measurable representative has the same
integral, and quasi-measure preservation transfers its time averages.
The zeroth average is canonically zero. The quantification retains every
measurable carrier and every integrable constant, including zero.

The book remains a citation-only mathematical source; no book code is
copied. The Lean proof source is separately attributed to
[facebookresearch/atlas-lean, MathlibExt/Dynamics/Ergodic/Birkhoff.lean](https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Dynamics/Ergodic/Birkhoff.lean),
revision `a60759060b5616df0d5775b42da4d337719feb32`, blob
`f74d3ac5012c0a72db00f494d14bf6bb7fcfdb9f`.
The source SHA-256 is
`20a939a70578ca91a268991ea4ba5310ca4c7110f605819305bdc5818d87e5c3`.
The original Meta Platforms copyright is retained in the Lean source.
The complete supplier license, including its intended-use preface, is
[atlas-LICENSE.txt](../../docs/reports/lovasz-suppliers/atlas-LICENSE.txt),
SHA-256 `fc78801eadec58b04e0d5cabe735eb6808e23f47b0cb92b89b55792019b54131`.
The adaptation uses the native namespace, private mathematical helpers,
Mathlib fixed-set iteration, and the canonical almost-everywhere transport
API. The proof applies the maximal integral inequality to invariant
rational divergence sets, uses ergodicity to make those sets null, and
combines the bounds for $g$ and $-g$ by order convergence. This is an
attributed source port with matching Lean and Mathlib pins, without an
originality claim or an added package dependency. An equivalent theorem
in the host-pinned library supplies the direct replacement for the port.

Concrete symbolic frequencies, context-dependent compositions,
joint-product moments, and entropy-production rates require their own
law, ergodicity, observable, integral and orbit-identification arguments.
The generic autonomous theorem does not supply those bridges.

## Invariant conditional-expectation limits

Theorem 6.2.1 also gives the nonergodic probability-space limit
E_mu[g | I], almost surely and in L1, where I is the invariant sigma-algebra.
`BirkhoffCondexp.birkhoff_conditional_expectation` proves both conclusions
for arbitrary finite measures, including zero, and arbitrary integrable real
inputs. It assumes measure preservation and does not assume ergodicity,
invertibility, boundedness, pointwise measurability of the input or a
standard-Borel carrier. The real integral of the absolute error tends to zero.

The almost-everywhere proof adapts
[Lua Viana Reis and Oliver Butterley's Pointwise.lean](https://github.com/lua-vr/mathlib4/blob/ebc0f703f74bec1576e2ca3b078fb173ba11039f/Mathlib/Dynamics/BirkhoffSum/Pointwise.lean),
the source of [Mathlib PR 42078](https://github.com/leanprover-community/mathlib4/pull/42078).
The source copyright is retained, and its complete supplier license is
[mathlib-PR42078-LICENSE.txt](../../docs/reports/licenses/birkhoff-condexp/mathlib-PR42078-LICENSE.txt),
SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
This source gives probability-space almost-everywhere convergence. The
finite-measure localization applies the existing maximal inequality to the
restricted invariant divergence set. For a nonnegative input, dominated
convergence of min(A_n,E_mu[g | I]) and equality of integrals yield L1
convergence; the positive and negative parts give the general real case.
This is a classical theorem with attributed proof reuse, without a new
package dependency or a claim of mathematical originality.

## Banach-valued conditional-expectation limits

`BirkhoffBanachCondexp.birkhoff_conditional_expectation` concerns an arbitrary
finite measure, including zero, and an integrable function with values in a
complete real normed space. The carrier and value types have independent
universes. Every finite average and every norm error against invariant
conditional expectation is integrable, including at time zero. The averages
converge almost everywhere in norm, and the integral of the norm error tends
to zero. No ergodicity, invertibility, global separability, reflexivity or
standard-Borel hypothesis is imposed.

Durrett's Section 6.2 is the scalar mathematical reference, rather than a
verbatim source for this Banach-valued statement. The Banach approximation
argument comes from the NormedAddCommGroup section of the same Reis--Butterley
PR 42078 source cited above, revision
`ebc0f703f74bec1576e2ca3b078fb173ba11039f`, source SHA-256
`ffa9688080e52c2cf2b7b87047605255f494bc695fb091c232d2651ff1063d6d`.
Its complete Apache-2.0 license is the existing
[mathlib-PR42078-LICENSE.txt](../../docs/reports/licenses/birkhoff-condexp/mathlib-PR42078-LICENSE.txt).
The source's probability-space scalar calls are replaced by direct applications
of `BirkhoffCondexp.birkhoff_conditional_expectation`; the finite-measure
exceptional-set estimate uses the same scalar norm-residual argument. Integrable
indicator functions times fixed vectors, addition, L1 closure and
almost-everywhere transport establish the pointwise Banach result.

The mean-convergence synthesis uses $d_n=\|A_n g-C\|$,
$r_n=|A_n\|g\|-c|$, $c=\mathbb E_\mu[\|g\|\mid I]$, and
$b=|c|+\|C\|$. The pointwise estimate $d_n\le r_n+b$ gives
$0\le F_n=\max(d_n-r_n,0)\le b$ and $F_n\le d_n$.
Every function in this estimate is integrable. The pointwise Banach limit
and dominated convergence give $\int F_n\to0$; the existing real L1 theorem
applied to $\|g\|$ gives $\int r_n\to0$. Integrating
$0\le d_n\le F_n+r_n$ yields the required L1 limit. This uses the pinned
Bochner dominated-convergence theorem directly, without a probability
normalization or a global dominating function for the original averages.
No mathematical originality or added package dependency is claimed.

## Nonnegative subadditive cocycles

Section 6.4, Theorem 6.4.1 on printed page 343, with proof on printed
pages 344–347, gives Liggett's version of Kingman's theorem for subadditive
arrays. It assumes subadditivity from time zero, stationarity of the
nonoverlapping blocks at each fixed block size, shift-independent laws
for the forward rows, integrability of the positive first increment and
a finite linear lower bound on the means. The book's formulation
also includes convergence in L1 and an infimum identity for the limiting
mean. Those conclusions require their own proof and are not part of the
local theorem.

`KingmanPointwise.kingman_subadditive` quantifies over every measurable
carrier and every finite measure, including zero. If T preserves that
measure, each real X(n) is integrable and nonnegative almost everywhere,
and X(m+n) is at most X(m)+X(n) composed with the mth iterate almost
everywhere, there exists an integrable real g, invariant almost everywhere,
to which X(n)/n converges almost everywhere. The original X(0) is arbitrary;
real division at zero is totalized. No pointwise measurability, probability,
positive total mass, ergodicity, invertibility or countability hypothesis
is added. The limit is neither asserted constant nor identified by an
infimum formula.

The proof uses Steele's adaptive greedy blocks, a stationary-tail estimate,
Fatou's lemma and the maximal ergodic inequality. Nonzero finite mass is
normalized internally; measurable representatives and a forward-invariant
full-measure set yield the everywhere cocycle. Only its internal zeroth
term is reset. The same g transfers back to the original measure without
scaling. Concrete stationary arrays require a realization by a common
measure-preserving shift and an identification with its cocycle. Matrix
products with signed logarithms require a signed reduction; first-passage
applications additionally need the actual environment, translation,
integrability and path correspondence. The generic theorem alone does
not establish these applications or their constant, L1 or infimum claims.

The classical sources include J. F. C. Kingman, “The ergodic theory of
subadditive stochastic processes,” Journal of the Royal Statistical Society
Series B 30 (1968), 499–510, DOI
[10.1111/j.2517-6161.1968.tb00749.x](https://doi.org/10.1111/j.2517-6161.1968.tb00749.x),
and J. M. Steele, “Kingman's subadditive ergodic theorem,” Annales de
l'Institut Henri Poincaré, Probabilités et Statistiques 25 (1989), 93–98.

The separate Lean code source is
[facebookresearch/atlas-lean, MathlibExt/Dynamics/Ergodic/Kingman.lean](https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Dynamics/Ergodic/Kingman.lean),
revision `a60759060b5616df0d5775b42da4d337719feb32`, SHA-256
`d7363bfb4d33d73517b93b75e361de0a8e0363f32350e25dd5ce1f6a21b2782c`.
The neighboring `KingmanSigned.exists_invariant_limit_of_nonneg` supplies
the broad finite-measure specification; the signed proof is not imported.
Both local modules retain the Meta Platforms copyright and refer to the
complete [supplier license](../../docs/reports/lovasz-suppliers/atlas-LICENSE.txt),
including its intended-use preface, SHA-256
`fc78801eadec58b04e0d5cabe735eb6808e23f47b0cb92b89b55792019b54131`.
This is a credited source adaptation with no originality claim. Matching
toolchain and Mathlib revisions do not themselves admit an external package.
The port is replaced by a direct invocation when an equivalent declaration
is present in the host-pinned Mathlib.
