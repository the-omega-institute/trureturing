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

## Nonnegative subadditive cocycles

Section 6.4, Theorem 6.4.1 on printed page 343, with proof on printed
pages 344–347, treats stationary subadditive arrays. The book's formulation
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
