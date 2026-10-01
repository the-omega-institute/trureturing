---
slug: ostrovskii-shcherbakov-conjecture-62-refutation
bibkey: ostrovskii2025amplitude
doi: 10.48550/arXiv.2508.13554
url: https://arxiv.org/abs/2508.13554v2
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.result
---

# Refutation of Ostrovskii–Shcherbakov Conjecture 6.2

## Problem

Ostrovskii and Shcherbakov, *Amplitude maximization in stable systems, Schur
positivity, and some conjectures on polynomial interpolation*, arXiv:2508.13554v2
[math.CV], state on page 15:

> For all $0 \le k < n \le t$ and self-conjugate $z_{1:n} \in \mathbb{D}^n$,
> $|Q_{t,n,k}(z_{1:n} + 1_n)| \le 1$. Moreover, if the grid additionally
> satisfies $\Re(z_{1:n}) \in \mathbb{R}^n_+$, then
> $|s_{(t-n|n-k-1)}(z_{1:n})| \le \binom{t}{n}
> |e_{n-k}(z_{1:n})|$.

The same paper labels this Conjecture 6.2 equivalent to Conjecture 6.1.
The formal claim retains both clauses, the self-conjugacy conditions, the closed
unit disk, and the natural inequalities k<n<=t.

## Motivation

The conjecture is a 2025 externally named open problem. Issue #11514
preregistered its source, full quantifiers, witness, tier and bounded literature
check before implementation. The Library note
Library/Analytic/ostrovskii2025amplitude.md records the arXiv locator,
DOI and the source definitions of self-conjugacy, Q and the tableau Schur
functions.

## Gap

The preregistered literature check found arXiv:2508.13554v2 to be the latest
version and found no subsequent settlement in the checked arXiv author and
abstract searches, MathDB problem records, Semantic Scholar citation record,
or the repository search. The one citing work reachable in that check concerns
a difference-equation part of the source; its treatment of Section 6 remains
ASSUMED-UNVERIFIED. These bounded readings do not establish exhaustive
worldwide literature coverage or publication priority.

## Route

For the hook shape $\lambda=(a+1,1^b)$, the Schur polynomial is the sum of
tableau monomials over semistandard Young tableaux of shape $\lambda$.
Regrouping first by content and then by permutations of that content gives
the source's Kostka expansion $s_\lambda=\sum_\mu K_{\lambda\mu}m_\mu$:
$K_{\lambda\mu}$ counts tableaux of shape $\lambda$ and content $\mu$, and
$m_\mu$ sums the distinct monomials with that exponent partition.
Specializing to the finite alphabet `Fin n` relabels $1,\ldots,n$ by
$0,\ldots,n-1$ and sets the remaining variables to zero. Thus

$$
s_\lambda(z)=\sum_{T\in\operatorname{SSYT}_n(\lambda)}
\prod_{u\in\lambda}z_{T(u)}
=\sum_{\mu:\,\ell(\mu)\le n}K_{\lambda\mu}m_\mu(z).
$$

In `schurHook`, a tableau has corner `c`, an arm multiset of cardinality
$a$ with entries at least `c`, and a leg subset of cardinality $b$ with
entries strictly greater than `c`. Sorting the arm and leg gives the weak
row and strict column, counting each tableau once. This is the finite
specialization of the source's expansion described in
Library/Analytic/ostrovskii2025amplitude.md. The other Lean definitions
specialize the elementary and complete homogeneous symmetric sums to
`Fin n`, then define the alternating ratio Q and the conjunction of the
two conjectured bounds.

For the refutation choose $(t,n,k)=(3,2,1)$ and
$z=(-9/10+(2/5)i,-9/10-(2/5)i)$. The entries are a conjugate pair, have
squared norm $97/100$, and have no real values. After adding the pointwise
numeral $1$, the finite sums give
$e_1=1/5$, $s_{(0|0)}=1/5$ and $s_{(1|0)}=-13/100$.
The resulting ratio is $Q(3,2,1,z+1)=73/60$, whose norm is greater than one.

The second-clause witness recorded in #11514 also has $(t,n,k)=(3,2,1)$,
but uses $z=(1/10+(9/10)i,1/10-(9/10)i)$. It is a nonreal conjugate pair,
with $|z_i|^2=41/50\le1$ and $\Re z_i=1/10\ge0$. Here
$e_1(z)=1/5$, $e_2(z)=41/50$, and the one-row hook gives
$s_{(1|0)}(z)=h_2(z)=e_1(z)^2-e_2(z)=-39/50$. Hence

$$
|s_{(1|0)}(z)|=|h_2(z)|=39/50>3/5=\binom{3}{2}|e_1(z)|.
$$

[computed: python3 `fractions.Fraction`, complex multiplication on rational
real/imaginary pairs; squared norms $41/50$, $h_2=-39/50$, right-hand side
$3/5$, strict gap $9/50$.] This is exact arithmetic evidence for failure
of the second clause. The single Lean settlement uses the first-clause
witness and does not separately formalize this second calculation.

## Falsifier

A proof of the formal universal claim would falsify this refutation. The
witness calculation would also fail if the pair were outside the closed disk,
were not self-conjugate, or produced a denominator different from the stated
nonzero value. The second conjectured clause is retained in the claim but is
not needed for this counterexample.

## Evidence

The canonical source is
D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation.lean.
Its public declarations are the definitions selfConjugate, e, h, schurHook,
Q, claim, and the theorem result : ¬ claim.
The freeze state pins statement identity
sha256:0db8847f194177b39d4133cf0557f6dce02ca1edeaf96dcf8f8ff837cb6be821;
the Freeze event is
sha256:30bb2e0d7cd063200d27cd082fd37251a325cd7f73d4a59ed2bd283e07c698d5.
The event has no prerequisite frozen node. The result is kernel-checked with
the standard axioms propext, Classical.choice and Quot.sound; no new axiom,
sorry or native_decide is used.

## Triage

Tier 1 externally named conjecture; resolution refuted. The failure mechanism
is the complex conjugate pair in the unit disk: after the shift, the imaginary
parts make the degree-two complete homogeneous value negative, so the first
Schur-ratio bound exceeds one. The public result is bind-only finite evaluation
under the open-problem-resolution admission basis; the settlement is the
new information that this named conjecture has a concrete counterexample.

### What the settlement shows

- **Proved:** the first clause fails at $(t,n,k)=(3,2,1)$ for the displayed
  self-conjugate pair.
- **Computed:** the second clause fails at the same parameters for
  $z=(1/10\pm(9/10)i)$, including its nonnegative-real-part premise,
  by the exact rational calculation above. This is not a second Lean
  settlement.
- **Open:** no universal corrected bound, no maximal admissible radius, and no
  proof for all real self-conjugate grids is claimed here. The t=n identity
  and the k=0 neighboring cases are not formalized or independently computed
  by this delivery.
- **Boundary:** the source's equivalence transfers the refutation to its
  Conjecture 6.1 reading; source results that use Conjecture 6.2 as an
  assumption require a replacement hypothesis or a restricted domain.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish that no later publication
settles the conjecture. The cited difference-equation paper's treatment of
Section 6 was not verified. The source's analytic equivalence to Conjecture 6.1
is quoted from the paper rather than formalized in this module.
