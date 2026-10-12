---
slug: negari-2610-01860-high-degree-constant-sharpness
bibkey: negari2026gaussianapproximation
doi: 10.48550/arXiv.2610.01860
url: https://arxiv.org/abs/2610.01860v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.result
---

# Sharpness of the high-degree fermionic Gaussian constants

## Problem

A.-R. Negari, F. Salek, Z. Zimborás, A. Harrow, P. Hayden and J. Eisert,
*Approximation theorems for fermionic Gaussian states*, arXiv:2610.01860v1
(2026), Section VI, printed page 26, state:

> It remains open, however, whether the constants in the resulting high-degree energy and free-energy estimates are optimal, since their derivation also uses edge averaging, Cauchy–Schwarz, and only the operator-norm normalization of the interactions.

The source estimates are Theorem III.1, equation (44), and Theorem III.5,
equation (79), both with prefactor $\sqrt{2m/D}$. The formal claim asks whether,
for every $m\ge1$, every $c<1$ and every degree cutoff $D_0$, a finite
regular graph and admissible quadratic fermionic edge interactions attain the
energy value $\sqrt{2m/D}$ and have a finite positive inverse temperature whose
free-energy gap is larger than $c\sqrt{2m/D}$.

## Motivation

Issue [#15127](https://github.com/the-omega-institute/trureturing/issues/15127)
preregistered this Tier 1 named question, its quantified statement and the
literature screen before implementation. The motivation declaration is the
frozen Lean result
`D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.result`.

## Gap

The source explicitly leaves optimality of the two downstream constants open.
The bounded search recorded in issue #15127 found only arXiv:2610.01860v1 and
found no settlement in the searched title, identifier, author, sharpness,
MathDB, formal-conjecture and repository scopes. The citation indexes and
MathDB endpoint were incomplete, so worldwide absence and priority remain
ASSUMED-UNVERIFIED.

## Route

For $q=2m$, choose a power-of-two conference order $s$ with
$2m(s-1)\ge D_0$ and use the Cartesian product of `q` complete graphs on
$s$ vertices. The recursive skew conference matrices satisfy
$C^2=-(s-1)I$ and provide real, self-adjoint, norm-one quadratic edge
interactions. The coordinate Hamiltonian is a normalized sum over all edges.

The coordinate skew identity gives a flat Clifford spectrum. A joint minus
sign projector is a trace-one physical ground density, so the physical ground
energy is $-\sqrt{2m/D}$. Site parity conjugation changes the sign of each edge
term and therefore makes every physical product energy zero; the energy gap is the stated bound.
The kernel-verified route (`D5/S3/Quantum/Fermionic/GibbsProductGap.gibbs_product_free_bound`) proves an entropy-budget
lower bound. The maximally mixed marginals and the exact log-cosh formula are derived below and are not kernel-verified. Fibre parity makes
each one-site Gibbs marginal maximally mixed. The Gibbs product entropy is bounded by the Fock dimension, and a finite
positive beta chosen from `c` gives the strict free-gap inequality.

## Falsifier

The settlement would fail if the conference matrices did not have the claimed
skew-square and off-diagonal properties, if the coordinate graph were not
regular with the stated degree and edge count, if the joint-sign projection
were not a physical trace-one ground density, or if site parity did not force
all physical product energies to zero. It would also fail if the Gibbs-marginal
and entropy estimates did not yield a finite positive beta for every $c<1$.
The result does not assert equality at finite beta, sharpness at every degree,
or sharpness at a fixed beta independent of system size.

## Evidence

The Lean module is
`D5/S3/Quantum/Fermionic/GaussianHighDegreeSharpness.lean`. Its public
settlement is `result : claim`; the definitions expose the source claim and
the coordinate witness family. The result and its supporting modules compile
with the pinned toolchain. The axiom closure of every public declaration is
contained in `{propext, Classical.choice, Quot.sound}`. The Scribe result node carries
`OpenProblemResolutionClaim` with `ResolutionKind.Proved` for this dossier.

## Triage

`theorem`; Tier 1 external named open problem, preregistered in issue #15127
before implementation. Resolution is `Proved` and the module admission basis
is `open-problem-resolution (#15127; Proved)`. The coordinate conference
family, joint ground sector, parity cancellation and finite-beta entropy bound
are the live proof content. Four-slot escape audit is unfinished: [issue #15194](https://github.com/the-omega-institute/trureturing/issues/15194).

### What the settlement shows

- **Kernel-verified mechanism:** `ConferenceMatrices.conference_properties`
  constructs skew conference matrices with $C_s^2=-(s-1)I$;
  `CoordinateCliffordSpectrum.coordinate_skew_flat` proves the coordinate
  skew-square identity on the product of $2m$ copies of $K_s$.
  `CoordinateAverage.coordinate_average` identifies the actual edge average.
  `JointSignProjectors.joint_sign_projection`,
  `CliffordGroundDensity.paired_clifford_ground` and
  `FlatCliffordGround.flat_clifford_ground` give the physical ground density
  with energy $-\sqrt{2m/D}$; `PhysicalSiteProducts.physical_products_zero`
  gives zero energy for every parity-preserving product.
- **Proved in this module:** the energy constant is attained uniformly for
  every positive mode count and every degree cutoff by the coordinate family;
  the physical product energy is zero and the ground energy is exactly the
  negative bound.
- **Proved in this module:** for every real $c<1$, a finite positive inverse
  temperature gives a free-energy gap strictly larger than `c` times the same
  bound. Thus the prefactor one cannot be lowered uniformly in degree in either
  estimate.
- **Kernel-verified:** `D5/S3/Quantum/Fermionic/GibbsProductGap.gibbs_product_free_bound` proves the entropy-budget
  lower bound used by the settlement. The maximally mixed marginals and the
  exact log-cosh formula are derived below and are not kernel-verified.
- **Proved by the paper argument below, not kernel-verified:** for the witness family, let $L=m|V|$
  and $\alpha=1/(L\sqrt{s-1})$. Then
  $Z=(2\cosh(\beta\alpha))^L$ and
  $F_{\rm gap}(\beta)=(L/\beta)\log\cosh(\beta/(L\sqrt{s-1}))$. Since
  $e^x/2<\cosh x<e^x$ for $x>0$,
  $a-L\log2/\beta<F_{\rm gap}(\beta)<a$ with
  $a=1/\sqrt{s-1}=\sqrt{2m/D}$. Hence $F_{\rm gap}\to a$ as $\beta\to\infty$, and
  $F_{\rm gap}<a$ at every finite $\beta>0$, so the bound is not attained on this
  family.
- **Proved by source inspection and the displayed algebra:** the two source parity phases differ for odd mode count. `main.tex:429–433`
  gives $P=i^m\prod\gamma$ and `main.tex:439–445` gives $(-i)^m\prod\gamma$; they
  differ by $(-1)^m$. For one mode, $c=\left(\begin{smallmatrix}0&1\\0&0\end{smallmatrix}\right)$, so $\gamma_1\gamma_2=\operatorname{diag}(-i,i)$: $i\gamma_1\gamma_2=\operatorname{diag}(1,-1)$ agrees with $\exp(i\pi c^\dagger c)$, while $-i\gamma_1\gamma_2$ is its negative.
  Both give the same commutation and physical-state conditions, so the settled
  statement is unaffected. The Lean carrier's parity is $e^{i\pi\widehat N}$ by the
  definition; its occupation-basis form is `FockMajoranaCarrier.numberParity_eq_diagonal`.
- **Proved boundary:** the argument extends to all power-of-two conference
  orders and their unbounded degree sequence. It does not prove equality at
  finite beta or at every integer degree.
- **Open:** sharpness at a degree outside the power-of-two conference sequence
  requires a construction or obstruction for that degree; sharpness at one beta
  independent of system size requires a uniform beta bound across the witness
  family; finite-beta equality requires a state attaining the entropy-budget
  bound together with equality in the displayed logarithmic squeeze; and a
  pointwise-in-degree optimality theorem requires a construction or obstruction
  for every sufficiently large integer degree. These are distinct missing
  inputs, and none is supplied by the current Lean result.
- **Source consequence:** any later use of either published estimate may retain
  prefactor one as a uniform sharp constant, while claims of finite-beta
  equality or pointwise-in-degree optimality require the missing inputs above.

- **Open:** sharpening edge averaging or Cauchy–Schwarz for nonuniform spectra. The flat-spectrum construction proves uniform sharpness but supplies no refined estimate for those spectra.

### Exact free-energy formula (paper argument)

This argument applies to the finite coordinate witnesses with $m\ge1$,
$s=2^{r+1}$, $D=2m(s-1)$, $n=s^{2m}$, $L=mn$ and $\beta>0$.
It proves the marginal and formula items in ordinary mathematics; these
items have no separate Lean declaration in this delivery.

The skew conference and coordinate identities give a real skew one-particle
matrix with square $-(s-1)I$ and zero blocks within each physical site.
Orthogonal pairing puts the actual averaged quadratic Hamiltonian in the form
$H=\alpha\sum_{j=1}^L B_j$, where $\alpha=1/(L\sqrt{s-1})$ and the
$B_j$ are commuting Hermitian involutions formed from paired Majoranas.
The Clifford relations and the joint-sign projector argument give one
rank-one sector for each $\varepsilon\in\{-1,1\}^L$. Consequently

$$
Z_\beta=\sum_{\varepsilon\in\{-1,1\}^L}
 e^{-\beta\alpha\sum_j\varepsilon_j}
 =(2\cosh(\beta\alpha))^L.
$$

In this paired basis the Gibbs density is a product of the $L$ two-level
thermal densities. Its Majorana covariance is a scalar multiple of the
orthogonally paired skew matrix, with scalar $\tanh(\beta\alpha)$.
Transport back to the site basis preserves the zero blocks within each site.
The Gibbs density is even and Gaussian: its odd moments vanish and its even
moments obey Wick's formula. Thus every nonconstant Majorana monomial within
one site has zero expectation. These monomials, together with the identity,
form an orthogonal basis of the site's full matrix algebra. Its trace-one
marginal is therefore $I/2^m$, and the product of all marginals is
$\sigma_\beta=I/2^L$.

The quadratic Hamiltonian has trace zero, so
$F_\beta(\sigma_\beta)=-L\log2/\beta$.
For the Gibbs density, the identity
$\log\rho_\beta=-\beta H-(\log Z_\beta)I$ yields
$F_\beta(\rho_\beta)=-(\log Z_\beta)/\beta$. Hence

$$
F_{\rm gap}(\beta)=\frac{L}{\beta}
 \log\cosh\left(\frac{\beta}{L\sqrt{s-1}}\right).
$$

For $x>0$, $e^x/2<\cosh x<e^x$. With
$a=1/\sqrt{s-1}=\sqrt{2m/D}$ this gives
$a-L\log2/\beta<F_{\rm gap}(\beta)<a$ and therefore
$\lim_{\beta\to\infty}F_{\rm gap}(\beta)=a$.
Every fixed finite witness has this limit; the argument makes no claim of
uniformity when the number of sites also grows.

### Experiment evidence boundary

The supplied experiment location is
[the pinned report directory](https://github.com/the-omega-institute/trureturing-experiments/tree/602ec65402d492351ebc19230b04caa93001cda8/docs/reports/negari-2610-01860-high-degree-constant-sharpness).
The exact-path check
`git -C /Users/auric/trureturing-experiments ls-tree -r --name-only 602ec65402d492351ebc19230b04caa93001cda8 docs/reports/negari-2610-01860-high-degree-constant-sharpness`
exits 0 with zero files. The numerical program, its SHA-256 and its tested
scope are ASSUMED-UNVERIFIED; no numerical result is claimed. The mechanism
and free-energy items above rely on the stated proofs.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources and queries recorded in issue
#15127 and the cited Library note; it does not establish exhaustive absence of
later or unindexed work. The semantic identification between the source's
fermionic conventions and the Lean carrier is supported by the formal source
and mirror but remains a fidelity obligation separate from kernel truth.
