---
slug: fucci-stanfill-2024-poschl-teller-coefficients
bibkey: fucci2024poschlteller
doi: 10.1007/s00023-025-01587-7
url: https://arxiv.org/abs/2411.17860v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.result
---

# Refutation of Fucci–Stanfill coefficient nonvanishing

## Problem

G. Fucci and J. Stanfill, *The exotic structure of the spectral ζ-function
for the Schrödinger operator with Pöschl–Teller potential*, arXiv:2411.17860v1,
Appendix B, Remark B.3, state:

> From calculations performed for particular choices of $p$, $q$, and $\beta$,
> we in fact conjecture that all of the $g_{m,j}(p/q,\beta)$ are nonzero for
> the choices of $p,\ q,$ and $\beta$ considered here.

The source range is relatively prime integers $0<p<q$ and
$\beta\in(0,\pi)\setminus\{\pi/2\}$. The admissible indices satisfy
$lp+kq=m$ for $l,k\in\mathbb N_0$, and $0\le j\le k_m$, where $k_m$
is the largest feasible $k$. The journal locator is Annales Henri Poincaré
27 (2026), 2073–2116, DOI 10.1007/s00023-025-01587-7.

## Motivation

Issue [#15069](https://github.com/the-omega-institute/trureturing/issues/15069)
preregisters the verbatim conjecture, full quantifiers, Tier 1 classification,
literature readings and binding coefficient conventions. The admission basis
is `open-problem-resolution (#15069; Refuted)`.
The source definitions and locators are recorded in
[the Library note](../Library/Eigenstructure/fucci2024poschlteller.md).

## Gap

The preregistration's bounded literature screen reports no settlement in the
source, the checked citing papers, MathDB or the repository. The checked
citation set comprises arXiv:2407.04847, 2508.15699, 2509.14513,
2604.10115 and 2606.04225. The sources of 2508.15699 and 2604.10115
were searched for these coefficients, genericity and nonvanishing; the other
three relevance assessments are seat-reported. These readings establish the
searched scope, not exhaustive publication priority.

## Route

The indeterminate $T$ represents
$\sin\alpha/[-\cos\alpha+\sin\alpha(\gamma_E+\ln(z^{1/2})-\ln2-i\pi/2)]$.
The generalized Bernoulli generating function is DLMF 24.16.1,
$\big(t/(e^t-1)\big)^a e^{xt}=\sum_n B_n^{(a)}(x)t^n/n!$.
The Lean definitions retain the source's $C_m$, $E_k$, $G_k$,
$\mathcal E_j$, $\mathcal P_k$, $\bar{\mathcal P}_k$, $\Omega_k$ and
formal logarithm. With $x=z^{-1/q}$, $\mathcal S_m$ is the coefficient
of $x^{m+p}$ in $\log(1+\sum_{k\ge0}\Omega_k x^{p+kq})$, and
$g_{m,j}$ is its coefficient of $T^j$.

For $(p,q)=(2,3)$, degree five of this logarithm receives the linear
coefficient $\Omega_1$. The square has no degree-five term, since its
nonzero input degrees below five can only be two. Every power of order
at least three is divisible by $x^6$. Thus $\mathcal S_3=\Omega_1$.
Since $G_0=1$, $[T]\mathcal P_1(y)=E_1(y)/2$. The identity
$E_1(1-y)=E_1(y)$ cancels the two contributions at
$y_\pm=(1\pm\nu)/2$. Hence $g_{3,1}(2/3,\beta)=0$ for every real
$\beta$. The admissible choice $\beta=\pi/4$, $m=3$, $j=1$ refutes
the universal claim.

## Falsifier

The refutation would fail if the coefficient convention differed from the
source, the tuple $(2,3,\pi/4,3,1)$ failed a conjecture hypothesis, or its
computed coefficient were nonzero. The literal source convention, positive
coprime parameters, interval membership, excluded angle, admissibility and
order bound are all part of the compiled claim and its refutation.

## Evidence

[The Lean module](../D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.lean)
has the public theorem `result : ¬ claim`. Every private lemma is a
consumed bind-only helper; direct frozen D5 dependencies and the escape
witness are both absent. The axiom closure of every public declaration is
contained in `{propext, Classical.choice, Quot.sound}`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The experiment entry is
[`docs/reports/fucci-stanfill-2024-poschl-teller-coefficients/check.py`](https://github.com/the-omega-institute/trureturing-experiments/blob/0e97aabf0e76c8d278d29e9a3b66ff6a2207e66e/docs/reports/fucci-stanfill-2024-poschl-teller-coefficients/check.py).
Run `python3 check.py` in that directory with SymPy. The implementation
reading has exit code 0 and final line `ALL_OK`; the script SHA-256 is
`50fcf972778131ed652e02d4b8998daea3dcb0f7e17a7042835b3ddded112909`.
Its exact scope is every coprime $0<p<q\le8$, with symbolic $\Omega_0$
and arbitrary symbolic higher coefficients $\Omega_2,\Omega_3,\Omega_4$.
It rebuilds $\mathcal P_1$ from the general definitions, verifies reflection
symmetry in both versions of (B.21), and checks $g_{q,1}=0$,
independence from higher $\Omega_k$, and the stated constant coefficient
for $p\ge2$. This is computed evidence, not a Lean proof of the family.

## Triage

Tier 1 external named conjecture; resolution **Refuted**. The new
information is failure of universal coefficient nonvanishing, with an
explicit admissible witness and a reflection mechanism. The settlement is
bind-only by proof shape and admitted through open-problem-resolution.

### What the settlement shows

- **Proved in this module:** the tuple $(p,q,\beta,m,j)=(2,3,\pi/4,3,1)$
  refutes the conjecture. Private lemmas `S_23`, `P_one_coeff_one`,
  `E_one_reflection`, `Omega_one_coeff_one` and `g_23_vanish` establish
  the logarithmic isolation and reflection cancellation. The private
  vanishing lemma applies to every real $\beta$ at $(p,q)=(2,3)$.
- **Proved in prose, computed for $q\le8$: the general index mechanism.**
  A term of the $n$th logarithmic power has degree $np+kq$ with $n\ge1$
  and $k\ge0$. At $m=q$, it obeys $(n-1)p+kq=q$. For $p\ge2$,
  coprimality excludes $k=0$, while $k\ge2$ is impossible; therefore
  $(n,k)=(1,1)$ and $\mathcal S_q=\Omega_1$. For $p=1$ there is also
  $(n,k)=(q+1,0)$; its contribution is
  $(-1)^{q+2}\Omega_0^{q+1}/(q+1)$, independent of $T$.
- **Proved in prose, computed for $q\le8$: the family.** For every
  coprime $0<p<q$ and $\beta\ne\pi/2$ in the source range,
  $g_{q,1}(p/q,\beta)=0$. Indeed,
  $\Omega_1=\Omega_0[\mathcal P_1(y_+)-\mathcal P_1(y_-)]$,
  $[T]\mathcal P_1=E_1/2$, and $y_+=1-y_-$ with
  $E_1(y)=4y-4y^2-2/3$ reflection symmetric. The extra $p=1$ term
  has no $T$ coefficient. Moreover $1\le k_q$ because $(l,k)=(0,1)$
  is feasible. This prose proof is uniform; the computation is limited
  to $q\le8$ and the Lean proof to the stated witness.
- **Proved in prose, computed for $q\le8$: the surviving constant term.**
  The general definitions give
  $[T^0]\mathcal P_1(y)=\frac23 y(2y^2-3y+1)$. Substitution of
  $y_\pm$ gives their difference $\nu(\nu^2-1)/3$. Hence for $p\ge2$,
  $g_{q,0}=\Omega_0\nu(\nu^2-1)/3\ne0$ in the source range. Here
  $0<\nu<1$, the gamma factors are finite and nonzero, the exponential
  and real power are nonzero, and $\cot\beta\ne0$. The source's pole
  contribution remains present at this order while its $j=1$ branch
  contribution is absent. At $(p,q)=(2,3)$ the constant is
  $-10\Omega_0/81$. This nonzeroness is not a Lean theorem in this module.
- **Proved in prose: consequence for the source.** Its assumption that
  all $g_{m,j}$ are nonzero has no instance in the considered parameter
  range. Thus the all-nonzero generic case used for Sections 3.1.1 and
  3.1.2 never occurs. In the source's expansion the branch contribution
  at $m=q$, $j=1$ is absent. This conclusion uses the source's analytic
  interpretation; spectral continuation itself is not formalized here.
- **Computed: (B.21) misprint.** The general definitions give
  $-(6y^2-6y+1)/3$ as the $T$ coefficient, whereas (B.21) prints
  $-(6y^2-6y-1)/3$. The printed coefficient exceeds the defined one
  by $2/3$. Both are reflection symmetric, so the refutation holds
  with either. Evidence is the pinned experiment above, `python3 check.py`,
  exit 0, `ALL_OK`, with the stated SHA-256.
- **Open:** classify the other vanishing $g_{m,j}$, including whether
  $g_{m,k_m}$ vanishes whenever its top-order term comes from a single
  reflection-symmetric product. The displayed cancellation does not
  prove that classification.
- **Open:** determine whether a corrected genericity hypothesis, such
  as $j\ge2$ or $m\notin q\mathbb N$, restores the conclusions of
  Sections 3.1.1–3.1.2. Neither restriction is asserted sufficient.

## ASSUMED-UNVERIFIED

The source and literature checks attributed to the orchestrator are the
bounded readings in #15069; exhaustive absence of prior settlement and
publication priority are not verified here. The report that the journal
retains Remark B.3 is supplied literature evidence. The family and analytic
consequences have the prose scope above, rather than kernel certification
beyond the single settling module.
