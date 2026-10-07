---
slug: garcia-volcic-2025-nc-hunter-kernel-rigidity
bibkey: garciavolcic2025hunter
doi: 10.1090/proc/17480
url: https://arxiv.org/abs/2503.12376v2
triage: theorem
motivation_gids:
  - D5/S3/Analytic/Hunter/NCHunterKernelRigidity.result
---

# Garcia–Volčič Conjecture 4.5

## Problem

S. R. Garcia and J. Volčič, “A noncommutative generalization of Hunter's
positivity theorem”, arXiv:2503.12376v2, Conjecture 4.5, states:

> Let $n,d\ge 2$. For all tuples of hermitian operators $X_1,\dots,X_n$ on a Hilbert space,
> $\ker(H_{2d}(X_1,\dots,X_n)-\mu_{n,d}(X_1^{2d}+\cdots+X_n^{2d}))=\ker X_1\cap\cdots\cap\ker X_n$.

The settled assertion is exactly the bounded complex Hilbert-space statement
preregistered in [#13735](https://github.com/the-omega-institute/trureturing/issues/13735).
Here $H_k(X)$ is the ordered word sum, with each word $w$ weighted by
$\prod_i m_i(w)!/k!$. This is the reciprocal cardinality of the word's
abelianization fibre. The constant $\mu_{n,d}$ retains the source's $n=1$,
odd-degree and even-degree branches.

## Motivation

`D5/S3/Analytic/Hunter/NCHunterKernelRigidity.result` proves the kernel
identity for all $n,d\ge2$, every complete complex inner-product space, and
every bounded complex-linear self-adjoint tuple. The conclusion is equality
of kernel submodules, without an additional positivity or certificate
hypothesis. `NCHunterPositivity.sharp_positivity` supplies the source's
operator lower bound for $n>0,d>0$.

## Gap

The source proves the case $n=d=2$ in Example 4.4 and leaves the general
kernel assertion as Conjecture 4.5. The Tier-1 preregistration records the
source statement, quantifiers, MathDB entry, and citing-work search.
Brazitikos–Pandis, arXiv:2512.12254, addresses scalar Hunter positivity;
arXiv:2606.12866 cites the positivity theorem. These checked sources supply
no settlement of the kernel assertion. This is a bounded literature search,
not an exhaustive claim about unpublished work.

## Route

The urn recursion gives an inverse-column formula and representers satisfying
$GR=E$. Together with the pure-word block bound, this yields
$G-\mu M\succeq0$. The residual's quadratic form is the factorial Gram
form of length-$d$ words applied to a vector.

A vector in the residual kernel has zero form, so every mixed-word row
vanishes. A positive definite shifted factorial kernel forces the grouped
word coefficients to vanish. Even and odd degrees use separate contractions.
Self-adjoint operators and their positive powers have the same kernel; this
converts the word relations into the common operator kernel. Every
positive-length word vanishes on that common kernel, giving the reverse
inclusion.

## Falsifier

A falsifier is a bounded self-adjoint tuple on a complex Hilbert space, with
$n,d\ge2$, and a vector belonging to exactly one side of the displayed
kernel equality. `GVHunter.result` excludes this within the stated carrier.
Unbounded operators and their domains do not belong to this assertion.

## Evidence

The Lean modules are `D5/S3/Analytic/Hunter/NCHunterPositivity.lean` and
`D5/S3/Analytic/Hunter/NCHunterKernelRigidity.lean`; their mirrors are under
`Blueprint/D5/S3/Analytic/Hunter/`. The settling Scribe node records an
`OpenProblemResolutionClaim` with resolution `Proved` for this dossier.

The positivity module has `admission_basis: escape-witness`, with
`urn_closed_form` on the live path through `inverse_word_sum`,
`representer_certificate`, `sharp_gram_posSemidef` and `sharp_positivity`.
The settling module has `admission_basis: open-problem-resolution` (#13735;
Proved). Consumed bind-only helpers organize the proof and supply no
independent admission basis.

The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

### What the settlement shows

- **Proved:** the preregistered bounded complex Hilbert-space kernel equality,
  by `GVHunter.result`. The decisive mechanism is the positive residual Gram
  form, mixed-row vanishing and strictly positive shifted factorial kernel.
  The argument has no finite-dimensional restriction.
- **Proved, direct consequence:** equality in the operator lower bound occurs
  precisely at the zero tuple. If the residual operator is zero, its kernel
  is the whole space; `GVHunter.result` then makes each $\ker X_i$ the whole
  space, hence each $X_i=0$. The reverse implication follows by evaluating
  the positive-degree word sum at the zero tuple. This consequence is not an
  additional public declaration in either module.
- **Open, outside the formal conclusion:** the source's finite-dimensional,
  tuple-dependent $\varepsilon>0$ improvement
  $H_{2d}(X)\succeq(\mu_{n,d}+\varepsilon)\sum_i X_i^{2d}$.
  The kernel identity supplies the common nullspace needed by the spectral
  argument, but a finite-dimensional spectral comparison is not formalized
  here. No uniform improvement over all tuples is asserted.
- **Open, outside the statement:** unbounded self-adjoint operators. Products,
  sums and kernels require common-domain hypotheses absent from the bounded
  operator encoding; no unbounded extension is asserted.
- **Open, untouched:** Conjecture 4.6, complete positivity of $G_{n,d}$,
  meaning a factorization $S^*S$ with entrywise nonnegative $S$.
  Positive semidefiniteness alone does not supply this factorization. The
  source's proposed sum-of-Hermitian-squares representations with nonnegative
  coefficients therefore remain outside this settlement.
- **Open, outside the formal conclusion:** optimality of $\mu_{n,d}$.
  Theorem 1.1(ii) attributes sharpness to the source; these modules prove
  positivity at that constant and the kernel equality, not optimality.
- **Open as an originality claim; literature-attested identity:** the scalar
  shifted factorial Gram identity is an application of Chu–Vandermonde,
  NIST DLMF equation 15.4.24, https://dlmf.nist.gov/15.4.E24 . Expanding
  $F(-a,-b;g+1;1)=(g+1+b)_a/(g+1)_a$ and multiplying by
  $(a+g)!(b+g)!/g!$ gives the scalar identity; products over letters give
  the finite Gram representation. Neither that scalar identity nor the
  product construction is claimed original. The new formal proof uses this
  representation to settle the preregistered kernel assertion.
- **Proved, scope of dependence:** the bounded version of the source's first
  consequence follows from the settled kernel identity. The finite-dimensional
  $\varepsilon$ consequence retains its unformalized spectral step. The
  source's existing positivity theorem is formalized, while Conjecture 4.6
  and its nonnegative-coefficient consequences are not settled.

## ASSUMED-UNVERIFIED

The literature inventory is limited to the source, the preregistration's
MathDB and citing-work checks, and the reviewed search scope. Absence of
unpublished settlements is not certified. Failed upstream-only probes show
failure of the tested direct routes only; they do not establish impossibility
of every alternative upstream route.
