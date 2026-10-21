---
slug: petr-turek-2025-wreath-eigenvalue-coincidence
bibkey: petrturek2025wreath
doi: 10.48550/arXiv.2501.07269
url: https://arxiv.org/abs/2501.07269v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.result
---

# Two indexed wreath eigenvalues coincide

## Problem

Jan Petr and Pavel Turek, *The wreath matrix*, arXiv:2501.07269v2,
Question 5.5, page 16, ask:

> Are the eigenvalues $\lambda_1,\lambda_2,\ldots,\lambda_k$ from Theorem 1.5 all distinct?

The source and its formulas appear in the [Library note](../Library/GraphInvariants/petrturek2025wreath.md).
The preregistration is [#19058](https://github.com/the-omega-institute/trureturing/issues/19058).
The answer is negative: at $(n,k)=(14,5)$, the values indexed by $3$ and $5$
are both $17107200$.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Positive integers $k<n/2$ | Natural parameters, $0<k$ and $2k<n$ in `claim` | Exactly the positive strict-half range |
| $g=\gcd(n,k)$ | `Nat.gcd`; `Nat.Coprime n k` in `claim` | Coprime restriction; a counterexample here refutes the unrestricted question |
| Both cases of $\lambda_1$ in Theorem 1.5 | `lambdaOne` | Literal rational formula; natural division and factorial arguments |
| Formula for $2\leq l\leq k$ when $g=1$ | `lam` | Index one uses `lambdaOne`; other indices use the published finite sum |
| All indexed values are distinct | `claim` quantifies over two distinct members of `Finset.Icc 1 k` | The conclusion compares the formula values |
| Negative answer | `result` proves the negation of `claim` | Witness $(14,5,3,5)$ |

The formulas are total outside the admissible range, without a spectral assertion there.
The factorial arguments and the sum exponent use natural subtraction; the factor
$n-2k-1$ uses rational subtraction. The source's identification of the formulas
with the spectrum is a literature premise, not a Lean theorem in this module.

## Motivation

Theorem 1.5 assigns multiplicities to indexed components. Distinct indexed
components need not have distinct eigenvalue values. The question asks whether
the values nevertheless separate them.

## Gap

The literature screen recorded in #19058 covers arXiv:2501.07269v2, the companion
arXiv:2501.07277v2, Semantic Scholar, arXiv full-text search, MathDB,
`google-deepmind/formal-conjectures`, and the repository's existing problem records.
No answer was found in that searched scope. Petr's thesis, *Colourings, dominating sets and wreaths*, §6.7, Question 6.7.1,
also poses the question. Exhaustiveness of this screen
is `ASSUMED-UNVERIFIED`.

## Route

Normalize the two rational expressions at $(n,k)=(14,5)$. The private consumed
helpers `lam_14_5_3` and `lam_14_5_5` both establish the value $17107200$.
Applying the distinctness assertion to indices $3$ and $5$ contradicts that equality.
The proof uses pinned Mathlib and Lean core; it imports no D5 owner.

## Falsifier

A different source formula, an inadmissible witness, or unequal formula values
would invalidate this refutation. The witness satisfies $0<5$, $2\cdot5<14$,
$\gcd(14,5)=1$, and distinct indices $3,5\in[1,5]$. The matrix-spectrum
identification remains the published Theorem 1.5's contribution.

## Evidence

The canonical Lean source is
`D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.lean`.
Its only public theorem is `result`; the two normalization helpers are private
and used by it. Its `proof_shape` is `bind-only`, admitted as
`open-problem-resolution (#19058; Refuted)`, with certified-instance utility
refuting `claim`. There is no atom or coverage operation.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

[Pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/5ceac7c1a27dc65493859cc5b5bad0056ad11a83/docs/reports/petr-turek-2025-wreath-eigenvalue-collision).
The script is `check.py`, SHA-256
`b2ecd5f4dfc53db8f8a153a0a4a7066c427175772edb8f828c802cdb51890fae`.
Command: `OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 python3 check.py`;
exit code $0$, result PASS. Exact integer arithmetic supplies the formula values,
collision census and finite factorisation check. The four small matrix spectra
use floating point diagonalization rounded to integers; they are numerical
corroboration, not kernel spectral certificates.

## Triage

Tier 1 published named question; resolution Refuted. Literature completeness:
`ASSUMED-UNVERIFIED`. The following scopes distinguish kernel proof, prose
algebra, computation and open questions.

### What the settlement shows

**Kernel-checked.** `result` refutes coprime pairwise distinctness through the
collision at $(14,5)$; its private helpers certify both formula values as
$17107200$. The failure mechanism is equality of the values assigned to two
distinct indices. A single value therefore does not distinguish these components.

**Proved in prose, not formalized.** For integer $n\geq10$, put $F=(n-10)!$ and
$P_r=\prod_{t=1}^{r}(n-10+t)$, with $P_0=1$. Thus $(n-10+r)!=FP_r$.
Substitution of $k=5$ in the published factorial sum gives

$$
\frac{\lambda_3(n,5)}{F}
=-3600(n-11)P_2-60P_5
 +90(-120P_2+24P_3-6P_4+2P_5),
$$

$$
\frac{\lambda_5(n,5)}{F}
=-7200(n-11)-60P_5
 +120(-120+24P_1-6P_2+2P_3-P_4+P_5).
$$

Expanding the displayed finite products and collecting factors yields

$$
\frac{\lambda_3(n,5)}{F}
=60(n-10)(n-9)(n-8)(n-3)(2n-19),
$$

$$
\frac{\lambda_5(n,5)}{F}
=60(n-10)(n-9)(n-5)(n^2-13n+52).
$$

The difference of these two polynomials expands to

$$60n^5-2520n^4+40020n^3-295560n^2+979440n-1058400$$

and factors as

$$60(n-14)(n-10)(n-9)(n-7)(n-2).$$

Expansion of the factored polynomial has exactly these coefficients, so the
symbolic residual is zero. Consequently

$$
\lambda_3(n,5)-\lambda_5(n,5)
=60(n-10)!(n-2)(n-7)(n-9)(n-10)(n-14).
$$

This factorial algebra is valid for all integer $n\geq10$; the source's spectral
interpretation here requires $n\geq11$ and $\gcd(n,5)=1$.
All factors except $n-14$ are positive on that latter range. The only admissible
root is therefore $14$, and the nearest surviving pairwise statement is
$\lambda_3(n,5)\ne\lambda_5(n,5)$ if and only if $n\ne14$.
This argument concerns this pair only; it does not establish distinctness of
all other pairs.

**Computed.** The experiment gives
$(\lambda_1,\ldots,\lambda_5)=(304819200,68947200,17107200,25401600,17107200)$
at $(14,5)$, with indexed multiplicities $(1,77,273,637,1001)$.
The source's multiplicity rule therefore assigns the common value multiplicity
$273+1001=1274$; this last addition is prose arithmetic using the computed
binomial values. The exact census on $5\leq n<120$, $1\leq k<n$,
$2k<n$, $\gcd(n,k)=1$ finds precisely $(14,5)$ with indices $(3,5)$ and
$(103,50)$ with indices $(27,37)$. The experiment checks the factorisation
numerically for $11\leq n<200$ with $\gcd(n,5)=1$.
The four explicitly constructed matrices at $(5,2),(7,2),(7,3),(8,3)$ have
$12,360,360,2520$ wreaths respectively and their rounded spectra agree with the
published formula, including multiplicities.

**Source theorem boundary.** Theorem 1.5 expressly allows repeated values and
adds their multiplicities, so its statement is unchanged. The source's wreath
conjecture is not settled by this collision.

**Open.** Infinitely many coprime collisions; collisions when $\gcd(n,k)>1$;
classification of other pairs beyond the stated finite census; and the wreath
conjecture itself. No uniform extension of the census or small-spectrum
computations is asserted.

## ASSUMED-UNVERIFIED

Completeness of the literature screen is `ASSUMED-UNVERIFIED`; no worldwide
novelty or priority conclusion follows from its bounded searches.
The correspondence between the rational formulas and the actual matrix spectrum
is supplied by the source's Theorem 1.5 and has not been formalized here.
The uniform pairwise identity and classification above are prose algebra;
the census and small spectra are computations, not Lean theorems.
