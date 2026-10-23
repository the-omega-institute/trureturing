---
bibkey: unkown2026primesquaremoment
authors: unkown
year: 2026
title: Uniform dominance of a prime-square term in an Euler-product moment
doi: null
url: https://mathoverflow.net/questions/516091/uniform-dominance-of-a-prime-square-term-in-an-euler-product-moment
claim: "The question asks whether the complete infinite valuation-factor moment admits a uniform logarithmic prime-square approximation for large real s and primes in a moving exponential window."
strata_touched:
  - D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation
license: CC-BY-SA-4.0
triage: anchor
---

# Prime-square dominance in a local Euler-product moment

The author display name is **unkown**, as spelled in the primary MathOverflow record. The source is question 516091, revision 1, GUID `5D544532-802E-47EE-9240-92FCF941D961`, at [its revision history](https://mathoverflow.net/posts/516091/revisions). Its creation timestamp is `2026-10-16T00:49:02Z`. The question text and the definitions reproduced below are attributed to that author under [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/). The proof and explicit sufficient delta interval below are the repository's mathematical contribution, rather than an attribution of a proof to the question's author.

The exact source definitions are

$$
e_p(0)=1,\qquad e_p(a)=\frac{p+3a(p-1)}{2[p+a(p-1)]}\quad(a\ge1),
$$

$$
m_p(s)=\left(1-\frac1p\right)\sum_{a=0}^{\infty}\frac{e_p(a)^s}{p^a},
\qquad s>0,\qquad c=\frac12\log\frac76,\qquad P=e^{cs}.
$$

The question asks for

$$
\log m_p(s)=\log\left(1+\frac{P^2}{p^2}\right)+o(1)
$$

uniformly over primes $p\equiv1\pmod4$ with $P^{1-\delta}<p\le BP$, for sufficiently small fixed $\delta>0$ and fixed $B>2$. It proposes $g(a)=(3a+1)/(2(a+1))$ and a slope $c_3<c$ controlling $\log g(a)$ for all $a\ge3$.

Its final question is:

> Does this argument establish the stated uniform approximation? In particular, is the bound on the entire sum over $a\ge3$ sufficient, or is additional uniform control required when taking logarithms of the local factors?

The explicit sufficient choice is $c_3=\log(5/4)/3$ and $0<\delta<1-c_3/c$. The induction $g(a)^3\le(5/4)^a$ controls the entire infinite tail. A relative comparison of the exponent-two term, and the prefactor bound, then justify the logarithms. The complete statement and derivation are in the [problem dossier](../../Problems/mathoverflow-516091-prime-square-local-moment.md) and [Blueprint](../../Blueprint/D5/S3/Analytic/SeriesInequalities/PrimeSquareMomentApproximation.md).

## Verified locator

The primary source is [MathOverflow question 516091](https://mathoverflow.net/questions/516091/uniform-dominance-of-a-prime-square-term-in-an-euler-product-moment), revision 1, GUID `5D544532-802E-47EE-9240-92FCF941D961`.

## Bounded source and overlap evidence

The primary StackExchange question, revisions, answers and comments endpoints were read at `2026-10-18T14:15:28.628834Z`. They returned one revision, zero answers and zero comments. A complete exact-phrase MathOverflow search for `"Euler-product moment"` returned only this question. These readings establish that bounded observation, not global priority.

The supplied ordinary qualification also inspected twelve version-pinned arXiv summaries and material statements/proofs in two official TeX sources:

- Emmanuel Kowalski, *Averages of Euler products, distribution of singular series and the ubiquity of Poisson distribution*, [arXiv:0805.4682v2](https://arxiv.org/abs/0805.4682v2), Section 2, proposition `pr-euler`. This compares a global random-product expectation to a product of local expectations under explicit summable tail controls. It does not supply the present rational local factors or their moving-prime, large-real-moment error.
- Julio Andrade and Asmaa Shamesaldeen, *The Moments and statistical Distribution of Class number of Primes over Function Fields*, [arXiv:2010.14941v1](https://arxiv.org/abs/2010.14941v1), random-product subsection, lemma `E=EP` and theorem `lumley theorem`. Its local factors are $(1-W_P/|P|)^{-1}$ with independent equiprobable signs. Its complex-moment average over function-field characters is different from this valuation-factor moment.

Neither inspected statement establishes this exact approximation. The two papers were not read in their entirety, and the other ten papers were screened only through returned summaries. Literature completeness and global priority are `ASSUMED-UNVERIFIED`. No claim of exhaustive clearance or author acceptance is made. These comparison papers are not Lean dependencies.
