---
bibkey: dimitrovlazarova2026part4c3
authors: Stoyan Dimitrov and Meglena Lazarova
year: 2026
title: "Lower Bounds on Expressions Depending on the Functions φ(n), ψ(n) and σ(n): Part 4"
doi: 10.3390/math14213935
url: https://mdpi-res.com/d_attachment/mathematics/mathematics-14-03935/article_deploy/mathematics-14-03935.pdf
claim: "Section 4, Conjecture 3 asks for the complete powered pair-sum quotient inequality for all n ≥ 2 and k ≥ 1."
strata_touched:
  - D5/S3/Arith/Divisors/DimitrovPartIVC3
license: CC-BY-4.0
triage: anchor
---

# Part 4, Conjecture 3

## Source and locator

Stoyan Dimitrov and Meglena Lazarova, *Mathematics* **14**(21) (2026), 3935,
DOI: https://doi.org/10.3390/math14213935, Section 4, page 13, Conjecture 3.
Definitions are in Section 1, pages 1–2. The publisher PDF has 14 pages,
3219707 bytes and SHA-256
`21c972599612cd12ac9354219cc73daa316fcdaff7548ed9be3ee381632a0d3a`.
The corresponding XML has 422720 bytes and SHA-256
`2a449be47b8bdecfcccf66158a6bf48b31637512d938e29bc4f5ff880e2507f9`;
MathML mm199–201 contains the full formula. The article is licensed CC BY 4.0.
These source identities and their agreement are attributed to the completed
independent source verification in
[the mathematical evidence](https://github.com/the-omega-institute/trureturing/issues/30625#issuecomment-6887043322).

## Exact statement and correspondence

For every natural $n\geq2$ and $k\geq1$,

$$
\frac{(\varphi(n)+\psi(n))^{3k}+(\psi(n)+\sigma(n))^{3k}+(\varphi(n)+\sigma(n))^{3k}}
{(\varphi(n)+\psi(n))^k(\psi(n)+\sigma(n))^k(\varphi(n)+\sigma(n))^k}
\geq\frac{2n^{3k}+(n+1)^{3k}}{n^{2k}(n+1)^k}.
$$

Euler's totient, Dedekind psi and the sum of positive divisors are the actual
arithmetic functions. Each pair sum is powered as a whole; powers have natural
exponents and quotients are real. There are no prime-only, squarefree,
finite-range or extra parameter restrictions.

`Nat.totient` supplies Euler's totient.
`OeisA344695GcdSigmaPsiPrimes.psi_prod` identifies the existing `psi n` with
$\prod_{p^e\parallel n}p^{e-1}(p+1)$ for nonzero $n$.
`ArithmeticFunction.sigma_one_apply` identifies `ArithmeticFunction.sigma 1 n`
with the sum of positive divisors. The source's Theorem 3, equation (11),
proves only $k=1$; it is not the full Conjecture 3.

## Application

Put $a=\varphi(n)$, $b=\psi(n)$, $c=\sigma(n)$ and $q=(n+1)/n$.
The existing arithmetic bounds give $0<a\leq n-1$, $n+1\leq b\leq c$ and
$q(a+b)\leq2b$. The pair-gap inequality gives
$q^2(a+b)(a+c)\leq(b+c)^2$. Raising this to $k$ gives
$Q^2xy\leq z^2$ for $x=(a+b)^k$, $y=(a+c)^k$, $z=(b+c)^k$ and $Q=q^k\geq1$.
With $u=\sqrt{xy}$, the cubic envelope uses $x^3+y^3\geq2u^3$ and
$z/u\geq Q$ to give
$(x^3+y^3+z^3)/(xyz)\geq Q^2+2/Q$. Exact field normalization recovers the
original quotient, including all three whole pair-sum powers.

This is an application of existing arithmetic order bounds and elementary real
inequalities. No new analytic inequality or priority is claimed. The imported
`DimitrovLowerBoundsC4C5` development retains its existing supplier attribution
and [license account](dimitrov2026c4c5.md); no supplier code is copied.

## Literature boundary

The bounded qualification in [issue 30625](https://github.com/the-omega-institute/trureturing/issues/30625)
reported current VOR metadata with no notices, all-state C3 ownership readings
3/3 and DOI readings 8/8, covering eight relevant bodies and seventeen comments.
It found no exact prior full settlement in that scope. The public Part III C3
supplier `pro20541/dimitrov-conjectures-lean` addresses a different assertion.
C3-specific arXiv access returned 429; blocked and unindexed channels and global
priority remain unverified. This is no worldwide absence or originality claim.
The direct publisher download in the publication check returned HTTP 403;
source-formula verification is the attributed completed check above.
