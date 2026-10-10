---
bibkey: lichtmanmartinpomerance2019primeraces
authors: Jared Duker Lichtman; Greg Martin; Carl Pomerance
year: 2019
title: Primes in prime number races
doi: 10.1090/proc/14569
url: https://arxiv.org/abs/1809.03033v2
claim: Theorem 2.1 transfers fixed-level logarithmic densities to prime samples under explicit stability and distribution hypotheses; the Mertens application assumes RH and LI and supplies no finite growing-level Robin count.
strata_touched: []
license: citation-only
triage: anchor
---

# Fixed-level densities and actual prime samples

The inspected primary is the [versioned HTML](https://arxiv.org/html/1809.03033v2)
of arXiv:1809.03033v2, revised 5 January 2019. The abstract metadata
lists *Proceedings of the American Mathematical Society* 147 (2019),
3743–3757 and the DOI above. The journal edition and complete proof
were not independently audited. All theorem locators below refer to
the inspected manuscript. This note cites the results and does not
rerun the paper's prime computations or claim Lean certification.

## The two hypotheses of the general sampling theorem

For $f:[1,\infty)\to\mathbb R$ and fixed $a\in\mathbb R$, put
$\mathcal M_a(f)=\{x:f(x)>a\}$. Theorem 2.1, §2, assumes both:

- For each pair of fixed real levels $a>b$, there is $x_0(a,b)$
  such that $x\ge x_0$ and $f(x)>a$ imply $f(z)>b$ for every
  $z\in[x,x+x^{1/3}]$. The same condition holds for $-f$.
- Every $\mathcal M_a(f)$ has logarithmic density, and
  $a\mapsto\delta(\mathcal M_a(f))$ is continuous.

Then, for each fixed $a$, the relative prime density exists and equals
the continuous logarithmic density:

$$
\lim_{Y\to\infty}\frac1{\log Y}
\sum_{\substack{p\le Y\\ f(p)>a}}\frac{\log p}{p}
=\lim_{Y\to\infty}\frac1{\log Y}
\int_{\substack{1\le x\le Y\\ f(x)>a}}\frac{dx}{x}.
$$

This is the source's $\delta^*$, not an unweighted finite interval
count. Section 1 distinguishes it from the $1/p$-weighted density
normalized by $\log\log Y$: existence of $\delta^*$ implies equality
of those limits, but the converse is not asserted. The general
theorem has no RH hypothesis; its two hypotheses must still be
proved for any proposed input function.

## The Mertens application keeps RH and LI

Section 4 uses the strict prime-product endpoint

$$
E_M(x)=\sqrt x\log x
\left[\log\prod_{q<x}(1-1/q)^{-1}-\log\log x-\gamma\right].
$$

Theorem 4.1 assumes RH and the paper's linear independence
hypothesis for positive zeta-zero ordinates. It gives relative
logarithmic density $1-\Delta$ for the primes with $E_M(p)>0$,
where $\Delta$ is the Rubinstein–Sarnak prime-race density recalled
in equation (1.2). The local stability and conditional limiting
distribution used there are existing arguments, not new project
proofs.

## The missing finite-scale and actual-source comparison

The [actual CA counting application](stadlmann2022meansquaregaps.md)
needs an unweighted count in a dyadic prime range at a threshold
$\delta X^{-\eta}$, with a particular fixed $0<\eta<1/2$ supplied
by the selected source. On the $\sqrt x\log x$ normalization, this
is a growing level of order $X^{1/2-\eta}\log X$, rather than a
fixed $a$. The theorem supplies neither a convergence rate nor a
uniform growing-level estimate in this range.

The project's Nicolas surplus uses a weak prime-product endpoint
and denominator $\log\vartheta(p)$, while $E_M$ uses $q<p$ and
denominator $\log p$. The complete post-event Robin quantity also
retains every exponent numerator and the actual size $\log C_{\tau_p}$.
These are distinct readouts. A finite joint comparison must pay all
of their differences before transporting a density or count.

Thus the general theorem is a reusable sampling result under its
stated hypotheses; its RH-and-LI Mertens application is not an
unconditional supplier for the selected Robin source. No signed
finite-scale count, full Robin tail estimate or RH proof is obtained.
