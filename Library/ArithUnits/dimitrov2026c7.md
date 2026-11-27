---
bibkey: dimitrov2026c7
authors: S. I. Dimitrov
year: 2026
title: "Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III"
doi: null
url: https://arxiv.org/abs/2606.12484v1
claim: "Conjecture 7 is the full real Nesbitt lower bound for the kth powers of the entire pair sums phi+psi, phi+sigma and psi+sigma, for every natural n at least two and k at least one."
strata_touched:
  - D5/S3/Arith/Divisors/DimitrovPairSumC7
license: source-reference
triage: anchor
---

# The powered pair-sum lower bound

## Verified locator

https://arxiv.org/abs/2606.12484v1, Conjecture 7, PDF page 4; definitions on pages 1–2.
The primary HTML is https://arxiv.org/html/2606.12484v1#Thmconjecture7.

The variables are x=phi(n)+psi(n), y=phi(n)+sigma(n), z=psi(n)+sigma(n).
The full statement is

\[
\frac{x^k}{y^k+z^k}+\frac{y^k}{x^k+z^k}+\frac{z^k}{x^k+y^k}
\ge \frac{4n^{2k}+(n+1)^{2k}+n^k(n+1)^k}
{2(n^{2k}+n^k(n+1)^k)}.
\]

Here n and k are arbitrary natural numbers with n at least two and k at least one.
The entire pair sums are powered. All ratios are real. The function psi is Dedekind's
product over exact prime powers and sigma is the sum of all positive divisors.

Let $q=(n+1)/n$. Totient positivity and the public
`DimitrovLowerBoundsC4C5.psi_ge` and `sigma_ge_psi` give $0<x\le y$.
The ratio separation gives $q\le z/y$ and hence $qy\le z$.
Raising to $k$ gives $0<x^k\le y^k\le z^k$ and
$1\le q^k\le z^k/y^k$. Applying the opposite-gap Nesbitt bound with
$X=x^k$, $Y=y^k$, $Z=z^k$ and $s=q^k$ yields $q^k/2+2/(1+q^k)$.
Exact field normalization yields the displayed right side.
The source's prime case attains the displayed bound, with x=y=2n and z=2(n+1).

## Consumed Lean suppliers

The C7 result directly applies the first projections of the existing
`DimitrovPsiSigmaSeparation.separation` and `DimitrovNesbittOppositeGap.opposite_gap`.
Their sources are
[DimitrovPsiSigmaSeparation.lean](../../D5/S3/Arith/Divisors/DimitrovPsiSigmaSeparation.lean)
and [DimitrovNesbittOppositeGap.lean](../../D5/S3/Arith/Divisors/DimitrovNesbittOppositeGap.lean).
The imported C4/C5 development retains its source attribution to Michael Mazur's
`pro20541/dimitrov-conjectures-lean`, documented in the
[C4/C5 Library note](dimitrov2026c4c5.md), with the
[Apache-2.0 license](../../docs/reports/licenses/dimitrov-LICENSE.txt).

## Bounded source comparison

Part III Theorem 5 treats $k=1$. The Part IV statements
([DOI 10.3390/math14213935](https://doi.org/10.3390/math14213935)) and the
public Lean donor at
[`95809b59deefd8dfad81e398250aedd7e1aea3b3`](https://github.com/pro20541/dimitrov-conjectures-lean/tree/95809b59deefd8dfad81e398250aedd7e1aea3b3)
leave the full C7 assertion uncovered in the bounded comparison supplied in
[#30579](https://github.com/the-omega-institute/trureturing/issues/30579).
The Sándor–Gryszka statements (DOI 10.7546/nntdm.2025.31.2.361-369)
also concern separate inequalities.
