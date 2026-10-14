---
bibkey: yamada2023arbitraryintervals
authors: Tomohiro Yamada
year: 2023
title: Explicit improvements of the Brun-Titchmarsh theorem for arbitrary intervals
doi: null
url: https://arxiv.org/pdf/2312.16090v1
claim: Theorem 2 gives an explicit uniform prime count for arbitrary real intervals; its modulus-one case supplies the finite thin-layer capacity in the existing CA-benefit application.
strata_touched: []
license: citation-only
triage: anchor
---

# A uniform finite interval input for the CA benefit

The inspected source is the [preprint arXiv:2312.16090v1](https://arxiv.org/pdf/2312.16090v1),
Theorem 2, equation (13), printed p.3. For relatively prime integers
$k\ge1$ and $b$, and every real $x>0$, $y>k$, it states

$$
\pi(x+y;k,b)-\pi(x;k,b)
<\frac{2y}{\varphi(k)(\log(y/k)+0.8601)}.
$$

In particular $k=1$ gives a bound at every interval centre, without an
existential large-length threshold. The application uses only the weaker
$2y/\log y$ consequence. The preprint's proof, numerical calculations,
and full general-modulus claim have not been independently verified or
formalized in Lean. No strongest-available or publication-priority claim
is made here.

The [existing benefit application](../ArithSums/erdosnicolas1975repartition.md#an-explicit-thin-layer-capacity-for-the-same-arbitrary-host)
uses it at $x=(1-2h)a>0$, $y=4ha\ge4\sqrt a$, for
$a\ge16$ and $a^{-1/2}\le h\le1/4$. Every counted prime keeps its own
logarithmic weight. Smaller $h$ is bounded by monotonicity; the complete
higher-layer mass is paid separately by the cited Dusart estimate.
This supplies an explicit version of an already used square-root-buffer
mechanism, not a new short-interval theorem or a signed Robin estimate.
