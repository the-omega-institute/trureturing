---
bibkey: tao2021stripfourier
authors: Terence Tao
year: 2021
title: 246B, Notes 2 — Some connections with the Fourier transform
doi: null
url: https://terrytao.wordpress.com/2021/01/23/246b-notes-2-some-connections-with-the-fourier-transform/
claim: Proposition 3(i)–(ii) transports horizontal holomorphic shifts to Fourier weights and gives exponential Fourier decay under uniform integrable polynomial decay on smaller closed strips.
strata_touched:
  - D5/S3/Analytic/Fourier
license: citation-only
triage: anchor
---

# Holomorphic strips and Fourier transport

Proposition 3 assumes a holomorphic function on $|\operatorname{Im}z|<a$,
$a>0$. On each smaller closed strip $|y|\le b<a$ it requires

$$
|f(x+iy)|\le\frac{C_b}{1+|x|^\eta},\qquad \eta>1.
$$

With the source convention
$\widehat f(\xi)=\int f(x)e^{-2\pi i x\xi}\,dx$, part (i) gives
$\widehat{f(\cdot+w)}(\xi)=e^{2\pi i w\xi}\widehat f(\xi)$.
Part (ii) gives $|\widehat f(\xi)|\le C_{b,\eta}e^{-2\pi b|\xi|}$.
The integrable strip decay is a hypothesis; holomorphy alone is not
the stated theorem. Parts (iii)–(v) concern partial/full inversion and
Poisson summation under the same hypotheses.

For the unitary angular-frequency convention used in the
[original-theta root supplier](../../docs/reports/theta-mixed-matrix/strip-root.md),
part (i) reads
$\widehat{f(\cdot+iy)}(\xi)=e^{-y\xi}\widehat f(\xi)$.
Plancherel then expresses the two horizontal-line squared norms as
$\int2\cosh(2b\xi)|\widehat f(\xi)|^2d\xi$ when those norms are finite.
This is a normalization and norm application of the published method,
not a new Fourier theorem or a Lean certification.

The source does not establish nonvanishing of the original theta kernel,
its square-root branch or the quantitative line envelopes. Those are
separate model-specific inputs in the linked supplier. Exact sharp
Fourier projections preserve the weighted $L^2$ norm structure, while
they can lose rapid spatial decay; the supplier checks the integrable
decay again after multiplication by $s$.

The public HTML containing Proposition 3 was inspected at the source
URL. No implementation code or full source document is copied here.
