---
bibkey: perellipintzsalerno1984shortintervals
authors: A. Perelli, J. Pintz and S. Salerno
year: 1984
title: Bombieri's theorem in short intervals
doi: null
url: https://www.numdam.org/item/ASNSP_1984_4_11_4_529_0/
claim: Theorem on printed p.530 and estimate (2) on p.529 give a uniform fixed-modulus short-interval estimate, including modulus 3; splitting longer intervals into blocks and removing prime powers supplies the actual Fibonacci affine tail's cumulative mass calibration. The original theorem is a literature input, not a Lean-verified result here.
strata_touched: []
license: citation-only
triage: anchor
---

# Fixed modulus in a uniform short-interval theorem

Perelli, Pintz and Salerno, *Bombieri's theorem in short intervals*, Annali della Scuola Normale Superiore di Pisa, Classe di Scienze, series 4, **11** (1984), no.4, 529–539. The [Numdam record](https://www.numdam.org/item/ASNSP_1984_4_11_4_529_0/) links the [original scan](https://www.numdam.org/item/ASNSP_1984_4_11_4_529_0.pdf). Estimate (2), its parameter definitions and the theorem were read directly on printed pp.529–530. This verifies the cited statement and its scope; it is not an independent audit of the complete proof or a Lean proof of that theorem.

The paper defines

$$
\psi(u,q;a)=\sum_{n\le u,\ n\equiv a\pmod q}\Lambda(n).
$$

Estimate (2) is

$$
\sum_{q\le Q}\max_{(a,q)=1}\max_{h\le y}\max_{x/2<z\le x}
\left|\psi(z+h,q;a)-\psi(z,q;a)-\frac h{\varphi(q)}\right|
\ll\frac y{(\log x)^A},
\tag{1}
$$

where $A>0$ is fixed, $y=x^\theta$ and $Q=x^\eta/(\log x)^B$. Here $\eta$ denotes the exponent printed as $\psi$ in the paper; it is not the Chebyshev function. The theorem on p.530 states that (1) holds for

$$
\theta>3/5,\qquad\eta\le\theta-1/2.
\tag{2}
$$

The constants and the logarithmic exponent $B$ may depend on the fixed parameters. The theorem is unconditional. Its maximum is over every stated starting point, every short length, and every reduced residue class. It is neither an almost-all statement nor only an ordinary-prime count.

Choose $\theta=2/3$ and $\eta=1/12$. Then $Q\to\infty$, so fixed $q=3$ is included eventually. Every term in the modulus sum is nonnegative, and $\varphi(3)=2$; therefore (1) supplies

$$
\left|\psi(z+h,3;1)-\psi(z,3;1)-h/2\right|
\ll_A\frac{x^{2/3}}{(\log x)^A}
\tag{3}
$$

uniformly for $x/2<z\le x$ and $0\le h\le x^{2/3}$.

## Longer tails and the prime-only function

Put

$$
\vartheta_1(t)=\sum_{p\le t,\ p\equiv1\pmod3}\log p.
$$

For $0\le v\le m/2$, split $(m-v,m]$ into at most $v/m^{2/3}+1$ adjacent blocks of length at most $m^{2/3}$. If the first start is exactly $m/2$, first remove a segment of length at most one; its error is $O(\log m)$, and all subsequent starts are strictly larger than $m/2$. Apply (3) with $x=m$ to each remaining block and add the errors. This gives an error $O_A((v+m^{2/3})/(\log m)^A)$ for the von Mangoldt sum, together with the harmless initial-segment error.

Remove prime powers only after the blocks have been combined. Their total contribution over the whole interval is at most

$$
\sum_{k\ge2}\sum_{p^k\le m}\log p=O(\sqrt m(\log m)^2).
$$

Thus

$$
\left|\vartheta_1(m)-\vartheta_1(m-v)-v/2\right|
\ll_A\frac{v+m^{2/3}}{(\log m)^A}+\sqrt m(\log m)^2,
\quad 0\le v\le m/2.
\tag{4}
$$

This is a paper application of the cited theorem and elementary telescoping and prime-power bounds. The prime-power loss is charged once, rather than once per block. The lower endpoint is strict, exactly as in the displayed theta difference.

At $\rho=m^{1/4}$, set $A=1$. Formula (4) gives nonnegative functions $\epsilon_m,\delta_m\to0$ such that

$$
\left|\vartheta_1(m)-\vartheta_1(m-v)-v/2\right|
\le\epsilon_m v+\delta_m\rho^3.
\tag{5}
$$

One may take, for a sufficiently large fixed $C$ and all sufficiently large $m$,

$$
\epsilon_m=\frac C{\log m},\qquad
\delta_m=C\left(\frac{m^{-1/12}}{\log m}
+m^{-1/4}(\log m)^2\right).
$$

In particular, if $D/\rho^3\to d>0$, the supremum of the error in (5) over $0\le v\le D$ is $o(D)$. This supplies the specified mod-3 short-edge law used in FIB §307. It fills a literature-input gap; it does not improve a prime-distribution theorem.

The actual source implications are in FIB §309: finite normalized removed mass forces a corresponding width and first distance moment, and those inputs feed the already defined centered Robin response. This paragraph identifies a consumer rather than treating the source application as a new prime estimate. The exact Lean transport uses the cumulative calibration as an explicit hypothesis; the PPS theorem and the analytic derivation of (5) are not Lean-verified here. No drift rate, common-baseline sign or RH conclusion follows from (1)–(5).
