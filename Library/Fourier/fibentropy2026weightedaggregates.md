---
bibkey: fibentropy2026weightedaggregates
authors: trureturing research synthesis
year: 2026
title: Fixed-modulus weighted aggregates, source entropy and moving product windows
doi: null
url: https://arxiv.org/abs/2607.00592v1
claim: "Smooth-number character estimates impose conductor, smoothness and coefficient conditions not established for the current Fibonacci target. Mellin inversion preserves moving product windows and exposes a weighted spectral interface, but supplies no bound at the Robin budget."
strata_touched: []
license: citation-only
triage: anchor
---

# Fixed-modulus weighted aggregates and the retained arithmetic target

This note distinguishes checked classical and recent source results from their proposed use in [the FIB theory](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md). Sections 223–224 there contain the full increment-law Rényi profile and its entropy and collision consequences. Section 225 combines the maximum source atom with short-factor multiplicative energy to obstruct every Hölder separation of the full-law residue majorant. Those are paper derivations without Lean verification or an originality claim. Their proofs are not duplicated here.

The [Bohr phase-box note](fibcharacter2026bohrbarrier.md) records the pointwise character-decay obstruction and exact moving-interval identity; the [complementary-divisor note](../ArithSums/fibcomplement2026weightedresidues.md) records the actual arithmetic kernel. This note specifies the conditions for importing aggregate literature and a Mellin interface that retains the product window. None of these interfaces establishes the needed actual FIB Robin budget.

## 1. The actual scale and the object requiring an estimate

Keep the prime-index family

$$
V=F_r,\quad I=[\lceil V/10\rceil,\lfloor V/5\rfloor]\cap\mathbb Z,
\quad N_g=1+Vg,\quad A=\min N_g,\quad X=\max N_g,
$$
$$
y=\log A,\quad \ell=\log y,\quad s=y\ell,
\quad R=y/\ell^2,\quad H=e^{aR},\quad D=X/H,
\quad Q=\varphi(V).
$$
Here $a>b_2=\pi^2/6$ is fixed, $\log X=y+O(1)$, $\log Q=y/2+O(1)$, and $H^k<V$ eventually for every fixed $k$. The lower-cutoff candidate construction uses smoothness $w=s+1\asymp y\ell$. For every actual $1\le h<H$, the core scale $x\asymp X/h$ satisfies $\log x/\log V\to2$, while $w\asymp\log x\log\log x$.

These smoothness parameters describe a proposed smooth-core decomposition. The full increment law below is not supported on smooth integers; applying a smooth-support theorem also requires a valid decomposition and control of its complementary contribution.

The actual increment law is

$$
Z(n)=\sigma(n)/n,\qquad b_s(p^j)=Z(p^j)^s-Z(p^{j-1})^s,
\quad b_s(1)=1,
$$
$$
U_p(s)=1+\sum_{j\ge1}\frac{b_s(p^j)}{p^j},\quad
U(s)=\prod_p U_p(s),\quad
\mu_s(d)=\frac{b_s(d)}{dU(s)}.
$$
Let $\eta_s$ be this probability conditioned on $(d,V)=1$, and $\nu_s$ its pushforward to $G=(\mathbb Z/V)^\times$. These are full, unbounded-source probabilities. A restriction to $d\le X$, an actual hit, or a cap on the same product $dh$ is a different law.

For nonnegative $a(d)$, the actual large-divisor sum is

$$
S_a=\sum_{\substack{d>D\\\exists g\in I:\ d\mid N_g}}a(d)
=\frac1Q\sum_{\chi\bmod V}
 \sum_{\substack{1\le h<H\\(h,V)=1}}\chi(h)A_\chi(J_h),
$$
$$
J_h=(D,X]\cap[A/h,X/h]\cap\mathbb N,
\qquad A_\chi(J)=\sum_{d\in J,(d,V)=1}a(d)\chi(d).
\tag{1}
$$
The actual kernel has $a(d)=(d/X)\mu_s(d)=b_s(d)/(XU(s))$. A hit divisor is a unit, and $d>D>V>|I|-1$ eventually, so it hits at most one actual integer. This is why the pair identity counts the original sum exactly. The principal term and the signed nonprincipal aggregate must both be retained. No uniform pointwise character-decay claim is used below.

## 2. Primary-source results: what transfers and what does not

### 2.1 An arbitrary-weight smooth large sieve, but at much smaller conductors

S. Drappeau, A. Granville and X. Shao, *Smooth-supported multiplicative functions in arithmetic progressions beyond the $x^{1/2}$-barrier*, arXiv **1704.04831v2**, updated 2017-06-15.

Original: [arXiv text, version 2](https://arxiv.org/html/1704.04831v2). Checked **§5, Theorem 5.1**, and **§5.3, Theorem 5.6**.

Theorem 5.1 gives absolute constants $C,c>0$ such that, for sufficiently large $(\log x)^C\le Y\le x$ and

$$
Q_0=\min\{Y^c,\exp(c\log x/\log\log x)\},
$$

one has, for **arbitrary complex coefficients** $a_n$,

$$
\sum_{q\le Q_0}\sum_{\chi\bmod q}^{*}
 \left|\sum_{n\le x,P^+(n)\le Y}a_n\chi(n)\right|^2
\ll \Psi(x,Y)\sum_{n\le x,P^+(n)\le Y}|a_n|^2.
\tag{2}
$$
The star means primitive characters. This arbitrary-coefficient clause is useful: growing coefficients are not excluded from (2) merely because they grow; their actual squared norm appears on the right. However, the FIB modulus $V=x^{1/2+o(1)}$ is much larger than $Y^c$ when $Y\asymp\log x\log\log x$. Moreover, the theorem does not promise $C\le1$, so its smoothness hypothesis cannot simply be asserted at the current cutoff.

Theorem 5.6 permits $Q_0=x^c$, but inserts $q^{-1/2}$ before the character sum and still requires $Y\ge(\log x)^C$. Neither the unspecified small exponent $c$, nor the conductor weight, can be dropped. Extracting one fixed modulus from either nonnegative sum is legitimate if all its hypotheses hold; it does not eliminate these losses or provide cancellation between its characters. The target also includes imprimitive characters at $V$; using a primitive-character estimate for that target requires a conductor decomposition that retains the relevant nonunit restrictions.

For comparison, **§1, the definition of class $\mathcal C$** requires $|\Lambda_f(n)|\le\Lambda(n)$ and implies $|f(n)|\le1$. The progression theorem **1.2** concerns that class and averages moduli. It must not be confused with the arbitrary coefficients of Theorem 5.1. The unnormalised $b_s$ has $b_s(2)=(3/2)^s-1$, so it is outside this bounded class. Dividing by a global constant other than 1 does not preserve multiplicativity or $f(1)=1$.

The later paper I. E. Shparlinski, *Character sums with smooth numbers*, **1705.10148v2** (2017-06-11), [original text](https://arxiv.org/html/1705.10148v2), **Lemma 2.2** and **Theorem 1.1**, uses this sieve and sharpens exceptional-pair counts. It retains the small-modulus and smoothness restrictions. It is not an estimate for all characters of the present fixed $V$.

### 2.2 A recent fixed-modulus low-moment theorem with explicitly incompatible scales

Seth Hardy and Max Wenqiang Xu, *Character sums over smooth numbers*, **2607.00592v1**, 2026-07-01.

Original: [arXiv text, version 1](https://arxiv.org/html/2607.00592v1). Checked **Theorems 1–3**, the discussion following Theorem 1, and **§4.1, equations (11)–(12)**.

Theorem 1 averages **all characters at one fixed modulus**, and permits composite moduli. Its assumptions include

$$
2\le x\le q,\qquad (\log x)^6\le Y\le x^{1/(32\log\log x)}.
$$
Writing $u=\log x/\log Y$ and $\alpha(x,Y)$ for the smooth-number saddle point, set

$$
\mathcal S=(\log x)^{3/2}(\log Y)^{1/2}
\left(Y^{1/2-\alpha(x,Y)}+
\exp\left[-\frac u4\left(\frac{\log\min(q,x^{3/2})}{\log x}-1\right)^2\right]\right).
$$
Then

$$
\frac1{\varphi(q)}\sum_{\chi\bmod q}
\left|\sum_{n\le x,P^+(n)\le Y}\chi(n)\right|
\ll\sqrt{\Psi(x,Y)\mathcal S}.
\tag{3}
$$
For every function $\varepsilon(x)\to\infty$, the theorem gives $\mathcal S=o_\varepsilon(1)$ uniformly when, in addition,

$$
\frac{\log q}{\log x}\ge
1+\sqrt{\frac{6\log\log x+2\log\log Y+\varepsilon(x)}{u}}.
$$

Theorem 2 allows a **completely multiplicative** twist $h$ satisfying $|h(p)|\le1$. It is not an arbitrary-weight theorem. Section 4.1 identifies the needed orthogonality/mean-square hypothesis at polynomial length at most the family-size parameter.

The present core scale has $x=V^{2-o(1)}>V$, while its cutoff $Y\asymp\log x\log\log x$ is below $(\log x)^6$. Its increment weight is also not the allowed twist. Thus three independent conditions fail. Theorem 3's average over primitive characters and varying $q\le Q_0$ has a family-size parameter $Q_0^2$; this is not a replacement for the fixed-modulus character family.

The paper itself identifies the small-smoothness regime $Y\le(\log x)^6$ as a further problem after Theorem 1. Its methods therefore suggest a direction but do not close the present interface.

### 2.3 Older smooth-number mean squares do not silently become fixed-modulus estimates

Adam J. Harper, *Bombieri–Vinogradov and Barban–Davenport–Halberstam type theorems for smooth numbers*, **1208.5992v1**, 2012-08-29.

Original: [arXiv text, version 1](https://arxiv.org/html/1208.5992v1). Checked **Theorems 1–3**.

Theorem 2, for an absolute large $K$, $(\log x)^K\le Y\le x$, and $Q_0\le\Psi(x,Y)$, gives

$$
\sum_{q\le Q_0}\sum_{(b,q)=1}
 \left|\Psi(x,Y;q,b)-\frac{\Psi_q(x,Y)}{\varphi(q)}\right|^2
\ll \Psi(x,Y)^2\left(e^{-cu/\log^2(u+1)}+Y^{-c}\right)+\Psi(x,Y)Q_0.
\tag{4}
$$
It is an actual aggregate estimate, but averages moduli and has an unproved smoothness premise at the present cutoff. Theorem 3 instead controls individual characters with conductor at most $Y^b$, alongside a specified zero-free condition; that does not cover the current large conductors. These are accurate theorem boundaries, not a claim that no suitable fixed-modulus result exists anywhere.

### 2.4 Weighted multiplicative energy is a useful norm, not freely chosen weights

Régis de la Bretèche, Marc Munsch and Gérald Tenenbaum, *Small Gál sums and applications*, **1906.12203v4**, 2020-07-10.

Original: [arXiv text, version 4](https://arxiv.org/html/1906.12203v4). Checked **§1.2, equations (1.3)–(1.6), Theorem 1.2**.

For nonnegative $c_n$, $\sum_{n\le N}c_n=1$, define

$$
\mathcal E(c;N)=\sum_{m\le N^2}
 \left(\sum_{dt=m,\ d,t\le N}c_dc_t\right)^2,
\qquad \mathcal E_N=\inf_c N^2\mathcal E(c;N).
$$
With $\delta_{\rm Gal}=1-(1+\log\log2)/\log2\approx0.08607$, their theorem states

$$
(\log N)^{\delta_{\rm Gal}}(\log\log N)^{3/2}
\ll\mathcal E_N
\ll(\log N)^{\delta_{\rm Gal}}(\log\log N)^6.
\tag{5}
$$
Thus carefully chosen nonnegative short-factor weights can improve on the all-ones energy, but not remove all logarithmic cost. The upper bound asserts existence of good weights, not small energy of the actual core law or every prescribed set. Replacing the target's counting weight by a favourable $c_h$ requires a domination, a partition, or an amplification identity and must pay for the compensating factor. With $N^2<V$, integer energy becomes an exact fixed-modulus fourth moment, as in §3 below; that transfer itself does not need $V$ prime.

A nearby composite-modulus result is Bryce Kerr, *Moments of character sums to composite modulus*, **1904.04578v1**, 2019-04-09, [original text](https://arxiv.org/html/1904.04578v1), **§2, Theorem 2**. It averages the shift $\lambda\bmod q$ of $\sum_{v\le N}\chi(\lambda+v)$ for one primitive character, with explicit square/cubefull-part factors. That is a different average from the current sum over all characters of one fixed modulus; its shift variable cannot be replaced by the moving source interval $J_h$.

### 2.5 Standard entropy results and exact migration conditions

Tim van Erven and Peter Harremoës, *Rényi Divergence and Kullback–Leibler Divergence*, **1206.2459v2**, 2014-04-24.

Original: [arXiv text, version 2](https://arxiv.org/html/1206.2459v2). Checked **Introduction equations (2), (4)**, **Theorem 9** (data processing), and **Theorem 28, equations (42)–(43)** (finite/countable additivity, with the stated exception at order zero).

For a probability on a finite group of order $Q$, $D_\alpha(\nu\|\mathrm{Unif})=\log Q-H_\alpha(\nu)$. This reference supplies the standard entropy/divergence framework; it does not itself estimate the present prime-valuation law. A hypothetical “uniform probability on all integers” is not a valid reference law. The nonnegative Euler sums and the order-dependent valuation tails in theory §223 justify the infinite-source limit without such an object.

Jonathan Hermon and Sam Olesker-Taylor, *Cutoff for Almost All Random Walks on Abelian Groups*, **2102.02809v2**, 2025-10-10, [original text](https://arxiv.org/html/2102.02809v2#S2.SS6), **§2.6, lower-bound proof of Theorem 2.5**, supplies the finite-image entropy mechanism with generators held fixed. If a source law $\rho$ puts most probability on $E_L=\{w:\rho(w)\ge e^L/Q\}$, then $|E_L|\le Qe^{-L}$ and every image has size at most this, hence

$$
\|\pi_*\rho-\mathrm{Unif}\|_{\rm TV}\ge\rho(E_L)-e^{-L}.
\tag{6}
$$
Theory §§223–224 supply source power-sum and entropy estimates for the specific increment law. This closes the source-concentration premise left open in the earlier Bohr note, without importing a random-generator mixing upper bound. The source remains the full unit-conditioned law; actual-hit conditioning or a product cap is a different operation.

## 3. An exact way to keep moving product windows while using short-factor energy

The existing fixed-rectangle fourth moment extends uniformly to a continuous Mellin twist. For a unit subset $\mathcal H\subseteq[1,H]$ and real $t$, define

$$
B_\chi(t)=\sum_{h\in\mathcal H}\chi(h)h^{-it}.
$$
If $H^2<V$, then character orthogonality gives

$$
\frac1Q\sum_\chi|B_\chi(t)|^4
=\#\{h_1h_2=h_3h_4:h_i\in\mathcal H\}
\le2H^2(1+\log H).
\tag{7}
$$
Indeed modular product equality becomes integer equality, and its continuous twist is then exactly one. The gcd parametrization $h_1=gu,h_3=gv,h_2=kv,h_4=ku$, $(u,v)=1$, proves the last bound. Nonnegative coefficients $c_h\le1$ can be inserted without increasing it. For arbitrary complex coefficients, the exact fourth moment is instead

$$
\frac1Q\sum_\chi\left|\sum_{h\in\mathcal H}c_h\chi(h)h^{-it}\right|^4
=\sum_m\left|\sum_{h_1h_2=m}c_{h_1}c_{h_2}\right|^2,
$$

with coefficients zero outside $\mathcal H$. This identity also needs only $H^2<V$, not a prime modulus. It does not supply a small energy for prescribed coefficients.

Take a nonnegative $W\in C_c^\infty((0,\infty))$ with $W(u)\ge1$ on $[A/X,1]$, and let

$$
\widetilde W(it)=\int_0^\infty W(u)u^{it-1}\,du,
\qquad A_\chi(t)=\sum_{D<d\le X,(d,V)=1}a(d)\chi(d)d^{-it}.
$$
The original moving-window sum has the legitimate positive majorant

$$
S_a\le S_W:=\sum_{\substack{D<d\le X,\ 1\le h<H\\dh\equiv1\pmod V}}
 a(d)W(dh/X).
$$
Mellin inversion gives the **exact** identity for this majorant

$$
S_W=\frac1{2\pi Q}\int_{\mathbb R}\widetilde W(it)X^{it}
 \sum_{\chi\bmod V}A_\chi(t)B_\chi(t)\,dt,
\tag{8}
$$
where $\mathcal H=\{1\le h<H:(h,V)=1\}$. The sums are finite and $\widetilde W$ decays rapidly, so the interchange is justified. Let $M_W$ be its principal-character term. Hölder and (7) yield

$$
|S_W-M_W|
\le \frac{[2H^2(1+\log H)]^{1/4}}{2\pi}
 \int_{\mathbb R}|\widetilde W(it)|
 \left(\frac1Q\sum_{\chi\ne1}|A_\chi(t)|^{4/3}\right)^{3/4}dt.
\tag{9}
$$

This explicitly accommodates the moving inequalities $A\le dh\le X$; it does not replace them by an unrelated rectangle. It exposes a concrete weighted $L^{4/3}$ spectral quantity, averaged also against a controlled Mellin kernel. To use a sharper signed correlation one can work with (8) before taking absolute values.

The price of smoothing remains real: $S_W-S_a$ is the sum, over the same congruence pairs, of the nonnegative terms

$$
a(d)\left[W(dh/X)-\mathbf1_{[A/X,1]}(dh/X)\right].
$$

If $W$ is chosen equal to one on the original interval, this excess is supported outside it. Narrowing the edge region requires quantitative control of the resulting Mellin norm; no uniform bound under such sharpening is assumed. Conditions such as a joint cap on $dh$ still cannot be factorized into an independent $A_\chi B_\chi$ without an additional representation. Dropping them supplies an upper bound, which may be too large. No bound at the Robin budget is proved by (9).

## 4. What remains to be estimated

The full-law Rényi asymptotic and near-maximal total variation in theory §§223–224 concern the complete source or its unit-conditioned residue image. They do not locate its large atoms relative to the prescribed inverse residues. Unit conditioning deletes the local coordinates for primes dividing $V$; conditioning on an actual hit does not have that product form. The raw and unit-conditioned transforms are related by

$$
\widehat\mu_s(\chi)=c_V\widehat\nu_s(\chi),\qquad
c_V=\mu_s((d,V)=1),
$$

and the mass factor must be retained when returning to the raw target.

Theory §225 uses the maximum source atom and a short-factor $L^1$ lower bound, obtained from second and fourth moments through multiplicative energy, to show that even the exact full-law Hölder norm product, optimized over every exponent, exceeds the needed budget exponentially in $R$. That is a lower bound on an upper-bound certificate, not on the actual correlation. It does not automatically apply to the truncated, Mellin-twisted $A_\chi(t)$ in (8)–(9), whose coefficients retain different information.

For the actual application one must control the principal term $M_W$, the nonprincipal contribution in (8), and any smoothing or discarded-filter cost after multiplication by

$$
\Lambda=\frac{XU(s)}{(e^\gamma\ell)^s}.
$$

Equation (9) is a sufficient route only if its specific weighted spectral integral and these costs are bounded at that scale. The references above do not supply that bound under the current simultaneous parameter conditions. The signed identity (8), a direct weighted intersection estimate, or an additional valid representation of product-dependent filters remains an open interface.

The source locators above refer to the specified arXiv versions. They support the displayed theorem scopes; they do not establish exhaustive prior-art coverage or originality of the arithmetic application. The Mellin and energy formulas are standard mathematical operations applied to the stated finite sums. No full-FIB Robin estimate or unrestricted RH criterion is settled here.
