---
bibkey: nicolas2025comparison
authors: Jean-Louis Nicolas
year: 2025
title: Comparison of large values of n/φ(n) and σ(n)/n
doi: null
url: https://hal.science/hal-05389053v1
claim: The manuscript gives unconditional asymptotic and effective comparisons between the two separate extremal envelopes Φ(X) and Σ(X); it does not identify common maximizers, arbitrary near-extremal prime profiles, or source-weighted concentration in a prescribed residue class.
strata_touched: []
license: citation-only
triage: anchor
---

# Comparison of large values of n/φ(n) and σ(n)/n

The primary manuscript is Jean-Louis Nicolas's single-author [HAL hal-05389053v1](https://hal.science/hal-05389053v1), with [versioned full text](https://hal.science/hal-05389053v1/document). Its title page is dated **15 July 2025**; the HAL cover and submission record say **29 November 2025**. The PDF has 38 numbered manuscript pages plus the HAL cover. These dates are distinct from later changes to the record's metadata. No journal publication or DOI is asserted here.

This source is not Axler–Nicolas, *Large values of n/φ(n) and σ(n)/n*, *Acta Arithmetica* **209** (2023), 357–383, DOI [10.4064/aa220705-12-10](https://doi.org/10.4064/aa220705-12-10). The latter is reference [2] in the 2025 manuscript and supplies an earlier effective comparison.

This card records the definitions, main theorem statements and relevant proof interfaces checked in the primary manuscript. It is not a full verification of all analytic proofs, external estimates or Maple computations, and supplies no Lean verification.

## The two envelopes and the actual quantifiers

For real $X\ge1$, equation (1.7), printed p.3, defines

$$
\Phi(X)=\max_{1\le n\le X}\frac n{\varphi(n)},
\qquad
\Sigma(X)=\max_{1\le n\le X}\frac{\sigma(n)}n.
$$

The maxima range over positive integers and are taken **separately**. The strict record holders for $n/\varphi(n)$ are the primorials; those for $\sigma(n)/n$ are the superabundant integers. Remark 1.1 reports that the only integers that are both primorial and superabundant are 2 and 6. This observation concerns strict records: because $n/\varphi(n)$ can tie, it does not imply that the two sets of maximizers are always disjoint. No common maximizing integer is supplied for a general $X$.

Theorem 1.2, printed p.4, states that for every fixed integer $J\ge1$, as real $X\to\infty$,

$$
\frac{\Phi(X)}{\Sigma(X)}
=1+\sum_{j=1}^{J}
\frac{c_j\sqrt2}{\sqrt{\log X}(\log\log X)^j}
+O_J\!\left(\frac1{\sqrt{\log X}(\log\log X)^{J+1}}\right),
$$

where, with $a=\log2$,

$$
c_1=2,\qquad c_2=-(2+a),\qquad c_3=8+4a+\frac{3a^2}{4}.
$$

The statement is **unconditional**. The error constant may depend on $J$; there is no uniform assertion for $J$ growing with $X$, and this is not a moment asymptotic with exponent $s$.

Equation (1.10) defines $\tau(X)$ by the exact equality, for $X>e$,

$$
\frac{\Phi(X)}{\Sigma(X)}
=1+\frac{2\sqrt2}{\sqrt{\log X}\log\log X}
-\frac{(2+\log2)\sqrt2}{\sqrt{\log X}(\log\log X)^2}
+\frac{\tau(X)}{\sqrt{\log X}(\log\log X)^3}.
$$

Theorem 1.3, on the same page, supplies **unconditional effective bounds**:

- $6.78\le\tau(X)\le94.73$ for every real $X\ge N^{(0)}$;
- $0.153\le\tau(X)\le129.08$ for every real $4\le X\le N^{(0)}$.

Here $N^{(0)}$ is the specific CA integer defined by its prime factorization in (3.13), with $\log N^{(0)}=1000014552.11\ldots$ in (3.14). The displayed decimal is a description of the threshold, not its definition. The finite part of the proof uses bounds from Axler–Nicolas 2023; this source inspection has not independently rerun that computation.

## What prime-profile information the argument uses

Section 3 parametrizes **CA reference integers** by the usual decreasing prime-power thresholds $F(\xi_k,k)=\epsilon$. Lemmas 3.2–3.4 estimate these thresholds, particularly the square layer $\xi_2$. Lemmas 3.5–3.6 compare $\xi$ with $\log X$ after choosing adjacent parameter-defined CA integers $N'\le X<N$.

Section 4, printed pp.23–24, then uses

$$
\frac{\sigma(N')}{N'}\le\Sigma(X)<\frac{\sigma(N)}N
$$

and the primorial attaining $\Phi(X)$ to compare the envelopes. Its “excess” is

$$
E(X)=\log N-\vartheta(\xi)
=\sum_{k\ge2}\vartheta(\xi_k),
$$

which measures the higher-prime-power content of that CA reference. It is not the deficit $J_s(d)$ of an arbitrary actual divisor from the FIB source.

These are forward estimates of extremizers and their envelopes. The checked theorem and lemma statements do not give an inverse assertion that every integer whose abundancy is close to the envelope shares a specified common core. They also do not preserve the original integer or its residue class when replacing it by a CA or primorial extremizer.

## Relation to the current actual-divisor estimates

| Current object or goal | What this source supplies | Additional obligation |
|---|---|---|
| Replacing $Z(n)=\sigma(n)/n$ by $n/\varphi(n)$ | Quantifies the discrepancy of the two **maxima up to the same $X$**, including its leading $2\sqrt2/(\sqrt{\log X}\log\log X)$ term. | It is not a lower bound for $[n/\varphi(n)]/Z(n)$ at the same integer. Separate maximizers cannot be treated as jointly realized. |
| A bound for an actual $n\le X$ | Any positive lower bound $L(X)$ for $\Phi(X)/\Sigma(X)$ gives the valid global bound $Z(n)\le\Sigma(X)\le\Phi(X)/L(X)$. | Proving this bound below the actual Robin budget requires an additional comparison with $e^\gamma\log\log n$; the envelope theorem does not already make that comparison. |
| The low-loss divisor set $J_s(d)\le O(R)$ for $w_s(d)=b_s(d)/d$ | CA prime-layer estimates provide related extremal arithmetic background. | No stated comparison identifies its CA reference objective with $b_s=\mu*Z^s$, its normalized weights, or $J_s=\log(\max w_s/w_s)$. |
| Uniform editing/common-core bounds for every low-loss divisor | No directly matching inverse theorem was located in the inspected statements. | The source-specific uniform bound remains to be justified; the unweighted §232 count already has the separate classical benefit/PNT simplification. |
| $s=\log A\log\log A$, $R=\log A/(\log\log A)^2$, and the full complementary moment | The paper studies fixed-order expansions of extremal envelopes. | It supplies no $s$-uniform source power sum, $J_s$-tail estimate, or actual-divisor incidence count. |
| Every prescribed growing reduced residue class | No progression or residue-class hypothesis is present in its main results. | A map to an extremizer is not a map preserving $n\equiv c\pmod m$, divisor incidence, or the candidate's complete joint weight. |

The unconditional status of Theorems 1.2–1.3 should be kept separate from RH-conditional bounds in Nicolas's other work. In particular, the frequently quoted bound with a $0.095/\sqrt{\log n}$ subtraction is **not** Theorem 1.2 or Theorem 1.3 of this manuscript; no such corollary is stated here. This card does not reclassify any result from the distinct 2022 paper.

The useful addition is an explicit comparison between the global Euler and divisor-sum envelopes. It does not by itself remove the possible singleton in §232, establish the missing FIB-to-CA transfer, or certify originality of the actual-source weighted concentration argument. The remaining common-implementation and uniformity requirements must not be erased by the shared terminology “large values.”

## Explicit comparison at the same candidate

The following is an application of the cited envelope statements, not an additional theorem attributed to Nicolas. For an actual integer $n>5040$, put $v=\log n$, $L=\log v$ and $t_n=e^\gamma L$. Let $a(n)=0.153$ for $n<N^{(0)}$ and $a(n)=6.78$ for $n\ge N^{(0)}$, with the exact threshold as above. Theorem 1.3 supplies the positive lower bound

$$
R_-(n)=\max\left\{1,\,
1+\frac{2\sqrt2}{\sqrt vL}
-\frac{(2+\log2)\sqrt2}{\sqrt vL^2}
+\frac{a(n)}{\sqrt vL^3}\right\}
\le\frac{\Phi(n)}{\Sigma(n)}.
$$

Here $\Phi(n)>\Sigma(n)$ for $n\ge2$: at any integer attaining $\Sigma(n)$, which is larger than one, $Z(m)<m/\varphi(m)\le\Phi(n)$. Thus the maximum with one preserves a lower bound without assuming that a truncated expression is positive at every parameter.

Write $D_n=\log(\Sigma(n)/Z(n))\ge0$. If $d_n\le D_n$ is independently established, then

$$
\log\frac{\Phi(n)}{t_n}<\log R_-(n)+d_n
$$

suffices for strict Robin at this same $n$. Taking $d_n=0$ uses only the cited envelope comparison. Defining $D_n$ does not establish a positive lower bound for it.

Let $p$ be the last prime for which $P_p=\prod_{q\le p}q\le n$, so that $P_p\le n<P_{p^+}$. The Euler envelope is exactly $\Phi(n)=\prod_{q\le p}(1-1/q)^{-1}$. Consequently the left side above equals

$$
E_M(p)+\log\frac{\log p}{L},\qquad
E_M(p)=\log\frac{\prod_{q\le p}(1-1/q)^{-1}}{e^\gamma\log p}.
$$

Both terms come from the same prime sequence; the second cannot be deleted or assigned a favorable sign. Writing $v=\vartheta(p)+h$ gives $0\le h<\log p^+$, and variation of $h$ contributes only $O(1/v)$ as $n\to\infty$.

The [Dusart estimates already used in the project](../Weil/dusart2010estimates.md) give a coarse $O(L^{-2})$ bound for this joint expression. Its guaranteed error scale is larger than the envelope saving $\log R_-(n)\sim2\sqrt2/(\sqrt vL)$ by a factor of order $\sqrt v/L$. This compares the available bounds, not the actual signed error. Even a fixed inverse-logarithmic error order does not reach the required scale; increasing the fixed order in Nicolas's ratio expansion alone does not repair it.

For fixed $C_0>1$, the growing moment $s=y\log y$ and $n\in[e^y,C_0e^y]$, the logarithmic envelope saving is $s\log R_-(n)\sim2\sqrt2\sqrt y$. This is $o(y/(\log y)^2)$, the scale of the existing global moment excess. It therefore cannot by itself pay that global relaxation cost. The individual candidate need not pay that global cost, so this observation does not refute a bound using additional information about the actual candidate.

Finally, the fixed-price benefit is not $D_n$. If $C$ maximizes $Z(m)m^{-1/s}$ and $\mathcal Q_s=Z(C)^s/C$, then

$$
D_n=\operatorname{Ben}_{C,1/s}(n)-K_s(n),\qquad
K_s(n)=\frac{\log \mathcal Q_s+\log n}{s}-\log\Sigma(n)\ge0.
$$

A benefit lower bound must therefore be accompanied by a bound for this support-line gap before it supplies $d_n$. The [FIB theory volume, §234](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md) gives the separate finite comparison between the actual increment loss and this classical price objective. Neither comparison establishes the missing fixed-residue candidate exclusion.

## Signed prime error at the actual primorial cutoff

The following application combines the envelope comparison above with classical partial summation. It introduces no new prime-distribution estimate. Its sufficient condition remains unproved at the FIB candidates; it is not a proof of Robin's inequality or a claim of originality.

For the same actual integer $N$, put $Y=\log N$ and let $x$ be the prime satisfying $P_x\le N<P_{x^+}$, where $x^+$ is the next prime. Write

$$
\mathcal P(x)=\prod_{p\le x}(1-1/p)^{-1}=\Phi(N),\qquad
f(x)=\frac{e^\gamma\log\vartheta(x)}{\mathcal P(x)},\qquad
b_N=\log\frac{\log Y}{\log\vartheta(x)}\ge0.
$$

Here $\vartheta(u)=\sum_{p\le u}\log p$ and $\psi(u)=\sum_{p^j\le u}\log p$. For any proved positive $\mathscr L(N)\le\Phi(N)/\Sigma(N)$, the exact normalization gives

$$
\log\frac{Z(N)}{e^\gamma\log Y}
\le-\log f(x)-\log\mathscr L(N)-b_N.
$$

This retains the correlation between the Euler product and the primorial logarithm. Also $0\le Y-\vartheta(x)<\log x^+$, so the prime number theorem gives $x\sim Y$ and $b_N=O(1/x)=o(1/(\sqrt x\log x))$ as $N\to\infty$.

### The unconditional Nicolas input and its endpoint term

Jean-Louis Nicolas, *Small values of the Euler function and the Riemann hypothesis*, [arXiv:1202.0729v2](https://arxiv.org/abs/1202.0729v2), Lemma 2.1, printed p.4, states for $x\ge121$ that

$$
I_\vartheta(x)-\frac{(\vartheta(x)-x)^2}{x^2\log x}
\le\log f(x)\le I_\vartheta(x)+\frac1{2(x-1)},
$$

where

$$
k(u)=\frac{1+\log u}{u^2\log^2u},\qquad
I_\vartheta(x)=\int_x^\infty(\vartheta(u)-u)k(u)\,du,\qquad
I_\psi(x)=\int_x^\infty(\psi(u)-u)k(u)\,du.
$$

The paper calls these integrals $K(x)$ and $J(x)$ in (1.15)–(1.16), and attributes Lemma 2.1 to Proposition 1 of its 1983 reference [6]. This lemma has no RH hypothesis. The later RH-dependent bounds in Lemma 2.4 and Proposition 2.1 are not used here.

Consequently, for $x\ge121$, the independently defined margin

$$
\mathfrak m_N=I_\vartheta(x)-\frac{(\vartheta(x)-x)^2}{x^2\log x}
+\log\mathscr L(N)+b_N
$$

gives $Z(N)\le e^\gamma\log\log N\,e^{-\mathfrak m_N}$. Positivity of this margin is sufficient, but has not been established for all actual candidates.

Partial summation also gives an exact version of the endpoint accounting. Put $a=(\vartheta(x)-x)/x$, $v=\log x$ and

$$
Q(x)=\frac a v-\log\left(1+\frac{\log(1+a)}v\right),\qquad
T_2(x)=\sum_{p>x}\sum_{j\ge2}\frac1{jp^j}>0.
$$

For $x\ge121$, all logarithms are defined, and

$$
\log f(x)=I_\vartheta(x)-Q(x)+T_2(x).
$$

Indeed, writing $B_1$ for the Meissel–Mertens constant, partial summation yields $\sum_{p\le x}1/p=\log\log x+B_1+a/v-I_\vartheta(x)$. Add the higher-power terms in $\log\mathcal P(x)$ and use $B_1+\sum_p\sum_{j\ge2}1/(jp^j)=\gamma$. This proves the identity and the positive sign of $T_2$. Thus $I_\vartheta-Q+\log\mathscr L+b_N$ is another valid lower margin. It comes from the same classical identity, not a new analytic estimate.

### What remains after the prime-square contribution

For this paragraph choose the specific $\mathscr L(N)=R_-(N)$ above, which has Nicolas's leading correction $2\sqrt2/(\sqrt Y\log Y)$. An arbitrary positive envelope-ratio lower bound need not have that correction. The unconditional prime number theorem gives

$$
\psi(u)-\vartheta(u)=\vartheta(\sqrt u)+O(u^{1/3}\log u)
=(1+o(1))\sqrt u.
$$

Integrating against the positive kernel gives

$$
I_\psi(x)-I_\vartheta(x)=\frac{2+o(1)}{\sqrt x\log x}.
$$

It follows that

$$
\sqrt x\log x\,\mathfrak m_N
=2\sqrt2-2+\sqrt x\log x\,I_\psi(x)
-\frac{(\vartheta(x)-x)^2}{x^{3/2}}+o(1).
$$

Thus a sufficient candidate-specific input is: there are fixed $\eta>0$ and $N_1$ such that at the associated prime cutoff of **every actual candidate** $N\ge N_1$,

$$
\frac{(\vartheta(x)-x)^2}{x^{3/2}}
-\sqrt x\log x\,I_\psi(x)\le2\sqrt2-2-\eta.
$$

This would give strict Robin with a positive margin of order $1/(\sqrt{\log N}\log\log N)$ for sufficiently large candidates. It permits compensation between the signed tail and endpoint error. The endpoint penalty cannot be discarded from the prime number theorem alone: its being negligible at this scale requires $\vartheta(x)-x=o(x^{3/4})$. The exact $Q$ version has

$$
\sqrt x\log x\,Q(x)=\frac{(\vartheta(x)-x)^2}{2x^{3/2}}
\left(1+\frac1{\log x}+O(|a|)\right).
$$

For example, bounds $I_\psi(x)\ge-\kappa/(\sqrt x\log x)$ and $|\vartheta(x)-x|\le Kx^{3/4}$ with fixed nonnegative constants satisfying $\kappa+K^2/2<2\sqrt2-2$ would suffice. These are additional prime-distribution hypotheses, not consequences of a large divisor core or of a FIB address. No equivalence between this restricted sufficient condition and RH is asserted.

### The endpoint condition at actual self-tangent sources

There is a more specific source condition under which the squared endpoint
term above is already negligible. Take an actual regular self-tangent CA
integer $N=C_A$ with $A=\log N$ as in the
[archived workload interface](../Analytic/mantovanelli2026primeworkload.md).
Keep $x$ as the primorial cutoff of this same $N$:
$\vartheta(x)\le A<\vartheta(x^+)$, with $x^+$ the next prime.
It is not the largest prime factor of $C_A$ or the clock coordinate $A$.

The archived manuscript's §8, `thm:theta-normal-form`, equation
`eq:self-tangent-theta`, already gives

$$
A-\vartheta(A)=\sqrt{2A}\,(1+o(1))
$$

along regular returns tending to infinity. The source uses a strict
prime cutoff; changing to the weak $\vartheta$ used here costs at most
$O(\log A)$ and preserves this assertion. This return identity is reused,
not rederived. The manuscript's §11, `lem:external-extremal-input` and
`thm:persistent-obstruction`, also supplies the existing reduction to a
proper GA1 regular source at or above the Robin level if RH fails.
The estimates here apply to that selected source class; GA1, CA status,
or a five-window address alone is not the self-tangency hypothesis.

The [existing uniform short-interval supplier and inverse-$\vartheta$
argument](../Analytic/guthmaynard2024largevalues.md) can now be applied at
this actual $A$. With $H=A^{2/3}$, it gives
$\vartheta(A+H)-\vartheta(A)\sim H$. Since the return deficit is only
$O(\sqrt A)$, eventually $\vartheta(A+H)>A$.
There is a prime in $(A,A+H]$; at the first such prime the added mass is
$O(\log A)$, smaller than the return deficit, so its $\vartheta$ value
is still below $A$. Monotonicity therefore locates the same primorial
cutoff and its residual as

$$
0<x-A\le A^{2/3},\qquad
0\le h_N:=A-\vartheta(x)<\log x^+=O(\log A).
$$

Consequently $\vartheta(x)-x=-(x-A)-h_N$ and

$$
\frac{(\vartheta(x)-x)^2}{x^{3/2}}=O(A^{-1/6})=o(1),
\qquad
\sqrt x\log x\,Q(x)=O(A^{-1/6}).
$$

The second estimate uses the already displayed expansion of the exact
endpoint $Q$. The exponent $2/3$ is a convenient choice within the cited
uniform short-interval range, not a new prime-gap estimate. This application
does not require an effective starting threshold or assume RH, and it
does not claim the endpoint estimate at arbitrary FIB candidates.

There is also a controlled transfer of the unnormalized tail. The same
manuscript's §8, `thm:psi-normal-form`, gives
$\psi(A)-A=-(\sqrt2-1)\sqrt A+o(\sqrt A)$ at a regular return.
At the primorial cutoff, $\vartheta(x)=A-h_N$ and the classical
prime-power decomposition gives $\psi(x)=A+O(\sqrt A)$.
For $A\le u\le x$, monotonicity of $\psi$ hence bounds
$|\psi(u)-u|=O(A^{2/3})$. Integrating over the same interval against
$k(u)=O(A^{-2}/\log A)$ yields

$$
I_\psi(x)=I_\psi(A)+O\!\left(\frac{A^{-2/3}}{\log A}\right).
$$

With $Z_\psi(t)=\sqrt t\log t\,I_\psi(t)$ this is precisely

$$
Z_\psi(x)=c_NZ_\psi(A)+O(A^{-1/6}),\qquad
c_N=\frac{\sqrt x\log x}{\sqrt A\log A}
=1+O(A^{-1/3}).
$$

The factor $c_N$ must remain unless a suitable bound on $Z_\psi(A)$ is
available; $x/A\to1$ alone does not justify an additive $o(1)$ comparison
of the normalized tails. A fixed one-sided lower bound at $A$ can be
transported with this factor. No such lower bound follows from the return
identity, which fixes a point value of $\psi$ rather than its entire tail.

For $\mathscr L(N)=R_-(N)$, the existing comparison margin therefore
simplifies on this source class to

$$
\sqrt x\log x\,\mathfrak m_N
=2\sqrt2-2+Z_\psi(x)+o(1).
$$

This pays the endpoint requirement of that comparison, not its signed-tail
requirement. The source-clock pressure identity and its reserve constant
$2(\sqrt2-1)$ are already recorded in the FIB volume, §§87 and 93;
rewriting the remaining tail condition is not a new RH criterion or a
stronger Robin estimate. This is a paper application connecting two
existing observation cutoffs, with no Lean or originality certification.

### The 2026 signed formula and the available absolute-error scale

Broadbent–Fiori–Kadiri–Ng–Wilk, *Bounds for Mertens sums*, [arXiv:2608.01498v1](https://arxiv.org/abs/2608.01498v1), Proposition 13(i), equation (55), gives an unconditional explicit formula for $I_\psi(x)$ for $x\ge2$. Its proof, equations (82)–(83), also gives the form

$$
\begin{aligned}
I_\psi(x)={}&\frac{\log x+1}{\log^2x}
\sum_\rho\frac{x^{\rho-1}}{\rho(\rho-1)}\\
&-\sum_\rho\frac1{\rho(\rho-1)}
\int_x^\infty t^{\rho-2}\left(\frac1{\log^2t}+\frac2{\log^3t}\right)dt
-\frac{\log(2\pi)}{x\log x}-\frac12\kappa_0(x),
\end{aligned}
$$

where the sums run over the nontrivial zeta zeros with multiplicity and $\kappa_0(x)=\int_x^\infty\log(1-t^{-2})k(t)\,dt$. The proof uses absolute convergence after integration by parts to pass to the infinite endpoint. This is a signed formula; Proposition 13(ii) is a separate absolute-value estimate. Merely expressing the integral through zeros gives no needed one-sided bound at FIB-selected cutoffs. Equation (54) is also the partial-summation identity used above. The relevant statements and these proof steps were inspected; no complete proof audit or Lean verification of the preprint is claimed.

Fiori–Jaskari, *Explicit bounds for the prime number theorem*, [arXiv:2609.23222v2](https://arxiv.org/abs/2609.23222v2), Theorem 1.1 and Table 1, state for $u\ge e^3$ that

$$
\frac{|\psi(u)-u|}{u}
<0.2390\exp\left[-D\left(1+\frac{\log\log\log u}{15\log\log u}\right)
\frac{(\log u)^{3/5}}{(\log\log u)^{1/5}}\right],\qquad
D=\frac52\left(\frac53\right)^{1/5}\left(\frac{2000}{161967}\right)^{3/5}.
$$

This is a September 2026 unconditional preprint statement. Its theorem and table were read in the primary text; its full analytic proof and computations have not been independently audited. Even this error shape, with any fixed constant $c>0$ in its leading exponential, is asymptotically larger than the required scale:

$$
\frac{\exp[-c(\log x)^{3/5}/(\log\log x)^{1/5}]}{1/(\sqrt x\log x)}
\longrightarrow\infty.
$$

Integration introduces no improvement to a power of $x$: with a slightly smaller fixed $c$, the same exponential shape bounds $|I_\psi(x)|$. This compares the **guaranteed upper bounds**, not the unknown actual signed error, and does not prove that the candidate condition fails.

There is a stronger obstruction to a different proposed shortcut. Diamond–Pintz, *Oscillation of Mertens' product formula*, [JTNB 21 (2009), Theorem 1.1, printed p.524](https://doi.org/10.5802/jtnb.687), prove that $\sqrt x(\mathcal P(x)-e^\gamma\log x)$ has arbitrarily large positive and negative values. Hence no fixed $K$ gives $\mathcal P(x)\le e^\gamma\log x+K/\sqrt x$ for all sufficiently large $x$. This refutes that raw-product certificate; it does not refute Robin or the comparison normalized by $\log\vartheta(x)$.

### Return to the actual source budget

Use the notation of the FIB volume's §233.5: $t=e^\gamma\log\log A$, $s=\log A\log\log A$, and $C_*+H_*=(Z(N)/t)^s$ at the possible actual candidate. Put $B_N=(\log\log N/\log\log A)^s$. Either valid margin above gives

$$
C_*+H_*\le B_Ne^{-s\mathfrak m_N}.
$$

Therefore $B_Ne^{-s\mathfrak m_N}+\varepsilon_A<B_N$ suffices for the already stated target $C_*+\varepsilon_A<B_N$. For $0<\varepsilon_A<B_N$, the needed margin for this certificate is exactly

$$
\mathfrak m_N>-\frac1s\log(1-\varepsilon_A/B_N).
$$

The fixed-slack prime condition above is stronger. In a fixed-ratio window $N\in[A,C_0A]$, with $C_0>1$ fixed and $y=\log A$, it supplies $s\mathfrak m_N\gg\sqrt y$ and $B_N=(N/A)(1+o(1))$. Conditional on the previously stated high-loss estimate $\varepsilon_A=\exp[-(\pi^2/9)y/(\log y)^2+o(y/(\log y)^2)]$, the budget then holds eventually. This application stays at the same integer throughout. It does not supply the missing signed-error hypothesis, certify an effective starting threshold, or extend a candidate-only result to the full RH criterion.

At a common primorial cutoff, the signed integral and endpoint terms coincide. FIB information must independently restrict the attained cutoffs or supply an actual-candidate lower bound for $D_N=\log(\Sigma(N)/Z(N))$; an address change alone supplies neither.

On the full CA test set this self-cutoff deficit is identically zero, including after restriction to each integer's actual residue; see the [classical CA scope note](../Arith/alaoglu1944highly.md). A positive-deficit estimate is therefore only an option for other candidates. The signed comparison remains applicable to CA integers with $d_C=0$, without providing the missing prime-error estimate.

The [Guth–Maynard short-interval application](../Analytic/guthmaynard2024largevalues.md) makes one limitation precise. On the cutoffs at the lower endpoints of **all** prime-index FIB windows, a uniform eventual square-root-scale lower bound for $I_\psi$ already implies RH: monotonicity controls interpolation between samples, and the cited short-interval theorem bounds their gaps. The same implication has not been established for the cutoffs of actually existing low-loss candidates, whose gaps are unknown. These two sets of cutoffs must remain distinct when using the sufficient condition above.

## The exponent-excess bound at an actual tied CA candidate

The following connects the existing CA estimate to the actual exception
budget in the [Pollack application](../Scale/pollack2017nonresidues.md).
It is an application of the cited estimates, not a new analytic theorem
or a Lean-verified result.

Fix a threshold parameter $\epsilon_i$ from (3.3), and let
$N=N_{\epsilon_i}>N^{(0)}$ be the representative defined by (3.8),
including every prime-power layer whose activation price equals
$\epsilon_i$. Let $n$ be any actual CA maximizer at this same parameter.
Remark 3.1, printed p.11, describes both ordinary and extraordinary
ties: every such $n$ divides $N$. This comparison transports no
canonical composition or discriminant from $N$ to $n$.

The exponent excess is monotone under divisibility, so

$$
B_{\rm exp}(n)=\log\frac n{\operatorname{rad}(n)}
\le\log\frac N{\operatorname{rad}(N)}
=E=\sum_{k\ge2}\vartheta(\xi_k).
\tag{C1}
$$

Here $\operatorname{rad}(N)=\prod_{p\le\xi}p$ follows from (3.8);
the final equality is (4.3)–(4.4), printed p.23. To apply Lemma 4.1,
printed p.24, take $X=N'=N_{\epsilon_{i-1}}$. Since $N>N^{(0)}$,
the adjacent representative satisfies $X=N'\ge N^{(0)}$ and $X<N$.
Thus, with $t=\log\xi$,

$$
E\le U(\xi):=\sqrt{2\xi}
\left(1-\frac{\log2}{2t}+\frac{19.512}{t^2}\right).
\tag{C2}
$$

The boundary $N=N^{(0)}$ is not covered by this particular
instantiation of the lemma. For the same actual $n$ with canonical
unit bit one and nonsquare signed discriminant, reuse the Pollack
application's $H_1,T_1,R_1,m_1$. Combining its exponent inequality
with (C1)–(C2) gives the explicit comparison

$$
\log H_1(n)\le\log5+U(\xi).
\tag{C3}
$$

This includes intermediate tied maximizers. It changes neither their
actual $c\bmod H_1$, their primitive conductor $q$, nor the signed
Euler budget.

For clarity, the upper bound already recorded in the Pollack
application is $m_1\le\mathcal U_n:=|D|R_1/T_1^2$. Its numerical
value itself satisfies

$$
\mathcal U_n\ge\frac{|D|}{H_1^2}
\ge\frac{|D|}{25}\exp[-2U(\xi)],
\tag{C4}
$$

because $T_1\mid H_1$ and $R_1\ge1$. Under the **additional**
same-candidate assumptions $|D|\asymp n$ and $\xi\sim\log n$,
this lower bound on $\mathcal U_n$ is $n^{1-o(1)}$. Consequently
this upper-bound certificate cannot establish $m_1^b\le\log n$
for fixed $b>0$ in that regime, even after maximizing the allowed
supported square-factor removal. This is not a lower bound on $m_1$.
Independent conductor information or square factors outside this
supported exception budget could still give a smaller modulus.
The assumption $|D|\asymp n$ has not been established for the actual
remaining extremal candidates; (C4) is conditional in that comparison.

## An effective core bound at the selected GA2 source

This application improves the effective positive-core allowance, while
leaving the complete signed Robin tail unbounded. It uses the same
critical integer and clock throughout. The envelope theorem, GA2
comparisons, prime-power estimates, and core identity are existing
results; no originality or Lean verification is claimed for their
combination.

Under a Robin counterexample, use the selected source in the
[Polak application](../Analytic/polak2026finiterobinca.md#application-at-the-same-critical-source-and-clock):
$N$ is CA and GA2, $A=\log N$, $P=P^+(N)$, and $P<A<P^+$.
Its actual exponents attain the full-support minimum at price
$1/(A\log A)$, so

$$
\Delta(N)=I_\psi(A)+D^*(A),\qquad
D^*(A)=R_{\rm core}(N,A)-C_{\rm pp}(A).
\tag{G1}
$$

Set $L=\log A$ and $T=\sqrt A L$. The classical CA record property in
[Alaoglu–Erdős](../Arith/alaoglu1944highly.md) gives
$\Sigma(N)=Z(N)$, where $Z(n)=\sigma(n)/n$.
Let $x$ be the primorial cutoff
$\vartheta(x)\le A<\vartheta(x^+)$, so
$\Phi(N)=\mathcal P(x)$, with
$\mathcal P(u)=\prod_{q\le u}(1-1/q)^{-1}$.
Since $\vartheta(P)\le A$, we have $x\ge P$.
Every prime in $(P,x]$ is absent from $N$ and exceeds $A$.

### Cancelling the suffix at the actual clock

For each such prime $q$, the GA2 comparison with $qN$ gives

$$
\log(1+1/q)
\le\log\frac{\log(A+\log q)}{\log A}
\le\frac{\log q}{A\log A}.
\tag{G2}
$$

The final inequality is the concavity tangent for
$u\mapsto\log\log(A+u)$ at $u=0$. Equivalently, the already established
CA optimality at price $1/(A\log A)$ supplies this local upper bound.
It is not a new gain from jointly optimizing different integers.
Using $\log(q/(q-1))=\log(1+1/q)-\log(1-q^{-2})$ yields

$$
\log\frac{\mathcal P(x)}{\mathcal P(P)}
\le\frac{\vartheta(x)-\vartheta(P)}{A\log A}
  +\sum_{q>A}-\log(1-q^{-2}).
\tag{G3}
$$

Put $m=\lfloor A\rfloor$. The prime sum is at most the integer sum,
which telescopes:

$$
\sum_{q>A}-\log(1-q^{-2})
\le\sum_{n=m+1}^\infty-\log(1-n^{-2})
=\log\frac{m+1}{m}<\frac1{A-1}.
\tag{G4}
$$

Consequently Nicolas's effective $R_-(N)$ above and
$\Sigma(N)=Z(N)$ give

$$
\begin{aligned}
R_{\rm core}(N,A)
&=\frac{A-\vartheta(P)}{A\log A}
  +\log\frac{\mathcal P(P)}{Z(N)}\\
&>\log R_-(N)+\frac{A-\vartheta(x)}{A\log A}
                -\frac1{A-1}\\
&\ge\log R_-(N)-\frac1{A-1}.
\end{aligned}
\tag{G5}
$$

This uses the primorial cutoff only to cancel its missing-prime suffix.
It neither transports $I_\psi(A)$ to $x$ nor requires an effective
prime-gap bound or an endpoint estimate for $\vartheta(x)-x$.

### An effective allowance stronger than the existing core envelope

The [Dusart prime-power input](../Weil/dusart2010estimates.md#同一-robin-来源的有效素数幂修正),
Proposition 3.2, gives
$TC_{\rm pp}(A)<2.00014+2.67A^{-1/6}$.
For $N\ge N^{(0)}$ and $L\ge26$, put

$$
b(L)=2\sqrt2-\frac{(2+\log2)\sqrt2}{L}+\frac{6.78}{L^2}.
$$

Then $0<b(L)<3$, and $R_-(N)=1+b(L)/T$.
The elementary inequality $\log(1+u)\ge u-u^2/2$, $u\ge0$, gives
$T\log R_-(N)>b(L)-5/T$.
Also $T/(A-1)<2L/\sqrt A$. Combining these inequalities with
(G1) and (G5) gives the explicit bound

$$
\boxed{\sqrt A\log A\,D^*(A)>\mathcal E(L),}
\tag{G6}
$$

where

$$
\mathcal E(L)=2\sqrt2-\frac{(2+\log2)\sqrt2}{L}
 +\frac{6.78}{L^2}-2.00014-2.67e^{-L/6}
 -(2L+5/L)e^{-L/2}.
\tag{G7}
$$

This is strictly stronger than the published $D_{\rm lb}(A)$ on the
whole range $L\ge26$, not just its half-unit simplification.
To check the comparison, set $a=\log2$ and

$$
U(L)=\frac1{\sqrt2}
\left(\frac L{L+a}-\frac{2L}{(L+a)^2}\right).
$$

The displayed definition of $D_{\rm lb}$ in the Polak note, with
$j_A>0$ and $s_A>0$, gives $D_{\rm lb}(A)<j_A/2<U(L)$.
For $L\ge26$,

$$
U'(L)=\frac1{\sqrt2}
\left(\frac a{(L+a)^2}+\frac{2(L-a)}{(L+a)^3}\right)
<\frac{a+2}{\sqrt2L^2}.
$$

Both exponential error terms in (G7) decrease, hence

$$
(\mathcal E-U)'(L)>
\frac1{L^2}\left(\frac{a+2}{\sqrt2}-\frac{13.56}{L}\right)>0.
$$

Elementary rational bounds
$1.414<\sqrt2<1.415$, $0.69<\log2<0.70$,
$e^{13/3}>75$, and $e^{13}>400000$ give
$\mathcal E(26)>0.65$ and $U(26)<0.64$.
For the exponential bounds one can use
$\sum_{j=0}^9 4^j/j!>54$,
$e^{1/3}>25/18$, and $e>8/3$.
The comparison therefore has the uniform strict surplus

$$
\mathcal E(L)>D_{\rm lb}(A)+0.01\qquad(L\ge26).
\tag{G8}
$$

Moreover $\mathcal E$ is increasing on this range and
$\lim_{L\to\infty}\mathcal E(L)=2\sqrt2-2.00014$.
This is the limit of the lower-bound function, not a new assertion
about the attained core's asymptotic. The core asymptotic
$2(\sqrt2-1)$ is already recorded in the FIB volume, §93.

### Paying the thresholds and retaining the signed obligation

The existing [Axler finite stop](../notes/axler2023robin.md),
Lemma 2.3, puts this selected source above the $K$th primorial,
$K=999999476056$. Hence $A>K\log2>K/2$ and $L>26$.
For the latter comparison, $e<11/4$ and
$(11/4)^{26}<4\cdot10^{11}<K/2$ suffice.

The exact $N^{(0)}$ in Nicolas's (3.13), printed p.12, has largest prime
$1000000007$ and maximum exponent $33$. It divides the $33$rd power of
that primorial. Dusart's Theorem 5.2, $k=0$, therefore gives

$$
\log N^{(0)}\le33\vartheta(1000000007)
<66(1000000007)<K/2<A.
$$

Thus the $6.78$ branch of Theorem 1.3 is paid using the same finite
supplier as the previous core application. The decimal approximation
to $\log N^{(0)}$ is not used to define or certify its threshold.
No new finite computation, unbounded source sequence, or additional
large finite Robin theorem is needed for (G6)–(G8).

At this fixed source the resulting sufficient condition is

$$
\sqrt A\log A\,I_\psi(A)\ge-\mathcal E(\log A).
\tag{G9}
$$

The strict core inequality then supplies strict Robin.
For a zero-response representation, retain the elementary terms from the
full signed formula above. With $L=\log A$, write

$$
\begin{aligned}
R_{\rm elem}(A)
&=\frac{\log(2\pi)}{AL}
 +\frac12\int_A^\infty\log(1-x^{-2})k(x)\,dx,\\
r_A&=\sqrt A L\,R_{\rm elem}(A).
\end{aligned}
$$

Thus $R_{\rm elem}=\log(2\pi)/(AL)-T_{\rm triv}$ in the notation
of (V4)–(V6), and it is $R_{\rm Ak}(1;A)$ in the Akatsuka formula below.
For $A\ge e^2$, the already used inequality
$-\log(1-u)\le u/(1-u)$ and $\int_A^\infty k(x)\,dx=1/(AL)$ give

$$
0<\frac{\log(2\pi)-1/[2(A^2-1)]}{\sqrt A}
\le r_A\le\frac{\log(2\pi)}{\sqrt A}.
$$

This is the elementary correction to the nontrivial-zero response,
not another zero term. In particular, the exact source identity and
(G9) read

$$
-\sqrt A L\,I_\psi(A)=\sqrt A L\,Z_{\rm orig}(A)+r_A,
\qquad
\sqrt A L\,Z_{\rm orig}(A)+r_A\le\mathcal E(L).
$$

The second inequality is equivalent to (G9). Although $r_A\to0$, its
positive sign must be retained in exact budgets. Every subsequent
approximation to $Z_{\rm orig}$ still requires this correction when
used to bound the full integral. These are applications of the existing
explicit formula, not a new signed estimate or Lean verification.

A selected counterexample would instead have to satisfy
$\sqrt A\log A\,I_\psi(A)<-\mathcal E(\log A)$.
The new allowance is weaker as a tail requirement than the existing
$-D_{\rm lb}(A)$ requirement; neither signed tail bound has been proved.
The full integral over $[A,\infty)$ remains in (G9).
This paper-level improvement does not prove RH, and finite source
checks and source inspection do not certify its external premises.

## The same effective allowance on actual GA2 cores

The allowance $\mathcal E$ in (G7) also bounds the actual extended core
of an arbitrary large GA2 integer. This uses the envelope theorem at
the original integer, without identifying it with an envelope maximizer
or a CA optimizer. It does not strengthen the independent $D^*(A)$.

Let $N$ be GA2, $A=\log N$, $L=\log A$, and $T=\sqrt A L$, with
$N\ge N^{(0)}$ and $L\ge26$. The
[GA2 support argument](../Analytic/polak2026finiterobinca.md#application-to-arbitrary-ga2-sources-including-extra-prime-support)
gives every $p\le A$ as a divisor of $N$. In particular
$\vartheta(A)\le A$. Let $x$ be the last prime for which
$\vartheta(x)\le A<\vartheta(x^+)$; its prime set includes all primes
at most $A$. Numeric $x\ge A$ is unnecessary. As above,
$\Phi(N)=\mathcal P(x)$ and $Z(N)\le\Sigma(N)$, so

$$
\frac{\mathcal P(x)}{Z(N)}
\ge\frac{\Phi(N)}{\Sigma(N)}\ge R_-(N).
\tag{A1}
$$

Every prime $q$ in the suffix $(A,x]$ satisfies
$\log(1+1/q)<1/q<\log q/(A\log A)$, whether or not $q$ divides
$N$. The Euler-factor splitting used in (G3), followed by the same
integer-tail payment (G4), therefore gives

$$
\begin{aligned}
\log\frac{\mathcal P(x)}{\mathcal P(A)}
&\le\frac{\vartheta(x)-\vartheta(A)}{A\log A}
 +\sum_{q>A}-\log(1-q^{-2})\\
&<\frac{\vartheta(x)-\vartheta(A)}{A\log A}+\frac1{A-1}.
\end{aligned}
\tag{A2}
$$

The non-strict first comparison and strict positive tail allowance also
cover an empty suffix. No absent-prime premise is used here.

The actual core in the linked extra-support identity is

$$
\begin{aligned}
K_N(A)
&=\frac{A-\vartheta(A)}{A\log A}
   +\log\frac{\mathcal P(A)}{Z(N)}-C_{\rm pp}(A)\\
&=\sum_{p\le A}\Phi_{p,A}(v_p(N))-C_{\rm pp}(A)
  +\sum_{\substack{p>A\\p\mid N}}\Xi_{p,A}(v_p(N)),\\
\Delta(N)&=I_\psi(A)+K_N(A).
\end{aligned}
\tag{A3}
$$

Combining (A1)–(A2) and $\vartheta(x)\le A$ gives

$$
K_N(A)>\log R_-(N)-\frac1{A-1}-C_{\rm pp}(A).
\tag{A4}
$$

The existing estimates used in (G6)–(G7) apply to this right-hand side
unchanged. They give

$$
\boxed{T K_N(A)>\mathcal E(L)>D_{\rm lb}(A)+0.01.}
\tag{A5}
$$

The $D_{\rm lb}$ comparison is (G8), not a new computation. Since GA2
gives $\Delta(N)\le0$, every such actual source must satisfy

$$
\boxed{T I_\psi(A)<-\mathcal E(L).}
\tag{A6}
$$

Thus the [conditional unbounded GA2 family](../Arith/caveney2012sacaga.md#the-published-unbounded-ga2-supplier-under-rh-failure)
can be used with this stronger allowance. An eventual lower bound
$T I_\psi(A)\ge-\mathcal E(L)$ on all sufficiently large GA2 clocks
would contradict that family under RH failure. This signed lower bound
remains unproved.

The result estimates $K_N(A)$, not $D^*(A)$: the inequality
$K_N(A)\ge D^*(A)$ does not transport a lower bound backwards to the
minimum. The selected CA source has equality by (G1); arbitrary GA2
sources have no such equality here. This is a source-scope application
of the existing envelope and payment estimates, without a new core
theorem, originality claim, finite verification, or Lean result.

### All-integer forward comparisons bound the envelope deficit

The CNS tail maximizers also retain more information than GA2 alone
provides for this argument. Let $N>e$ satisfy
$G(m)\le G(N)$ for every integer $m\ge N$, and keep the existing
$D_N=\log(\Sigma(N)/Z(N))\ge0$. Choose an actual $d\le N$ attaining
$\Sigma(N)$ and put

$$
m=d\left\lceil\frac Nd\right\rceil,
\qquad N\le m<N+d\le2N.
$$

Divisibility monotonicity gives $Z(d)\le Z(m)$. Applying the same
forward record condition at this actual $m$ gives

$$
\frac{\Sigma(N)}{Z(N)}
\le\frac{Z(m)}{Z(N)}
\le\frac{\log\log m}{\log\log N}
<\frac{\log\log(2N)}{\log\log N}.
$$

Hence, with the same $A=\log N$ and $L=\log A$,

$$
\boxed{0\le D_N
<\log\frac{\log(A+\log2)}{\log A}
<\frac{\log2}{A\log A}.}
$$

The last comparison is the strict concavity tangent used in (G2).
The case $d=N$ or $m=N$ has $D_N=0$ and satisfies these strict
positive allowances. The constructed $m$ need not be a multiple of
$N$, so this proof uses the all-integer forward comparisons of the
published tail maximizers, rather than just their GA2 comparisons.

Along the CNS family under RH failure,

$$
0\le\sqrt A\log A\,D_N<\frac{\log2}{\sqrt A}\longrightarrow0.
$$

Thus replacing $Z(N)$ by $\Sigma(N)$ loses only a vanishing amount at
the original critical scale on these actual sources. Conversely, an
upper bound of this size cannot supply a fixed positive lower funding
term from $D_N$. It neither identifies an exponent profile nor makes
$N$ CA or GA1. This is a short application of standard divisibility
monotonicity and the existing source comparisons, without a priority
claim, new Lean wrapper, or signed-tail estimate.

## A fixed positive scale mixture cannot remove the functional-equation weight

The signed formula above and the actual-source condition (G9) are
retained here. Durkan–Hughes–Pearce-Crump, *Generalisations of the
Landau–Gonek theorem and applications to mean values of zeta*,
[arXiv:2601.18025v1](https://arxiv.org/abs/2601.18025v1), Theorem 5,
instead estimates the dyadic sum

$$
D_T(X)=\sum_{T<\operatorname{Im}\rho\le2T}\chi(\rho)X^\rho,
\qquad \zeta(s)=\chi(s)\zeta(1-s).
$$

The sum uses the actual zeros with multiplicity. Its complex,
zero-dependent weight is part of the theorem; the RH-dependent errors
cannot be used unconditionally. This application addresses only one
proposed weight-removal interface. It does not reassess that theorem,
claim an original transform obstruction, or provide Lean verification.

Fix the same cutoff $A>1$ throughout. The coefficient contributed by
the original tail to a zero $s$ is

$$
F_A(s)=\frac1s\int_A^\infty
u^{s-2}\frac{1+\log u}{\log^2u}\,du,
\qquad 0<\operatorname{Re}s<1.
\tag{M1}
$$

In the signed explicit formula its contribution is $-F_A(\rho)$.
The pole term and the trivial-zero integral remain those displayed
above. Integration by parts identifies (M1) with the two corresponding
terms of that existing formula; no zero tail is truncated here.

### The original coefficient already has a positive Mellin representation

Put $k(u)=(1+\log u)/(u^2\log^2u)$. Since

$$
\int_v^\infty k(u)\,du=\frac1{v\log v}\qquad(v>1),
$$

integrating $x^{s-1}$ over $0<x<u$ and changing the order gives

$$
F_A(s)=\int_0^\infty
\frac{x^{s-1}}{\max(A,x)\log\max(A,x)}\,dx.
\tag{M2}
$$

For real $0<s<1$ this follows by Tonelli. For complex $s$ in the
same strip, the absolute integral is the finite integral with exponent
$\operatorname{Re}s$, so Fubini gives the identical formula. Thus
$F_A(s)=\int x^s\,d\nu_A(x)$ for the positive scale measure

$$
d\nu_A(x)=\frac{dx}{x\max(A,x)\log\max(A,x)}.
$$

This representation by itself supplies no one-sided bound for the
signed zero sum. Applying it directly to $D_T$ would retain the unwanted
$\chi(\rho)$ factor.

### The reciprocal weight destroys fixed positive scale representability

The classical functional equation, in
[DLMF 25.4.2](https://dlmf.nist.gov/25.4.E2), has

$$
\chi(s)=2^s\pi^{s-1}\sin(\pi s/2)\Gamma(1-s).
$$

Consequently, for real $\sigma\uparrow1$,
$\chi(\sigma)>0$ and $\chi(\sigma)^{-1}\sim(1-\sigma)/2$.
For $0<\sigma<1$, $F_A(\sigma)/\chi(\sigma)$ is strictly positive,
but

$$
\lim_{\sigma\uparrow1}\frac{F_A(\sigma)}{\chi(\sigma)}=0.
\tag{M3}
$$

To verify the endpoint, set $\epsilon=1-\sigma$ and
$w(u)=(1+\log u)/\log^2u$, which tends to zero. For every $\eta>0$,
choose $B\ge A$ with $w(u)\le\eta$ for $u\ge B$. The finite-prefix
contribution to $\epsilon\int_A^\infty u^{-1-\epsilon}w(u)\,du$
tends to zero, while its tail is at most
$\eta\epsilon\int_B^\infty u^{-1-\epsilon}du
=\eta B^{-\epsilon}\le\eta$. This proves (M3), including the
complete infinite tail and the fixed original cutoff.

Suppose a nonnegative Borel measure $\mu_A$ on $(0,\infty)$ had
finite real moments throughout $0<\sigma<1$ and satisfied the exact
all-strip transport identity

$$
F_A(s)=\chi(s)\int_0^\infty X^s\,\mu_A(dX),
\qquad 0<\operatorname{Re}s<1.
\tag{M4}
$$

It may depend on $A$, but is fixed as $s$ varies. Fatou along any real
sequence $\sigma\uparrow1$ and (M3) imply

$$
0\le\int_0^\infty X\,\mu_A(dX)
\le\liminf_{\sigma\uparrow1}\int_0^\infty X^\sigma\,\mu_A(dX)=0.
$$

Since $X>0$ everywhere on the scale domain, $\mu_A=0$. This contradicts
the strict positivity of $F_A(\sigma)/\chi(\sigma)$. Hence no such
nonnegative measure exists, even without requiring finite total mass
or a finite first moment in advance. Matching the real interval alone
already produces the contradiction.

If (M4) held, each finite dyadic actual-zero multiset would obey
$\sum F_A(\rho)=\int D_T(X)\,\mu_A(dX)$, with its multiplicities
unchanged. The result rules out this fixed positive, all-strip kernel
transport before any summation over heights. It does not rule out
signed or complex measures, interpolation only on the actual zero
set, height-dependent transforms, or approximation with a separately
bounded remainder. Those are different interfaces requiring their own
integrability, uniform error and sign estimates. In particular, an
all-strip identity is a sufficient universal matching requirement,
not a necessary condition for every use of the weighted theorem.

No estimate for the original signed $I_\psi(A)$ follows. Condition
(G9), at the same selected integer and with the full tail, remains
unproved; RH remains unproved.

## Exact signed scale transport and the cost of its large-scale tail

The preceding positive-measure exclusion leaves signed and complex
transports open. For the same fixed $A>1$ and original coefficient
$F_A$ in (M1), a classical cosine–Mellin calculation constructs a real
signed transport. Its absolute moments also explain why the displayed
error in Durkan–Hughes–Pearce-Crump's Theorem 5 cannot simply be
integrated over all scales. This is an application of classical
transforms and the already assessed theorem, with no originality or
Lean-verification claim.

### A reciprocal-coordinate cosine transform

Let $h_A(u)=1/[\max(A,u)\log\max(A,u)]$ and put

$$
v_A(x)=\frac{h_A(1/x)}x=
\begin{cases}
1/\log(1/x),&0<x\le1/A,\\
1/(A\log A\,x),&x\ge1/A.
\end{cases}
\tag{S1}
$$

The two branches agree at $1/A$. Set $v_A(0)=0$.
The function is locally absolutely continuous, tends to zero at
infinity, and has the integrable derivative

$$
v_A'(x)=
\begin{cases}
1/[x\log^2(1/x)],&0<x<1/A,\\
-1/(A\log A\,x^2),&x>1/A,
\end{cases}
\qquad \int_0^\infty|v_A'(x)|\,dx=\frac2{\log A}.
$$

Define the improper cosine transform for $X>0$ by

$$
g_A(X)=2\int_0^\infty v_A(x)\cos(2\pi Xx)\,dx
=-\frac1{\pi X}\int_0^\infty v_A'(x)\sin(2\pi Xx)\,dx.
\tag{S2}
$$

The first integral converges by Dirichlet on its $1/x$ tail; the
second is absolutely convergent. Integration by parts gives the
equality without a boundary term. In particular,

$$
|g_A(X)|\le\frac2{\pi X\log A}.
\tag{S3}
$$

At the other endpoint, splitting the tail at $1/X$ gives

$$
g_A(X)=\frac2{A\log A}\log(1/X)+O_A(1)
\qquad(X\downarrow0).
\tag{S4}
$$

Indeed, the compact part is bounded. In the tail integral, subtracting
one from the cosine between $1/A$ and $1/X$ has a bounded integral
after the substitution $t=Xx$, and the integral from $1/X$ to
infinity is bounded by Dirichlet. Thus
$\int_0^\infty X^{\sigma-1}|g_A(X)|\,dX<\infty$ for every
$0<\sigma<1$.

The standard cosine moment in
[DLMF 5.9.6](https://dlmf.nist.gov/5.9.E6), followed by integration
by parts, yields

$$
\int_0^\infty t^{s-2}\sin t\,dt
=\frac{\Gamma(s)\cos(\pi s/2)}{1-s}
\qquad(0<\operatorname{Re}s<1).
$$

Applying this to the second integral in (S2) is a justified Fubini
step: its absolute double integral is a finite constant depending on
$\sigma=\operatorname{Re}s$ times
$\int_0^\infty|v_A'(x)|x^{1-\sigma}\,dx<\infty$.
Integration by parts in $x$ then gives

$$
\begin{aligned}
\int_0^\infty X^{s-1}g_A(X)\,dX
&=2(2\pi)^{-s}\Gamma(s)\cos(\pi s/2)
\int_0^\infty v_A(x)x^{-s}\,dx\\
&=\frac{F_A(s)}{\chi(s)}.
\end{aligned}
\tag{S5}
$$

Here $x=1/u$ identifies the last integral with (M2), and the
classical functional equation identifies its prefactor with
$\chi(1-s)=1/\chi(s)$. Thus $d\mu_A(X)=g_A(X)dX/X$ is a locally
finite real signed Borel scale measure with finite absolute moments
throughout the open strip; finite total variation is not required.
The preceding positive-measure result and the strictly positive real
moments imply that this density has both signs; no large-$X$
pointwise asymptotic or sign location is assumed.

For each finite actual dyadic zero multiset, (S5) gives the exact
coefficient identity

$$
\sum_{T<\operatorname{Im}\rho\le2T}F_A(\rho)
=\int_0^\infty D_T(X)\,\mu_A(dX).
\tag{S6}
$$

Absolute strip moments justify the finite sum interchange and preserve
all multiplicities. Summing over infinitely many height blocks is a
separate interchange or remainder obligation; (S6) alone does not pay it.

### Every absolutely integrable exact transport has a missing higher moment

There is a sharper endpoint than (M3). With $L=\log A$ and
$\epsilon=1-\sigma\downarrow0$, substituting $u=e^y$ in (M1) gives

$$
F_A(1-\epsilon)=\frac1{1-\epsilon}
\int_L^\infty e^{-\epsilon y}\left(\frac1y+\frac1{y^2}\right)dy
=\log(1/\epsilon)+O_A(1).
$$

For the $1/y$ integral, split at $1/\epsilon$: replacing the
exponential by one below that point changes the answer by at most
one, while the rescaled tail is a fixed convergent integral. The
$1/y^2$ integral is at most $1/L$. Since
$\chi(1-\epsilon)^{-1}=\epsilon/2+O(\epsilon^2)$,

$$
\frac{F_A(1-\epsilon)}{\chi(1-\epsilon)}
=\frac\epsilon2\log(1/\epsilon)+O_A(\epsilon).
\tag{S7}
$$

Suppose any locally finite signed or complex Borel scale measure
$\mu$, allowing infinite total variation, had finite absolute
moments at every $0<\sigma<1$, realized the exact all-strip
identity (M4), and also had a finite absolute moment at $1+\delta$
for some $\delta>0$. For $\sigma$ in a neighborhood of one,
$X^\sigma\log X$ is dominated against $|\mu|$ by a fixed
subunit moment on $0<X<1$ and the $1+\delta$ moment on $X\ge1$.
Dominated convergence therefore makes $\int X^\sigma\,\mu(dX)$
differentiable at one, with a finite derivative. Its value there is
zero by (M3). But (S7) forces its left difference quotient to tend
to $-\infty$, a contradiction. Hence every such exact transport has

$$
\boxed{\int_0^\infty X^{1+\delta}\,|\mu|(dX)=\infty
\quad\text{for every }\delta>0.}
\tag{S8}
$$

This includes the constructed real density. Its divergent higher
moment comes from $X\ge1$, because its absolute subunit moments
already bound the contribution of $0<X<1$. No explicit asymptotic
for $g_A$ is needed for this moment obstruction.

### Consequence for the existing error supplier

Theorem 5, printed p.4, equation (2.1), is uniform for $X\ge1$ and
$T>1$. One term in its displayed absolute-error majorant is

$$
\frac{(\log T)^2}{\sqrt T}\,X^{1+1/\log T}.
$$

For every fixed $T>1$, (S8) shows that integrating this term against
the total variation of any exact all-strip transport is infinite.
Thus the displayed error majorant cannot, by direct absolute
integration over $[1,\infty)$, control the complete signed transport
in (S6). This is a limitation of that guaranteed majorant, not a
claim that the actual error integral diverges. The source theorem
also leaves the scale interval $(0,1)$ to a separate argument.

Using a scale truncation requires an independent bound for its
complement. A cancellation-sensitive integrated remainder, a
different large-scale error estimate, or matching only on the actual
zero set could change the conclusion. No such supplier is established
here. The original infinite $I_\psi(A)$ tail, same selected integer,
and sufficient condition (G9) remain unchanged and unproved; RH
remains unproved.

## A finite first absolute moment controls a scale complement

The higher-moment obstruction (S8) does not assert that the first
absolute moment is infinite. For the constructed density, that endpoint
is finite and has an explicit tail allowance. The following estimates
use (S1)–(S6), without repeating the cosine–Mellin transport proof or
the Durkan–Hughes–Pearce-Crump theorem. They are paper-level applications
of the elementary Dirichlet estimate for an oscillatory integral; no
originality, numerical-experiment or Lean-verification claim is made.

### An explicit bound at the large-scale endpoint

Let $A\ge e^2$, $L=\log A$ and $k=2\pi X\ge A$. On
$0<x\le1/A$ the function

$$
u(x)=\frac1{x\log^2(1/x)}
$$

is decreasing: its derivative is
$-(\log(1/x)-2)/[x^2\log^3(1/x)]\le0$. Split the first branch of
$v_A'$ in (S2) at $1/k$. On its initial part,

$$
\left|\int_0^{1/k}u(x)\sin(kx)\,dx\right|
\le k\int_0^{1/k}\frac{dx}{\log^2(1/x)}
\le\frac1{\log^2k}.
$$

For a nonnegative decreasing function $w$ on $[a,b]$, integrating
against the primitive $\int_a^x\sin(kt)dt$, whose modulus is at most
$2/k$, gives
$|\int_a^bw(x)\sin(kx)dx|\le2w(a)/k$.
Apply this once to $u$ on $[1/k,1/A]$, and once to
$1/(ALx^2)$ on $[1/A,\infty)$. These contributions are bounded by
$2/\log^2k$ and $2A/(kL)$ respectively. Thus

$$
\boxed{
|g_A(X)|\le\frac3{\pi X\log^2(2\pi X)}
             +\frac A{\pi^2X^2L}
\qquad(2\pi X\ge A\ge e^2).}
\tag{C1}
$$

This is a bound rather than an asserted asymptotic or an eventual sign
for the density. Integrating it gives, for $R\ge A$,

$$
J_A(R):=\int_R^\infty|g_A(X)|\,dX
\le\frac3{\pi\log(2\pi R)}+\frac A{\pi^2RL}
<\frac2{\log R}.
\tag{C2}
$$

For the last inequality, put $v=R/A\ge1$ and use
$1+\log v/L\le v$, so $A/(RL)\le1/\log R$; also
$3/\pi+1/\pi^2<2$. The existing small-$X$ estimate (S4) and local
continuity of (S2) then give

$$
\int_0^\infty X\,|\mu_A|(dX)
=\int_0^\infty|g_A(X)|\,dX<\infty.
\tag{C3}
$$

Dominated convergence at the endpoint $\sigma\uparrow1$, using (S4),
(C3) and the exact strip moments, also transports (M3) to the signed
identity

$$
\int_0^\infty X\,\mu_A(dX)
=\int_0^\infty g_A(X)\,dX=0.
\tag{C4}
$$

This signed cancellation coexists with a finite, positive first
absolute moment and with the divergent higher moments in (S8).

### Bound the actual block remainder on its scale complement

Keep the actual positive-ordinate zero multiset
$\mathcal Z_T=\{\rho:T<\operatorname{Im}\rho\le2T\}$, with every
multiplicity, and $D_T$ from the preceding note. Let $M_T(X)$ be the
three-branch main expression in the already assessed Theorem 5, and
define its actual remainder by

$$
\mathcal E_T(X)=D_T(X)-M_T(X),\qquad X\ge1.
$$

For $X\ge R\ge\max(A,T)$ its third branch applies. With
$y=\pi X/T>1$ it is

$$
M_T(X)=-X\sum_{y\le n<2y}\frac{\Lambda(n)}n
                                    e^{2\pi iX/n}.
$$

The [already inspected Dusart inputs](../Weil/dusart2010estimates.md)
$\vartheta(t)<2t$ and
$\psi(t)-\vartheta(t)<1.00007\sqrt t+1.78t^{1/3}$ give
$\psi(t)<5t$ for $t\ge1$. Hence

$$
|M_T(X)|\le\frac Xy\psi(2y)<10X.
$$

Define the finite block factor

$$
K_T=\sum_{\rho\in\mathcal Z_T}
                   |\chi(\rho)|T^{\operatorname{Re}\rho-1}.
$$

Because $0<\operatorname{Re}\rho<1$ and $X\ge T$,
$|D_T(X)|\le XK_T$. Thus the actual remainder, independently of
its printed superlinear majorant, obeys

$$
\boxed{
\int_R^\infty|\mathcal E_T(X)|\,|\mu_A|(dX)
\le(K_T+10)J_A(R)
<\frac{2(K_T+10)}{\log R}
\quad(R\ge\max(A,T),\ A\ge e^2).}
\tag{C5}
$$

The factor $K_T$ refers to the same actual finite multiset; it is not
an RH assumption, a numerical zero certificate or a selected favorable
configuration. In particular (C5) does not change the real parts to
$1/2$. It shows that this constructed transport's actual large-scale
remainder is absolutely integrable for each fixed block, although
direct integration of the published majorant remains infinite.
The two statements concern different integrands and do not contradict
one another.

### The omitted scale complements can receive a full height budget

Let $T_j=2^{j-1}T_0$, $j\ge1$, for any fixed $T_0>1$.
For any chosen $\varepsilon>0$, select finite cutoffs

$$
R_j\ge\max(A,T_j),\qquad
\log R_j\ge\frac{2^{j+1}(K_{T_j}+10)}{\varepsilon}.
\tag{C6}
$$

Then the entire, unbounded sequence of scale-complement remainders
has the absolute allowance

$$
\sum_{j\ge1}\left|
\int_{R_j}^\infty\mathcal E_{T_j}(X)\,\mu_A(dX)\right|
<\varepsilon.
\tag{C7}
$$

This follows directly from (C5) and $\sum_{j\ge1}2^{-j}=1$.
All ordinates above $T_0$ remain assigned to their original dyadic
blocks. No finite-height RH verification, critical-line substitution
or discarded infinite-height suffix is involved. The cutoffs depend
on $A$, the block factor and the requested allowance; a fixed moderate
cutoff is not asserted to suffice.

For each block, its exact coefficient sum in (S6) can consequently
be kept in the grouped form

$$
\begin{aligned}
\sum_{\rho\in\mathcal Z_{T_j}}F_A(\rho)
={}&\int_0^1D_{T_j}(X)\,\mu_A(dX)
   +\int_1^\infty M_{T_j}(X)\,\mu_A(dX)\\
 &+\int_1^{R_j}\mathcal E_{T_j}(X)\,\mu_A(dX)
   +r_j,\qquad \sum_{j\ge1}|r_j|<\varepsilon.
\end{aligned}
\tag{C8}
$$

The small-scale term is retained, and the main-expression integral
exists by (C3) and its finite-scale branches. The original integrated
explicit formula already supplies absolute convergence of the
$F_A(\rho)$ zero series. Together with (C7), this permits summing
(C8) with its first three terms **grouped per block**; it does not
permit separating those three infinite series without further
estimates. In the real signed explicit formula the conjugate blocks
give $-2\operatorname{Re}\sum F_A(\rho)$, so the complementary error
allowance is $2\varepsilon$ before the original
$\sqrt A\log A$ normalization. Pole and trivial-zero contributions
are unchanged.

This pays one complement obligation without proving the original
one-sided Robin bound. The remaining grouped small-scale, main and
retained-error terms still require a signed estimate at the same
selected cutoff. The printed theorem's error can be integrated on
each finite retained scale interval, but (C6) supplies no bound making
that increasing cost fit the Robin reserve. No such uniform balance,
effective zero computation or proof of RH is asserted here.


## Centering the large-scale arithmetic main expression

The first-moment cancellation (C4) also removes the continuous
prime-density contribution of the third branch of $M_T$. The
[previously assessed Fiori–Jaskari application](../Weil/broadbent2026mertens.md)
supplies an independent bound for the remainder. This concerns the
arithmetic main expression, with the same kernel and height blocks;
it does not estimate the actual zero remainder $\mathcal E_T$ or
reproduce the prime-number-theorem proof. These deductions are
paper-level applications with no originality or Lean-verification claim.

### Keep the moving frequency in the prime-error estimate

Reuse the explicit positive constant

$$
d=\frac52\left(\frac53\right)^{1/5}
            \left(\frac{2000}{161967}\right)^{3/5}
$$

from that existing application. Its unconditional conclusion is

$$
|\psi(u)-u|\le0.239u\,e^{-d\sqrt{\log u}}
\qquad(u\ge e^3).
\tag{P1}
$$

No new inspection or certification of its source computation is
claimed. In particular the prime powers are part of $\psi$.

Put $\psi_-(u)=\sum_{n<u}\Lambda(n)$. The endpoint difference
$\psi(u)-\psi_-(u)$ is at most $\log u$. Also $d<1$: use
$5/3<2$ and $2000/161967<1/64$ to get $d<5/16$.
For $v\ge3$, $v-\log v\ge\sqrt v$, hence
$\log u\le u e^{-d\sqrt{\log u}}$. Consequently

$$
|\psi_-(u)-u|<2u\,e^{-d\sqrt{\log u}}
\qquad(u\ge e^3).
\tag{P2}
$$

This includes the endpoint convention of the actual interval
$y\le n<2y$, including when $y$ or $2y$ is a prime power.

For $T>1$, $X$ with $y=\pi X/T\ge e^3$, write

$$
S_T(X)=\sum_{y\le n<2y}\frac{\Lambda(n)}n e^{2\pi iX/n},
\qquad
b_T=\int_T^{2T}\frac{e^{it}}t\,dt.
$$

Substituting $t=2\pi X/u$ gives
$\int_y^{2y}u^{-1}e^{2\pi iX/u}du=b_T$.
For $w_X(u)=u^{-1}e^{2\pi iX/u}$, Stieltjes integration with the
retained endpoints gives exactly

$$
\begin{aligned}
S_T(X)-b_T={}&w_X(2y)[\psi_-(2y)-2y]
             -w_X(y)[\psi_-(y)-y]\\
 &-\int_y^{2y}[\psi(u)-u]w_X'(u)\,du.
\end{aligned}
\tag{P3}
$$

The integral may use either endpoint version of $\psi$, since their
difference is supported at integers. As
$|w_X'(u)|\le u^{-2}+2\pi Xu^{-3}$, (P1)–(P2), with
$\delta_y=e^{-d\sqrt{\log y}}$, give

$$
|S_T(X)-b_T|
\le(4+2\log2+2T)\delta_y
<8T\delta_y.
\tag{P4}
$$

The factor $T$ records the moving phase. It has not been replaced by
a fixed-frequency constant or omitted after changing variables.
Ordinary integration by parts also gives $|b_T|\le2/T$.

### A signed cancellation and a controlled centered complement

Since $M_T(X)=-XS_T(X)$ on this large-scale branch, define the
centered expression on all $X\ge1$ by

$$
\widetilde M_T(X)=M_T(X)+Xb_T.
$$

Here the other two branches of $M_T$ remain their original formulas;
(P4) is used only where its threshold holds. Combining (P4) with
(C2) gives the independent complement estimate

$$
\boxed{
\int_R^\infty|\widetilde M_T(X)|\,|\mu_A|(dX)
<\frac{16T}{\log R}
       e^{-d\sqrt{\log(\pi R/T)}}
\quad\left(R\ge\max(A,e^3T/\pi),\ A\ge e^2\right).}
\tag{P5}
$$

The linear part is eliminated by the full signed moment, not by
discarding a part of the scale interval:

$$
\int_1^\infty M_T(X)\,\mu_A(dX)
=\int_1^\infty\widetilde M_T(X)\,\mu_A(dX)
 +b_T\int_0^1g_A(X)\,dX.
\tag{P6}
$$

Thus the small-scale term in (C8) changes to
$\int_0^1[D_T(X)+Xb_T]\,\mu_A(dX)$ when its main term is
replaced by the centered one. The actual zero remainder
$\mathcal E_T=D_T-M_T$ is unchanged. This retains all endpoint,
small-scale and conjugate contributions at the same cutoff.

### Cutoffs for the centered arithmetic contribution

With the same $T_j=2^{j-1}T_0$, any requested
$\varepsilon>0$ has explicit sufficient main-term cutoffs

$$
\begin{aligned}
V_j&=\max\left(3,
  d^{-2}\left[\max\left(0,
          \log\frac{16T_j2^j}{\varepsilon}\right)\right]^2\right),\\
Q_j&=\max\left(A,\frac{T_j}{\pi}e^{V_j}\right).
\end{aligned}
\tag{P7}
$$

Since $\log Q_j\ge2$, (P5) gives

$$
\sum_{j\ge1}\int_{Q_j}^\infty
|\widetilde M_{T_j}(X)|\,|\mu_A|(dX)<\varepsilon.
\tag{P8}
$$

For fixed $A,T_0,\varepsilon$, this choice has
$\log Q_j=O(j^2)$ as $j\to\infty$. It is a sufficient allowance
for the centered **arithmetic main** complement, not a necessary
cutoff or a replacement for (C6)'s zero-remainder cutoffs. It uses
the same cumulative error law for each prime interval and does not
combine independently favorable phases.

These estimates control another scale complement and make its
continuous cancellation explicit. They do not bound the signed
combination left in (C8): the small-scale zero sum, retained centered
main and actual zero remainder must still be compared together.
The growing-scale error cost and the original full Robin inequality
remain unpaid; no bound for $\sqrt A\log A\,I_\psi(A)$ at the selected
integer or proof of RH follows.


## A finite scale band already costs a growing absolute-error allowance

The infinite-moment obstruction (S8) and complement estimates (C5)–(C8)
leave a different question: can a retained scale cutoff make the printed
Durkan–Hughes–Pearce-Crump error majorant small enough? For the constructed
transport, a finite band gives a quantitative obstruction even before
its large-scale complement is considered. This is a paper-level
application of (S2) and the already assessed Theorem 5, not a new source
audit, originality claim or Lean-verified result.

### Locate a positive band of the same signed kernel

Let $A\ge e^8$, $L=\log A$, and write $X=A\xi$ and $k=2\pi\xi$.
Rescale the two branches of $v_A'$ in (S2), without changing the
original cutoff. Then

$$
ALg_A(A\xi)=\frac2k\left[B(k)-LI_L(k)\right],
\qquad
B(k)=\int_1^\infty\frac{\sin(kt)}{t^2}\,dt,
\quad
I_L(k)=\int_0^1\frac{\sin(kt)}{t(L-\log t)^2}\,dt.
\tag{R1}
$$

For $0<k\le1/2$, the sine is nonnegative on $[1,\pi/k]$.
Its chord bound on $[1,\pi/(2k)]$, followed by an absolute bound
on the remaining tail, gives

$$
B(k)\ge\frac{2k}{\pi}\log\frac\pi{2k}-\frac k\pi
>\frac k4.
\tag{R2}
$$

Here $\log(\pi/(2k))\ge\log\pi>1$ and $\pi<4$.
Also $\sin(kt)\le kt$ on $0<t<1$, so
$LI_L(k)\le k/L\le k/8$. Thus (R1) gives the uniform, explicit
positive band

$$
\boxed{g_A(X)>\frac1{4A\log A}
\qquad\left(\frac A{8\pi}\le X\le\frac A{4\pi},\ A\ge e^8\right).}
\tag{R3}
$$

This does not claim positivity on all scales; (C4)'s complete signed
first moment is still zero. The band is contained in $[1,R]$ for
every $R\ge A$. From $d|\mu_A|(X)=|g_A(X)|dX/X$, (R3),
$\log2>1/2$ and $\pi<4$ imply

$$
\int_1^R|\mu_A|(dX)>\frac1{8A\log A},\qquad
\int_1^RX^{1+\delta}|\mu_A|(dX)
>\frac{(A/32)^\delta}{128\log A}\quad(\delta>0).
\tag{R4}
$$

Both lower bounds concern the transport's absolute weights, not an
actual prime or zero error. No critical-line assumption, zero count
or finite zero computation is used.

### Balance the two printed height costs at every height

Theorem 5, printed p.4, (2.1), includes the two error shapes

$$
\sqrt T(\log T)^2,
\qquad \frac{(\log T)^2}{\sqrt T}X^{1+1/\log T}
\qquad(T>1,\ X\ge1).
$$

Their uniform implied constants are not numerically certified here.
Define the **unit-coefficient majorant allowance**, after the original
Robin normalization, by

$$
\mathcal B_A(T,R)=\sqrt A\log A\,(\log T)^2
\int_1^R\left(\sqrt T+\frac{X^{1+1/\log T}}{\sqrt T}\right)
|\mu_A|(dX).
\tag{R5}
$$

For $h=\log T>0$ and $R\ge A\ge e^8$, (R4) gives

$$
\mathcal B_A(T,R)>
 h^2\left[\frac18\sqrt{T/A}
       +\frac1{128}\sqrt{A/T}(A/32)^{1/h}\right]
\ge\frac{h^2}{16}\exp\left(\frac{\log(A/32)}{2h}\right).
\tag{R6}
$$

For any $c>0$, the minimum of $h^2e^{c/(2h)}$ over $h>0$
is $e^2c^2/16$, attained at $h=c/4$. Consequently

$$
\boxed{\mathcal B_A(T,R)>
\frac{e^2}{256}\,[\log(A/32)]^2
\quad\text{for every }T>1,\ R\ge A\ge e^8.}
\tag{R7}
$$

This is a lower bound on the allowance produced by integrating these
two positive majorant shapes. It is not a lower bound on
$|\mathcal E_T|$, on its actual integral, or on a Robin violation.
The other two printed error shapes can only increase this particular
absolute allowance. If the two shapes receive any fixed positive
coefficients $c_1,c_2$, the same argument has (R7)'s right side
multiplied by $\sqrt{c_1c_2}$. No numerical value for those coefficients
or effective failure threshold is inferred from big-$O$ notation.

The core reserve $\mathcal E(\log A)$ in (G7) remains bounded as
$A\to\infty$. In contrast, (R7) grows quadratically in $\log A$
for every choice of height $T$, including a height depending on $A$.
Thus this direct absolute-majorant transfer on retained intervals
$[1,R]$ with $R\ge A$ cannot provide a uniform bounded Robin allowance
uniformly as the clock tends to infinity. No unbounded sequence of
selected sources is asserted. Increasing those cutoffs, or improving
only their omitted complements, does not remove the finite band.
An actual-remainder bound that improves on these shapes, integration
that controls the remainder's sign, or a different scale decomposition
could change this conclusion; none is excluded by (R7).

The result specifies a finite retained-scale obstruction to one
estimate method. It does not supply the required signed estimate at
the same selected integer, drop any zero multiplicity or infinite
height block, or settle RH. The centered arithmetic-main estimates
(P5)–(P8) remain valid independently; they do not alter the actual
zero remainder used in (R5).


## Fixed Gaussian probes leave a coefficient remainder at unbounded height

Moriya, *A Gaussian-Perron Prime-Side Defect and Local Profiles Near
Critical-Line Zeros of the Riemann Zeta Function*,
[arXiv:2607.04316v2](https://arxiv.org/abs/2607.04316v2), Theorem 3.3,
printed p.7, gives an exact smoothed prime-defect formula with crossed
zero, pole, trivial-zero and shifted-contour terms. Its zero coefficient,
at a fixed observation point $z$, is

$$
G_{X,\alpha,z}(s)
=\frac{X^{s-z}\exp\!\bigl(\alpha^2\log X\,(s-z)^2\bigr)}{s-z},
\qquad X>1,\quad\alpha>0.
$$

Only zeros in the source's crossed strip contribute to that zero term.
The conditional localization in Theorem 7.4 requires its stated damping,
pole and contour hypotheses and concerns a fixed simple critical-line
zero; Theorem 7.6 additionally assumes RH. Those local conclusions are
not used below. The following paper-level application compares the
coefficient in Theorem 3.3 with the unchanged original $F_A$ in (M1),
without repeating the source's explicit-formula proof or asserting
originality or Lean verification.

### The original coefficient has a uniform algebraic lower bound

Fix $A\ge e^2$, put $L=\log A$, and define

$$
w(u)=\frac{1+\log u}{\log^2u},\qquad
h(u)=uw'(u)=-\frac{\log u+2}{\log^3u}.
$$

For $s=\sigma+it$ with $0<\sigma<1$, two integrations by parts in
(M1) give

$$
F_A(s)=\frac{w(A)A^{s-1}}{s(1-s)}
 +\frac{h(A)A^{s-1}+\int_A^\infty u^{s-1}h'(u)\,du}
        {s(1-s)^2}.
\tag{H1}
$$

The boundary terms at infinity vanish in this strip. Moreover
$h'(u)=2(\log u+3)/(u\log^4u)>0$ and $h(u)\to0$, so the numerator
of the remainder has modulus at most $2|h(A)|A^{\sigma-1}$.
Relative to the leading term its bound is

$$
\frac{2|h(A)|}{w(A)|1-s|}
=\frac{2(L+2)}{L(L+1)|1-s|}
\le\frac4{3|t|}.
$$

Thus, uniformly throughout the actual critical strip,

$$
\boxed{
|F_A(\sigma+it)|
\ge\frac{2w(A)A^{\sigma-1}}{3|s||1-s|}
\ge\frac{2w(A)}{3A(1+t^2)}
\qquad(A\ge e^2,\ |t|\ge4).}
\tag{H2}
$$

No real part has been replaced by $1/2$. This is a lower bound on an
individual complex coefficient's modulus, not on the signed zero sum
or on the Robin margin.

### Compare any finite family of fixed probes

For this same $A$, choose any finite nonempty family
$(X_j,\alpha_j,z_j,b_j)$, with $X_j>1$, $\alpha_j>0$ and arbitrary
complex coefficients $b_j$. The family may depend on $A$, but its
parameters are fixed as the zero height varies. Put

$$
a_j=\alpha_j^2\log X_j,\qquad
a_0=\min_j a_j>0,\qquad H=\max_j|\operatorname{Im}z_j|,
$$

$$
C_j=\max_{0\le\sigma\le1}
 X_j^{\sigma-\operatorname{Re}z_j}
 e^{a_j(\sigma-\operatorname{Re}z_j)^2},\qquad
C=\sum_j|b_j|C_j.
$$

Let $\eta_j(s)$ be the source's crossed-strip indicator; the same
argument permits any $|\eta_j(s)|\le1$. Define the zero coefficient
of the proposed finite reconstruction by

$$
Q(s)=\sum_j b_j\eta_j(s)G_{X_j,\alpha_j,z_j}(s).
$$

For $0<\sigma<1$ and $|t|\ge\max(4,2H)$, each denominator has
modulus at least $|t|/2$, and each Gaussian factor has its height part
at most $e^{-a_0t^2/4}$. Consequently

$$
\boxed{|Q(\sigma+it)|\le\frac{2C}{|t|}e^{-a_0t^2/4}.}
\tag{H3}
$$

The discrepancy even has an explicit height threshold. Since
$e^x\ge x^2/2$ for $x>0$, (H3) is at most
$64C/(a_0^2|t|^5)$. Set

$$
\Gamma=\max\!\left(4,2H,
 \left[\frac{384AC}{a_0^2w(A)}\right]^{1/3}\right).
$$

For $|t|\ge\Gamma$, this upper bound is at most
$w(A)/(3A(1+t^2))$. The triangle inequality and (H2) therefore give

$$
\boxed{
|F_A(\sigma+it)-Q(\sigma+it)|
\ge\frac{w(A)}{3A(1+t^2)}
\qquad(0<\sigma<1,\ |t|\ge\Gamma).}
\tag{H4}
$$

The classical zero-counting theorem supplies actual nontrivial zeros
at unbounded positive ordinates. Applying (H4) to those zeros shows
that this finite family cannot match $F_A(\rho)$ at every actual zero,
even with complex coefficients. Multiplicities remain unchanged:
multiplying a coefficient by its positive multiplicity cannot remove
the mismatch. Matching only on the actual zero set already fails in
this class; an all-strip identity is not required for the conclusion.

This restriction concerns exact coefficient reconstruction by finitely
many probes with positive fixed Gaussian parameters. It does not
exclude an identity for the aggregate signed sum, an inequality using
these probes, or an approximation with an independently paid remainder.
No conclusion is asserted here for infinite or height-dependent
reconstructions; unbounded center heights or $\inf_j a_j=0$ are not
covered by (H3). Pole, trivial-zero and shifted-contour terms from the
source still need their own treatment; they have not been discarded or
declared to satisfy the original Robin budget.

The calculation identifies a remainder that any such finite exact
replacement would otherwise omit. Controlling its signed sum, or
constructing a different reconstruction with a uniform remainder at
the same selected integer, remains necessary. Condition (G9), its full
infinite tail and the strict core remain unchanged and unproved; RH
remains unproved.


### The discrepancy also survives real conjugate pairing

The modulus restriction (H4) alone does not control a real part. The
existing [Ford–Zaharescu fixed-phase input](../Weil/fordzaharescu2005zerophases.md),
Corollary 2, supplies a way to select actual zero phases where the
real coefficient remains large. This is an application of that
published theorem and (H1)–(H3), not a new phase-distribution theorem,
source proof audit or Lean-verified result.

Keep the same fixed $A\ge e^2$, $L=\log A$ and finite fixed family
$Q$ above. For $s=\sigma+it$ with $0<\sigma<1$, put

$$
B_A(\sigma,t)=\frac{w(A)A^{\sigma-1}}{t^2}>0.
$$

Since
$s(1-s)=t^2+\sigma(1-\sigma)+it(1-2\sigma)$, with
$0<\sigma(1-\sigma)\le1/4$ and $|1-2\sigma|\le1$, comparison of
its reciprocal with $t^{-2}$ and the remainder estimate in (H1) give

$$
\begin{aligned}
\left|F_A(\sigma+it)-B_A(\sigma,t)e^{itL}\right|
&\le B_A(\sigma,t)
 \left(\frac7{3|t|}+\frac1{4t^2}\right)\\
&\le\frac13B_A(\sigma,t)\qquad(|t|\ge8).
\end{aligned}
\tag{H5}
$$

In particular $\operatorname{Re}F_A(s)\ge B_A/6$ when
$\cos(tL)\ge1/2$, and $\operatorname{Re}F_A(s)\le-B_A/6$ when
$\cos(tL)\le-1/2$. The actual real part $\sigma$ is still present
in $B_A$.

For an actual zero $\rho=\beta+i\gamma$ with $\gamma>0$, define the
real discrepancy of its conjugate pair by

$$
\Delta_A(\rho)=2\operatorname{Re}F_A(\rho)
 -\operatorname{Re}\!\left[Q(\rho)+Q(\overline\rho)\right].
$$

This definition allows arbitrary complex probe weights; $Q$ need not
commute with conjugation. The same estimate (H3) applies at both
ordinates. For

$$
\Gamma_{\mathrm R}=\max\!\left(8,2H,
 \left[\frac{768AC}{a_0^2w(A)}\right]^{1/3}\right),
$$

the elementary exponential bound used above gives

$$
\left|Q(\rho)+Q(\overline\rho)\right|
\le\frac{128C}{a_0^2\gamma^5}
\le\frac{w(A)}{6A\gamma^2}
\le\frac16B_A(\beta,\gamma)
\qquad(\gamma\ge\Gamma_{\mathrm R}).
$$

Consequently, at those actual heights,

$$
\boxed{
\begin{aligned}
\cos(\gamma L)\ge\tfrac12
&\ \Longrightarrow\quad
\Delta_A(\rho)\ge\tfrac16B_A(\beta,\gamma)
                 \ge\frac{w(A)}{6A\gamma^2},\\
\cos(\gamma L)\le-\tfrac12
&\ \Longrightarrow\quad
\Delta_A(\rho)\le-\tfrac16B_A(\beta,\gamma)
                 \le-\frac{w(A)}{6A\gamma^2}.
\end{aligned}}
\tag{H6}
$$

### Both signs occur on a positive proportion of actual zero pairs

Use the published theorem only with the **fixed** frequency
$\eta=L/(2\pi)>0$. Take the fixed $C^2(\mathbb T)$ minorants

$$
f_+(u)=8\bigl(\cos(2\pi u)-\tfrac12\bigr)_+^3,
\qquad f_-(u)=f_+(u-\tfrac12).
$$

Here $v_+=\max(v,0)$.
They lie in $[0,1]$ and have the same mean $c_0$. On
$|u|\le1/12$ modulo one, $\cos(2\pi u)\ge\sqrt3/2>3/4$, so
$f_+(u)\ge1/8$ and $c_0\ge1/48$.
Let $\mathcal N(T)$ count actual nontrivial zeros with
$0<\gamma\le T$, including every multiplicity. The fixed smooth-test
sum below ranges over distinct zeros, with $m_\rho$ supplying their
multiplicities. The expansion already supplied by Ford–Zaharescu, together with the
classical $\mathcal N(T)\sim T\log T/(2\pi)$, gives

$$
\frac1{\mathcal N(T)}
\sum_{0<\gamma_\rho\le T}m_\rho f_\pm(\eta\gamma_\rho)
\longrightarrow c_0.
$$

The source's correction is $O_A(T)$ and its error is $o_A(T)$,
so neither changes this normalized limit. No interval indicator is
substituted into its $C^2$ theorem.

Let $\mathcal C_+(T)$ count, with multiplicity, the zeros satisfying
$\Gamma_{\mathrm R}\le\gamma\le T$ and
$\Delta_A(\rho)\ge B_A(\beta,\gamma)/6$; define
$\mathcal C_-(T)$ using $\Delta_A(\rho)\le-B_A(\beta,\gamma)/6$.
The support of $f_\pm$ lies in the corresponding phase region of
(H6). Removing the finite head below $\Gamma_{\mathrm R}$ does not
change the normalized limit, hence

$$
\boxed{
\liminf_{T\to\infty}\frac{\mathcal C_\pm(T)}{\mathcal N(T)}
\ge c_0\ge\frac1{48}.}
\tag{H7}
$$

Conjugate zeros have the same positive multiplicity, so this also
prevents the fixed finite family from reproducing every real
conjugate-pair coefficient. The conclusion is asymptotic for each
fixed $A$ and probe family; it supplies no effective first qualifying
height and no uniform transition when $A$ or the family varies with
$T$.

The original zero contribution has the negative of these real pair
coefficients. Both signs of the discrepancy therefore remain in the
original bookkeeping. Counts of phases cannot replace its weights
$A^{\beta-1}/\gamma^2$ or control their joint signed sum. Neither
(H6) nor (H7) pays the full Robin remainder, rules out an aggregate
identity or a paid approximation, or changes the sufficient target
(G9) at the original selected integer. That bound and RH remain
unproved.


## A signed infinite-height allowance from the existing Landau formula

The existing [Gonek uniform Landau input](../Weil/gonek1985landau.md),
Theorem 1, printed pp.92–93, can be applied with the arithmetic variable
fixed at the original $A$. Integrating its actual-zero sum in **height**
retains a prime-power main term. This is different from the continuum
scale pairing in that note, where the point-supported main term has
zero ordinary integral. The following applies the already inspected
unconditional theorem and (H5); it is not a new Landau formula, source
proof audit, numerical zero computation, originality claim or Lean
certification.

The [existing real-part density allowance](../Analytic/polak2026finiterobinca.md#keeping-the-real-part-weights-in-the-complete-high-zero-tail),
(W1)–(W11), already pays a complete infinite-height tail on a finite
source-clock range and restricts the selected source to $A>10^{34}$.
Those results are reused. The application here instead estimates the
signed height suffix uniformly in both $A$ and a variable cut $T$.
Its implied constants are not numerically certified, and its moving
finite head remains unpaid.

### Preserve the arithmetic variable and the whole original coefficient

Let $A\ge e^2$, $L=\log A$, $T\ge8$, and
$\mathcal J(A)=\log(2A)\log\log(3A)$. Sums below range over distinct
actual nontrivial zeros, with $m_\rho$ supplying their multiplicities
exactly once. Define

$$
S_A(U)=\sum_{0<\gamma_\rho\le U}m_\rho A^\rho,
\qquad \rho=\beta+i\gamma_\rho.
$$

Gonek's uniform formula, with $x=A$ and height $U$, gives

$$
S_A(U)=-\frac{U}{2\pi}\Lambda(A)+E_A(U),
\qquad
|E_A(U)|\ll A[\mathcal J(A)+\log(2U)]+LU
\quad(U\ge8).
\tag{J1}
$$

The implied constant is absolute on the stated domain. To obtain this
weaker uniform remainder from the displayed source errors, use only

$$
L\min\!\left(U,\frac A{\langle A\rangle}\right)\le LU,
\qquad
\min\!\left(\frac{\log U}{L},U\log U\right)
\le\frac{\log U}{L}\le A\log(2U).
$$

No separation from prime powers is assumed. $\Lambda(A)$ remains the
source's nonnegative point-supported real-variable function, equal to
$\log p$ at $A=p^k$ and zero otherwise. It is not replaced by a prime
measure, and no assertion that $A$ avoids prime powers is needed.

Keep the complete original coefficient $F_A$ from (M1), and set

$$
\mathcal T_A(T)=\sum_{\gamma_\rho>T}m_\rho F_A(\rho).
$$

The more precise first inequality in (H5) retains the actual real part
and gives

$$
\left|F_A(\rho)-\frac{w(A)}A\frac{A^\rho}{\gamma_\rho^2}\right|
\ll\frac{w(A)A^{\beta-1}}{\gamma_\rho^3}
\le\frac{w(A)}{\gamma_\rho^3}.
$$

The classical zero count gives
$\sum_{\gamma>T}m_\rho\gamma^{-3}\ll\log(2T)/T^2$.
Thus, with uniform implied constants,

$$
\mathcal T_A(T)=\frac{w(A)}A
 \sum_{\gamma_\rho>T}\frac{m_\rho A^\rho}{\gamma_\rho^2}
 +O\!\left(\frac{w(A)\log(2T)}{T^2}\right).
\tag{J2}
$$

Both sums converge absolutely for each fixed $A$: use
$|A^\rho|\le A$ and the reciprocal-square zero count, together with
the preceding remainder. This step pays the coefficient approximation;
it does not replace $F_A$ by its leading term without a remainder.

### Integrate in zero height with the endpoint convention fixed

Stieltjes partial summation, with the inclusive head and exclusive
suffix specified above, gives

$$
\sum_{\gamma_\rho>T}\frac{m_\rho A^\rho}{\gamma_\rho^2}
=-\frac{S_A(T)}{T^2}
 +2\int_T^\infty\frac{S_A(u)}{u^3}\,du.
\tag{J3}
$$

The boundary term at infinity vanishes. If $T$ is a zero ordinate,
its full multiplicity stays in $S_A(T)$ and outside the suffix;
(J3) retains that convention. The linear main term in (J1)
contributes exactly $-\Lambda(A)/(2\pi T)$.

For the remainder use

$$
\int_T^\infty\frac{du}{u^3}=\frac1{2T^2},\qquad
\int_T^\infty\frac{\log(2u)}{u^3}\,du
=\frac{\log(2T)}{2T^2}+\frac1{4T^2},\qquad
\int_T^\infty\frac{du}{u^2}=\frac1T.
$$

Combining (J1)–(J3) therefore bounds the **entire** suffix:

$$
\boxed{
\mathcal T_A(T)
=-\frac{w(A)\Lambda(A)}{2\pi AT}
 +O\!\left(w(A)\left[
 \frac{\mathcal J(A)+\log(2T)}{T^2}+\frac{L}{AT}
 \right]\right),
\quad A\ge e^2,\ T\ge8.}
\tag{J4}
$$

This is an unconditional uniform application for actual complex zeros,
not a critical-line formula. No infinite height block, real part or
multiplicity has been omitted. Keeping $A$ fixed during the height
integration is compatible with the uniform estimate holding for all
$A,T$ in the stated domain.

### A moving cut makes this signed suffix allowance tend to zero

In the original explicit formula the high-zero contribution is
$-2\operatorname{Re}\mathcal T_A(T)$. Its normalized prime-power
main term is favorable. Equation (J4) gives an absolute constant $C_*>0$
such that

$$
\begin{aligned}
\sqrt A L\,[-2\operatorname{Re}\mathcal T_A(T)]
\ge{}&\frac{(1+1/L)\Lambda(A)}{\pi\sqrt A\,T}\\
&-C_*\left[
 \frac{\sqrt A[\mathcal J(A)+\log(2T)]}{T^2}
 +\frac{L+1}{\sqrt A\,T}\right].
\end{aligned}
\tag{J5}
$$

The nonnegative main term can be kept or discarded for this lower
bound; it must not be assigned an adverse sign. No numerical value
of $C_*$ or resulting effective source-clock threshold is asserted.

For the admissible moving cut $T=A^{1/4}L$, the adverse allowance in
(J5) is

$$
O\!\left(
 \frac{\mathcal J(A)+\log(2A^{1/4}L)}{L^2}
 +\frac{L+1}{A^{3/4}L}\right)
=O\!\left(\frac{\log L}{L}\right)\longrightarrow0.
\tag{J6}
$$

Thus the complete infinite-height suffix has an asymptotically vanishing
one-sided allowance at this moving cut. This gains height cancellation
over a direct reciprocal-square absolute sum, whose normalized generic
allowance is of order $\sqrt A\log(2T)/T$. It leaves the actual
finite signed head $0<\gamma\le A^{1/4}\log A$ in the original
formula, including all its real parts and multiplicities. That head
eventually exceeds the existing verified height and has not been
bounded uniformly here. The pole and trivial-zero terms are still
those in the original explicit formula.

For any prescribed positive allowance, (J6) gives an existential
large-$A$ threshold for this suffix alone. It supplies no certified
numerical threshold at the conditional source $A>10^{34}$, no new
finite-zero verification, and no assertion of an unbounded sequence
of selected sources. The original same-source condition (G9), with
its complete signed integral and strict core, remains unproved.
RH remains unproved. The remaining obstacle includes the signed
moving finite head; the infinite suffix cannot simply be dropped.


## A continuous Gaussian approximation of the complete original zero response

The fixed-family comparison (H3)–(H7) leaves continuous scale mixtures
and paid approximations available. The following application uses the
same original coefficient (M1), the already assessed Gaussian coefficient
of Moriya's Theorem 3.3, and the classical Riemann–von Mangoldt count.
It supplies a uniform coefficient-error estimate, rather than repeating
any source proof or claiming an original analytic theorem or Lean
verification. No nontrivial zero is moved to the critical line.

Fix $A\ge e^2$, $L=\log A$ and $0<a\le1/16$. Retain
$w(X)=(1+\log X)/\log^2X$. At observation $z=0$ choose, separately
for each $X\ge A$,

$$
\alpha_X=\sqrt{a/\log X},\qquad
G_{X,\alpha_X,0}(s)=\frac{X^s e^{as^2}}s.
$$

The positive scale measure $w(X)X^{-2}dX$ gives the exact identity

$$
Q_{A,a}(s):=\int_A^\infty G_{X,\alpha_X,0}(s)
                      \frac{w(X)}{X^2}\,dX
=e^{as^2}F_A(s),\qquad 0<\operatorname{Re}s<1.
\tag{U1}
$$

For every such $s$, the scale integral is absolutely convergent. The
width parameter varies with $X$, while the Gaussian coefficient $a$
is fixed throughout the integral. This realizes the damped coefficient
exactly; it does not claim exact reconstruction of $F_A$ by a finite
family of fixed probes.

### A bound valid before taking the infinite scale endpoint

For $R\ge A$ put

$$
F_{A,R}(s)=\frac1s\int_A^R X^{s-2}w(X)\,dX.
$$

Since $w$ is positive and decreasing, one integration by parts gives,
for $\sigma=\operatorname{Re}s<1$ and $s\ne0$,

$$
|F_{A,R}(s)|\le
\frac{2w(A)A^{\sigma-1}}{|s||1-s|}.
\tag{U2}
$$

Indeed the two endpoint terms and the derivative integral are bounded
by $A^{\sigma-1}[w(A)+w(R)+\int_A^R|w'(X)|dX]$, which is
$2A^{\sigma-1}w(A)$. The bound is uniform in $R$. Passing to the
infinite endpoint gives the same bound for $F_A$. In particular, for
an actual zero $\rho=\beta+i\gamma$ with $\gamma\ge4$,

$$
|F_{A,R}(\rho)|,\ |F_A(\rho)|\le\frac{2w(A)}{\gamma^2}.
$$

This is the same reciprocal-square coefficient control used in the
existing [Fiori density application](../Analytic/fiori2026shortzerodensity.md),
now also applied to finite scale intervals. It will justify the
scale-endpoint passage below; it is not a new zero-density input.

### Pay the discrepancy over all actual zeros

With multiplicities $m_\rho$ retained, uniformly in $A$ and $a$,

$$
\boxed{
\sum_{\operatorname{Im}\rho>0}m_\rho
 |F_A(\rho)-Q_{A,a}(\rho)|
\ll w(A)\sqrt a\log(2/a).}
\tag{U3}
$$

To prove this, set $U=a^{-1/2}\ge4$. For $4\le\gamma\le U$,

$$
|e^{a\rho^2}-1|
=\left|a\rho^2\int_0^1e^{ta\rho^2}\,dt\right|
\le ae^a|\rho|^2\ll a\gamma^2,
$$

because $0<\beta<1$. The preceding coefficient bound and
$N(U)\ll U\log(2U)$ give a contribution
$O(w(A)aU\log(2U))$. For $\gamma>U$ use
$|e^{a\rho^2}-1|\le1+e^a$ and the classical consequence
$\sum_{\gamma>U}m_\rho/\gamma^2\ll\log(2U)/U$ of the same
zero count. Their sum has the size in (U3).

The finite multiset $0<\gamma<4$ is not omitted or assumed empty.
Directly from the defining integral,

$$
|F_A(\rho)|\le\frac{w(A)}{|\rho|(1-\beta)},
$$

so its discrepancy is at most
$ae^aw(A)\sum_{0<\gamma<4}m_\rho|\rho|/(1-\beta)=O(aw(A))$.
This fixed zeta-dependent constant is finite and independent of $A,a$;
it is absorbed into (U3). No finite-height verification is needed for
this step. All implied constants here are uniform but not numerically
certified.

Consequently the original conjugate-paired response has allowance

$$
\sqrt A L\left|2\operatorname{Re}
 \sum_{\gamma>0}m_\rho(F_A(\rho)-Q_{A,a}(\rho))\right|
\ll\sqrt{Aa}\log(2/a).
\tag{U4}
$$

The admissible choice

$$
a_A=\frac1{A(\log A)^4}
$$

makes (U4) $O(1/\log A)$ as $A\to\infty$. This estimate covers the
complete positive-ordinate multiset and infinite height tail, with
actual real parts and multiplicities unchanged. It pays unsmoothing
of the zero response, while giving no signed lower bound for that
response. Positivity of the scale measure in (U1) is not positivity
of a sum of complex zero coefficients.


## Transport to a centered Gaussian prime integral with the contour paid

The coefficient approximation (U1)–(U4) can be realized on the prime
side without discarding the pole, the shifted contour, or the original
trivial-zero correction. Use only Moriya,
[arXiv:2607.04316v2](https://arxiv.org/abs/2607.04316v2),
Proposition 2.2, equations (17)–(19), Theorem 3.3, equations (35)–(36),
and Lemma 3.1. This is an application of those assessed interfaces;
none of their explicit-formula proofs or RH-dependent localization
claims is reproved or used.

### Center the pole before the infinite scale integration

For $A\ge e^2$ and $0<a\le1/16$ define

$$
\Psi_a(X)=\sum_{n\ge1}\Lambda(n)\,
 \frac12\operatorname{erfc}\!\left(
 \frac{\log n-\log X}{2\sqrt a}\right).
\tag{V1}
$$

In the cited formula take observation $s=0$, right line $c=2$, left
line $-d=-1/2$, and $\alpha_X^2\log X=a$. The observation is not a
zero or the pole of $\zeta$. All nontrivial zeros and the pole at $1$
are crossed; no trivial zero is crossed. The left line avoids all
zeros and the pole. The source's prime term is $-\Psi_a(X)$, and
$\zeta'/\zeta(0)=\log(2\pi)$, so its exact formula reads

$$
\Psi_a(X)-e^aX
=-\sum_\rho m_\rho\frac{X^\rho e^{a\rho^2}}\rho
 -\log(2\pi)-R_a(X),
\tag{V2}
$$

where

$$
R_a(X)=\frac1{2\pi i}\int_{\operatorname{Re}z=-1/2}
 \frac{\zeta'}\zeta(z)\frac{X^z e^{az^2}}z\,dz.
$$

For each fixed $a>0$ this contour integral and the zero sum in (V2)
converge absolutely. Define the centered improper integral

$$
J_a(A)=\lim_{R\to\infty}\int_A^R
 [\Psi_a(X)-e^aX]\frac{w(X)}{X^2}\,dX.
\tag{V3}
$$

The prime and pole terms must be centered before taking this limit.
Their separate integrals diverge, since $w(X)/X\sim1/(X\log X)$
and $\Psi_a(X)\sim e^aX$. The latter asymptotic also follows from
(V2): its Gaussian zero series divided by $X$ tends to zero by
absolute domination, and the fixed-$a$ contour is $O_a(X^{-1/2})$.

For finite $R$, Gaussian decay allows exchange of the scale integral
and the zero sum. Its zero coefficients are
$e^{a\rho^2}F_{A,R}(\rho)$. The bound (U2) and the finite low-zero
bound dominate them independently of $R$ by a summable multiset.
Thus dominated convergence passes $R\to\infty$. This uses finite
scale intervals first; no absolute exchange over the infinite scale
range is assumed. The constant integrates exactly to
$\log(2\pi)/(A\log A)$.

For the contour, the scale exchange over $[A,\infty)$ is absolutely
convergent for each fixed $a>0$, using $X^{-5/2}w(X)$ on the scale
side and Gaussian decay on the vertical line. Therefore (V3) exists
and

$$
J_a(A)=-2\operatorname{Re}\sum_{\gamma>0}m_\rho Q_{A,a}(\rho)
 -\frac{\log(2\pi)}{A\log A}-C_a(A),
\tag{V4}
$$

$$
C_a(A)=\frac1{2\pi i}\int_{\operatorname{Re}z=-1/2}
 \frac{\zeta'}\zeta(z)e^{az^2}F_A(z)\,dz.
$$

Here $F_A$ is defined by the same integral (M1) at $\operatorname{Re}z<1$,
$z\ne0$. No new analytic continuation assumption is needed.

### Bound the contour after integrating the scale

The infinite-endpoint version of (U2) on $z=-1/2+it$ gives

$$
|F_A(-1/2+it)|\ll\frac{w(A)A^{-3/2}}{1+t^2}.
$$

This line has a fixed positive distance from every zero and the pole,
so the source's Lemma 3.1 gives
$|\zeta'/\zeta(-1/2+it)|\ll\log^2(3+|t|)$.
Moreover $|e^{az^2}|\le e^{a/4}$. Taking absolute values after the
scale integration, rather than before it, therefore gives

$$
\boxed{|C_a(A)|\ll w(A)A^{-3/2}}
\quad(A\ge e^2,\ 0<a\le1/16),
\tag{V5}
$$

since $\log^2(3+|t|)/(1+t^2)$ is integrable. The implied constant is
independent of the shrinking width $a$, but is not numerically certified.

The original signed formula already recorded above is

$$
I_\psi(A)=-2\operatorname{Re}\sum_{\gamma>0}m_\rho F_A(\rho)
 -\frac{\log(2\pi)}{A\log A}+T_{\rm triv}(A),
\qquad
T_{\rm triv}(A)=-\frac12\int_A^\infty
 \log(1-X^{-2})\frac{w(X)}{X^2}\,dX.
$$

In particular $0\le T_{\rm triv}(A)\ll w(A)A^{-3}$. Thus the pole
constant matches exactly, the Gaussian shifted contour is paid by
(V5), and the original trivial term is retained. Combining (U4)
and (V5) yields the full prime-side approximation

$$
\boxed{
\sqrt A\log A\,|I_\psi(A)-J_a(A)|
\ll\sqrt{Aa}\log(2/a)+A^{-1}.}
\tag{V6}
$$

For $a_A=1/[A(\log A)^4]$ this is
$O(1/\log A+1/A)\to0$. The bound alone does not assert convergence
at fixed $A$ as $a\to0$, because its $A^{-1}$ allowance remains.

### The estimate still needed at the selected Robin source

At the same conditional least integer $N>5040$ attaining the global
Robin-ratio maximum, retain $A=\log N$ and condition (G9). The
[existing density restriction](../Analytic/polak2026finiterobinca.md)
requires $A>10^{36}$ if RH fails and its cited inputs hold. An eventual
bound of the form

$$
\sqrt A\log A\,J_{a_A}(A)
\ge-\mathcal E(\log A)+\eta(A)
$$

would imply (G9) wherever $\eta(A)$ pays the discrepancy in (V6).
This is a sufficient condition, not an estimate established here;
its validity at this selected source remains unproved. Without a
numerical constant in (V6), no explicit margin or new source threshold
is certified. Neither positive prime weights nor positive scale
weights give a lower bound after subtracting the pole main term.

The application closes the full-coefficient approximation and its
prime-side contour transport, not the signed Robin estimate. It does
not discard an infinite zero tail, use RH-dependent localization,
replace real parts by $1/2$, or turn the selected global maximizer into
the least counterexample. RH remains unproved; all conclusions are
paper-level applications without Lean certification.


## A signed heat-weight application permits a broader Gaussian window

The absolute all-zero discrepancy (U3) pays a narrow Gaussian window.
The uniform actual-zero phase sum (J1) also controls a signed
heat-weight discrepancy. The following application combines those
already assessed inputs, (H5)'s paid coefficient approximation and
the classical zero count. It does not repeat Landau's formula or
claim an original phase theorem or Lean verification.

Keep $A\ge e^2$, $L=\log A$, $0<a\le1/16$, and
$\mathcal J(A)=\log(2A)\log\log(3A)$. All sums run over distinct
actual zeros $\rho=\beta+i\gamma$ with $\gamma>0$, with each
multiplicity $m_\rho$ included once. Define

$$
b_a(u)=\frac{1-e^{-au^2}}{u^2}=\int_0^a e^{-vu^2}\,dv\quad(u>0),
\qquad b_a(0)=a.
$$

This is a nonnegative decreasing real function. Its total variation
and first weighted variation are

$$
\int_0^\infty(-b_a'(u))\,du=a,\qquad
\int_0^\infty u(-b_a'(u))\,du
=\int_0^\infty b_a(u)\,du=\sqrt{\pi a}.
\tag{W1}
$$

For the final equality, integrate
$(1-e^{-au^2})/u^2$ by parts and use the classical Gaussian integral.
Boundary terms vanish both at zero and at infinity. With
$U=a^{-1/2}\ge4$, the bounds $b_a(u)\le\min(a,u^{-2})$ also give

$$
\begin{aligned}
\int_0^\infty\log(2+u)(-b_a'(u))\,du
&=a\log2+\int_0^\infty\frac{b_a(u)}{2+u}\,du\\
&\le a\log(2+U)+a/2\ll a\log(2/a).
\end{aligned}
\tag{W2}
$$

### Apply the existing Landau sum to this variation measure

Use exactly the sum $S_A(u)=\sum_{0<\gamma\le u}m_\rho A^\rho$
from (J1). Its remainder
$E_A(u)=S_A(u)+u\Lambda(A)/(2\pi)$ has the bound

$$
|E_A(u)|\ll A[\mathcal J(A)+\log(2+u)]+Lu
\qquad(u\ge0).
$$

For $u\ge8$ this is (J1). For $0\le u<8$ the same weaker envelope
follows from the fixed finite zero count, $|A^\rho|\le A$ and
$0\le\Lambda(A)\le L$; no low zero is assumed absent or verified.
The implied constant remains independent of $A,u$.

Stieltjes partial summation over the entire positive-ordinate multiset
now yields

$$
\begin{aligned}
\sum_{\gamma>0}m_\rho A^\rho b_a(\gamma)
&=-\int_0^\infty S_A(u)b_a'(u)\,du\\
&=-\frac{\Lambda(A)\sqrt a}{2\sqrt\pi}
 +O\!\left(Aa[\mathcal J(A)+\log(2/a)]+L\sqrt a\right).
\end{aligned}
\tag{W3}
$$

At zero $S_A(0)=0$; at infinity the boundary term vanishes by (J1)
and $b_a(u)\le u^{-2}$. The series is absolutely convergent for
fixed $A$, by $|A^\rho|\le A$ and the reciprocal-square zero count.
Equations (W1)–(W2) pay the remainder integral. This applies the
existing uniform formula to a new weight; it is not a reproof of
that formula. $\Lambda(A)$ retains its point-supported real-variable
meaning, and no nonzero main term is assumed at a selected source.

### Pay the coefficient and the actual-real-part phase changes

The first inequality in (H5) gives, uniformly for $\gamma\ge8$,

$$
F_A(\rho)=\frac{w(A)}A\frac{A^\rho}{\gamma^2}
 +O\!\left(\frac{w(A)A^{\beta-1}}{\gamma^3}\right).
$$

After multiplication by $1-e^{-a\gamma^2}$, the total error is
$O(w(A)a\log^2(2/a))$. Indeed, the classical count gives

$$
\sum_{\gamma\ge8}m_\rho
 \frac{\min(a\gamma^2,1)}{\gamma^3}
\ll a\log^2(2/a),
$$

by splitting at $U$ and using the existing reciprocal-cube tail
estimate. The finite multiset $0<\gamma<8$ contributes $O(aw(A))$
to this comparison, using the pointwise finite-zero bound in (U3).
Its fixed constants are independent of $A,a$; it is retained even
when $U<8$.

The Gaussian in (U1) contains the actual square $\rho^2$, not just
$-\gamma^2$. The additional phase change is explicitly bounded by

$$
|e^{a\rho^2}-e^{-a\gamma^2}|
\le ae^a(1+2\gamma)e^{-a\gamma^2},
$$

since $0<\beta<1$. Applying (U2) and the same zero count gives

$$
\sum_{\gamma>0}m_\rho|F_A(\rho)|
 |e^{a\rho^2}-e^{-a\gamma^2}|
\ll w(A)a\log^2(2/a).
\tag{W4}
$$

For large ordinates split at $U$: below it
$\sum m_\rho/\gamma\ll\log^2(2U)$; above it Gaussian decay and
the same count give $O(\log(2U))$ for the weighted reciprocal-first
sum. The finite low multiset again costs $O(aw(A))$. These are
absolute error estimates for the changes, not critical-line
replacements of the zeros themselves.

Consequently the full signed coefficient discrepancy obeys

$$
\boxed{\begin{aligned}
D_{A,a}&:=\sum_{\gamma>0}m_\rho F_A(\rho)(1-e^{a\rho^2})\\
&=-\frac{w(A)\Lambda(A)\sqrt a}{2\sqrt\pi A}
 +O\!\left(w(A)\left[
 a\bigl(\mathcal J(A)+\log^2(2/a)\bigr)
 +\frac{L\sqrt a}{A}\right]\right).
\end{aligned}}
\tag{W5}
$$

This is a uniform estimate for a complex signed sum. The actual real
parts, multiplicities, finite low zeros and infinite height tail have
not been discarded. Its cancellation comes from (J1), while (W4)
pays the mismatch between real-ordinate damping and the actual
Gaussian coefficient. No numerical value for the implied constants
is asserted.


## The broader window retains a vanishing full Robin transport allowance

Use the exact centered prime integral $J_a(A)$ in (V3), the matching
pole constant in (V4), the uniform contour bound (V5), and the original
trivial-zero correction already retained there. Subtracting their
exact formulas gives

$$
I_\psi(A)-J_a(A)=-2\operatorname{Re}D_{A,a}
 +T_{\rm triv}(A)+C_a(A).
$$

Therefore (W5) supplies the complete normalized transport estimate

$$
\boxed{\begin{aligned}
\sqrt A L\,[I_\psi(A)-J_a(A)]
={}&\frac{(1+1/L)\Lambda(A)\sqrt a}{\sqrt\pi\sqrt A}\\
&+O\!\left(
 \sqrt A\,a\bigl[\mathcal J(A)+\log^2(2/a)\bigr]
 +\frac{L\sqrt a}{\sqrt A}+\frac1A\right).
\end{aligned}}
\tag{Y1}
$$

The nonnegative displayed main term is favorable for a lower bound
on $I_\psi$ in terms of $J_a$. No positive main term is presumed at
the selected integer, and no effective value for the error constant
is certified. The pole, contour and trivial-zero contributions are
those of the full exact formulas, with no further truncation.

### A larger admissible Gaussian width

For $A\ge e^2$ choose

$$
a_A^\sharp=\frac1{\sqrt A(\log A)^3}\le\frac1{16}.
$$

Then $\log(2/a_A^\sharp)=L/2+3\log L+\log2=O(L)$ and
$\mathcal J(A)=O(L\log L)$, so the adverse allowance in (Y1) is

$$
O\!\left(\frac1L+\frac{\log L}{L^2}
 +\frac1{A^{3/4}\sqrt L}+\frac1A\right)=O(1/L).
\tag{Y2}
$$

The displayed main term is also $O(A^{-3/4}/\sqrt L)$, because
$\Lambda(A)\le L$. Thus the full normalized absolute discrepancy
is $O(1/\log A)$ at this larger width as well.

Compared with $a_A=1/[A(\log A)^4]$ in (V6),
$a_A^\sharp/a_A=\sqrt A\log A\to\infty$. The reciprocal Gaussian
height scale changes from $\sqrt A(\log A)^2$ to
$A^{1/4}(\log A)^{3/2}$. This specifies damping of the full response,
not a cutoff that permits any zero to be omitted.

At the larger width, the earlier generic absolute allowance
$\sqrt{Aa}\log(2/a)$ grows like $A^{1/4}/\sqrt{\log A}$.
Equation (Y1) instead uses the existing signed Landau cancellation
and the paid actual-real-part phase error to obtain (Y2). This compares
the two guaranteed allowances; it does not claim the earlier bound
is attained by the actual discrepancy.

### The unchanged selected-source obligation

At the same conditional least integer $N>5040$ attaining the global
Robin-ratio maximum, set $A=\log N$ and retain the existing condition
(G9), its complete infinite integral and strict core. The existing
restriction $A>10^{36}$ under RH failure and the cited inputs remains
unchanged. A lower bound

$$
\sqrt A\log A\,J_{a_A^\sharp}(A)
\ge-\mathcal E(\log A)+\eta(A)
$$

would suffice wherever $\eta(A)$ pays the adverse allowance in (Y1).
Such a signed lower bound is not proved here. The new estimate allows
a broader Gaussian window with a vanishing transport cost; it does
not certify that cost numerically at $A>10^{36}$, control the remaining
signed response, verify a new zero height, or turn the selected global
maximizer into the least counterexample. All inputs are reused
paper-level interfaces without Lean certification; RH remains unproved.

## A smaller moving cut from joint density and zero-free support

The complete coefficient (M1) can use a smaller moving height than
(J6), by combining two existing inputs on the same actual zero
multiset. This controls the infinite suffix and reduces the height
of the still-uncontrolled signed head. It does not establish that
head's sign or the original selected-source Robin condition.

Corollary 1 and Table 1, printed p.2, of
[Chourasiya–Simonič, arXiv:2507.15184v2](https://arxiv.org/pdf/2507.15184v2)
also extend the existing count (W1) in the
[Polak application](../Analytic/polak2026finiterobinca.md)
to $5/8\le\sigma<1$, with the same larger constants $47,10,168$.
The additional rows have $B_1\le13.66$, $B_2\le8.290$, $B_3\le147.0$.
Lemma 2.10, printed p.6, of
[Johnston–Yang, arXiv:2204.01980v2](https://arxiv.org/pdf/2204.01980v2)
supplies Ford's zero-free region

$$
\beta<1-\eta(\gamma),\qquad
\eta(t)=\frac1{R(\log t)^{2/3}(\log\log t)^{1/3}},
\quad R=57.54,\quad \gamma\ge3.
$$

Their analytic proofs and finite verified-height input remain
external premises. The constant is sufficient for this interface;
no optimal-constant claim or source proof rerun is needed.

Put $L=\log A$, $\Omega=(L/\log L)^{1/3}$ and

$$
\kappa=\frac1{28R},\qquad
T=A^{1/4}e^{-\kappa\Omega},\qquad U=A^{2/7}.
$$

Work for sufficiently large $A$ so $T\ge H=3\cdot10^{12}$.
Then $U>T$, $T\to\infty$, and $T/(A^{1/4}L)\to0$.
No numerical starting clock is certified here.
Define

$$
B_2(A;T)=\sum_{\gamma>T}
 \frac{m_\rho(A^{\beta-1/2}+A^{1/2-\beta})}{\gamma^2}.
$$

The full coefficient estimate (H5), including its remainder, and
multiplicity-preserving reflection give

$$
\sqrt A L\,2\sum_{\gamma>T}m_\rho|F_A(\rho)|
\le\frac43(1+1/L)B_2(A;T).
$$

Thus an absolute bound on $B_2$ pays the original signed suffix.
The original head $\gamma\le T$, pole and trivial-zero terms remain.

Use the existing layer calculation with
$\sigma_0=5/8$ and $Q_A(\sigma)=A^{\sigma-1/2}+A^{1/2-\sigma}$.
For the inclusive count and exclusive suffix, the reflected count
has the endpoint term

$$
F_2(\sigma;T)=-\frac{2N(\sigma,T)}{T^2}
 +4\int_T^\infty\frac{N(\sigma,t)}{t^3}\,dt
\le4\int_T^\infty\frac{N(\sigma,t)}{t^3}\,dt.
$$

Consequently,

$$
B_2(A;T)\le Q_A(\sigma_0)S_2(T)
 +4\int_{\sigma_0}^1Q_A'(\sigma)
          \int_T^\infty N(\sigma,t)t^{-3}\,dt\,d\sigma,
\qquad S_2(T)=\sum_{\gamma>T}\frac{m_\rho}{\gamma^2}.
$$

Tonelli preserves all heights, real parts and multiplicities.
Write $\epsilon=1-\sigma$. The existing density exponent satisfies
$d=3\epsilon/(1+\epsilon)\le3\epsilon$, $d\le9/11$ and
$q=2+d<3$. Uniformly on this range,
$N(\sigma,t)\ll t^d(\log t)^3$ and
$Q_A'(\sigma)\le L\sqrt A e^{-\epsilon L}$.

The classical full zero count gives $S_2(T)\ll\log T/T$.
The base layer therefore costs

$$
Q_A(\sigma_0)S_2(T)\ll L A^{-1/8}e^{\kappa\Omega}.
$$

For $T<t\le U$, finite verification and monotonicity of the
zero-free region jointly imply $N(\sigma,t)=0$ when
$\sigma\ge1-\eta(U)$. On this same band,

$$
A^{-\epsilon}t^d\le e^{-\epsilon L/7},\qquad
\eta(U)\ge\frac1{RL^{2/3}(\log L)^{1/3}},\qquad
\int_{\eta(U)}^{3/8}e^{-\epsilon L/7}\,d\epsilon
\le\frac7L e^{-\eta(U)L/7}.
$$

If $\eta(U)>3/8$ the band is empty. Otherwise these bounds,
$\log t\le L$ and $\int_T^Ut^{-3}dt\le1/(2T^2)$ give the
whole finite-band allowance $O(L^3e^{-\Omega/(14R)})$.

For $t>U$, use the density bound without imposing the fixed-$U$
zero-free restriction. Uniformly for $0\le d\le9/11$,
$\int_U^\infty t^{d-3}(\log t)^3dt\ll U^{d-2}(\log U)^3$.
Also $A^{-\epsilon}U^d\le e^{-\epsilon L/7}$, whose layer
integral cancels the outer factor $L$. The complete infinite band
therefore costs $O(L^3\sqrt A/U^2)=O(L^3A^{-1/14})$.

Combining the three allowances yields

$$
\boxed{
\sqrt A L\left|2\operatorname{Re}
             \sum_{\gamma>T}m_\rho F_A(\rho)\right|
\ll L A^{-1/8}e^{\kappa\Omega}
    +L^3e^{-\Omega/(14R)}+L^3A^{-1/14}\longrightarrow0.}
$$

The absolute-sum bound above satisfies the same estimate. Every
implied constant is independent of $A$; no ordinate tail or
coefficient correction is dropped. The limit follows from
$\Omega/\log L\to\infty$ and $\Omega/L\to0$.
Using the old $3/4$ base clip would instead leave
$O(Le^{\kappa\Omega})$, so it cannot support this vanishing claim.

This is an asymptotic application of established density and
zero-free results. The same selected integer, its original clock,
strict core and complete signed target are retained. The actual
finite head still grows without bound and remains uncontrolled;
neither a new finite source-clock exclusion nor RH is proved.
There is no Lean verification of this application.

## Pay coefficient error below the whole-response cut

The full-response suffix estimate above and the existing coefficient
comparisons (H1), (H5) can be used together at two different heights.
Keep the same selected source $A=\log N>10^{36}$, every actual zero real
part and multiplicity, and the original complete coefficient (M1).
This is a paper-level application of the already cited density and
zero-free inputs, without a new source theorem, numerical starting
clock, originality claim or Lean verification.

Put $L=\log A$, $\Omega=(L/\log L)^{1/3}$, $R=57.54$ and
$\kappa=1/(28R)$ as above. Define

$$
S=A^{1/6}e^{-\kappa\Omega},\qquad
T=A^{1/4}e^{-\kappa\Omega},\qquad U=A^{1/5}.
$$

Work for sufficiently large $A$ with $S\ge H=3\cdot10^{12}$.
Then $S<U<T$ eventually. The cut $S$ concerns coefficient error;
$T$ remains the previously paid cut for the full original response.
Both cuts tend to infinity, so fixed unverified zero heights remain
in the exact lower head.

For an actual zero $\rho=\beta+i\gamma$ with $\gamma>0$, set

$$
G_A(\rho)=\frac{w(A)A^{\rho-1}}{\gamma^2},\qquad
B_3(A,S)=\sum_{\gamma>S}m_\rho
 \frac{A^{\beta-1/2}+A^{1/2-\beta}}{\gamma^3},
\qquad w(A)=\frac{1+L}{L^2}.
$$

Reflection of this same multiplicity-weighted zero multiset gives
$B_3(A,S)=2\sum_{\gamma>S}m_\rho A^{\beta-1/2}/\gamma^3$.
The first inequality of (H5) therefore pays the full approximation
error by

$$
\sqrt A L\,2\sum_{\gamma>S}m_\rho
 |F_A(\rho)-G_A(\rho)|
 \le(1+1/L)\left(\frac73+\frac1{4S}\right)B_3(A,S).
\tag{RC1}
$$

The actual weight $A^{\beta-1/2}$ and phase $e^{i\gamma L}$ remain
in $G_A$. If a transport instead uses
$P_A(\rho)=w(A)A^{\rho-1}/[\rho(1-\rho)]$, (H1) gives the
supplementary bound

$$
\sqrt A L\,2\sum_{\gamma>S}m_\rho
 |F_A(\rho)-P_A(\rho)|
 \le\frac{2(L+2)}{L^2}B_3(A,S).
\tag{RC2}
$$

This is an alternative coefficient comparison; it is not an additional
error to add to (RC1).

### The same layer estimate with a reciprocal cube

Reuse the real-part layer identity with $\sigma_0=5/8$ and
$Q_A(\sigma)=A^{\sigma-1/2}+A^{1/2-\sigma}$. Replacing the
reciprocal square by a reciprocal cube changes the reflected
partial-summation formula to

$$
F_3(\sigma;S)
 =-\frac{2N(\sigma,S)}{S^3}
   +6\int_S^\infty N(\sigma,t)t^{-4}\,dt.
$$

The endpoint term is nonpositive. Dropping it only for an upper bound,
with the same inclusive head and exclusive suffix convention, gives

$$
B_3(A,S)\le Q_A(\sigma_0)S_3(S)
 +6\int_{\sigma_0}^1 Q_A'(\sigma)
           \int_S^\infty N(\sigma,t)t^{-4}\,dt\,d\sigma,
\qquad
S_3(S)=\sum_{\gamma>S}\frac{m_\rho}{\gamma^3}
 \ll\frac{\log S}{S^2}.
\tag{RC3}
$$

The already retained density bound on $5/8\le\sigma<1$ is
$N(\sigma,t)\le C_0t^{d(\sigma)}(\log t)^3$ for $t\ge H$,
where, with $\varepsilon=1-\sigma$,
$d=3\varepsilon/(1+\varepsilon)\le3\varepsilon$ and $d\le9/11$.
All constants below are independent of $A$ and $\sigma$.

The base layer in (RC3) is
$O(LA^{-5/24}e^{2\kappa\Omega})$. On $S<t\le U$, use the same
actual-zero support $N(\sigma,t)=0$ when
$\sigma\ge1-\eta(U)$. Here

$$
A^{-\varepsilon}U^d\le e^{-2\varepsilon L/5},\qquad
\eta(U)\ge\frac{\Omega}{RL},\qquad
\int_{\eta(U)}^{3/8}e^{-2\varepsilon L/5}\,d\varepsilon
 \le\frac5{2L}e^{-2\eta(U)L/5},
$$

when $\eta(U)\le3/8$; otherwise this count band is empty.
Using $\log t\le L$ and
$\int_S^Ut^{-4}dt\le1/(3S^3)$, its allowance is
$O(L^3e^{-41\Omega/(140R)})$.

Above $U$, no fixed-$U$ zero-free support is imposed.
Since $3-d\ge24/11$, the complete height integral is bounded uniformly
by $C_1U^{d-3}(\log U)^3$. Integrating
$e^{-2\varepsilon L/5}$ over $\varepsilon\ge0$ cancels the outer $L$;
this entire infinite band costs $O(L^3A^{-1/10})$. Thus

$$
B_3(A,S)\ll
 LA^{-5/24}e^{2\kappa\Omega}
 +L^3e^{-41\Omega/(140R)}+L^3A^{-1/10}
 \longrightarrow0.
\tag{RC4}
$$

All three terms vanish because $\Omega/\log L\to\infty$.
Equations (RC1) and (RC2) pay complete absolute coefficient errors above
$S$, rather than just at the larger whole-response cut $T$.

### Retain the exact lower head and the oscillatory middle

Let $Z_{\rm orig}(A)=2\operatorname{Re}\sum_{\gamma>0}
 m_\rho F_A(\rho)$ denote the original paired zero sum, and set

$$
Z_{\rm split}(A)=2\operatorname{Re}\left[
 \sum_{0<\gamma\le S}m_\rho F_A(\rho)
 +\sum_{S<\gamma\le T}m_\rho G_A(\rho)\right].
$$

Its contribution to $I_\psi$ is $-Z_{\rm orig}$; the approximation
there uses $-Z_{\rm split}$ with the same sign. All elementary terms
remain unchanged. Combining (RC1) with the already retained
complete absolute suffix estimate gives

$$
\sqrt A L\,|Z_{\rm orig}(A)-Z_{\rm split}(A)|
 \le(1+1/L)\left(\frac73+\frac1{4S}\right)B_3(A,S)
 +\sqrt A L\,2\sum_{\gamma>T}m_\rho|F_A(\rho)|
 \longrightarrow0.
\tag{RC5}
$$

This restores every coefficient error and every infinite height.
It reduces the range requiring exact-coefficient treatment while
preserving the actual signed oscillatory middle. Its sign, the exact
lower head, the original full sufficient Robin bound and RH remain
unproved. This asymptotic reduction does not certify a finite numerical
clock exclusion or a uniform safe margin.

## Localized complex Mellin transport of the moving middle

Reuse (RC2), (RC4) and the complete original suffix above $T$;
their density and zero-free-region proofs are not repeated. The
following application of Mellin inversion keeps the actual real
parts and multiplicities. It supplies a finite-frequency interface
to the unconditional Theorem 2 of
[Garunkštis–Sourmelidis–Steuding, version 1](https://arxiv.org/abs/2505.14228v1),
without repeating that theorem's proof or using its RH-conditional
corollary. This is a paper-level transport, with no originality or
Lean-verification claim.

Keep $A,L,S,T,B_3$ as in (RC1)–(RC5), and assume $A$ is sufficiently
large that $S\ge H$, $S\ge L\ge1$ and $L/\log S\le7$. These are
eventual conditions, not a certified numerical starting threshold.
Partition $(S,T]$ into disjoint bands $(V,W]$, where $V=2^jS$ and
$W=\min(2V,T)$. A zero at a shared endpoint belongs to exactly one
band. Every sum below retains $m_\rho$.

### Localize the kernel and pay the compensating weight

For $\rho=\beta+i\gamma$ put

$$
r=i(1/2-\rho)=\gamma+i\delta,\qquad
\delta=1/2-\beta,\qquad
f_L(r)=\frac{e^{iLr}}{r^2+1/4}.
$$

The rational coefficient from (RC2) satisfies the exact identity
$\sqrt A L P_A(\rho)=(1+1/L)f_L(r)$.
For each band set $c_{\rm loc}=3/2$, $a_V=L/V^2$ and

$$
f_V(r)=e^{-a_V(r-c_{\rm loc}V)^2}f_L(r),\qquad
h_V(v)=\frac{e^{a_V(v-c_{\rm loc}V)^2}}v,\qquad
J_V(\tau)=\sum_{V<\gamma\le W}m_\rho
 h_V(\gamma)r^{-i\tau}.
\tag{LM1}
$$

All complex powers use the principal logarithm in $\operatorname{Re}r>0$.
The kernel reconstructed with this height weight is

$$
h_V(\gamma)r f_V(r)
 =\frac r\gamma e^{E_\rho}f_L(r),\qquad
E_\rho=a_V\delta^2-2ia_V\delta(\gamma-c_{\rm loc}V).
$$

Since $|\delta|\le1/2$ and $|\gamma-c_{\rm loc}V|\le V/2$,
$|E_\rho|\le L/(4V^2)+L/(2V)\le3L/(4V)\le1$.
Using $|e^z-1|\le e|z|$ on $|z|\le1$ and $e<3$ gives

$$
\left|\frac r\gamma e^{E_\rho}-1\right|
 \le\frac{4L}V.
$$

Also $|r^2+1/4|=|\rho(1-\rho)|\ge\gamma^2$ and
$|e^{iLr}|=A^{\beta-1/2}$. Thus $\gamma\le2V$ and reflection
in $\beta=1/2$ give the complete paired approximation allowance

$$
2(1+1/L)\sum_{\text{bands}}\sum_{V<\gamma\le W}m_\rho
 |h_V(\gamma)r f_V(r)-f_L(r)|
 \le8(1+1/L)L B_3(A,S)\longrightarrow0.
\tag{LM2}
$$

The final limit uses the explicit terms of (RC4), which remain
vanishing after multiplication by $L$. This error pays both the
local Gaussian compensation and the outer $\gamma$ versus $r$
weight. No replacement $\beta=1/2$ is made.

### Absolute inversion on the actual complex zeros

Define the real-axis Mellin transform

$$
M_V(\tau)=\int_0^\infty
 e^{-a_V(u-c_{\rm loc}V)^2}\frac{e^{iLu}}{u^2+1/4}u^{i\tau}\,du.
$$

In the logarithmic coordinate the profile is $g_V(z)=e^z f_V(e^z)$.
Shift its Fourier contour to $\operatorname{Im}z=\pm\alpha_V$,
where $\alpha_V=1/V$. There are no poles in this strip and
$\cos(2/V)\ge1/2$. On either boundary line the real part of
the exponential exponent is at most

$$
-a_V\cos(2/V)u^2+b u-a_Vc_{\rm loc}^2V^2,
\qquad b\le2a_Vc_{\rm loc}V+L/V=4L/V.
$$

Completing the square bounds it by
$8L-9L/4=23L/4<6L$.
The denominator satisfies
$|u^2e^{\pm2i/V}+1/4|\ge\tfrac12(u^2+1/4)$;
the integral of $(u^2+1/4)^{-1}$ on $(0,\infty)$ is $\pi$.
Consequently

$$
|M_V(\tau)|\le2\pi e^{6L}e^{-|\tau|/V}.
\tag{LM3}
$$

The vertical contour sides vanish: near zero the logarithmic
profile is $O(e^{\operatorname{Re}z})$, and at infinity the positive
$\cos(2/V)$ gives quadratic damping. Fourier inversion and analytic
continuation therefore give

$$
f_V(r)=\frac1{2\pi r}\int_{\mathbb R}
 M_V(\tau)r^{-i\tau}\,d\tau
\qquad(|\arg r|<1/V).
$$

For every actual zero in the band,
$|\arg r|\le1/(2\gamma)\le1/(2V)$, so this inverse converges
absolutely. Define

$$
Q_V=\frac{1+1/L}{\pi}\operatorname{Re}
 \int_{\mathbb R}M_V(\tau)J_V(\tau)\,d\tau.
$$

Finite summation with multiplicity commutes with the absolute integral,
and exactly
$Q_V=2(1+1/L)\operatorname{Re}\sum_{V<\gamma\le W}
m_\rho h_V(\gamma)r f_V(r)$.

### Pay the entire frequency tail within a fixed source range

Let $n_V=\sum_{V<\gamma\le W}m_\rho$ and let $Q_{V,K}$ use
only $|\tau|\le K$. Since

$$
h_V(\gamma)\le e^{L/4}/V,\qquad
|J_V(\tau)|\le\frac{n_V e^{L/4}}V e^{|\tau|/(2V)},
$$

(LM3) pays the complete two-sided omitted frequency integral:

$$
|Q_V-Q_{V,K}|
 \le8(1+1/L)n_V e^{25L/4}e^{-K/(2V)}.
$$

Choose $K_V=20VL$. Then this allowance is
$8(1+1/L)n_V A^{-15/4}$.
The bands are disjoint, so $\sum n_V\le N_0(T)\ll T\log T$.
Using the retained $T=A^{1/4}e^{-\kappa\Omega}$ gives

$$
\sum_{\text{bands}}|Q_V-Q_{V,K_V}|
 \ll LA^{-7/2}\longrightarrow0.
\tag{LM4}
$$

Moreover $K_V/(V\log V)=20L/\log V\le140$ under the stated
eventual conditions. The positive frequencies lie within the fixed
$O(V\log V)$ range of GSS Theorem 2; its implied constants must
be those for this prescribed fixed range. Reflection preserves
$h_V(\gamma)$ and sends $r$ to $\overline r$, hence
$J_V(-\tau)=\overline{J_V(\tau)}$. This accesses negative frequencies
without assuming RH. The frequency-range statement alone supplies
no signed bound.

### Height weights, endpoint atoms and the remaining source error

For $V\le v\le W$ let
$I_V(v,\tau)=\sum_{V<\gamma\le v}m_\rho r^{-i\tau}$.
Ordinary finite partial summation yields

$$
J_V(\tau)=h_V(W)I_V(W,\tau)
 -\int_V^W h_V'(v)I_V(v,\tau)\,dv,
\qquad
|h_V'(v)|\le\frac{e^{L/4}(L+1)}{V^2}.
$$

The source uses $[V,v)$ rather than $(V,v]$. Define the exact atom
$E_z(\tau)=\sum_{\gamma=z}m_\rho r^{-i\tau}$. Then

$$
I_V(v,\tau)=I_{\rm GSS}(V,v,\tau)+E_v(\tau)-E_V(\tau).
$$

Keep these atoms in the endpoint term and in the partial-summation
integral. In that integral $E_v$ is supported on finitely many
ordinates and contributes zero as a Lebesgue integral; the lower
$E_V$ term and the upper $E_W$ term still require their exact
contributions. Equivalently, the exact weighted correction to the
source partial sum is $h_V(W)E_W(\tau)-h_V(V)E_V(\tau)$.
At $v=V$, use the empty sum. Every other pair $(V,v)$
is comparable; the whole interval $(S,T]$ is never substituted as
a comparable source interval.

Fix the independent GSS splitting parameter $c_{\rm GSS}=1/2$;
its low/high-frequency transition is $\tau=V\log2/2$.
GSS's high-frequency remainder includes

$$
e^{\tau/(2V)}
 \left((\log V)^2+(\tau/V)^2\log V\right)
 +\frac{\tau^{3/2}}V e^{\tau/(2V)-\tau/v}.
$$

Its low-frequency remainder is $O((\log V)^2)$.
Retain both, as well as the main prime sum and the exact endpoint
atoms. The elementary absolute envelope (LM3) combined with
the displayed height-weight bounds gives, for the integrated
source remainder on one band, only the coarse allowance

$$
O\!\left(A^{25/4}
 \left(L^3+V^{1/2}L\right)\right).
$$

For example the first term uses
$\int_0^\infty e^{-\tau/(2V)}
[(\log V)^2+(\tau/V)^2\log V]d\tau=O(VL^2)$;
the second uses $v\le2V$ and
$\int_0^\infty\tau^{3/2}e^{-\tau/V}d\tau=O(V^{5/2})$.
The partial-summation weight has total bound
$e^{L/4}(L+2)/V$.
There are $O(L)$ bands and $\sum\sqrt V=O(\sqrt T)$, so the
corresponding allowance for the entire middle is
$O(A^{25/4}(L^4+\sqrt T\,L))$.
This growing upper allowance does not control the desired signed
response. It is neither a lower bound for the actual remainder nor
an impossibility result for cancellation or a sharper transport.

### Restore the complete original response

Put

$$
Y(A)=\sqrt A L\,2\operatorname{Re}
 \sum_{0<\gamma\le S}m_\rho F_A(\rho)
 +\sum_{\text{bands}}Q_{V,K_V}.
$$

(RC2), (LM2), (LM4) and the retained complete original suffix give

$$
\begin{aligned}
|\sqrt A L Z_{\rm orig}(A)-Y(A)|
\le{}&\left(\frac{2(L+2)}{L^2}+8(1+1/L)L\right)B_3(A,S)\\
&+\sqrt A L\,2\sum_{\gamma>T}m_\rho|F_A(\rho)|
 +O(LA^{-7/2})\longrightarrow0.
\end{aligned}
\tag{LM5}
$$

Every actual real part, multiplicity, coefficient and height is
retained or covered by an explicit error. The contribution to
$I_\psi$ is $-Z_{\rm orig}$, so its normalized approximation is
$-Y(A)$; all elementary terms and the strict core remain unchanged.
The exact low head, the signed transformed middle and its integrated
GSS prime and error contributions are still unpaid. This interface
does not prove the full signed Robin estimate, a numerical threshold,
a uniform strict margin or RH.

## A norm floor for the local GSS absolute endpoint allowance

The local inversion permits a sharper method diagnosis than the
growing sufficient allowance displayed above. Retain exactly the
kernel, height weight and cutoff in (LM1)–(LM5), on the same bands
$S\le V<W\le\min(2V,T)$, with the same eventual
conditions. Put $\tau_0=V\log2/2$, the fixed GSS splitting point.
As in (R5)–(R7), distinguish a positive majorant allowance from the
actual signed source error. The following is a paper-level application
of the existing inverse, with no originality or Lean-verification claim.

### The actual transform has an in-range weighted norm floor

Use the analytic test point
$r_*=c_{\rm loc}V-i/2$, with $c_{\rm loc}=3/2$.
It is not an asserted zeta zero. Since $|\arg r_*|\le1/(3V)$,
the absolute inverse from (LM3) gives

$$
\int_{\mathbb R}|M_V(\tau)|e^{|\tau|/(2V)}\,d\tau
 \ge2\pi|r_*f_V(r_*)|\ge\frac{2\pi\sqrt A}{3V}.
\tag{LM6}
$$

For the last inequality write $x=c_{\rm loc}V\ge1$.
The Gaussian factor has modulus $e^{a_V/4}\ge1$ and
$|e^{iLr_*}|=\sqrt A$. Moreover

$$
\frac{|r_*|}{|r_*^2+1/4|}
 =\frac{\sqrt{x^2+1/4}}{x\sqrt{x^2+1}}
 \ge\frac1{2x}=\frac1{3V}.
$$

This uses the chosen analytic kernel at a test point, without replacing
any actual zero's real part.

The floor cannot be assigned only to frequencies outside GSS's retained
range. In the defining real-axis integral for $M_V$, split at $V/2$.
On the lower part the Gaussian is at most $A^{-1}$; on the upper
part $(u^2+1/4)^{-1}\le4/V^2$ and the complete real Gaussian
integral is $\sqrt\pi V/\sqrt L$. Thus, for every real $\tau$,

$$
|M_V(\tau)|\le\frac\pi A+\frac{4\sqrt\pi}{V\sqrt L}.
$$

Consequently the weighted norm on $|\tau|\le\tau_0$ is at most
$2\pi V/A+8\sqrt\pi/\sqrt L$. From (LM3), the entire weighted
norm beyond $K_V=20VL$ is at most

$$
\int_{|\tau|>K_V}|M_V(\tau)|e^{|\tau|/(2V)}\,d\tau
 \le8\pi V e^{6L-K_V/(2V)}=8\pi V A^{-4}.
$$

Subtract both parts from (LM6) to obtain

$$
\begin{aligned}
\int_{\tau_0<|\tau|\le K_V}|M_V(\tau)|e^{|\tau|/(2V)}\,d\tau
\ge{}&\frac{2\pi\sqrt A}{3V}-\frac{2\pi V}A
 -\frac{8\sqrt\pi}{\sqrt L}-8\pi V A^{-4}\\
\ge{}&\frac{\pi\sqrt A}{3V}
\qquad\text{eventually, uniformly for }S\le V\le T.
\end{aligned}
\tag{LM7}
$$

Indeed $\sqrt A/V\ge A^{1/4}e^{\kappa\Omega}$ grows, whereas
each subtracted bound vanishes uniformly. The source range and
negative-frequency reflection are precisely those already retained
in (LM4); no new source theorem or range calculation is required.

### The defined endpoint budget cannot tend to zero

GSS's high-frequency remainder includes the positive majorant shape
$e^{\tau/(2V)}(\log V)^2$. Define the **unit-coefficient allowance**
for its term-by-term absolute propagation through the weighted
height endpoint by

$$
\mathcal B^{\rm GSS}_V(A)=\frac{1+1/L}{\pi}
 h_V(W)(\log V)^2
 \int_{\tau_0<|\tau|\le K_V}
 |M_V(\tau)|e^{|\tau|/(2V)}\,d\tau.
$$

Since $h_V(W)\ge1/W\ge1/(2V)$, (LM7) gives

$$
\mathcal B^{\rm GSS}_V(A)
 \ge\frac{\sqrt A(\log V)^2}{6V^2}
 \ge\frac{L^2e^{2\kappa\Omega}}{294}
 \longrightarrow\infty.
\tag{LM8}
$$

Here $\log V\ge\log S\ge L/7$ and
$V\le T=A^{1/4}e^{-\kappa\Omega}$.
Multiplying the printed majorant shape by any fixed positive source
coefficient multiplies this floor by that coefficient. No numerical
value for it or effective starting threshold follows from big-$O$
notation. No unbounded sequence of selected integer sources is
asserted, nor a failure at a particular selected $A$.

This is a lower bound for the explicitly defined allowance, not for
the actual remainder, its integral, the total propagated error or a
Robin violation. The second printed source-error shape, derivative
terms and endpoint atoms retain their roles in (LM5).
Because (LM8) uses the actual transform, merely sharpening its crude
upper bound $e^{6L}$ cannot make this same absolute endpoint budget
tend to zero. Joint cancellation, stronger source information,
another kernel or a favorable bound for the combined main and exact
low head could change the budget comparison; none is excluded or
supplied here. The original full signed Robin condition and RH remain
unproved, with all coefficients, real parts, multiplicities and
height ranges unchanged.

### A shrinking strip improvement alone leaves the first-band allowance large

Retain the kernel and complete frequency range of (LM1)–(LM8).
Grant, only for this comparison, a strengthened source endpoint
majorant in which $e^{|\tau|/(2V)}$ is replaced by
$e^{(1/2-\delta(V))|\tau|/V}$, where $\delta(V)\ge0$ and
$\delta(V)\to0$. No such strengthened GSS estimate is inferred merely
from a zero-free region. Define $\mathcal B_{V,\delta}$ by this
replacement in the same unit-coefficient absolute allowance
$\mathcal B^{\rm GSS}_V$.

Since the retained range has $|\tau|\le K_V=20VL$, direct comparison
of the existing positive integrals gives

$$
\mathcal B_{V,\delta}(A)
\ge e^{-20\delta(V)L}\mathcal B^{\rm GSS}_V(A)
\ge e^{-20\delta(V)L}\frac{\sqrt A(\log V)^2}{6V^2}.
$$

On the first band, $V=S=A^{1/6}e^{-\kappa\Omega}$ and eventually
$W=2S\le T$, the already retained $\log S\ge L/7$ therefore yields

$$
\mathcal B_{S,\delta}(A)
\ge\frac{L^2}{294}
 \exp\!\left(\frac L6+2\kappa\Omega-20\delta(S)L\right)
\longrightarrow\infty.
$$

Here $S\to\infty$, $\delta(S)\to0$ and $\Omega=o(L)$.
For example, the existing gap $\delta(V)=\eta(2V)$ from the
Vinogradov–Korobov input above has these properties. Thus even granting
this exponential improvement, while retaining the other endpoint
prefactors, cannot make the same independently absolute allowance
uniformly bounded on all middle bands. Any fixed positive source
coefficient preserves the conclusion.

This is a direct application of (LM8), not a new norm, density or
zero-free theorem. The lower bound concerns only the defined
allowance; it is not a lower bound for the actual remainder, a Robin
violation or a failure at a certified numerical clock. Additional
prefactor savings, joint signed cancellation, other kernels or a
favorable combined head/main bound retain their roles. The original
complete signed estimate and RH remain unproved.

### Actual zero jumps obstruct a uniform inverse-height prefactor

The classical jump principle gives a further application boundary for
the retained source interface. Reuse GSS Theorem 2, printed p.3 of
[arXiv:2505.14228v1](https://arxiv.org/pdf/2505.14228v1), and its
Riemann–von Mangoldt inputs (3)–(4), printed p.2. No source proof is
repeated. This evaluates a proposed strengthening of that particular
interface; it is not a mathematical originality claim or an improved
Robin estimate.

With the source's half-open convention, write

$$
I(V,v,\tau)=\sum_{V\le\gamma<v}m_\rho r_\rho^{-i\tau},
\qquad r_\rho=\gamma+i(1/2-\beta),
$$

and retain its complete high-frequency main term

$$
P(V,v,\tau)=
\frac{e^{i(\tau+\pi/4)}\tau^{1/2-i\tau}}{\sqrt{2\pi}}
\sum_{e^{\tau/v}\le n\le e^{\tau/V}}
\frac{\Lambda(n)(\log n)^{i\tau}}{n^{1/2}\log n}.
$$

Here sums over $\rho$ list distinct zeros and attach their actual
multiplicities $m_\rho$. Suppose one attempted to strengthen only the
first printed error shape by a factor $V^{-1}$, leaving the main term
and second shape unchanged:

$$
|I(V,v,\tau)-P(V,v,\tau)|
\le C\left[
 V^{-1}e^{\tau/(2V)}
 \left((\log V)^2+(\tau/V)^2\log V\right)
 +\frac{\tau^{3/2}}{V}e^{\tau/(2V)-\tau/v}
\right].
\tag{JP1}
$$

The proposed $C$ is fixed and uniform in $v,\tau$ on the same
comparable-height source range, including
$21V/20<v<6V/5$ and the frequencies used below. Such a uniform
strengthening cannot hold, unconditionally and even under RH.

For every sufficiently large $V$, the cited count gives an actual
zero ordinate $\Gamma\in(21V/20,23V/20)$. Choose

$$
\frac74V\log V<\tau<\frac74V\log V+V
$$

outside the finitely many values $\Gamma\log n$ in this interval.
Then $P(V,v,\tau)$ is locally constant as $v$ crosses $\Gamma$:
its lower cutoff crosses no integer there, and its upper cutoff and
coefficients are independent of $v$. The frequency lies in the
printed fixed $O(V\log V)$ regime. For $S\le V\le T$ it also lies
below the retained $K_V=20VL$ eventually, using the existing scale
relations, without changing that frequency range.

By contrast, the two one-sided values of $I$ differ by the exact atom

$$
J_\Gamma(\tau)=\sum_{\Im\rho=\Gamma}
 m_\rho\bigl(\Gamma+i(1/2-\beta)\bigr)^{-i\tau}.
$$

The actual functional-equation reflection
$\rho\mapsto1-\overline\rho$ preserves this ordinate and
multiplicity and sends $r_\rho$ to $\overline r_\rho$.
For a reflected noncritical pair, with the usual logarithm in the
right half-plane, its contribution is

$$
m_\rho(r^{-i\tau}+\overline r^{-i\tau})
=2m_\rho\cosh(\tau\arg r)\,e^{-i\tau\log|r|}.
$$

A critical-line zero is counted once, with its original
multiplicity and phase $e^{-i\tau\log\Gamma}$. Since
$|1/2-\beta|<1/2$, every reflected pair has phase displacement
from this central phase at most

$$
0\le\tau\log(|r|/\Gamma)
\le\frac{\tau}{8\Gamma^2}
=O(\log V/V).
$$

Choose $k\in\{0,1,2,3\}$ so that the central phase after
multiplication by $i^k$ is within $\pi/4$ of the positive real axis.
Eventually every pair and critical-line contribution is within
$\pi/3$, and $2\cosh(\tau\arg r)\ge2$. Therefore

$$
\operatorname{Re}\bigl(i^kJ_\Gamma(\tau)\bigr)
\ge\frac12\sum_{\Im\rho=\Gamma}m_\rho\ge\frac12.
\tag{JP2}
$$

The four phases here are output observation directions. This
projection does not assert a new intertwining between the FIB
operators $M,J,C=MJ$ and the actual zeta spectrum.

For $v$ on either side sufficiently close to $\Gamma$, take
$v\le6V/5$. The two proposed majorants in (JP1) satisfy

$$
V^{-1}e^{\tau/(2V)}
 \left((\log V)^2+(\tau/V)^2\log V\right)
=O\!\left(V^{-1/8}(\log V)^3\right),
$$

$$
\frac{\tau^{3/2}}V e^{\tau/(2V)-\tau/v}
=O\!\left(V^{-1/12}(\log V)^{3/2}\right).
$$

Both tend to zero, uniformly in this neighborhood. A locally
constant main and two vanishing one-sided residuals cannot produce
the nonvanishing jump (JP2). More explicitly, one of the actual
one-sided residual magnitudes is at least $|J_\Gamma|/2\ge1/4$.
This contradicts (JP1) for any fixed $C$. The conclusion also rules
out a still smaller first shape obtained by combining this factor
$V^{-1}$ with a nonnegative exponential reduction $\delta(V)$.

The preceding allowance comparison separately shows why this
restricted prefactor question matters. If its first shape alone
were multiplied by $V^{-p}$, with fixed $p\ge0$ and
$\delta(V)\to0$, its defined first-band allowance would have the
lower bound

$$
S^{-p}\mathcal B_{S,\delta}(A)
\ge\frac{L^2}{294}
 \exp\!\left(
 \frac{1-p}{6}L+(2+p)\kappa\Omega-20\delta(S)L
 \right).
\tag{JP3}
$$

For every fixed $p<1$ this diverges. Thus a uniform pure
inverse-height-power repair of the first shape cannot supply the
required bounded independent allowance: powers below one retain
this allowance floor, while powers at least one encounter the
actual-jump obstruction. This is not a sufficiency equivalence;
the unchanged second shape and all other terms still matter.

The lower bound $1/4$ concerns the actual pointwise residual near
the chosen zero jumps, not its signed Mellin integral or its
height-weighted integral. Restricted parameter ranges, smoothing,
explicit atomic main terms, joint signed cancellation and other
kernels can escape this particular model. Keep the exact endpoint
atoms in (LM5), the actual real parts and multiplicities, the
original rational coefficient, the low head and all heights. The
complete signed Robin estimate and RH remain unproved. These
application calculations are paper-level and have no Lean
verification or certified numerical starting clock.

### Scope of the Gaussian single-zero-sum formula

Kamiya–Suzuki, *An asymptotic formula for a sum involving zeros of
the Riemann zeta-function*, Publications de l'Institut Mathématique
76(90) (2004), 81–88,
[DOI 10.2298/PIM0476081K](https://doi.org/10.2298/PIM0476081K),
[primary text](http://elib.mi.sanu.ac.rs/files/journals/publ/96/n090p081.pdf),
studies

$$
H(u,v)=\sum_\rho e^{u\rho^2-v\rho}.
$$

Theorem 1.1 is unconditional and retains actual zero real parts and
multiplicities. Its $u\downarrow0$ resonance estimates at
$v=\pm\log m$ have constants depending on the fixed integer $m>2$;
its off-resonance estimates are uniform on fixed closed intervals
contained in the positive or negative half-line and avoiding the
corresponding prime-power logarithms. These intervals exclude zero.
Neither statement
supplies uniform control when the frequency parameter grows with $A$.
The subsequent RH specialization is an illustration, not a hypothesis
of the theorem.

Lemma 2.1 gives the exact Gaussian explicit formula for every $u>0$
and real $v$. It is a special case of Weil's formula, already available
as an interface. Lemma 3.1 bounds its real convolution residual between
zero and one; this does not bound the complete prime and archimedean
contributions.

For the localized kernel above, put $a=L/V^2$, $c=3/2$ and
$r=i(1/2-\rho)$. Its numerator has the exact parameter correspondence

$$
e^{-a(r-cV)^2+iLr}
=e^{a/4-L/2+iacV-ac^2V^2}
 e^{a\rho^2-v_V\rho},\qquad
v_V=a-L+2iacV.
$$

Here $v_V$ is complex, while the printed lemma takes real $v$.
Analytic continuation of an identity alone supplies no uniform signed
estimate in this moving parameter range. The rational denominator
$r^2+1/4=\rho(1-\rho)$, the height restrictions and the compensating
weight $h_V(\gamma)$ also remain to be transported. Thus the printed
Gaussian results do not pay the signed middle, its combined prime and
error contribution, or the exact low head in (LM5). They are reused
within their stated scope, without excluding a future weighted
application or establishing the original Robin bound or RH.

### A real-parameter heat integral transports the rational high response

The exact real-parameter formula of Kamiya–Suzuki, Lemma 2.1, can
also be used with a different kernel. Keep the original selected
integer, $A,L,S$ and complete coefficient $F_A$. Reuse (RC2)–(RC4),
the reciprocal-square zero count and the printed Gaussian formula;
their source proofs are not repeated. This application pays a
transport error, not the sign of the resulting prime expression.
It makes no mathematical originality or Lean-verification claim.

Put

$$
u_*=\frac{L}{S^2},\qquad
\mathcal H(u,v)=\sum_\rho m_\rho e^{u\rho^2-v\rho},\qquad
\mathcal H_{\le S}(u,v)=
 \sum_{|\operatorname{Im}\rho|\le S}m_\rho e^{u\rho^2-v\rho}.
$$

These sums list distinct nontrivial zeros, with their actual
multiplicities. Both conjugate signs of the ordinate are included.
The head includes every zero at the cut. Work eventually with
$L\ge2$, $S\ge H$ and $u_*\le1/16$; no numerical starting clock is
certified. The head below $S$ includes unverified heights above $H$
and is retained exactly.

For an actual $\rho=\beta+i\gamma$,
$\operatorname{Re}[\rho(1-\rho)]=\gamma^2+\beta(1-\beta)>0$.
Consequently the elementary scalar resolvent identity gives

$$
\frac{A^{\rho-1/2}}{\rho(1-\rho)}
=A^{-1/2}\int_0^\infty
 e^{u\rho^2-(u-L)\rho}\,du.
\tag{HR1}
$$

The Gaussian parameter $v=u-L$ is real throughout. No continuation
of the printed lemma to complex $v$ is needed. Its fixed-parameter
asymptotic theorem is not used in this moving range.

For $|\gamma|>S$, the modulus of the normalized integrand in
(HR1) is at most $\sqrt A e^{-u\gamma^2}$. Thus summation and
integration are absolutely interchangeable, since
$\sum_{\gamma>S}m_\rho/\gamma^2\ll\log S/S$. The entire discarded
heat-time suffix, still summing every zero height, has allowance

$$
\begin{aligned}
A^{-1/2}\int_{u_*}^\infty
 \sum_{|\gamma|>S}m_\rho
  |e^{u\rho^2-(u-L)\rho}|\,du
&\le2\sqrt A\,e^{-u_*S^2}
 \sum_{\gamma>S}\frac{m_\rho}{\gamma^2}\\
&\ll A^{-1/2}\frac{\log S}{S}\longrightarrow0.
\end{aligned}
\tag{HR2}
$$

Here $e^{-u_*S^2}=A^{-1}$. This truncates heat time, not the zero
height range. In particular every zero above the previously paid
whole-response cut $T$ is included before this bound is applied.

Write

$$
\mathcal G_u(t)=\frac{e^{-t^2/(4u)}}{\sqrt{4\pi u}},
\qquad
\mathcal D_{A,u_*}=A^{-1/2}\int_0^{u_*}
 \left[A-\sum_{n\ge2}\Lambda(n)
       \mathcal G_u(\log n-L+u)\right]du.
\tag{HR3}
$$

The pole is centered at the same arithmetic clock as the primes.
Indeed the continuous background is exactly

$$
\int_0^\infty\mathcal G_u(\log x-L+u)\,dx=A.
$$

Retain this difference as a combined signed expression; its
definition gives no estimate for its sign or size. The integrated
prime terms are not replaced by an average over other clocks.

At $v=u-L$, the two pole terms in the literal source formula are
$A+1$. Its first prime sum is precisely the one in (HR3). Its
remaining terms contribute a vanishing allowance after multiplying
by $A^{-1/2}$ and integrating over $0<u<u_*$. To see this using
only the printed interfaces, its logarithmic archimedean term becomes

$$
\frac{e^{-u/4}}{2\pi}\int_{\mathbb R}
 \log|1/4+it/2|\,e^{-ut^2+itL}\,dt.
$$

Since $|\log|1/4+it/2||\ll\log(2+|t|)$, its complete absolute
integral over heat time is

$$
O\!\left(\int_0^{u_*}u^{-1/2}\log(2/u)\,du\right)
=O\!\left(\sqrt{u_*}\log(2/u_*)\right)
\longrightarrow0.
$$

The source's Lemma 3.1 gives
$0\le(E*\mathcal G_u)(u-L)\le1$. Its convolution term and the
constant pole $1$ together cost at most $2A^{-1/2}u_*$.
The $\log\pi$ term and the second prime sum have allowance

$$
O\!\left(A^{-1/2}\sqrt{u_*}
           e^{-L^2/(16u_*)}\right).
$$

For the second sum this follows from $L-u\ge L/2$ and
$(L-u)/(2u)\ge1$:

$$
\sum_{n\ge2}\frac{\Lambda(n)}n
 e^{-(u-L-\log n)^2/(4u)}
\le e^{-L^2/(16u)}
     \sum_{n\ge2}\frac{\log n}{n^2},
$$

where the last series is finite. All these terms retain the signs
and coefficients of Lemma 2.1; only their absolute propagation
is bounded. Because $S=A^{1/6}e^{-\kappa\Omega}$,
$\sqrt{u_*}\log(2/u_*)=O(L^{3/2}/S)\to0$.

No endpoint value at $u=0$ is substituted. For each fixed $A$,
the Gaussian zero sum is integrable on this finite heat interval:
the reciprocal-square count controls its high part, and its head is
finite. All other source terms just bounded are integrable there.
The nonnegative first prime sum is consequently integrable by the
exact source identity; Tonelli then permits its prime summation and
heat integral to be interchanged. This includes the case where $A$
is exactly a prime power, without importing fixed-resonance
asymptotics. Integrating the two pole terms separately to infinite
heat time would diverge and is not used.

Define the exact combined head

$$
\mathcal J_{\rm head}(A)=
 \sqrt A L\,2\operatorname{Re}
      \sum_{0<\gamma\le S}m_\rho F_A(\rho)
 -(1+1/L)A^{-1/2}\int_0^{u_*}
      \mathcal H_{\le S}(u,u-L)\,du.
\tag{HR4}
$$

The finite subtraction belongs to the same zero multiset and
clock; it is not an independently optimized head allowance.
Combining (HR1)–(HR4) with the single coefficient comparison (RC2)
gives the complete original response

$$
\boxed{
\sqrt A L\,Z_{\rm orig}(A)
=\mathcal J_{\rm head}(A)
 +(1+1/L)\mathcal D_{A,u_*}+o(1).}
\tag{HR5}
$$

More precisely, the absolute discrepancy is at most

$$
\frac{2(L+2)}{L^2}B_3(A,S)
 +O\!\left(
 A^{-1/2}\frac{\log S}{S}
 +\sqrt{u_*}\log(2/u_*)
 +A^{-1/2}u_*
 +A^{-1/2}\sqrt{u_*}e^{-L^2/(16u_*)}
 \right),
\tag{HR6}
$$

which tends to zero by the already retained (RC4). All actual real
parts, conjugate and reflected multiplicities, original coefficient
errors and infinite zero heights are covered. No complex-v
extension, GSS pointwise remainder or independent GSS endpoint
allowance is used in this alternative transport.

The nontrivial-zero contribution to the original $I_\psi$ is still
$-Z_{\rm orig}$. Paying (G9) through (HR5) requires an upper bound for
its combined right side, plus the positive elementary correction $r_A$
defined after (G9) and an allowance for the signed discrepancy (HR6).
The strict core at the same integer remains the one already proved.
Neither $\mathcal D_{A,u_*}$ nor $\mathcal J_{\rm head}$ is bounded
here by the required margin. In particular the head subtraction
does not establish positivity or an estimate for the unverified
head. The full original Robin bound and RH remain unproved.

### The heat prime response has a paid finite arithmetic window

The positive kernel in (HR3) permits an unconditional localization
of its prime sum. This uses only $\Lambda(n)\le\log n$, the
Gaussian bound below and the same $A,L,S,u_*$. It is an application
estimate for this profile, not a new prime-distribution theorem,
an originality claim or a Lean-verified result.

For $0<U\le1/16$ and $d\in\mathbb R$, put

$$
K_U(d)=\int_0^U\mathcal G_u(d+u)\,du.
$$

Expanding the square inside the Gaussian gives

$$
0\le K_U(d)
=e^{-d/2}\int_0^U
 \frac{e^{-d^2/(4u)-u/4}}{\sqrt{4\pi u}}\,du
\le\sqrt{U/\pi}\,e^{-d/2}e^{-d^2/(4U)}.
\tag{HR7}
$$

For $A\ge e^2$, $L=\log A$ and any $D>0$, split the last
Gaussian exponent into two equal parts. On $|d|>D$ one part is
at most $e^{-D^2/(8U)}$. Consequently

$$
\sum_{|\log(n/A)|>D}\Lambda(n)K_U(\log(n/A))
\ll\sqrt U\,e^{-D^2/(8U)}\sum_{n\ge2}f_{A,U}(n),
$$

where

$$
f_{A,U}(x)=\log x\,(A/x)^{1/2}
 \exp\!\left[-\frac{(\log x-L)^2}{8U}\right],\qquad x\ge1.
$$

This nonnegative function vanishes at $1$ and at infinity and
has just one maximum. Indeed, for $t=\log x>0$, its logarithmic
derivative with respect to $t$ is
$1/t-1/2-(t-L)/(4U)$, which is strictly decreasing from positive
infinity to negative infinity. The elementary unimodal
sum–integral comparison therefore gives

$$
\sum_{n\ge2}f_{A,U}(n)
\le\int_1^\infty f_{A,U}(x)\,dx
    +2\sup_{x\ge1}f_{A,U}(x).
$$

Write $d=\log x-L$. Completing the square first with
$e^{-d/2}$ and then with $e^{d/2}$ gives, uniformly in the stated
parameters,

$$
\sup_{x\ge1}f_{A,U}(x)
\le e^{U/2}(L+2U+2\sqrt U)\ll L+1,
$$

$$
\begin{aligned}
\int_1^\infty f_{A,U}(x)\,dx
&\le A e^{U/2}\int_{\mathbb R}
 (L+|d|)e^{-(d-2U)^2/(8U)}\,dd\\
&\ll A\sqrt U(L+1).
\end{aligned}
$$

These comparisons account for the integer grid as well as the
continuous background. Combining them with (HR7) proves the
complete positive arithmetic tail bound

$$
\boxed{
\sum_{|\log(n/A)|>D}\Lambda(n)K_U(\log(n/A))
\ll (L+1)(AU+\sqrt U)e^{-D^2/(8U)}.}
\tag{HR8}
$$

No prime powers outside the displayed window are dropped before
this bound is applied, and no prime-counting asymptotic or average
over $A$ is assumed.

Now use the same $U=u_*=L/S^2$ as (HR1)–(HR6), and take

$$
D_*=4\sqrt{u_*L}=\frac{4L}{S},\qquad
\mathcal W_A=\{n\ge2:Ae^{-D_*}\le n\le Ae^{D_*}\}.
$$

Keep both endpoints in this finite window. Define

$$
\mathcal D^{\rm loc}_{A,u_*}
=A^{-1/2}\left[
 Au_*-\sum_{n\in\mathcal W_A}\Lambda(n)
       K_{u_*}(\log(n/A))\right].
$$

Since $e^{-D_*^2/(8u_*)}=A^{-2}$, (HR8) yields

$$
0\le\mathcal D^{\rm loc}_{A,u_*}-\mathcal D_{A,u_*}
\ll(L+1)\left(\sqrt A\,u_*+
 \frac{\sqrt{u_*}}{\sqrt A}\right)A^{-2}
\longrightarrow0.
\tag{HR9}
$$

The direction is relevant to Robin: removing the outside positive
prime terms increases $\mathcal D$, hence gives an upper estimate
for its contribution to $Z_{\rm orig}$ and a lower estimate for
the corresponding contribution $-Z_{\rm orig}$ to $I_\psi$.
The separate bound in (HR9) also pays the absolute discrepancy.
Together with (HR5)–(HR6), it gives

$$
\sqrt A L\,Z_{\rm orig}(A)
=\mathcal J_{\rm head}(A)
 +(1+1/L)\mathcal D^{\rm loc}_{A,u_*}+o(1),
\tag{HR10}
$$

with no discarded zero heights or unpaid arithmetic tail.

The relative log window $D_*=4L/S$ tends to zero. Its continuous
arithmetic width is asymptotic to $8AL/S$; this is a window at
$A=\log N$, not a window at the original integer $N$. The weighted
prime-power sum within it is still not estimated by the required
signed margin. Nor is the exact unknown head in (HR4) paid by
localization. The original selected-source joint estimate, strict
core, all actual real parts and multiplicities remain unchanged,
and RH remains unproved. All limits are eventual, with no
certified numerical starting clock.

## Whole multiplicative sums do not control prescribed prime blocks

Granville–Lamzouri, *Large values of exponential sums with
multiplicative coefficients*,
[arXiv:2604.02306v1](https://arxiv.org/pdf/2604.02306v1),
Corollary 1.1 and Example 1.2, printed pp.5–6, give a useful one-way
interface. Write $e(t)=\exp(2\pi it)$ and

$$
S_f(x,\alpha)=\sum_{n\le x}f(n)e(\alpha n),\qquad
f:\mathbb N\to\{z:|z|\le1\}\text{ multiplicative}.
$$

For fixed $\epsilon\in(0,1/10)$, Corollary 1.1 assumes
$|\alpha-a/q|\le1/(qx)$, $(a,q)=1$ and
$(\log x)^{2+\epsilon}\le q\le x/(\log x)^{3+\epsilon}$.
An inequality $|S_f(x,\alpha)|\ge cx/\log x$, with fixed
$c\in(0,1)$, forces a dyadic prime sum with large modulus for some
positive integer harmonic $h\ll c^{-2}\log(1/c)$ and a block location
$c^2x/\log(1/c)\ll z\le x/(2h)$. This is an existential conclusion,
not a bound for a prescribed prime block.

The source's Example 1.2 supplies a completely multiplicative $f$
with $|f|\le1$, a cutoff $y\sim3x/4$, $z=y/2$ and
$\delta\in\{0,1\}$ such that

$$
S_f(x,\alpha)=e(\alpha)+\delta,\qquad
\sum_{z<p\le2z}f(p)e(\alpha p)\sim\frac{x}{4\log x}.
$$

Thus multiplicativity and cancellation of the whole integer sum alone
do not imply cancellation of each prime block. This printed
counterexample is reused directly; it concerns the source's selectable
coefficients, not a counterexample for the actual
$\Lambda(n)n^{-it}$ Gaussian response.

The actual von Mangoldt weight is not multiplicative:
$\Lambda(6)=0$ while $\Lambda(2)\Lambda(3)>0$; multiplication by a fixed
nonzero scalar preserves that obstruction. Putting $n^{-it}$ into an
admissible multiplicative coefficient instead leaves the prime support,
$\Lambda$ weight, Gaussian cutoff and signed transport to be justified.
Corollary 1.1 supplies no such bridge or original-kernel estimate.
The same selected integer, complete rational coefficient, actual zero
real parts and multiplicities, exact low head and all remaining height
ranges therefore retain their roles in (LM5) and (G9). The required
joint signed estimate and RH remain unproved.


### The same-source price minimum gives a nonnegative heat cost

The existing unrestricted price pressure and selected-source contact
can be transported into the real heat kernel (HR7). This application
identifies the direction and scale of the resulting constraint. It
reuses the pressure, derivative and limit in the
[FIB theory volume, §98](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
the actual tangent optimum (G1), and (HR1)–(HR10). It does not
reprove those results or the
[packet and cone theorems](../Analytic/mantovanelli2026primeworkload.md).
No mathematical originality or Lean verification is claimed.

Keep the same conditional least global Robin-ratio maximizer $N>5040$,
$A=\log N$, $L=\log A$ and $U=L/S^2$. Write

$$
g(x)=\frac1{x\log x},\qquad
q(x)=-g'(x)=\frac{\log x+1}{x^2(\log x)^2},
$$

$$
\mathcal B(\epsilon)=\max_{m\ge1}
 \{\log Z(m)-\epsilon\log m\},\qquad
\mathcal P(x)=\gamma+\log\log x-g(x)x-\mathcal B(g(x)).
$$

Here $\mathcal P$ is the existing $\mathfrak D$, and $q$ is its
positive derivative weight, not the price. Let
$a_C(x)=\log C_x$ for an unrestricted optimum at price $g(x)$;
ties may use either consistent prefix convention. Local finiteness
of activation events and the existing pressure derivative give

$$
\mathcal P'(x)=q(x)[x-a_C(x)]\quad\hbox{almost everywhere},
\qquad \mathcal P(x)\longrightarrow0.
$$

The selected $N$ attains the optimum at $g(A)$, so
$\mathcal P(A)=\gamma+\log\log A-\log Z(N)$.
Choose a fixed $x_0>1$ such that every optimum for $x\ge x_0$
exceeds $5040$; it suffices that the first thirteen $2$-layers
are strictly active. The actual global Robin maximum and the
concavity tangent for $b(t)=\gamma+\log\log t$ imply

$$
0\le\mathcal P(x)-\mathcal P(A)\le c_A(x)
\quad(x\ge x_0),\qquad
c_A(x)=\log\log x-\log\log A+g(x)(A-x).
\tag{PH1}
$$

For the lower inequality use the Robin comparison at this same
$C_x$ and $b(a_C)\le b(x)+g(x)(a_C-x)$.
For the upper inequality insert the same $N$ as a competitor in
$\mathcal B(g(x))$. Concavity gives $c_A(x)\ge0$ for all $x>1$.
The global comparison does not cover optima at most $5040$;
their fixed interval is paid below, not included in (PH1).

#### A positive kernel row with the correct atom

Put $\ell=\log x$, $d=\log(x/A)$ and
$a(\ell)=\ell^2/(\ell+1)$. The integrated Gaussian obeys, in
the distributional sense on the $d$-line,

$$
K_U''(d)+K_U'(d)=\mathcal G_U(d+U)-\delta_0(d).
$$

Indeed, this is the heat equation integrated over $0<u<U$;
the initial Gaussian is a unit atom. Its one-sided derivatives are

$$
K_U'(d)=
\begin{cases}
 \tfrac12e^{-d}\operatorname{erfc}((-d+U)/(2\sqrt U)),&d<0,\\
 -\tfrac12e^{-d}\operatorname{erfc}((d-U)/(2\sqrt U)),&d>0.
\end{cases}
$$

Thus the derivative jumps by $-1$ at $0$. Define

$$
h(x)=x\,a(\ell)K_U'(d),\qquad
r(x)=a(\ell)\mathcal G_U(d+U)+a'(\ell)K_U'(d).
$$

Using one-sided values at $A$ gives the exact row identity

$$
dh=r(x)\,dx-Aa(L)\delta_A,
\qquad
\pi_{A,U}(dx)=\frac{r(x)}{Aa(L)}\,dx.
\tag{PH2}
$$

The atom has coefficient $Aa(L)$, including the Jacobian
$\delta_0(\log(x/A))=A\delta_A(x)$.
For $d<0$ every term in $r$ is nonnegative. For $d>0$ put
$t=(d-U)/(2\sqrt U)\ge-1/8$, using $U\le1/16$. Then

$$
\frac{-K_U'(d)}{\mathcal G_U(d+U)}
 =\sqrt{\pi U}\,e^{t^2}\operatorname{erfc}(t)
 \le5\sqrt U.
$$

For $t\ge0$ use $e^{t^2}\operatorname{erfc}(t)\le1$;
for $-1/8\le t<0$ use $\operatorname{erfc}(t)\le2$ and
$e^{t^2}\le e^{1/64}$. Since $x>A$, $L\ge2$ and

$$
\frac{a(\ell)}{a'(\ell)}
 =\frac{\ell(\ell+1)}{\ell+2}\ge\frac32
 >5\sqrt U,
$$

we again have $r\ge0$. Moreover $h(1+)=h(\infty)=0$;
the Gaussian decay controls the latter endpoint. Integrating
(PH2) therefore gives $\int_1^\infty r(x)\,dx=Aa(L)$.
Consequently $\pi_{A,U}$ is an actual nonnegative probability
measure on $(1,\infty)$, formed from the same $A$ and kernel.
It is not an average over independently selected extremal integers.

#### The arithmetic correction vanishes at the paid heat scale

Write $\Delta(x)=\psi(x)-a_C(x)$, so

$$
\psi(x)-x=-\frac{\mathcal P'(x)}{q(x)}+\Delta(x).
$$

Only a crude uniform activation estimate is needed here.
The first active prime layer differs from the cutoff $p\le x$
only for $x-1<p\le x$: use
$1/(p+1)<\log(1+1/p)<1/p$ in the activation rule.
Every active higher layer satisfies $p^j\log p<x\log x$,
so there are $O(\log x)$ layers and all their primes lie below
$\sqrt{x\log x/\log2}$. With the elementary
$\vartheta(t)\le t\log t$, the higher layers of $a_C$ and
$\psi$ give the uniform bound

$$
|\Delta(x)|\ll\sqrt x\,[\log(2x)]^{5/2}\qquad(x>1).
$$

This estimate follows from activation, not from imposing GA1
on every intervening CA prefix. In particular it uses neither
a new source-selector theorem nor a square-root PNT error.
For $d\ne0$, differentiating the integral defining $K_U$ and
taking absolute values gives the almost-everywhere estimate

$$
e^{d/2}|K_U'(d)|
\le\int_0^U
 \left(\frac{|d|}{2u}+\frac12\right)
 \mathcal G_u(d)e^{-u/4}\,du.
$$

Gaussian moments and $0<U\le1/16$ therefore imply

$$
\int_{\mathbb R}e^{d/2}(1+|d|)^{5/2}|K_U'(d)|\,dd
 \ll\sqrt U.
$$

At $d=0$ use the one-sided jump in (PH2); differentiation under
the integral there does not supply either one-sided derivative.

After $x=Ae^d$, the complete arithmetic correction satisfies

$$
A^{-1/2}\left|\int_1^\infty\Delta(x)
 \frac{K_U'(\log(x/A))}{x}\,dx\right|
\ll(L+1)^{5/2}\sqrt U
=O(L^3/S)\longrightarrow0.
\tag{PH3}
$$

All actual prime powers are present in this comparison. No
fixed-beta or zero-height simplification is made.

#### Exact direction and the remaining upper requirement

Stieltjes integration by parts in (HR3), including the interval
$0<x\le1$, yields

$$
\mathcal D_{A,U}=A^{-1/2}
 \left[\int_0^1K_U(\log(x/A))\,dx-K_U(-L)
 +\int_1^\infty(\psi(x)-x)
   \frac{K_U'(\log(x/A))}{x}\,dx\right].
$$

The first two terms have allowance
$O(\sqrt U e^{-L^2/(4U)})$ by (HR7).
For the pressure term, $1/(xq(x))=xa(\ell)$, so
integration by parts with (PH2) gives

$$
-A^{-1/2}\int_1^\infty\mathcal P'(x)h(x)\,dx
=\sqrt A\,a(L)\left[\int\mathcal P(x)\,\pi_{A,U}(dx)
 -\mathcal P(A)\right].
$$

There are no pressure atoms at activation events: the existing
pressure is continuous and locally absolutely continuous.
Near $1$, $\mathcal B(g(x))=0$ and
$\mathcal P(x)=\gamma+\log\ell-1/\ell$, while
$a(\ell)=O(\ell^2)$ and $a'(\ell)=O(\ell)$.
These facts justify the lower boundary and integrability.
At infinity reuse $\mathcal P(x)\to0$ and Gaussian decay.

Set the independently nonnegative cost

$$
V_{A,U}=\int_{x_0}^\infty
 [\mathcal P(x)-\mathcal P(A)]\,\pi_{A,U}(dx)\ge0.
$$

The omitted fixed interval $1<x<x_0$ costs at most
$O_{x_0}(U^{-1/2}e^{-(L-\log x_0)^2/(4U)})=o(1)$
after multiplying by $\sqrt A a(L)$. To obtain this bound,
use the preceding integrability at $1$, boundedness of
$\mathcal P(A)$ from its existing limit, and the negative-$d$
derivative formula. No small-prefix Robin comparison is used.
Together with (PH3), this proves the specific transport

$$
\boxed{\mathcal D_{A,U}=\sqrt A\,a(L)V_{A,U}+o(1).}
\tag{PH4}
$$

Combining with (HR5)–(HR10) retains the exact same-source head:

$$
\boxed{\sqrt A L Z_{\rm orig}
 =\mathcal J_{\rm head}
  +(1+1/L)\sqrt A\,a(L)V_{A,U}+o(1).}
\tag{PH5}
$$

All actual zero real parts, multiplicities and heights remain
as specified in those equations. In particular the unknown
head above the verified height is not paid by (PH4).

The existing support gap in (PH1) does give an upper allowance,
but not one of Robin strength. Since $c_A(A)=0$ and
$c_A'(x)=q(x)(x-A)$, (PH2) and integration by parts give

$$
\begin{aligned}
0\le\sqrt A\,a(L)V_{A,U}
&\le\sqrt A\,a(L)\int_1^\infty c_A(x)\,\pi_{A,U}(dx)\\
&=A^{-1/2}\left[\int_1^\infty K_U(\log(x/A))\,dx
 -(A-1)K_U(-L)\right]\\
&\le\sqrt A\,U
=L A^{1/6}e^{2\kappa\Omega}.
\end{aligned}
\tag{PH6}
$$

The final normalization uses the already fixed
$S=A^{1/6}e^{-\kappa\Omega}$.
The displayed allowance diverges. This is not a lower bound
on the actual cost and does not rule out a sharper joint estimate.
It is the same ceiling obtained by merely dropping positive
prime terms in (HR3); the price constraint has not improved it.

Thus the price minimum supplies $\mathcal D_{A,U}\ge-o(1)$.
To apply (G9), retain the elementary correction $r_A>0$ defined there.
Let $\varepsilon_{\rm PH5}(A)$ be the signed discrepancy in (PH5),
so $\varepsilon_{\rm PH5}(A)=o(1)$ by (HR6), (PH3) and the fixed-prefix
allowance. The exact complete response is

$$
-\sqrt A L\,I_\psi(A)
=\mathcal J_{\rm head}
 +(1+1/L)\sqrt A\,a(L)V_{A,U}
 +r_A+\varepsilon_{\rm PH5}(A).
$$

Consequently the remaining joint target, equivalent to (G9), is

$$
\mathcal J_{\rm head}
 +(1+1/L)\sqrt A\,a(L)V_{A,U}
 +r_A+\varepsilon_{\rm PH5}(A)\le\mathcal E(L).
$$

For any proved allowance $\delta(A)\ge|\varepsilon_{\rm PH5}(A)|$,
a sufficient upper estimate is

$$
\mathcal J_{\rm head}
 +(1+1/L)\sqrt A\,a(L)V_{A,U}
 \le\mathcal E(L)-r_A-\delta(A).
$$

The absolute allowance is sufficient, not necessary. Its constants
have not been numerically certified at the selected finite clock.
A vanishing discrepancy alone does not establish (G9) without enough
signed slack; the strict core remains the one already proved.
No such bound, numerical starting clock, unbounded sequence of
selected sources, or proof of RH is established here. The
nonnegative quantity is independently constructed; naming it
does not prove that its size fits the available Robin budget.

## An unconditional primary source already contains the full response coefficient

Akatsuka, *Maximal order for divisor functions and zeros of the Riemann
zeta-function*, [arXiv:2411.19259v1](https://arxiv.org/abs/2411.19259v1),
Proposition 4.4, printed p.15, supplies an unconditional explicit formula
at divisor-weight exponent $1$. Write $\nu$ for the paper's $\kappa$;
this exponent is distinct from the moving-cut constant used above.
This application reuses that proposition and the project's existing
finite-tail identity; it does not reprove the explicit formula or claim
new mathematical content. The selected source statements, exponential
integral convention and parameter correspondence were inspected, not
the complete source proofs or a Lean implementation.

Let $P(X)=\sum_{2\le n\le X}\Lambda(n)/(n\log n)$, using the
prime-power cutoff rather than the full Euler-product logarithm.
Equations (4.9) and (4.11) give

$$
P(X)-\frac{\psi(X)-X}{X\log X}
=\log\log X+\gamma+Z_{\rm Ak}(1;X)+R_{\rm Ak}(1;X),
$$

where

$$
Z_{\rm Ak}(1;X)=-\sum_\rho\left[
 \operatorname{Ei}((\rho-1)\log X)
 -\frac{X^{\rho-1}}{\rho\log X}\right],
$$

$$
R_{\rm Ak}(1;X)=\frac{\zeta'(0)}{\zeta(0)X\log X}
-\sum_{k\ge1}\left[
 \frac{X^{-2k-1}}{2k\log X}
 +\operatorname{Ei}(-(1+2k)\log X)\right].
$$

The zeros retain their actual complex values and multiplicities.
The exponential integral defined immediately before Proposition 4.4
uses the cut $[0,\infty)$ and the horizontal integral from left infinity.
That convention matters: adding a lateral $i\pi$ constant would change
the individual coefficient and its absolute-convergence statement.

For the existing $A=\log N$, $L=\log A$, write (M1) in the source's
convention:

$$
F_A(s)=\frac{A^{s-1}}{sL}-\operatorname{Ei}((s-1)L),
\qquad 0<\Re s<1.
$$

This is the defining integral in the source's convention: the endpoint
term at infinity vanishes in this strip. Thus
$Z_{\rm Ak}(1;A)=Z_{\rm orig}$ with the **complete** $F_A$,
without replacing it by a leading asymptotic term or moving zeros onto
the critical line. Substitution into the existing finite-tail identity
retains the other explicit terms as well:

$$
I_\psi(A)=-Z_{\rm Ak}(1;A)-R_{\rm Ak}(1;A).
$$

The source's maximal-order Theorem 1 concerns fixed
$\nu\in[1/2,1)$; its boundedness condition is equivalent to the stated
zero-free half-plane, not an unconditional upper estimate. Definition
2.1 optimizes $\sigma_\nu(n)/n^{\nu(1+\varepsilon)}$, so its
half-power extremum is not identified with the selected ordinary Robin
extremum. Lemma 4.5 gives $O_\nu$ bounds only for $0<\nu<1$;
it supplies neither a uniform limit as $\nu\to1$ nor the missing signed
bound at exponent $1$. The formula above is an available primary
representation of the original response. The required same-source
upper bound on $Z_{\rm Ak}(1;A)+R_{\rm Ak}(1;A)$, equivalently the
original lower bound on $I_\psi(A)$, remains unproved, as do the strict
Robin margin and RH.

## Quantitative Tauberian hypotheses for the complete response

Pierce, Turnage-Butterbaugh and Zaman, *A guide to Tauberian theorems for arithmetic applications*, [arXiv:2504.16233v4](https://arxiv.org/html/2504.16233v4), §2.3, Hypothesis B and Theorem B, give a quantitative result for a general Dirichlet series $D(s)=\sum_j a_j\lambda_j^{-s}$ with nonnegative coefficients. Write their parameters as $\alpha_{\rm T}>0$, $0<\delta_{\rm T}<\alpha_{\rm T}$, $k_{\rm T}>0$ and $m\ge1$ for the quoted positive-growth version, to distinguish them from the FIB atoms and the moving-cut parameter. Hypothesis B permits $k_{\rm T}=0$ as well. Its assumptions require analytic continuation throughout $\Re s\ge\alpha_{\rm T}-\delta_{\rm T}$ except for the pole of order $m$ at the single real point $\alpha_{\rm T}$, the strip bound

$$
|(s-\alpha_{\rm T})^mD(s)|\le M_1\exp(|s|^{M_2}),\qquad
\alpha_{\rm T}-\delta_{\rm T}\le\Re s\le\alpha_{\rm T},
$$

and, on the left boundary, a uniform bound

$$
|D(s)|\le C(1+|\Im s|)^{k_{\rm T}}
 (\log(3+|\Im s|))^{m-1}.
$$

Under these hypotheses, for $X\ge2$,

$$
\sum_{\lambda_j\le X}a_j
=\operatorname*{Res}_{s=\alpha_{\rm T}}\frac{D(s)X^s}{s}
+O\!\left(X^{\alpha_{\rm T}-\delta_{\rm T}/(k_{\rm T}+1)}
 (\log X)^{m-1}\right).
$$

The implied constant depends on $\alpha_{\rm T},\delta_{\rm T},k_{\rm T},m,C,D(\alpha_{\rm T}+\delta_{\rm T})$, and is independent of $M_1,M_2$. Remark 9.3.1 gives the $k_{\rm T}=0$ version with remainder $O(X^{\alpha_{\rm T}-\delta_{\rm T}}(\log X)^m)$. The parameters are fixed; applying the result to a changing family requires controlling this dependence. In particular, the stated saving is $\delta_{\rm T}/(k_{\rm T}+1)$, rather than a saving of $\delta_{\rm T}$ from analytic continuation alone.

Theorems B.4–B.5 supply limiting examples for $k_{\rm T}>1/2$: general Dirichlet series satisfying Hypothesis B can have a remainder of size $\Omega(X^{\alpha_{\rm T}-\delta_{\rm T}/(k_{\rm T}+1/2)}(\log X)^{m-1})$, including examples with $0\le a_j\le1$. These examples do not identify the exact optimum between the two displayed exponents. The B.4 construction can use integer frequencies when $(k_{\rm T}+1/2)/\delta_{\rm T}$ is a positive integer. The B.5 bounded-coefficient construction uses general real frequencies without giving this integer-frequency guarantee. Neither result asserts a counterexample for the Riemann zeta function or the selected Robin integer.

For the direct prime-counting series $D(s)=-\zeta'(s)/\zeta(s)$, $\lambda_j=j$, $a_j=\Lambda(j)$ and $\alpha_{\rm T}=m=1$. Each actual zeta zero in the proposed half-plane is an additional pole, so the single-pole hypothesis must be verified for all heights. A finite zero subtraction supplies no such verification for the remaining zeros. Applying Theorem B to a resulting remainder also requires a proved nonnegative-coefficient representation and the stipulated uniform growth bounds; none is supplied by this source application.

The same conditional least integer $N>5040$ attaining the global Robin-ratio maximum remains fixed, with $A=\log N>10^{36}$ and $L=\log A$. The original complete $\sqrt A\,L\,I_\psi(A)$ lower allowance, or equivalently the full zero-plus-remainder upper allowance above, has not been obtained from these hypotheses. The actual zero real parts and multiplicities, every height, all remaining explicit terms and the strict core remain present. The published theorem and examples are reused without reconstructing their proofs; this applicability check supplies neither a new prime-error estimate nor a Robin/RH proof.

## A bounded-shape Gamma mixture retains an original coefficient remainder

Balanzario, Cárdenas Romero and Chacón Serna,
*A smooth version of Landau's explicit formula*,
[arXiv:2311.04347v1](https://arxiv.org/abs/2311.04347v1),
Theorem 1, supplies the Gamma density

$$
w_{\alpha,\lambda}(x)
=\frac{x^{\alpha-1}e^{-x/\lambda}}{\lambda^\alpha\Gamma(\alpha)},
\qquad
G_{\alpha,\lambda}(s)
=\lambda^{s-1}\frac{\Gamma(\alpha+s-1)}{\Gamma(\alpha)}.
$$

For $\alpha,\lambda>0$, $\alpha\notin\mathbb N$ and
$\mu=\alpha\lambda$, the stated formula is

$$
\sum_{n\ge1}\Lambda(n)w_{\alpha,\lambda}(n)
=1-\sum_\rho m_\rho G_{\alpha,\lambda}(\rho)-R(\mu,\alpha).
$$

This statement has no RH premise. The source defines $R$ by two separate
series involving falling factorials and $\zeta'/\zeta$; those terms
remain present, with no assumed sign or uniform budget. Its Theorem 2,
which gives a finite-ordinate formula near a natural-number center
$\mu$, assumes RH and fixes its window parameters. That truncated
formula is not an unconditional supplier at $A=\log N$.

The existing algebraic lower bound (H2) also specifies a restriction on
exact replacement by these Gamma coefficients. Fix $A\ge e^2$ and a
finite $B>0$. Let $\nu_A$ be a locally finite signed or complex measure on

$$
\{(\alpha,\lambda):0<\alpha\le B,
\ \alpha\notin\mathbb N,\ \lambda>0\}
$$

which is fixed as the zero height varies, and assume only the critical-line
absolute moment

$$
M_A=\int\lambda^{-1/2}\,d|\nu_A|(\alpha,\lambda)<\infty.
$$

This does not require finite total mass or moments at the endpoints of
the critical strip. Set

$$
Q_A(1/2+it)=\int G_{\alpha,\lambda}(1/2+it)
                         \,d\nu_A(\alpha,\lambda),\qquad t\ne0.
$$

The standard vertical-line Stirling formula,
[DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9), is uniform for bounded real
arguments. Here $\alpha-1/2\in[-1/2,B-1/2]$ and
$1/\Gamma(\alpha)$ is bounded for $0<\alpha\le B$. Consequently,
for a constant $C_B$ and sufficiently large $|t|$,

$$
|Q_A(1/2+it)|
\le C_BM_A|t|^{B-1}e^{-\pi|t|/2}.
$$

In contrast, (H2) on this same line gives, for $|t|\ge4$,

$$
|F_A(1/2+it)|
\ge\frac{2w(A)}{3\sqrt A(t^2+1/4)},
\qquad w(A)=\frac{1+\log A}{(\log A)^2}.
$$

Exponential decay is eventually smaller than this algebraic bound.
Hence there is a threshold depending on $A,B,M_A$ such that

$$
|F_A(1/2+it)-Q_A(1/2+it)|
\ge\frac{w(A)}{3\sqrt A(t^2+1/4)}
$$

above that threshold. There are unconditionally infinitely many actual
critical-line zeros, as recalled in
[DLMF §25.10(i)](https://dlmf.nist.gov/25.10.i).
Thus the mismatch occurs at actual zeros of arbitrarily large height;
it is not merely an off-spectrum difference on the whole strip. Their
positive multiplicities do not remove the coefficient difference.

This applies even to infinitely many scales and to complex mixture
weights under the stated absolute moment. It reuses (H2), uniform
Stirling and the classical critical-line zero theorem; no new version
of those results or mathematical originality is claimed. Shapes and
weights may depend on $A$, but their bound is fixed at each such $A$.
The conclusion concerns exact coefficient matching at every actual zero.
It does not give a sign for a paired residual or exclude equality of an
aggregate signed sum, unbounded shape support, nonabsolute constructions,
or approximation on a finite height range with a paid remainder.
In particular the original suffix above $T$ is already paid independently;
this restriction does not invalidate that transport or prohibit a useful
approximation of its lower head. The complete same-selected-source signed
Robin estimate and RH remain unproved. This application is not Lean
verified.


## Uniform control of the combined Gamma remainder

The two remainder series in Balanzario, Cárdenas Romero and Chacón
Serna, [arXiv:2311.04347v1](https://arxiv.org/abs/2311.04347v1),
Theorem 1, need not be integrated separately. Their combined remainder
has a uniform bound under the existing canonical scale measure. The
following is a `repo-derived` paper-level application of that theorem, the classical
explicit formula displayed as equation (1) in the same source, the
existing coefficient estimate (H5), and unconditional PNT bounds. It
does not reconstruct those source proofs or claim mathematical
originality or Lean verification.

Let $A\ge e^2$, $L=\log A$, and retain (M2):

$$
h_A(\mu)=\frac1{\max(A,\mu)\log\max(A,\mu)},\qquad
k(u)=\frac{1+\log u}{u^2\log^2u}.
$$

For noninteger $\alpha\ge4$, write the source's prime response as

$$
P_\alpha(\mu)=\sum_{n\ge1}\Lambda(n)
 \frac{(\alpha/\mu)^\alpha n^{\alpha-1}e^{-\alpha n/\mu}}
      {\Gamma(\alpha)}
=1-\sum_\rho m_\rho G_{\alpha,\mu/\alpha}(\rho)
 -R(\mu,\alpha).
$$

The sum indexes distinct zero locations, and $m_\rho$ carries their
actual multiplicities. No zero is moved to the critical line. Define

$$
\overline R_\alpha(A)
 =\int_0^\infty h_A(\mu)R(\mu,\alpha)\,d\mu,
\qquad
M_3(\alpha)=\frac{\alpha^3}
 {(\alpha-1)(\alpha-2)(\alpha-3)}.
$$

This integral exists absolutely for each such $\alpha$. There is an
absolute constant $K$, independent of both $A$ and $\alpha$, for which

$$
\boxed{
\left|\overline R_\alpha(A)
 -\frac{\log(2\pi)}{A\log A}\frac{\alpha}{\alpha-1}\right|
 \le\frac{K M_3(\alpha)}{A^3\log A}.}
\tag{GR1}
$$

Since $M_3(\alpha)\le32/3$ and $\alpha/(\alpha-1)\le4/3$,
this is uniform even when the noninteger shape grows with $A$ or
approaches an integer. In particular,

$$
\sqrt A\log A\,\overline R_\alpha(A)
 =\frac{\log(2\pi)}{\sqrt A}\frac{\alpha}{\alpha-1}
  +O(A^{-5/2})\longrightarrow0
\tag{GR2}
$$

uniformly over the stated shapes. The constant is not numerically
certified; no finite starting clock follows.

### Convergence and the dilation representation

Put $D(x)=\psi(x)-x$. Reuse an unconditional PNT bound in the global
form

$$
|D(x)|\le C_\psi\frac{x}{\log^2(2+x)}\qquad(x>0).
\tag{GR3}
$$

An absolute $C_\psi$ exists by PNT with a fixed logarithmic saving,
with the bounded initial interval absorbed into the constant. This is
not a square-root prime-error estimate. Integration by parts against
the fixed-shape Gamma density, splitting its argument at $\sqrt\mu$,
gives $P_\alpha(\mu)-1=O_\alpha((\log\mu)^{-2})$ at infinity.
At zero, $P_\alpha(\mu)=O_\alpha(\mu^{-\alpha}e^{-\alpha/\mu})$.
Consequently $h_A(1-P_\alpha)$ is absolutely integrable. These
convergence constants may depend on the fixed shape; they are not used
as the uniform constants in (GR1).

For fixed $\alpha$, vertical-line Stirling gives exponential decay of
the Gamma coefficient. Moreover (M2) implies, for $0<\beta<1$,

$$
F_A(\beta)\le\frac{A^{\beta-1}}L
 \left(\frac1\beta+\frac1{1-\beta}\right).
$$

The already cited zero-free region and its reflection bound the two
reciprocal endpoint distances by powers of logarithms of the ordinate.
Together with the classical zero count this makes

$$
\sum_\rho m_\rho\int_0^\infty h_A(\mu)
 |G_{\alpha,\mu/\alpha}(\rho)|\,d\mu<\infty.
$$

The source identity therefore proves absolute convergence of the
combined $\overline R_\alpha(A)$, without integrating either printed
remainder series term by term. It also justifies

$$
\overline R_\alpha(A)
 =J_\alpha(A)-\sum_\rho m_\rho H_\alpha(\rho)F_A(\rho),
\quad
J_\alpha(A)=\int_0^\infty h_A(\mu)(1-P_\alpha(\mu))\,d\mu,
\tag{GR4}
$$

where the existing coefficient identity is
$H_\alpha(s)=\Gamma(\alpha+s-1)/[\Gamma(\alpha)\alpha^{s-1}]$.
The constant pole and the prime response have been kept together.

Let $C>0$ have Gamma shape $\alpha$ and rate $\alpha$, so its mean is
one. The source primitive and its negative moments are

$$
U_\alpha(\mu)=\mathbb E\frac{\psi(C\mu)}C,
\qquad U_\alpha'(\mu)=P_\alpha(\mu),
\qquad
\mathbb E C^{-1}=\frac{\alpha}{\alpha-1},
\quad \mathbb E C^{-3}=M_3(\alpha).
$$

The derivative follows by differentiating the Gamma integral for each
prime-power jump. Thus integration by parts gives

$$
J_\alpha(A)=\mathbb E J_C(A),\qquad
J_c(A)=-\frac1c\int_A^\infty D(cu)k(u)\,du.
\tag{GR5}
$$

Here the exchange is an absolute one. For $u\ge A$, (GR3) and the
split $C\ge u^{-1/2}$ or $C<u^{-1/2}$ give

$$
\mathbb E\frac{|D(Cu)|}C
 \le C_\psi u\left[\frac4{\log^2u}
       +\frac{M_3(\alpha)u^{-3/2}}{(\log2)^2}\right].
$$

Multiplication by $k(u)$ is integrable. The same bound pays the
integration-by-parts boundary at infinity; the boundary at zero
vanishes by $|D(x)|\ll x$. No separate infinite-mass integral of the
pole term has been taken.

### A bound valid on both sides of the unit cutoff

For each $c>0$, define the absolutely convergent zero sum and its
arithmetic remainder

$$
Z_c(A)=\sum_\rho m_\rho c^{\rho-1}F_A(\rho),\qquad
r_c(A)=J_c(A)-Z_c(A).
$$

The existing (H5) and $\sum_\rho m_\rho/\gamma^2<\infty$ give

$$
|Z_c(A)|\le\sum_\rho m_\rho |c^{\rho-1}F_A(\rho)|
 \le\frac{C_0}L\max\{1,(cA)^{-1}\}.
\tag{GR6}
$$

If $cA\ge1$, applying the classical explicit formula to (GR5) gives

$$
r_c(A)=\frac{\log(2\pi)}{cA L}
 +\frac12\int_{cA}^\infty\log(1-x^{-2})
 \frac{1+\log(x/c)}{x^2\log^2(x/c)}\,dx.
\tag{GR7}
$$

Take finite scale endpoints first and use the existing finite-endpoint
bound (U2), then dominated convergence for the zero coefficients. The
prime-power half-value convention changes no integral.
At $cA=1$ the logarithmic singularity is integrable. For $1\le cA\le2$,
use

$$
\int_1^\infty\frac{-\log(1-x^{-2})}{x^2}\,dx
 =2-2\log2<1.
$$

For $cA\ge2$, use $-\log(1-x^{-2})\le4/(3x^2)$.
Since $\log(x/c)\ge L$, both ranges give

$$
\left|r_c(A)-\frac{\log(2\pi)}{cA L}\right|
 \le\frac{K_1}{(cA)^3L}\qquad(cA\ge1).
\tag{GR8}
$$

For $cA<1$, do not extend the explicit formula below one. There
$D(x)=-x$. Substitution $x=cu$ in (GR5) and direct integration over
$[cA,1]$ give, with $d=-\log(cA)>0$,

$$
\int_{cA}^1\frac{1+\log(x/c)}{x\log^2(x/c)}\,dx
 =\log(1+d/L)+\frac1L-\frac1{L+d}
 \le\frac{d+1}L\le\frac2{cA L}.
$$

On $x\ge1$, (GR3) bounds the remaining absolute integral by

$$
\frac{C_1}L\int_1^\infty\frac{dx}{x\log^2(2+x)}
 \le\frac{C_2}L.
$$

Together with (GR6), this yields
$|r_c(A)|\le C_3/(cA L)$. Because $(cA)^{-1}\le(cA)^{-3}$ in this
range, (GR8), with a larger absolute constant, holds for every $c>0$.
This pays the entire small-scale contribution, including $cA<1$.

Finally, $\mathbb E C^{\rho-1}=H_\alpha(\rho)$.
Equation (GR6) and $\mathbb E C^{-1}<\infty$ justify averaging the
complete zero series. Equations (GR4)–(GR5) therefore give
$\overline R_\alpha(A)=\mathbb E r_C(A)$. Average (GR8) and use the
exact inverse-third moment to obtain (GR1).

The result bounds the combined source remainder, not its individual
series. It adds no Gamma coefficient approximation or replacement for
the existing complete Gaussian transport. At the same conditional
least global Robin maximizer $N>5040$, $A=\log N>10^{36}$, the full
centered prime response and any signed comparison of
$H_\alpha(\rho)F_A(\rho)$ with the original $F_A(\rho)$ still require
control. All actual zeros, multiplicities, heights, original pole and
trivial terms, and the strict core remain present. The complete signed
Robin estimate and RH remain unproved.


## A directed prime-weight comparison for the complete Gamma response

The combined-remainder estimate (GR1) can be paired with a one-sided
arithmetic comparison. This `repo-derived` application uses the same
canonical measure (M2), nonnegative von Mangoldt weights, the standard
unconditional Chebyshev bound, and the Gamma law already used in
(GR4)–(GR5). It does not replace the original coefficient by a pointwise
approximation or claim mathematical originality or Lean verification.

Keep $A\ge e^2$, $L=\log A$ and noninteger $\alpha\ge4$. Let $C$ have
Gamma shape $\alpha$ and rate $\alpha$, and put

$$
h_A(t)=\frac1{\max(A,t)\log\max(A,t)},\qquad
w_c(t)=\frac1c h_A(t/c),\qquad
\Delta_\alpha(t)=\mathbb E w_C(t)-h_A(t).
$$

The resulting complete signed comparison is

$$
\boxed{
-I_\psi(A)\le J_\alpha(A)
 +\frac{\psi(A)}{(\alpha-1)A\log A}.}
\tag{GP1}
$$

Here $J_\alpha$ is the centered prime response in (GR4), not the
uncentered integral of its pole or prime terms. No source extremality
assumption is needed for (GP1); it therefore applies at the same
selected Robin integer without changing that integer.

### A global tangent majorant on the infinite prime tail

Fix $t\ge A$ and write $s=t/A\ge1$, $v=\log t$. As a function of the
dilation $c>0$, the transported prime weight is

$$
f_t(c)=w_c(t)=
\begin{cases}
 [t(v-\log c)]^{-1},&0<c\le s,\\
 (A L c)^{-1},&c\ge s.
\end{cases}
$$

On $0<c<s$,

$$
f_t''(c)=\frac{2-(v-\log c)}
 {t c^2(v-\log c)^3}\le0,
$$

because $v-\log c\ge L\ge2$. Thus its tangent at $c=1$ majorizes
the first branch:

$$
f_t(c)\le \frac1{tv}+\frac{c-1}{tv^2}\qquad(0<c\le s).
$$

The same affine function is increasing and majorizes $f_t(s)$. The
second branch decreases for $c\ge s$, so this is a global majorant,
even though $f_t$ is not globally concave. At $s=1$ use the left
tangent and the same argument. Since $\mathbb EC=1$, averaging gives

$$
\Delta_\alpha(t)\le0\qquad(t\ge A).
\tag{GP2}
$$

For $0<t<A$, $h_A(t)=1/(A L)$ and $h_A(t/c)\le1/(A L)$.
The existing inverse-first Gamma moment therefore gives

$$
\Delta_\alpha(t)\le
 \frac{\mathbb EC^{-1}-1}{A L}
 =\frac1{(\alpha-1)A L}.
\tag{GP3}
$$

### Centering and absolute convergence of the full prime difference

The pole and prime integrals are not subtracted as separate infinite
quantities. First fix $c>0$ and set $T=A\max(1,c)$. Reuse a fixed
unconditional bound $\psi(x)\le Bx$. Below $T$, the absolute
prime-weight difference is bounded by

$$
\sum_{n\le T}\Lambda(n)|w_c(n)-h_A(n)|
\le\frac{B}{L}(1+c^{-1})\max(1,c).
$$

For $n>T$ both weights use their logarithmic branch, and

$$
|w_c(n)-h_A(n)|
 =\frac{|\log c|}{n\log n\,\log(n/c)}
 \le\frac{|\log c|(1+|\log c|/L)}{n\log^2n}.
$$

Partial summation with the same Chebyshev bound gives
$\sum_{n>T}\Lambda(n)/(n\log^2n)\le2B/L$. Since
$|\log c|+(\log c)^2\ll c+c^{-1}$, these estimates yield an absolute
constant $B_1$ such that

$$
\sum_{n\ge2}\Lambda(n)|w_c(n)-h_A(n)|
 \le\frac{B_1}{L}(c+c^{-1}).
\tag{GP4}
$$

The analogous Lebesgue integral is also absolutely convergent.
Changing variables in finite integrals shows

$$
\int_0^\infty(w_c(t)-h_A(t))\,dt=0:
$$

for sufficiently large $R$, the difference of integrals up to $R$
is $\log\log(R/c)-\log\log R$, which tends to zero. Integration by
parts against $D(t)=\psi(t)-t$, using (GR3) at infinity and $D(t)=-t$
below one, therefore gives

$$
J_1(A)-J_c(A)
 =\sum_{n\ge2}\Lambda(n)[w_c(n)-h_A(n)],
\qquad J_1(A)=-I_\psi(A).
$$

The $J_c$ here is the deterministic dilation in (GR5); $J_1$ is its
value at dilation one, not a Gamma response with shape one. All
boundary terms vanish. Equation (GP4), $\mathbb EC=1$ and
$\mathbb EC^{-1}<\infty$ justify averaging and termwise summation.
Reusing (GR5) yields the absolutely convergent identity

$$
-I_\psi(A)-J_\alpha(A)
 =\sum_{n\ge2}\Lambda(n)\Delta_\alpha(n).
\tag{GP5}
$$

Apply (GP2) to the entire infinite tail, (GP3) to the finite lower
part, and $\Lambda(n)\ge0$ to prove (GP1). An atom at $n=A$ has the
nonpositive sign in (GP2); using $\psi(A)$ in the upper allowance
remains valid.

### Pay the remainder and retain the original signed target

Define the complete real zero response

$$
Z_\alpha(A)=\sum_\rho m_\rho H_\alpha(\rho)F_A(\rho),
\qquad
H_\alpha(s)=\frac{\Gamma(\alpha+s-1)}
 {\Gamma(\alpha)\alpha^{s-1}}.
$$

Its absolute convergence and reality under conjugate pairing follow
from the existing fixed-shape argument in (GR4). No zero real part,
multiplicity or height is changed. Since
$J_\alpha=Z_\alpha+\overline R_\alpha$, (GR1) and (GP1) give

$$
\boxed{\begin{aligned}
\sqrt A L[-I_\psi(A)]\le{}&\sqrt A L Z_\alpha(A)
 +\frac{\psi(A)}{(\alpha-1)\sqrt A}\\
&+\frac{\log(2\pi)}{\sqrt A}\frac\alpha{\alpha-1}
 +\frac{K M_3(\alpha)}{A^{5/2}}.
\end{aligned}}
\tag{GP6}
$$

This is a directed bound for the original full response, with a paid
finite prime budget and the complete combined remainder. It is not an
absolute coefficient approximation, a bound on the sum of coefficient
moduli, or a deletion of the original explicit-formula terms.

For shapes with $\alpha(A)/\sqrt A\to\infty$, the added allowance in
(GP6) tends to zero by the existing PNT bound. This gives a sufficient
transfer from a full signed Gamma-response upper estimate to (G9),
provided the estimate has enough slack to pay the displayed allowance.
The signed upper estimate on $Z_\alpha(A)$ is not established here.
At the same conditional least global Robin maximizer $N>5040$,
$A=\log N>10^{36}$, the original strict core, complete infinite
response and target remain unchanged. Neither (G9) nor RH is proved.


## An explicit one-sided bound for the combined Gamma remainder

For finite source clocks, the absolute constant in (GR1) need not be
assigned an unproved numerical value. The following upper bound instead
uses the existing finite-height verification and zero-count constants in
[(F3) of the Polak application](../Analytic/polak2026finiterobinca.md#reusing-the-complete-residual-envelope),
together with (U2), (GR5) and (GR7). These inputs are reused without a new
zero computation or reconstruction of their source proofs.

Put $H=3\cdot10^{12}$, and let every zero sum retain the full actual
nontrivial-zero multiset, with multiplicities. Write

$$
c_0=2+\gamma-\log(4\pi)<0.05,\qquad
S_2(H)=\sum_{\Im\rho>H}\frac{m_\rho}{(\Im\rho)^2}
 <1.48\cdot10^{-12}.
$$

The same sources supply criticality up to $H$ and the classical identity
$\sum_\rho m_\rho/[\rho(1-\rho)]=c_0$.
For $\rho=\beta+i\gamma$ in the critical strip,

$$
\Re\frac1{\rho(1-\rho)}
=\frac{\gamma^2+\beta(1-\beta)}{|\rho(1-\rho)|^2}>0.
$$

On the verified head the denominator is the positive real number
$\gamma^2+1/4$. On the remaining zeros,
$|\rho||1-\rho|\ge\gamma^2$.
Consequently the complete absolute weight obeys

$$
\mathcal C_\zeta:=\sum_\rho
 \frac{m_\rho}{|\rho||1-\rho|}
\le c_0+2S_2(H)<0.051.
\tag{GE1}
$$

The factor two accounts for the two ordinate signs, not an additional
independently chosen zero population.

Keep $A\ge e^2$ and $L=\log A$. For the same deterministic dilation
$r_c(A)=J_c(A)-Z_c(A)$ in (GR5)–(GR7), one has the uniform upper bound

$$
\boxed{r_c(A)<\frac5{cAL}\qquad(c>0).}
\tag{GE2}
$$

If $cA\ge1$, (GR7) immediately gives
$r_c(A)\le\log(2\pi)/(cAL)<2/(cAL)$, since its logarithmic integral
is nonpositive. This includes the integrable endpoint $cA=1$.

If $cA<1$, put $B=1/c>A$ and $d=\log(B/A)>0$.
Since $\psi(cu)-cu=-cu$ on $A<u<B$, (GR5) gives exactly

$$
r_c(A)=\log(1+d/L)+\frac1L-\frac1{L+d}
 +r_c(B)-\sum_\rho m_\rho c^{\rho-1}F_{A,B}(\rho).
\tag{GE3}
$$

The initial elementary term is at most $2/(cAL)$, as already computed
in the proof of (GR8). At $cB=1$, (GR7) gives
$r_c(B)<2/\log B\le2/(cAL)$.
The finite-endpoint bound (U2), (GE1) and
$(cA)^{\beta-1}\le(cA)^{-1}$ give

$$
\left|\sum_\rho m_\rho c^{\rho-1}F_{A,B}(\rho)\right|
\le\frac{2(1+1/L)\mathcal C_\zeta}{cAL}
\le\frac{3\mathcal C_\zeta}{cAL}<\frac{0.153}{cAL}.
$$

Thus (GE2) also holds below the unit cutoff. In particular, no classical
explicit formula has been extended to $cu<1$ and no small Gamma scales
have been discarded.

For the same noninteger shapes $\alpha\ge4$ as in (GR1), averaging (GE2)
by (GR5) and the existing inverse-first Gamma moment yields

$$
\overline R_\alpha(A)
\le\frac{5M_1(\alpha)}{AL},\qquad
M_1(\alpha)=\frac\alpha{\alpha-1}.
\tag{GE4}
$$

This is an explicit upper bound, not an absolute bound or a replacement
for the sharper asymptotic assertion (GR1). With the original full
prime-integral comparison (GP1), it gives the finite inequality

$$
\boxed{\sqrt A L[-I_\psi(A)]
\le\sqrt A L Z_\alpha(A)
 +\frac{\psi(A)}{(\alpha-1)\sqrt A}
 +\frac{5M_1(\alpha)}{\sqrt A}.}
\tag{GE5}
$$

The full elementary and trivial contributions are paid through
$\overline R_\alpha$; the left side is the original complete integral.
No signed main estimate or unbounded source-clock conclusion follows
from (GE5) alone.


## A larger finite clock from the verified-height Gamma response

The explicit directed inequality (GE5) can be paired with a uniform
Gamma modulus estimate. It bounds the original signed integral on a
larger finite interval, while keeping the same conditional least integer
$N>5040$ attaining the global Robin-ratio maximum. This is not a reduction
to the least counterexample or an all-integer finite Robin verification.
No arithmetic profiles or zero ordinates are newly enumerated.

### Uniform damping with the actual real parts retained

Use the classical product
[NIST DLMF 5.8.3](https://dlmf.nist.gov/5.8.E3), for $x>0$:

$$
\left|\frac{\Gamma(x+it)}{\Gamma(x)}\right|
=\prod_{k=0}^\infty
 \left(1+\frac{t^2}{(x+k)^2}\right)^{-1/2}.
$$

The summand $\log(1+t^2/(x+u)^2)$ is positive and decreasing in $u$.
Using $\log(1+v)\ge v/(1+v)$ in its integral gives

$$
\sum_{k=0}^\infty\log\left(1+\frac{t^2}{(x+k)^2}\right)
\ge |t|\arctan(|t|/x)
\ge\frac{t^2}{x+|t|}.
$$

The last inequality uses $\arctan v\ge v/(1+v)$ for $v\ge0$.
For $0<\beta<1$, the already used Gamma law has
$\mathbb E C^{\beta-1}\le(\mathbb EC^{-1})^{1-\beta}\le M_1(\alpha)$
by Hölder. Set $x=\alpha+\beta-1\le\alpha$ in the product. It follows that

$$
\boxed{|H_\alpha(\beta+it)|
\le M_1(\alpha)
 \exp\left(-\frac{t^2}{2(\alpha+|t|)}\right).}
\tag{GH1}
$$

This is uniform over the whole actual critical strip. Criticality is
used only on the already verified head below $H$.

Passing to the infinite endpoint in the existing (U2) gives

$$
\sqrt A L|F_A(\rho)|
\le2(1+1/L)\frac{A^{\beta-1/2}}{|\rho||1-\rho|}.
\tag{GH2}
$$

The function $t^2/[2(\alpha+t)]$ increases for $t>0$.
Split the complete $Z_\alpha$ at the verified height $H$.
Use the positive $c_0$ identity on the critical head, and (GH1), (GH2),
$\beta<1$, and $2S_2(H)$ on every remaining zero. This gives

$$
\sqrt A L|Z_\alpha(A)|
\le2M_1(\alpha)(1+1/L)
 \left[c_0+2\sqrt A\,S_2(H)
   \exp\left(-\frac{H^2}{2(\alpha+H)}\right)\right].
\tag{GH3}
$$

Every height beyond $H$ is included to infinity. Replacing the actual
$A^{\beta-1/2}$ by $\sqrt A$ in this upper bound does not assume RH
outside the verified head.

### Pay the constants at the same selected source

Take the exact noninteger shape and clock range

$$
\alpha=10^{23}+\frac12,\qquad
10^{36}<A\le10^{45},\qquad L=\log A.
$$

Then $L>78$, $\sqrt A<3.2\cdot10^{22}$,
$M_1(\alpha)<1.0001$, and

$$
\frac{H^2}{2(\alpha+H)}>40,\qquad e^{40}>10^{17}.
$$

The latter follows from $e>8/3$ and
$8^{40}>10^{17}3^{40}$.
The two contributions in (GH3) are bounded by the rational inequalities

$$
2(1.0001)(1.02)(0.05)<0.103,
$$

$$
4(1.0001)(1.02)(3.2\cdot10^{22})
 (1.48\cdot10^{-12})10^{-17}<0.000003.
\tag{GH4}
$$

For the prime-comparison allowance, reuse Dusart's
[Theorem 5.2, $k=0$, and Proposition 3.2](../Weil/dusart2010estimates.md):
$\vartheta(A)<2A$ and
$\psi(A)-\vartheta(A)<1.00007\sqrt A+1.78A^{1/3}$.
On this range they give $\psi(A)<2.01A$. Therefore

$$
\frac{\psi(A)}{(\alpha-1)\sqrt A}
<\frac{2.01(3.2\cdot10^{22})}{0.9999\cdot10^{23}}<0.644,
\qquad
\frac{5M_1(\alpha)}{\sqrt A}<6\cdot10^{-18}.
\tag{GH5}
$$

Combining (GE5) and (GH3)–(GH5) pays the full original signed integral:

$$
\boxed{-\sqrt A L I_\psi(A)
<0.103+0.000003+0.644+6\cdot10^{-18}<\frac34
\qquad(10^{36}<A\le10^{45}).}
\tag{GH6}
$$

The same selected source still satisfies
$\Delta(N)=I_\psi(A)+D^*(A)$ and the strict core (G6).
The already proved bound
[(X5) in the Polak application](../Analytic/polak2026finiterobinca.md#pay-the-full-signed-margin-with-the-same-strict-core)
gives $\mathcal E(L)>0.778$ for every $L\ge78$.
Thus at this actual source and clock,

$$
\boxed{\sqrt A L\Delta(N)>0.778-0.75=0.028
\qquad(10^{36}<A\le10^{45}).}
\tag{GH7}
$$

The existing restriction $A>10^{36}$ and (GH7) therefore force
$\log N>10^{45}$ for the same hypothetical least global maximizer.
This conclusion is specific to that selected source; it does not assert
strict Robin for every integer below $\exp(10^{45})$.

This application reuses the published finite-height verification,
zero-count and prime estimates, the classical Gamma product, and the
existing core and directed-transport results. It makes no mathematical
priority claim and has no Lean certification. The fixed shape and verified
height give no uniform bound as $A\to\infty$: the comparison and high-zero
allowances in (GE5), (GH3) still grow with $\sqrt A$.
The full unbounded signed Robin target and RH remain unproved.


## A one-sided entire envelope retaining the original cutoff

The original prime weight has a derivative jump at its cutoff. A signed
mixture of published power-function extremals gives entire lower and
upper envelopes with an exact error while retaining that cutoff. Use
the power-function corollary in Carneiro, Littmann and Vaaler,
[arXiv:1008.4969v2](https://arxiv.org/abs/1008.4969v2), Part III,
“Extremal Functions for $|x|^\sigma$”, can instead be applied before
mixing the actual second-derivative measure. This is a paper-level
application of that published corollary and elementary signed-measure
integration, with no mathematical priority or Lean-verification claim.

Retain $A\ge e^2$, $L=\log A$, and the original weight and derivative

$$
H_A(x)=\frac1{\max(A,|x|)\log\max(A,|x|)},\qquad
k(t)=\frac{1+\log t}{t^2\log^2t},\qquad
\kappa_A=k(A).
$$

The distributional second derivative is the signed measure

$$
\mu_A=\mu_A^+-\mu_A^-,\qquad
\mu_A^+(du)=-k'(|u|)\mathbf1_{\{|u|>A\}}\,du,
\qquad
\mu_A^-=\kappa_A(\delta_{-A}+\delta_A).
\tag{CE1}
$$

Here $k'<0$. Both parts have mass $2\kappa_A$, and
$\int(1+|u|)\,d|\mu_A|(u)<\infty$. The negative cutoff atoms have
not been dropped. Direct integration gives the absolutely convergent
potential representation

$$
\boxed{H_A(x)=\frac12\int_{\mathbb R}|x-u|\,d\mu_A(u).}
\tag{CE2}
$$

For example, differentiation off $\pm A$ gives the original derivative;
the value at zero is
$-A\kappa_A+\int_A^\infty u[-k'(u)]\,du=1/(AL)$.
These facts and continuity identify the potential with $H_A$.

Use the source corollary at $\sigma=1$, where its normalization is
$\gamma(-1)=-2\pi$ and $\gamma(2)=1/\pi$. Reversing the inequalities
when dividing by $-2\pi$, and then rescaling, provides even real entire
functions $P_\delta,Q_\delta$ of exponential type at most $2\pi\delta$
for every $\delta>0$, satisfying

$$
P_\delta(x)\le |x|\le Q_\delta(x),\qquad
\int_{\mathbb R}(|x|-P_\delta(x))\,dx=\frac1{6\delta^2},\qquad
\int_{\mathbb R}(Q_\delta(x)-|x|)\,dx=\frac1{12\delta^2}.
\tag{CE3}
$$

This reuses the source result rather than reconstructing its proof.
The two nonnegative errors sum to the integrable entire function
$Q_\delta-P_\delta$. The standard real-line bound for an integrable
entire function of finite exponential type makes that difference
bounded; hence both power extremals are $O_\delta(1+|x|)$ on the real
line. The usual polynomial-growth version of the Paley–Wiener bound
then gives $O_{K,\delta}(1+|u|)$ for their translates $z-u$, uniformly
for $z$ in a fixed compact subset $K$ of the complex plane. This bound
and the first moment in (CE1) justify locally uniform integration below,
including differentiation on compact subsets.

Define

$$
\begin{aligned}
\ell_{A,\delta}(z)
 &=\frac12\left[\int P_\delta(z-u)\,d\mu_A^+(u)
                  -\int Q_\delta(z-u)\,d\mu_A^-(u)\right],\\
u_{A,\delta}(z)
 &=\frac12\left[\int Q_\delta(z-u)\,d\mu_A^+(u)
                  -\int P_\delta(z-u)\,d\mu_A^-(u)\right].
\end{aligned}
\tag{CE4}
$$

They are even real entire functions of exponential type at most
$2\pi\delta$, and the signs in (CE4) give

$$
\boxed{\ell_{A,\delta}(x)\le H_A(x)\le u_{A,\delta}(x)
\qquad(x\in\mathbb R).}
\tag{CE5}
$$

Tonelli applies to the nonnegative differences from (CE2). Using the
actual two masses in (CE1), rather than treating the signed measure as
positive, gives the exact errors

$$
\int_{\mathbb R}(H_A-\ell_{A,\delta})\,dx
=\int_{\mathbb R}(u_{A,\delta}-H_A)\,dx
=\frac{\kappa_A}{4\delta^2}.
\tag{CE6}
$$

Evenness therefore yields

$$
\boxed{\int_0^\infty(H_A-\ell_{A,\delta})\,dt
       =\frac{\kappa_A}{8\delta^2}.}
\tag{CE7}
$$

These are explicit envelopes for the unchanged cutoff weight. They do
not assert extremality for $H_A$, arithmetic sampling convergence, a
compact zero-height cutoff, or a sign estimate on the original complete
zero response. Fourier support on the additive real variable is not
spectral truncation at the actual complex zeta zeros.

### A finite centered prime comparison

The lower envelope (CE5) gives a finite arithmetic consumer without
assuming that an unweighted $L^1$ error controls an infinite
von-Mangoldt weighted sum. Keep $R\ge A\ge e^2$, $V=\log R$,
$D(t)=\psi(t)-t$, and the existing unconditional constant $C_\psi$ in
(GR3). Define the finite centered response

$$
\mathcal J_{A,\delta}(R)
=\int_0^R\ell_{A,\delta}(t)\,dt
 -\sum_{2\le n\le R}\Lambda(n)\ell_{A,\delta}(n).
\tag{CP1}
$$

Both terms are finite. No separately divergent pole or prime integral
has been taken. Set $e=H_A-\ell_{A,\delta}\ge0$. For this same $R$,
nonnegative von Mangoldt weights and (CE7) give

$$
\begin{aligned}
\int_0^R H_A(t)\,dt-\sum_{2\le n\le R}\Lambda(n)H_A(n)
&=\mathcal J_{A,\delta}(R)+\int_0^R e(t)\,dt
                -\sum_{2\le n\le R}\Lambda(n)e(n)\\
&\le\mathcal J_{A,\delta}(R)+\frac{\kappa_A}{8\delta^2}.
\end{aligned}
\tag{CP2}
$$

An atom at $n=A$ satisfies the same pointwise order. No zero real part,
multiplicity, or height is altered in the original response.

Partial summation, with the right endpoint included in $\psi(R)$,
keeps the full original integral:

$$
-I_\psi(A)
=\left[\int_0^R H_A(t)\,dt
       -\sum_{2\le n\le R}\Lambda(n)H_A(n)\right]
 +D(R)H_A(R)-\int_R^\infty D(t)k(t)\,dt.
\tag{CP3}
$$

The existing (GR3) implies $|D(t)|\le C_\psi t/\log^2t$ for $t>1$.
Its boundary allowance is $C_\psi/V^3$, and direct integration pays
all of the remaining tail by

$$
\int_R^\infty |D(t)|k(t)\,dt
\le C_\psi\left(\frac1{2V^2}+\frac1{3V^3}\right).
$$

Consequently the finite directed upper bound is

$$
\boxed{\begin{aligned}
-\sqrt A L I_\psi(A)\le{}&\sqrt A L\mathcal J_{A,\delta}(R)
 +\frac{1+L}{8A^{3/2}L\delta^2}\\
&+C_\psi\sqrt A L
   \left(\frac1{2V^2}+\frac4{3V^3}\right).
\end{aligned}}
\tag{CP4}
$$

This pays the approximation and the entire omitted arithmetic tail for
any displayed parameters. It neither requires nor proves convergence
of an infinite prime sample of the envelope error. For instance,
$\delta=1$ and $R=\exp(A^{1/4}\log A)$ make both displayed added
allowances tend to zero as $A\to\infty$; this is asymptotic, since
$C_\psi$ has not been numerically certified. It gives no starting clock
and no claim that evaluating this finite prime sum is inexpensive.

At the unchanged conditional least global Robin-ratio maximizing
integer, a sufficiently strong upper estimate on the actual
$\mathcal J_{A,\delta}(R)$ would still be needed to pay the strict
core after (CP4). No such main estimate is supplied. The original
$F_A$, actual zero multiset, complete elementary contributions and
unbounded Robin/RH goal remain unchanged; no compact spectral
truncation or RH inference follows from additive exponential type.
This is a paper-level comparison, not a Lean-verified result.

## Joint short-interval cancellation in the Gamma comparison

The allowance in (GP6) discards the cancellation between the two sides
of the original cutoff. The uniform short-interval input already
recorded in the [Guth–Maynard note](../Analytic/guthmaynard2024largevalues.md),
Corollary 1.3 of [arXiv:2405.20552v2](https://arxiv.org/abs/2405.20552v2),
supplies a two-sided comparison with a smaller admissible Gamma shape.
The global PNT input is the Fiori–Jaskari theorem quoted above. These
source theorems, the absolute centering in (GP4)–(GP5), and the full
combined remainder (GR1) are reused. The following is a paper-level
application, without mathematical-priority or Lean-verification claims.

Retain $A\to\infty$, $L=\log A$, $D(t)=\psi(t)-t$, $h_A,w_c,J_\alpha$
and the Gamma law from (GP1)–(GP5). Define

$$
\begin{aligned}
\eta_0(A)&=\sup_{t\ge A}\frac{|D(t)|}{t},\\
\eta_{\rm si}(A)&=
\sup_{\substack{A/2\le u<v\le3A/2\\v-u\ge A^{2/3}}}
\frac{|D(v)-D(u)|}{v-u}.
\end{aligned}
\tag{GS1}
$$

There are absolute constants $K,c>0$ such that, for all sufficiently
large $A$ and every noninteger $\alpha\ge4$,

$$
\boxed{\begin{aligned}
\sqrt A L|J_1(A)-J_\alpha(A)|\le K\bigg\{&
\frac{\sqrt A}{\alpha}
 [\eta_0(A)+\eta_{\rm si}(A)+A^{-1/30}]\\
&+\sqrt{A\alpha}\,A^{-9/10}
 +\sqrt A e^{-c\alpha}\bigg\}.
\end{aligned}}
\tag{GS2}
$$

The starting value and constants are not numerically certified. This
is an asymptotic comparison, not an additional finite Robin clock.

### The local prime input and its uniform range

The retained global PNT theorem gives, for some fixed $c_0>0$,

$$
\eta_0(A)\ll
\exp\left[-c_0\frac{L^{3/5}}{(\log L)^{1/5}}\right].
\tag{GS3}
$$

Use Guth–Maynard Corollary 1.3 with the fixed parameter $\epsilon=1/20$.
For $u\in[A/2,3A/2]$ and $A^{2/3}\le h\le A^{9/10}$, its required
range $u^{37/60}\le h\le u^{0.99}$ holds uniformly for sufficiently
large $A$. Multiplying the prime count by $\log u$ introduces an error
$O(h^2/(A L))$ from the variation of $\log p$. Thus

$$
\vartheta(u+h)-\vartheta(u)
=h+O\bigl(h[L e^{-L^{1/4}}+A^{-1/10}]\bigr).
$$

Here $(\log u)^{1/4}=L^{1/4}+O(L^{-3/4})$ uniformly. If
$A^{9/10}<h\le A$, with $u+h\le3A/2$, partition into equal pieces of lengths between
$A^{9/10}/2$ and $A^{9/10}$ and add the same estimates. The classical
Chebyshev bound and prime-power identity give
$\psi(t)-\vartheta(t)=O(\sqrt t)$; paying this at the two endpoints,
with $h\ge A^{2/3}$, proves

$$
\boxed{\eta_{\rm si}(A)\ll
 L e^{-L^{1/4}}+A^{-1/10}+A^{-1/6}.}
\tag{GS4}
$$

This uses the uniform corollary, not the separate almost-all theorem.
It neither assumes a short-interval relative error from global PNT
nor substitutes $\pi$ or $\vartheta$ for $\psi$ without paying prime
powers.

### Remove only the exactly centered linear dilation

Choose the following endpoint convention and retain it in the prime
sum:

$$
a_A(t)=
\begin{cases}
-1/(AL),&0<t\le A,\\
1/(t\log^2t),&t>A.
\end{cases}
\qquad
B_c(t)=w_c(t)-h_A(t)-(c-1)a_A(t).
\tag{GS5}
$$

Both $a_A$ and $w_c-h_A$ are absolutely integrable against $dt$ and
$d\psi(t)$; for the latter use (GP4). Moreover
$\int_0^\infty a_A(t)\,dt=-1/L+1/L=0$ and
$\int_0^\infty(w_c-h_A)\,dt=0$. The absolute $d\psi+dt$ norm of
$a_A$ is $O(1/L)$ by Chebyshev and partial summation. Consequently
(GP5), Fubini, and $\mathbb E(C-1)=0$ give the unchanged arithmetic
difference

$$
\boxed{J_1-J_\alpha
 =\mathbb E\int_0^\infty B_C(t)\,dD(t).}
\tag{GS6}
$$

No divergent pole and prime quantities are separated in this identity.

For $1/2\le c\le3/2$, put $e=c-1$ and split $B_c=b_c+v_c$, where

$$
b_c(t)=
\begin{cases}
e^2/(cAL),&0<t\le A,\\[2pt]
\displaystyle\frac1{t(\log t-\log c)}-
 \frac1{t\log t}-\frac e{t\log^2t},&t>A.
\end{cases}
\tag{GS7}
$$

This regular part agrees with $B_c$ outside the interval between $A$
and $cA$. Taylor's theorem in $c$, uniformly on $[1/2,3/2]$, gives

$$
|b_c(t)|\ll\frac{e^2}{t\log^2t},\qquad
|b_c'(t)|\ll\frac{e^2}{t^2\log^2t}\qquad(t>A).
$$

Partial summation on $(A,\infty)$, together with the constant part on
$(0,A]$, therefore yields

$$
\left|\int_0^\infty b_c(t)\,dD(t)\right|
\ll\eta_0(A)e^2/L.
\tag{GS8}
$$

In particular, the boundary contribution is paid using $D(A)$; the
change of formula at $A$ has not been ignored.

The local residual $v_c$ is zero outside the closed interval with
endpoints $A,cA$. Inside that interval its nonzero formula is

$$
\begin{cases}
\displaystyle\frac1{cAL}-\frac1{t\log(t/c)},&c>1,\ A<t<cA,\\[4pt]
\displaystyle\frac1{t\log(t/c)}-\frac1{cAL},&c<1,\ cA<t<A.
\end{cases}
$$

The actual endpoint values are those of $B_c-b_c$ in (GS5)–(GS7).
The first derivative of $1/[t\log(t/c)]$ is $O(1/(A^2L))$ in this
interval. Including the possible jump at $A$ gives

$$
\|v_c\|_\infty+\operatorname{Var}(v_c)
\ll |e|/(AL).
\tag{GS9}
$$

### Pay the shrinking cutoff interval, including its atoms

Set $H_0=A^{2/3}$, $H_1=A^{7/10}$ and $h=A|e|$. For
$h\ge H_1$, (GS1) bounds $|D(t)-D(A)|$ by
$\eta_{\rm si}(A)h$ whenever $|t-A|\ge H_0$. For smaller distances,
monotonicity of $\psi$ and (GS4) applied to
$[A-H_0,A+H_0]$ give the bound $O(H_0)$. Since
$H_0/H_1=A^{-1/30}$, it follows uniformly on the support of $v_c$ that

$$
|D(t)-D(A)|\ll
[\eta_{\rm si}(A)+A^{-1/30}]h.
$$

The same bound holds for one-sided limits after paying a possible
endpoint prime-power atom of size at most $\log(2A)=O(\log A)$,
absorbed in $H_0$. Integration of a bounded-variation function against
these increments, using (GS9), gives

$$
\left|\int v_c(t)\,dD(t)\right|
\ll [\eta_{\rm si}(A)+A^{-1/30}]e^2/L
\qquad(H_1\le h\le A/2).
\tag{GS10}
$$

For $h<H_1$, the support lies in $[A-H_1,A+H_1]$. Its total
$d\psi+dt$ mass is $O(H_1)$ by (GS4), with the endpoint atom included.
Therefore
$|\int v_c\,dD|\ll |e|H_1/(AL)$. The maximum of the Gamma density
is $O(\sqrt\alpha)$ uniformly for $\alpha\ge4$, by the standard
Stirling bound at its mode. Hence

$$
\begin{aligned}
\mathbb E[|C-1|\mathbf1_{\{|C-1|<H_1/A\}}]
 &\ll\sqrt\alpha(H_1/A)^2,\\
\sqrt A L\,
\mathbb E\left[\left|\int v_C\,dD\right|
                  \mathbf1_{\{|C-1|<H_1/A\}}\right]
 &\ll\sqrt{A\alpha}\,A^{-9/10}.
\end{aligned}
\tag{GS11}
$$

For the remaining event $C\notin[1/2,3/2]$, (GP4) and the absolute
norm of $a_A$ give
$|\int B_c\,dD|\ll(1+c+c^{-1})/L$ for every $c>0$.
The Gamma moment-generating function and Chernoff's inequality give
$\Pr(C\notin[1/2,3/2])\le2e^{-c_1\alpha}$ for an absolute
$c_1>0$. The second moment of $1+C+C^{-1}$ is bounded uniformly for
$\alpha\ge4$, using
$\mathbb EC^2=1+1/\alpha$ and
$\mathbb EC^{-2}=\alpha^2/[(\alpha-1)(\alpha-2)]$.
Cauchy–Schwarz thus pays the entire event by
$O(\sqrt A e^{-c_1\alpha/2})$ after normalization. In particular no
scales with $cA<1$ have been discarded.

Finally average (GS8) and (GS10), use
$\mathbb E(C-1)^2=1/\alpha$, and add (GS11) and this Gamma tail.
This proves (GS2) uniformly over its stated shapes.

### A smaller shape family with vanishing full comparison error

Fix $0<b_-\le b_+<\infty$, and take any noninteger shape satisfying

$$
b_-a_*(A)\le\alpha\le b_+a_*(A),
\qquad a_*(A)=\sqrt A\,e^{-L^{1/4}/2}.
\tag{GS12}
$$

For $b_-=1/2$ and $b_+=2$, for example,
$\alpha=\lfloor a_*(A)\rfloor+1/2$ is lawful eventually.
The first term of (GS2), using (GS3)–(GS4), is
$O_{b_-,b_+}(L e^{-L^{1/4}/2})$. The small-interval term is
$O_{b_-,b_+}(A^{-3/20}e^{-L^{1/4}/4})$, and the Gamma tail is smaller.
Reusing the complete elementary remainder in (GR1) gives

$$
\boxed{-\sqrt A L I_\psi(A)
 =\sqrt A L Z_\alpha(A)
  +O_{b_-,b_+}(L e^{-L^{1/4}/2}) .}
\tag{GS13}
$$

Every zero in $Z_\alpha$ still has its actual real part,
multiplicity and height, and the coefficient remains
$H_\alpha(\rho)F_A(\rho)$. No main spectral response has been bounded.
In (GS12) the old allowance $\sqrt A/\alpha$ diverges, whereas the
joint arithmetic comparison tends to zero. This is the gained
transport regime; it supplies neither a sign nor a finite numerical
threshold for the remaining main response.

At the same conditional least integer $N>5040$ attaining the global
Robin-ratio maximum, this estimate uses $A=\log N$ without changing
the selected source, the strict core, or the existing conclusion
$A>10^{45}$. The asymptotic starting point in (GS2) has not been
numerically compared with this finite exclusion. A full signed upper
bound for $Z_\alpha(A)$ with enough strict slack remains required.
Robin's criterion and RH remain
unproved by these applications.

## Reusing the coefficient remainder on a larger finite clock

Keep the same conditional least integer $N>5040$ attaining the global
Robin-ratio maximum under the Robin-violation hypothesis. The preceding
finite-clock application already gives $A=\log N>10^{45}$; put
$L=\log A$. The following application uses the existing coefficient
remainder (H1), directed comparison (GE5), Gamma damping (GH1), verified
height and complete zero-count bound. It does not construct a new
smoothing transform or repeat their proofs.

### Use the full coefficient remainder separately on the two height ranges

The existing (H1) and its numerator estimate give, throughout the actual
critical strip $0<\beta<1$,

$$
\sqrt A L|F_A(\beta+it)|
\le(1+1/L)\frac{A^{\beta-1/2}}{|\beta+it||1-\beta-it|}
\left(1+\frac{2(L+2)}{L(L+1)|1-\beta-it|}\right).
\tag{GJ1}
$$

This retains the complete original coefficient, including its remainder;
it sharpens the coarser factor two in (GH2) by direct use of the already
available estimate. No zero coefficient is replaced by only its leading
term. For $L>78$, the verified critical head has
$|1-\rho|\ge1/2$, so its parenthesized factor is less than $1.054$:

$$
\frac{4(L+2)}{L(L+1)}
<\frac{4\cdot80}{78\cdot79}<0.054.
$$

For the actual unverified tail $|t|>H=3\cdot10^{12}$,
$|1-\rho|\ge|t|>H$ instead bounds that factor by $1.0001$.
Criticality is used only on the verified head. The original real parts
and the complete infinite multiset of tail zeros are retained.

Using the same positive $c_0$ identity, both ordinate signs and (GH1),
(GJ1) gives the finite bound

$$
\sqrt A L|Z_\alpha(A)|
<M_1(\alpha)(1+1/L)
\left[1.054c_0+2(1.0001)\sqrt A S_2(H)
 \exp\left(-\frac{H^2}{2(\alpha+H)}\right)\right].
\tag{GJ2}
$$

Here $M_1(\alpha)=\alpha/(\alpha-1)$, $c_0<0.05$ and
$S_2(H)<1.48\cdot10^{-12}$ are the same previously paid quantities.
In particular, this argument does not need a new verified height or a
new zero enumeration.

### Pay the complete response on the added interval

Take the exact noninteger shape and additional interval

$$
\alpha=\frac{29}{20}10^{23}+\frac12,
\qquad 10^{45}<A\le10^{46}.
$$

Then $L>78$, $\sqrt A\le10^{23}$,
$M_1(\alpha)<1.0001$, and

$$
\frac{H^2}{2(\alpha+H)}>31,
\qquad e^{31}>10^{13}.
$$

For the exponential inequality, $e>8/3$ and
$8^{31}>10^{13}3^{31}$ suffice. The head and complete tail in (GJ2)
therefore obey the exact rational budgets

$$
(1.0001)(1.02)(1.054)(0.05)<0.054,
$$

$$
2(1.0001)^2(1.02)(10^{23})
 (1.48\cdot10^{-12})10^{-13}<0.031.
\tag{GJ3}
$$

For the arithmetic comparison term, reuse
[Dusart's Theorem 5.2 and Proposition 3.2](../Weil/dusart2010estimates.md).
The original v1 theorem's $k=2$, $\eta_2=3.965$, $x_2=2$ row and the
complete prime-power correction give

$$
\frac{\psi(A)}A
<1+\frac{3.965}{L^2}+1.00007A^{-1/2}+1.78A^{-2/3}
<1.001.
$$

The final inequality follows from $3.965/78^2<0.0007$ and
$1.00007\cdot10^{-22}+1.78\cdot10^{-30}<0.0003$.
The source row applies throughout the added interval; no asymptotic
starting threshold is substituted for its explicit $x_2=2$.
Since $\alpha-1>1.4499\cdot10^{23}$, the two remaining terms of (GE5)
satisfy

$$
\frac{\psi(A)}{(\alpha-1)\sqrt A}
<\frac{1.001}{1.4499}<0.691,
\qquad
\frac{5M_1(\alpha)}{\sqrt A}<6\cdot10^{-22}.
\tag{GJ4}
$$

Combining (GE5) with (GJ2)–(GJ4) pays the original full signed response:

$$
\boxed{-\sqrt A L I_\psi(A)
<0.054+0.031+0.691+6\cdot10^{-22}<0.777,
\qquad 10^{45}<A\le10^{46}.}
\tag{GJ5}
$$

All elementary and trivial contributions, including Gamma scales below
the unit cutoff, are retained through the already proved (GE5).
The strict core for this same selected source still gives
$\sqrt A L D^*(A)>\mathcal E(L)>0.778$. Hence

$$
\boxed{\sqrt A L\Delta(N)>0.001,
\qquad 10^{45}<A\le10^{46}.}
\tag{GJ6}
$$

Together with the preceding $A>10^{45}$ restriction, this forces
$\log N>10^{46}$ for the same hypothetical least global maximizer.
It is a paper-level enlargement of the excluded selected-source window,
with no new classical theorem, priority claim, Lean certification or
all-integer finite Robin verification. The fixed verified height and
shape still provide no uniform main bound as $A\to\infty$; the complete
unbounded signed Robin target and RH remain unproved.

## An effective directed Gamma comparison retaining the cutoff sign

Retain the original $h_A,w_c,J_1,J_\alpha,D=\psi-\mathrm{id}$ and
the endpoint convention in (GS5). Reuse the absolutely convergent
centering (GP4)–(GP5), (GS6), and the decomposition (GS7)–(GS9).
The following explicit upper comparison preserves the sign of the local
residual against the actual nonnegative prime-power measure. No new
short-interval theorem or smoothing transform is required.

For $A\ge e^{78}$, $L=\log A$, and every noninteger $\alpha\ge4$, put
$\eta_0(A)=\sup_{t\ge A}|\psi(t)-t|/t$ as in (GS1). Then

$$
\boxed{\sqrt A L[J_1(A)-J_\alpha(A)]
\le [0.52+2\eta_0(A)]\frac{\sqrt A}{\alpha}
 +400\sqrt A\,e^{-\alpha/60000}.}
\tag{GK1}
$$

This is a directed inequality. The absolute asymptotic comparison
(GS2) retains its stated scope; (GK1) supplies explicit constants without
assigning a numerical starting point to that asymptotic result.

### Pay the regular part using only the global error

Fix $99/100\le c\le101/100$ and write $e=c-1$. For $t>A$, put
$v=\log t$ and $u(c,t)=1/[t(v-\log c)]$. Its derivatives are

$$
\partial_c^2u=
\frac{2-(v-\log c)}{t c^2(v-\log c)^3},\qquad
\partial_t\partial_c^2u=
\frac{(v-\log c)^2-6}{t^2c^2(v-\log c)^4}.
$$

Throughout the segment joining $1$ to $c$, one has
$v-\log c\ge v-1/100\ge(999/1000)v$ and $c\ge99/100$.
Taylor's formula and
$[(99/100)^2(999/1000)^2]^{-1}<1.024$ therefore give

$$
|b_c(t)|\le\frac{0.512e^2}{t\log^2t},\qquad
|b_c'(t)|\le\frac{0.512e^2}{t^2\log^2t}\quad(t>A).
\tag{GK2}
$$

On $(0,A]$, the same existing regular part equals
$e^2/(cAL)$. Partial summation against $D$, including its actual value
at $A$ and the change of formula there, gives

$$
\int b_c\,dD=
\left[\frac{e^2}{cAL}-b_c(A+)\right]D(A)
 -\int_A^\infty D(t)b_c'(t)\,dt.
$$

The upper boundary vanishes by the global PNT input already used in
(GS3). Applying (GK2), $|D(t)|\le\eta_0(A)t$ for all $t\ge A$, and
$\int_A^\infty dt/(t\log^2t)=1/L$ yields

$$
\left|\int b_c\,dD\right|
\le\frac{\eta_0(A)e^2}{L}
 \left[\frac{100}{99}+0.512+\frac{0.512}{L}\right]
 \le\frac{2\eta_0(A)e^2}{L}.
\tag{GK3}
$$

This uses a bound on the regular part against the global error; no
short-interval bound has been inferred from global PNT.

### Retain the negative local residual, including the endpoint atoms

The actual local residual $v_c=B_c-b_c$ from (GS5)–(GS7) is
nonpositive. For $c>1$ its formula on $A<t<cA$ is
$1/(cAL)-1/[t\log(t/c)]$, and $v_c(A)=v_c(cA)=0$.
For $c<1$ its formula on $cA<t\le A$ is
$1/[t\log(t/c)]-1/(cAL)$, with $v_c(cA)=0$.
It is zero elsewhere. Since $1/[t\log(t/c)]$ decreases with $t$ on
these intervals, both displayed formulas are nonpositive. These values
also fix the sign at a possible prime-power atom at $A$ or $cA$.

Consequently the actual measure $d\psi\ge0$ gives

$$
\int v_c\,dD=\int v_c\,d\psi-\int v_c\,dt
\le-\int v_c\,dt.
$$

On the entire interval with endpoints $A,cA$,
$t\ge(99/100)A$ and $\log(t/c)\ge L-1/100$. Thus

$$
\left|\frac{d}{dt}\frac1{t\log(t/c)}\right|
\le\frac{1.034}{A^2L}.
$$

Indeed, the ratio to $1/(A^2L)$ is at most
$[(99/100)^2]^{-1}[L/(L-1/100)][1+1/(L-1/100)]<1.034$
for $L\ge78$. The local residual vanishes at $cA$, so integrating
the resulting triangular upper bound gives

$$
\boxed{\int v_c\,dD
\le\frac{1.034(A|e|)^2}{2A^2L}
 \le\frac{0.52e^2}{L}.}
\tag{GK4}
$$

An atom contributes to the nonpositive prime term; it is not replaced
by a Lebesgue density or discarded with an unknown sign.

### Pay all Gamma scales outside the narrow interval

An explicit global bound needed only for this tail follows directly
from the existing Dusart Theorem 5.2 $k=0$ row and Proposition 3.2:
$\psi(t)\le4t$ for $t>0$. For $t<2$, $\psi(t)=0$; for $t\ge2$ use
$\vartheta(t)<2t$ and
$1.00007t^{-1/2}+1.78t^{-2/3}<2$.
Applying the already established (GP4) estimates with this constant
gives, for every $c>0$,

$$
\int|w_c-h_A|\,d\psi\le\frac{16(c+c^{-1})}{L},\qquad
\int|w_c-h_A|\,dt\le\frac{4(c+c^{-1})}{L}.
$$

For clarity, below $A\max(1,c)$ the corresponding bound with
$\psi(t)\le Bt$ is $2B(c+c^{-1})/L$. Above that point it is also
$2B(c+c^{-1})/L$: use the logarithmic difference and
$|\log c|+\tfrac12(\log c)^2\le c+c^{-1}$, since $L\ge2$.
This is a numerical use of the existing all-scale convergence argument.
The affine derivative in (GS5) satisfies
$\int|a_A|\,(d\psi+dt)\le14/L$ by the same partial summation.
Since $|c-1|\le c+c^{-1}$, these estimates pay the complete centered
kernel, with room in the constant:

$$
\left|\int B_c\,dD\right|
\le\frac{100(c+c^{-1})}{L}\qquad(c>0).
\tag{GK5}
$$

This includes every scale with $cA<1$. Only absolutely convergent
differences are integrated, as in (GP4)–(GP5).

Let $C$ have the same mean-one Gamma law with shape and rate $\alpha$.
Use its existing moment-generating function and Chernoff bound with
$\delta=1/100$. The two exponents satisfy
$\delta-\log(1+\delta)\ge\delta^2/[2(1+\delta)]>1/30000$ and
$-\delta-\log(1-\delta)\ge\delta^2/2>1/30000$. Therefore

$$
\Pr(C\notin[99/100,101/100])\le2e^{-\alpha/30000},\qquad
\mathbb E(C+C^{-1})^2
\le\frac54+2+\frac83<6.
$$

Cauchy–Schwarz and (GK5) bound the normalized contribution from that
whole event by $400\sqrt A e^{-\alpha/60000}$. On its complement,
(GK3)–(GK4) apply. Averaging with
$\mathbb E(C-1)^2=1/\alpha$ proves (GK1) using the globally centered
identity (GS6). No conditional mean-one assertion has been used.

### Preserve the complete original zero response

Reusing $J_1=-I_\psi$, $J_\alpha=Z_\alpha+\overline R_\alpha$ and
the full elementary upper bound (GE4) gives

$$
\boxed{\begin{aligned}
-\sqrt A L I_\psi(A)\le{}&\sqrt A L Z_\alpha(A)
 +[0.52+2\eta_0(A)]\frac{\sqrt A}{\alpha}\\
&+400\sqrt A e^{-\alpha/60000}
 +\frac{5M_1(\alpha)}{\sqrt A}.
\end{aligned}}
\tag{GK6}
$$

Here $Z_\alpha$ retains the original $H_\alpha(\rho)F_A(\rho)$,
every actual real part, multiplicity and height. The improvement is an
effective directed arithmetic payment obtained from the retained local
sign, not a new bound on the main response. The unbounded signed Robin
estimate and RH remain unproved. This is a paper-level application of
the existing prime bounds and kernel identities, without a mathematical
priority or Lean-certification claim.

## A further finite clock from the effective cutoff-sign payment

Keep the same conditional least integer $N>5040$ attaining the global
Robin-ratio maximum under the Robin-violation hypothesis. The preceding
application already excludes $A=\log N\le10^{46}$; put $L=\log A$.
Apply (GK6) on the additional interval

$$
10^{46}<A\le\frac72\,10^{46},\qquad
\alpha=\frac75\,10^{23}+\frac12.
$$

This uses the effective directed comparison, the full original
coefficient bound (GJ1), Gamma damping (GH1), and the existing complete
elementary remainder. No primes, arithmetic profiles or zero ordinates
are newly enumerated.

### Pay the actual global arithmetic error

Dusart's original Theorem 5.2 $k=2$, $\eta_2=3.965$, $x_2=2$ row and
Proposition 3.2, already used in (GJ4), give for every $t\ge A$

$$
\frac{|\psi(t)-t|}{t}
\le\frac{3.965}{\log^2t}+1.00007t^{-1/2}+1.78t^{-2/3}
<0.001.
$$

Hence $\eta_0(A)<0.001$. Moreover $L>78$,
$\sqrt A<1.871\cdot10^{23}$ and $\alpha\ge1.4\cdot10^{23}$.
The normalized central comparison term in (GK6) is therefore

$$
[0.52+2\eta_0(A)]\frac{\sqrt A}{\alpha}
<\frac{0.522(1.871)}{1.4}<0.698.
\tag{GL1}
$$

The Gamma tail is explicit: $\alpha/60000>10^{18}$ and
$e^x>x^3/6$ for $x>0$ imply $e^{\alpha/60000}>10^{53}$.
Thus $400\sqrt A e^{-\alpha/60000}<8\cdot10^{-28}$.
The entire elementary contribution is less than $6\cdot10^{-23}$ by
(GE4). This includes Gamma scales below the unit cutoff.

### Pay every original zero above the verified height

The existing (GJ2) gives, with $H=3\cdot10^{12}$,

$$
\sqrt A L|Z_\alpha(A)|
<M_1(\alpha)(1+1/L)
\left[1.054c_0+2(1.0001)\sqrt A S_2(H)
 e^{-H^2/[2(\alpha+H)]}\right].
$$

Here $c_0<0.05$, $S_2(H)<1.48\cdot10^{-12}$ and
$M_1(\alpha)<1.0001$ are unchanged. For the selected shape,
$H^2/[2(\alpha+H)]>32$ and $e^{32}>4\cdot10^{13}$;
the latter follows from $e>8/3$ and
$8^{32}>4\cdot10^{13}3^{32}$. Both ordinate signs, the actual tail
real parts and all heights to infinity remain included. The head and
tail satisfy the exact rational budgets

$$
(1.0001)(1.02)(1.054)(0.05)<0.054,
$$

$$
2(1.0001)^2(1.02)(1.871\cdot10^{23})
 (1.48\cdot10^{-12})(4\cdot10^{13})^{-1}<0.015.
\tag{GL2}
$$

Combining (GK6), (GL1) and (GL2) pays the original full signed response:

$$
\boxed{-\sqrt A L I_\psi(A)
<0.054+0.015+0.698+8\cdot10^{-28}+6\cdot10^{-23}
<0.768.}
\tag{GL3}
$$

The same selected source obeys the strict core
$\sqrt A L D^*(A)>\mathcal E(L)>0.778$ and
$\Delta(N)=I_\psi(A)+D^*(A)$. Therefore

$$
\boxed{\sqrt A L\Delta(N)>0.01,
\qquad10^{46}<A\le\frac72\,10^{46}.}
\tag{GL4}
$$

Together with the preceding exclusion, this forces
$\log N>(7/2)10^{46}$ for the same hypothetical least global maximizer.
It is a selected-source finite exclusion with a normalized margin,
not an all-integer finite Robin verification or an unbounded main
estimate. The full RH objective remains unproved. All classical prime,
zero-count and verified-height inputs are reused; this paper-level
application carries no mathematical-priority or Lean-certification claim.

## Absolute full-weight cost at a fixed negative heat time

Keep the same conditional least global Robin-ratio maximizer $N$, the
arithmetic clock $A=\log N>(7/2)10^{46}$, and $L=\log A$. The result
below also holds for every fixed $A>1$. It concerns a particular
absolute transport through negatively deformed zeros; it supplies no
upper bound for the original signed response $-\sqrt A L I_\psi(A)$.

The inputs are Alexander Dobner, *A proof of Newman's conjecture for
the extended Selberg class*, [Acta Arithmetica 201 (2021), 29–62](https://doi.org/10.4064/aa200603-23-7), inspected in
[arXiv:2005.05142v2](https://arxiv.org/html/2005.05142v2), Theorems 4–5,
Lemma 3 and §3.1, and the NIST DLMF
[principal exponential integral](https://dlmf.nist.gov/6.2#E1) and
[sector asymptotic expansion](https://dlmf.nist.gov/8.20#E2).
These published results are reused as `literature-attested` inputs.
The combined full-weight convergence restriction is a `repo-derived`
paper-level source application; no
mathematical-priority or Lean-certification claim is made.

### Continue the complete coefficient, keeping its cancellation

For $0<\Re s<1$, put $v=\log u$ in the unchanged coefficient (M1).
The DLMF principal $E_1$ definition and one integration by parts give

$$
\begin{aligned}
F_A(s)
&=\frac1s\int_L^\infty e^{(s-1)v}
                 \left(\frac1v+\frac1{v^2}\right)\,dv\\
&=\frac{A^{s-1}}{sL}+E_1((1-s)L).
\end{aligned}
\tag{NH1}
$$

Thus the right side defines the natural principal continuation
$\widehat F_A$ on $\mathbb C\setminus(\{0\}\cup[1,\infty))$.
Continuation defines these individual terms beyond the integral's
half-plane of convergence; it does not itself establish a spectral
transport identity.

Let $s=x+iy$, $y\to+\infty$, with $|x|\le B\log y$ for a fixed $B$.
Then $z=(1-s)L$ lies, eventually, in $|\arg z|\le3\pi/4$.
DLMF (8.20.2), with its parameter $p=1$, supplies uniformly there

$$
E_1(z)=e^{-z}\left(z^{-1}-z^{-2}+O(|z|^{-3})\right).
$$

Substitution into the **full** (NH1) yields

$$
\begin{aligned}
\widehat F_A(s)
&=A^{s-1}\left(
 \frac1{Ls(1-s)}-\frac1{L^2(1-s)^2}+O_{A,B}(y^{-3})\right)\\
&=\frac{1+L}{L^2}\frac{A^{s-1}}{y^2}
       \left(1+O_{A,B}\!\left(\frac{\log y}{y}\right)\right).
\end{aligned}
\tag{NH2}
$$

The terms $1/(sL)$ and $1/((1-s)L)$ cancel at order $y^{-1}$.
The $-z^{-2}$ term supplies the additional $1/L^2$ in the nonzero
leading coefficient. Neither part of the original weight has been
discarded. All asymptotics here fix $A$ before taking the height limit.

### Obtain enough distinct actual zeros from the source's shifts

Fix one $\epsilon>0$ throughout and use Dobner's heat parameter
$t=-\epsilon$. In the Riemann specialization his equations (11)–(12)
give

$$
D_\epsilon(s)=\sum_{n\ge1}
 e^{-\epsilon\log^2 n/4}n^{-s},\qquad
J_\epsilon(s)=s+\frac\epsilon4\operatorname{Log}\frac{s}{2\pi}.
\tag{NH3}
$$

The completion has the normalization
$\xi_t((1+iz)/2)=8H_t(z)$, with the same heat time $t$.
These are deformed $\xi_{-\epsilon}$ zeros, not original zeta zeros.

Dobner's Lemma 3 supplies a zero of $D_\epsilon$. His §3.1 proof,
using Theorems 4–5, supplies actual zeros of
$\xi_{-\epsilon}(J_\epsilon(s))$ in sufficiently high translates
of one fixed zero-isolating circle of radius $r$. The same shift
sequence satisfies

$$
\liminf_{m\to\infty}(\tau_{m+1}-\tau_m)>0,
\qquad \limsup_{m\to\infty}\frac{\tau_m}{m}<\infty.
$$

In particular $\tau_m\asymp_\epsilon m$. Choose $d>0$ such that
the consecutive gaps are eventually at least $d$, and retain every
$q$-th shift, where $qd>2r+\epsilon\pi/4$. On the upper half-plane,
$J_\epsilon$ adds an imaginary offset in $(0,\epsilon\pi/4)$.
Consequently the images of the retained circles have disjoint height
intervals. Choosing one actual zero in each produces **distinct**
zeros $w_m$ of the same $\xi_{-\epsilon}$ with

$$
\Im w_m\asymp_\epsilon m,\qquad
\Re w_m=\frac\epsilon4\log(\Im w_m)+O_\epsilon(1).
\tag{NH4}
$$

This uses the source's shift-density information, not merely the
existence of infinitely many zeros. The selected preimages stay in
one fixed bounded real strip, and $\Im J_\epsilon(s)=\Im s+O_\epsilon(1)$,
which proves the real-part statement in (NH4).

### A necessary absolute-budget condition, including equality

Write $\kappa=\epsilon L/4$. Equations (NH2) and (NH4) imply, for
all sufficiently large $m$,

$$
|\widehat F_A(w_m)|\asymp_{A,\epsilon}m^{\kappa-2}.
\tag{NH5}
$$

The constants are positive because $(1+L)/L^2>0$ and
$A^{\Re w_m-1}\asymp_{A,\epsilon}(\Im w_m)^\kappa$.
Hence, counting the actual deformed zeros with multiplicities,

$$
\boxed{
\epsilon\log A\ge4
\quad\Longrightarrow\quad
\sum_{\substack{\xi_{-\epsilon}(w)=0\\\Im w>0}}
 |\widehat F_A(w)|=\infty.}
\tag{NH6}
$$

At equality the selected subseries dominates the harmonic series;
for larger $\epsilon L$ it dominates a divergent power series.
Thus $\epsilon\log A<4$ is a **necessary** condition for this
principal-continued, complete-weight, absolute full-spectrum
transport. For $\epsilon\log A<4$, (NH5) makes this particular
selected subseries converge, but establishes no convergence or
uniform bound for the rest of the deformed spectrum.

The conclusion is about absolute cost at one fixed negative heat
time. It proves neither signed divergence nor a failure of Robin or
RH, and does not exclude transports that retain cancellation or use
additional comparison terms. Such a route still needs an all-height
identity and a paid signed error returning to the original zeros,
their real parts and multiplicities, the original elementary
correction and the strict core at the same $N$. No changing heat time
per zero, finite-spectrum truncation or unproved positive-time
certificate is used to discharge that obligation.

## The subcritical full-spectrum absolute boundary

The necessary condition (NH6) has a converse for every fixed $A>1$
and fixed $\epsilon>0$. The additional step is a uniform right-half-plane
comparison, not a use of Dobner's Theorem 4 outside its stated
$|\Re s|\le C(\Im s)^{1/4}$ range. Reuse his exact negative-heat
convolution (9), the Riemann completion, and the already retained
(NH1)–(NH6). The [DLMF digamma expansion (5.11.2)](https://dlmf.nist.gov/5.11#E2)
is used in its fixed sector $|\arg z|\le\pi/2$.
These are `literature-attested` inputs; the uniform comparison and
combined convergence boundary below are `repo-derived` paper-level
applications, with no mathematical-priority or Lean-certification claim.

### A uniform comparison on the entire right half-plane

Write

$$
\gamma(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2),\qquad
c=\epsilon/4,\qquad
J_\epsilon(s)=s+c\operatorname{Log}(s/(2\pi)),
$$

$$
\gamma_{-\epsilon}(s)=\gamma(s)
 \exp((s-J_\epsilon(s))^2/\epsilon).
$$

For fixed $\epsilon>0$, the comparison is

$$
\boxed{\frac{\xi_{-\epsilon}(J_\epsilon(s))}
 {\gamma_{-\epsilon}(s)}
 =D_\epsilon(s)+O_\epsilon(|s|^{-1}),
 \qquad \Re s\ge2,\quad |s|\longrightarrow\infty.}
\tag{NH7}
$$

Uniformity includes arbitrarily large $\Re s$, both ordinate signs,
and the real axis. It is not uniform in $\epsilon$ as $\epsilon\to0$.

Here is the required interface proof. The DLMF expansion gives uniformly
in this half-plane

$$
\frac{\gamma'}{\gamma}(s)
=\frac1s+\frac1{s-1}-\frac12\log\pi
 +\frac12\frac{\Gamma'}{\Gamma}(s/2)
=\frac12\operatorname{Log}(s/(2\pi))+O(|s|^{-1}).
$$

Its imaginary part is bounded on the whole half-plane: the principal
argument is bounded, and the remaining bounded part is covered by
continuity on a compact set. Consequently, for an absolute $M$ and
all real $v$,

$$
\left|\frac{\gamma(s+iv)}{\gamma(s)}\right|\le e^{M|v|}.
$$

Set

$$
R_s(v)=\frac{\gamma(s+iv)}{\gamma(s)}
 \exp\!\left(-\frac{iv}{2}\operatorname{Log}(s/(2\pi))\right),
\qquad r=|s|.
$$

Then $|R_s(v)|\le e^{(M+\pi/4)|v|}$ for all $v$. Integrating the
logarithmic derivative along the vertical segment, for
$|v|\le r^{1/4}$ and large $r$, gives

$$
|R_s(v)-1|\ll\frac{|v|+v^2}{r}.
$$

Indeed, $|s+iu|\ge r/2$ on that segment and
$|\operatorname{Log}(s+iu)-\operatorname{Log}s|\le2|u|/r$.
The integrated exponent is $O((|v|+v^2)/r)=o(1)$ uniformly on this
range. No bounded-real-part Stirling estimate is used at an unbounded
real part.

In Dobner's (9), shift the vertical contour to $\Re z=\Re s$ and
write $z=s+iv$. For each fixed $s$ this is a finite contour shift;
the Gaussian and the usual vertical decay kill the horizontal ends.
After division by $\gamma_{-\epsilon}(s)$ the exact identity is

$$
\frac{\xi_{-\epsilon}(J_\epsilon(s))}{\gamma_{-\epsilon}(s)}
=\frac1{\sqrt{\pi\epsilon}}\int_{\mathbb R}
 e^{-v^2/\epsilon}R_s(v)\zeta(s+iv)\,dv.
\tag{NH8}
$$

Replacing $R_s$ by $1$ gives exactly $D_\epsilon(s)$ by the Gaussian
Fourier integral and the absolutely convergent Dirichlet series.
On $\Re s\ge2$, $|\zeta(s+iv)|\le\zeta(2)$. The local difference
therefore has integral $O_\epsilon(r^{-1})$. On $|v|>r^{1/4}$ the
uniform exponential bound for $R_s$ gives
$O_\epsilon(\exp(-r^{1/2}/(2\epsilon)))=o_\epsilon(r^{-1})$.
This proves (NH7), without estimating every Dirichlet term separately.

### Every sufficiently high zero lies in a logarithmic region

On $\Re s\ge2$,
$|D_\epsilon(s)-1|\le\zeta(2)-1<1$.
The completion $\gamma_{-\epsilon}$ is nonzero there, so (NH7) shows
that $\xi_{-\epsilon}(J_\epsilon(s))\ne0$ for all sufficiently large
$|s|$ in this entire half-plane.

To cover the rightmost region, let $w$ have sufficiently large modulus
and satisfy
$\Re w\ge c\log(|w|/(2\pi))+3$.
Put $s_0=w-c\operatorname{Log}(w/(2\pi))$.
On $|s-s_0|=1/2$ one has $\Re s\ge5/2$ and

$$
J_\epsilon(s)-w=(s-s_0)
 +c[\operatorname{Log}(s/(2\pi))-
       \operatorname{Log}(w/(2\pi))].
$$

The second term is $O_\epsilon(\log|w|/|w|)<1/2$.
The logarithms and the intervening segments stay in the right
half-plane. Rouché's theorem gives a preimage $s$ inside the circle;
it satisfies $\Re s\ge2$ and $|s|\asymp|w|$.
Thus there is no such zero $w$. Apply the same argument to $1-w$ using
$\xi_{-\epsilon}(1-w)=\xi_{-\epsilon}(w)$.
Together these bounds imply, for every zero of sufficiently large
modulus,
$|\Re w|\le c\log|w|+O_\epsilon(1)$.
This forces $|\Im w|\to\infty$ with $|w|$ and then gives

$$
\boxed{1-c\log y-O_\epsilon(1)
 \le\Re w\le c\log y+O_\epsilon(1),
 \qquad y=\Im w\longrightarrow+\infty.}
\tag{NH9}
$$

All actual zeros are covered; this is not the lower-density subsequence
in (NH4). To replace $|w|$ by $y$, note that the bound on $|\Re w|$
precludes $|\Re w|\ge|\Im w|$ at arbitrarily large modulus, and hence
$|w|\le\sqrt2\,|\Im w|$ eventually.

### Count the whole spectrum and use the complete original coefficient

The original Fourier kernel $\Phi$ in Dobner's (2) is positive for
$u\ge0$: each summand has the positive factor
$2\pi n^2e^{4u}-3$. Evenness gives positivity on the whole real line.
For $|s-1/2|\le R$, its exact Fourier representation implies

$$
|\xi_{-\epsilon}(s)|
\le\int_{\mathbb R}\Phi(u)e^{2R|u|}\,du
\le2\xi_0(1/2+R),
\qquad \xi_{-\epsilon}(1/2)>0.
$$

Classical real Stirling growth gives a logarithm
$O(R\log(R+2))$ for the upper bound. Jensen's zero-count theorem,
applied at $1/2$ with radii $R$ and $2R$, therefore gives
$O_\epsilon(R\log(R+2))$ zeros in the disk, counted with multiplicities.
Together with (NH9), this gives the complete height count

$$
N_\epsilon(T)=\#\{w:\xi_{-\epsilon}(w)=0,\ 0<\Im w\le T\}
\ll_\epsilon T\log(T+2).
\tag{NH10}
$$

The bounded-height exceptions are finite by (NH9) and analyticity.
This step reuses the standard Jensen theorem, not an original-zeta
zero count applied to a different function.

Fix $A>1$ as well, write $L=\log A$ and $\kappa=\epsilon L/4$.
The retained complete-weight asymptotic (NH2), with (NH9), now gives
for every sufficiently high actual zero

$$
|\widehat F_A(w)|\ll_{A,\epsilon} (\Im w)^{\kappa-2}.
$$

For $\kappa<1$, the mass in a dyadic height band is at most
$O_{A,\epsilon}(j2^{j(\kappa-1)})$ by (NH10), and these bounds sum.
Thus the converse to (NH6) is

$$
\boxed{\sum_{\substack{\xi_{-\epsilon}(w)=0\\\Im w>0}}
 |\widehat F_A(w)|<\infty
 \quad\Longleftrightarrow\quad \epsilon\log A<4,
 \qquad A>1,\quad\epsilon>0.}
\tag{NH11}
$$

Every zero has its actual real part and multiplicity, and all positive
heights are retained. (NH6) supplies divergence at and above the
boundary; (NH7)–(NH10) supply full-spectrum convergence below it.
The tail below the boundary is
$O_{A,\epsilon}(T^{\kappa-1}\log(T+2))$ as $T\to\infty$,
with fixed parameters. No uniform allowance as $\epsilon\to0$ or
$\epsilon\log A\to4$ is asserted.

This determines the absolute convergence domain of the particular
continued complete-weight deformation. It provides no numerical
Robin budget, signed transport identity, or comparison error returning
to the original zero multiset. The same selected integer $N$,
$A=\log N>(7/2)10^{46}$, the original $F_A$, positive elementary
correction and strict core remain in the unproved target (G9).
In particular, absolute convergence of the deformed trace does not
prove its signed upper bound or RH.

## A joint small-negative-time comparison of the complete signed trace

The fixed-parameter convergence in (NH11) can be supplemented with a
quantitative comparison to the original trace. Reuse (NH8), its global
vertical ratio bound, the principal continuation (NH1), and the
all-spectrum count and convergence (NH9)–(NH11). The new interface is
uniform in the arithmetic clock and in small negative heat time; no
individual zero trajectories or zero-gap bounds are required.

Write $H_\epsilon=\xi_{-\epsilon}'/\xi_{-\epsilon}$, with $H_0$ for
the original completion. Define the full real trace

$$
Z_\epsilon(A)=\sum_{\xi_{-\epsilon}(w)=0}\widehat F_A(w).
$$

All zeros here are nonreal: positivity of the original Fourier kernel
makes $\xi_{-\epsilon}(x)>0$ for every real $x$. The trace includes both
ordinate signs and every multiplicity. At $\epsilon=0$ it is precisely
$Z_{\rm orig}(A)$ from (G9). The branch continuation is used for deformed
zeros with real part beyond $1$; their coefficients are not replaced
by convergent original integrals there.

There are absolute constants $\epsilon_0>0$ and $C<\infty$ such that

$$
\boxed{|Z_\epsilon(A)-Z_{\rm orig}(A)|\le C\epsilon A^2,
\quad A\ge e^2,\quad 0<\epsilon\le\epsilon_0,
\quad \epsilon\log A\le1.}
\tag{NH12}
$$

This is a `repo-derived` paper-level application of the retained
convolution and spectral interfaces, together with the standard Cauchy,
Hadamard and argument-principle theorems. It does not assert mathematical
priority, Lean certification, a numerical value of $C$ or
$\epsilon_0$, or a signed Robin upper bound.

### Center the small-time error before taking a logarithmic derivative

Keep $J_\epsilon,\gamma_{-\epsilon},R_s$ from (NH7)–(NH8), and set

$$
U_\epsilon(s)=
 \frac{\xi_{-\epsilon}(J_\epsilon(s))}{\gamma_{-\epsilon}(s)}.
$$

For $\Re s\ge2$, (NH8) gives the exact Gaussian average of
$R_s(v)\zeta(s+iv)$. The retained log-Gamma estimates imply that the
first two $v$ derivatives of this product are bounded uniformly for
$|v|\le1$ and $\Re s\ge2$. To see the needed uniformity, use

$$
\partial_v\log R_s(v)
=i\left[\frac{\gamma'}\gamma(s+iv)
 -\tfrac12\operatorname{Log}(s/(2\pi))\right].
$$

The bracket and its $v$ derivative are bounded there. The DLMF
sector estimate supplies the large-$|s|$ bound, Cauchy's derivative
estimate supplies its derivative, and the remaining compact region
has no Gamma pole or zero. The series for $\zeta,\zeta',\zeta''$ are
uniformly absolutely convergent in $\Re s\ge2$.

Taylor-expand the product at $v=0$ and subtract its linear term.
The centered Gaussian integrates that linear term to zero, while its
second moment is $\epsilon/2$. On $|v|>1$, the retained
$e^{(M+\pi/4)|v|}$ envelope pays the whole tail by $O(\epsilon)$ for
$0<\epsilon\le1/2$, including the subtracted affine term. Hence

$$
U_\epsilon(s)=\zeta(s)+O(\epsilon)
\quad(\Re s\ge2),
\tag{NH13}
$$

with an absolute constant. This improves the parameter dependence
needed here; (NH7)'s fixed-$\epsilon$ height estimate is not assigned
a uniform constant without proof.

Since $|\zeta(s)|\ge2-\zeta(2)>0$, choose an absolute
$\epsilon_0\le1/2$ small enough that $U_\epsilon$ is bounded away
from zero on the entire half-plane. On $\Re s=3$, Cauchy's estimate
on radius-$1/2$ disks also gives $U_\epsilon'-\zeta'=O(\epsilon)$.
The denominators are now paid, so
$U_\epsilon'/U_\epsilon-\zeta'/\zeta=O(\epsilon)$.

The exact normalization obeys

$$
\frac{\gamma_{-\epsilon}'}{\gamma_{-\epsilon}}(s)
=\frac{\gamma'}\gamma(s)
 +\frac\epsilon8\frac{\operatorname{Log}(s/(2\pi))}{s}.
$$

Consequently, on the whole line $\Re s=3$,

$$
K_\epsilon(s):=H_\epsilon(J_\epsilon(s))J_\epsilon'(s)
=H_0(s)+O(\epsilon),
\qquad |H_0(s)|\ll\log(|s|+2).
\tag{NH14}
$$

Both bounds have absolute constants. No function-value estimate is
substituted for a logarithmic-derivative estimate without this step.

### Transport the complete coefficient on these curves

Differentiating the exact (NH1), including its exponential-integral
part, gives

$$
\widehat F_A'(z)=A^{z-1}
 \left[\frac1{z(1-z)}-\frac1{Lz^2}\right],\qquad L=\log A.
\tag{NH15}
$$

This derivative is single-valued away from $0,1$; the original weight
itself still has its branch cut. Put $s=3+iy$, $r=|s|$,
$\kappa=\epsilon L/4\le1/4$, and

$$
Q_\epsilon(s)=\widehat F_A(J_\epsilon(s))
             +\widehat F_A(1-J_\epsilon(s)).
$$

On the segments from $s$ to $J_\epsilon(s)$ and their reflections,
$|z|,|1-z|\asymp r$. They remain respectively in the right and left
half-planes, and the first segment has the same ordinate sign at both
ends. Its real part is at most $3+(\epsilon/4)\max(\log(r/(2\pi)),0)$.
For bounded $r$, any analogous reflected increase is bounded by
$\epsilon L\le1$. Thus (NH15) gives

$$
|Q_\epsilon(s)-Q_0(s)|
 \ll\epsilon A^2\log(r+2)r^{\kappa-2}.
$$

One also has $|Q_0(s)|\ll A^2r^{-2}$ uniformly for $A\ge e^2$.
This full-coefficient bound can be obtained from (NH15) without losing
its cancellation: integrate from $3+iy$ to the corresponding imaginary
infinity, where (NH2) gives zero, and integrate $e^{iLt}$ once by
parts. The rational bracket is $O((1+t^2)^{-1})$ and its derivative
is $O((1+|t|^3)^{-1})$; $L\ge2$ pays the integration factor.
Use the same calculation on $-2-iy$, whose exponential factor is
$A^{-3}$. Each ordinate sign is treated on its own branch; at $y=0$
take the one-sided limits. It follows that

$$
\begin{aligned}
|Q_0(s)|&\ll A^2r^{-2},\\
|Q_\epsilon(s)|&\ll A^2\log(r+2)r^{\kappa-2},\\
|Q_\epsilon(s)-Q_0(s)|
 &\ll\epsilon A^2\log(r+2)r^{\kappa-2}.
\end{aligned}
\tag{NH16}
$$

No leading-term replacement of $\widehat F_A$ is used.

### The whole trace has an exact contour, cut and pole balance

Let $\Gamma_\epsilon$ be $J_\epsilon(3+i\mathbb R)$, oriented upward,
and put $b_\epsilon=J_\epsilon(3)$. The curve and its reflection enclose
all zeros. For completeness, $J_\epsilon$ is injective on $\Re s>2$:
the real part of

$$
\frac{J_\epsilon(s_1)-J_\epsilon(s_2)}{s_1-s_2}
=1+\frac\epsilon4\int_0^1
 \frac{dt}{s_2+t(s_1-s_2)}
$$

is positive. Its boundary line maps to a graph, since
$\Im J_\epsilon(b+iy)=y+(\epsilon/4)\arctan(y/b)$ is strictly
increasing and onto. Properness at infinity then identifies the
half-plane image with the region to the right of that graph.
By (NH13) there are no zeros in this image. The reflected exterior
is zero-free by the functional equation. In particular all zeros lie
between $\Gamma_\epsilon$ and $1-\Gamma_\epsilon$.

Use the argument principle in this intervening region, slit along
$[1,b_\epsilon]$ and with the pole at $0$ accounted for. The already
cited [DLMF (6.2.4)](https://dlmf.nist.gov/6.2#E4),
$E_1(z)=\operatorname{Ein}(z)-\operatorname{Log}z-\gamma$, shows

$$
\widehat F_A(x+i0)-\widehat F_A(x-i0)=2\pi i\quad(x>1),
\qquad \operatorname{Res}_{z=0}\widehat F_A(z)=\frac1{AL}.
$$

The upper side of the slit is traversed from $1$ to $b_\epsilon$;
its contribution is therefore
$\log(\xi_{-\epsilon}(b_\epsilon)/\xi_{-\epsilon}(1))$.
The logarithms here are real logarithms of positive values.
The circle at the logarithmic branch point $1$ tends to zero.
Reflection changes $H_\epsilon(1-z)$ to $-H_\epsilon(z)$,
so the two exterior curves combine into the exact balance

$$
\boxed{
Z_\epsilon(A)=\frac1{2\pi i}
 \int_{3-i\infty}^{3+i\infty}Q_\epsilon(s)K_\epsilon(s)\,ds
 +\log\frac{\xi_{-\epsilon}(b_\epsilon)}{\xi_{-\epsilon}(1)}
 -\frac{H_\epsilon(0)}{AL}.}
\tag{NH17}
$$

The two integral halves use the corresponding principal boundary
values at the real crossing; the integral is absolutely convergent
by (NH14)–(NH16). Both ordinate signs and all multiplicities remain.
At $\epsilon=0$ this is the identical contour balance for
$Z_{\rm orig}$, not a different kernel or another maximizing integer.

The infinite-contour limit also needs its horizontal ends paid.
The retained Fourier growth and a positive lower bound at $1/2$
give the (NH10) disk/height counts uniformly for
$0\le\epsilon\le\epsilon_0$; the lower bound may use
$\xi_{-\epsilon_0}(1/2)>0$. In each large dyadic interval choose
heights whose unit neighborhoods contain $O(\log T)$ zeros and whose
distance from every zero ordinate is at least $c/\log T$.
These heights exist by averaging the complete count and removing
intervals of that radius with sufficiently small $c$.

The standard genus-one Hadamard logarithmic derivative is

$$
H_\epsilon(z)=B_\epsilon+
 \sum_w\left(\frac1{z-w}+\frac1w\right).
$$

Its finite part at these heights is $O(T\log T)$: only
$O(\log T)$ zeros have ordinate distance below $1$, their reciprocals
cost $O(\log^2T)$, and the other $O(T\log T)$ terms have distance
at least $1$. The $1/w$ terms cost $O(\log^2T)$, and the
$|w|>4T$ tail costs $O(\log T)$ by the complete count.
Here $|z|\asymp T$ on the horizontal ends, and the endpoints' real
width is $O(\log T)$. The complete-coefficient estimate (NH2) therefore
pays these ends by $O_{A,\epsilon}(T^{\kappa-1}\log^2T)\to0$.
The Hadamard theorem is used for the deformed entire function itself;
no original-zeta count or simple-zero assumption is imported.
This justifies (NH17) over the full spectrum, including collisions.

### Pay the signed trace difference on the same arithmetic clock

Subtract (NH17) at zero heat time. Equations (NH14)–(NH16) give

$$
\left|\frac1{2\pi i}\int
 [Q_\epsilon K_\epsilon-Q_0H_0],ds\right|
\ll\epsilon A^2\int_{\mathbb R}
 |3+iy|^{\kappa-2}\log^2(|3+iy|+2)\,dy
\ll\epsilon A^2,
$$

uniformly for $\kappa\le1/4$. The exact slit and pole differences
are $O(\epsilon)$ as well. Indeed, $b_\epsilon-3=O(\epsilon)$,
and the Fourier representation has uniformly bounded $x$ and
$\epsilon$ derivatives on the fixed real compact set $0\le x\le3$,
$0\le\epsilon\le\epsilon_0$. Positivity bounds its denominators away
from zero there. The required moments are finite by the original
super-exponential kernel decay. Hence the real logarithm difference
and $H_\epsilon(0)-H_0(0)$ are $O(\epsilon)$; $1/(AL)\le1$.
This proves (NH12), with every contour correction retained.

For one common heat time at each $A$, choose

$$
\epsilon(A)=\min(\epsilon_0/2,A^{-3}).
$$

It satisfies all the preceding hypotheses for $A\ge e^2$. Using the
unchanged positive elementary term $r_A$ from (G9), (NH12) gives

$$
\boxed{-\sqrt A L I_\psi(A)
=\sqrt A L Z_{\epsilon(A)}(A)+r_A
 +O\!\left(LA^{-1/2}\right).}
\tag{NH18}
$$

The implicit constant is independent of $A$. The same selected
$N$ and $A=\log N>(7/2)10^{46}$ remain the source, and the original
zero real parts, multiplicities and infinite height range are paid
through the complete comparison. The time depends on the one
arithmetic clock, never on individual zeros. No uniform fixed negative
time is used as $A\to\infty$.

The comparison provides no upper bound for the signed main trace
$\sqrt A L Z_{\epsilon(A)}(A)$. In particular its absolute convergence
and its zero-free exterior do not establish the Robin budget
$\mathcal E(L)$. The constants have not been numerically certified
against the selected finite clock, so an $o(1)$ comparison alone is
not an exact finite Robin certificate. The original strict core and
positive $r_A$ still require enough signed slack. RH remains unproved.

## Project supplement: a uniform selected-source interval through 4.03e46

This is a project derivation from the named premises below, extending
(GL4) on one additional interval. The interval choice and rational
enclosures are project calculations, not results attributed to Nicolas's
manuscript or the other cited papers. This is a conditional ordinary
proof and application, without a literature-priority, Lean-certification,
or all-integer finite-verification claim.

### Keep the selected integer, exact clock and source premises

Suppose Robin's strict inequality fails at some integer above 5040.
By the [Caveney–Nicolas–Sondow reduction](../Arith/caveney2012sacaga.md#which-potentially-critical-robin-source-is-covered),
Theorems 4(ii) and 5(iii), select the **same least global maximizer**
$N>5040$ of $G(n)=\sigma(n)/(n\log\log n)$. Put

$$
A=\log N,\qquad L=\log A,\qquad T=\sqrt A L,\qquad
W(n)=\log\frac{\sigma(n)}n,\qquad \lambda=\frac1{AL}.
$$

The selected level is at least $e^\gamma$, so
$\Delta(N)=\gamma+\log L-W(N)\le0$. This $N$ is not the least
counterexample. Reuse the finite ladder ending in (GL4), with its
[Axler finite-stop premise](../notes/axler2023robin.md) and its cited
zero-free and density inputs, to obtain $A>(7/2)10^{46}$.

For comparison, at an arbitrary integer $n>5040$ use its own
$A=\log n$, $L=\log A$ and $\lambda=1/(AL)$, and define
$\Delta(n)=\gamma+\log L-W(n)$. Here primes and positive powers
are used in $P_{\rm pp}$, and the pressure maximum is over integers:

$$
\begin{aligned}
M(\lambda)&=\max_{m\in\mathbb Z_{\ge1}}\{W(m)-\lambda\log m\},&
d_n&=M(\lambda)-W(n)+\lambda A\ge0,\\
P_{\rm pp}(A)&=\sum_{p^j\le A}\frac1{jp^j},&
R(A)&=P_{\rm pp}(A)-\lambda\psi(A)-M(\lambda),\\
I_\psi(A)&=\int_A^\infty(\psi(t)-t)
                  \frac{1+\log t}{t^2\log^2t}\,dt.
\end{aligned}
$$

The existing pressure and tail identities give
$\Delta(n)=I_\psi(A)+R(A)+d_n$; $d_n$ remains in this all-integer
identity. At the selected $N$ alone, the
[same-source transport](../Analytic/polak2026finiterobinca.md#application-at-the-same-critical-source-and-clock)
gives $d_N=0$ and $R(A)=D^*(A)$, hence (G1). Its premises are explicit:
CNS Fact 1 and GA2 make $N$ proper, so $N/p\ge4>e$ for deletion;
[Mantovanelli's archived direct bridge](../Analytic/mantovanelli2026primeworkload.md#the-existing-prime-local-bridge)
at the exact price $\lambda$ gives the event-free CA optimizer;
the existing unrestricted-exponent
[SevenSmooth exclusion](../../Blueprint/D5/S3/Arith/Robin/SevenSmooth.md)
rules out support index $k\le4$; and
[Kalyabin's Theorem 2 endpoint conditions](../Analytic/kalyabin2026maximalgronwall.md)
give $P=P^+(N)<A<P^+$ and exponent one at $P$.
Thus primes $p\le A$ are exactly the actual support, every actual
exponent attains Polak's full-support minimum over $a\ge1$, and his
Proposition 6 has $z(N,A)=B_2(N,A)=0$. There is no transfer of this
zero defect to arbitrary integers.

Reuse (G6)–(G7), including Nicolas's effective Theorem 1.3 branch
$6.78$, whose exact $N^{(0)}$ threshold is paid above. The primorial
cutoff $x$, support endpoint $P$ and clock $A$ stay distinct: (G2)–(G5)
pay the absent-prime suffix by GA2 and use $\Sigma(N)=Z(N)$ from CA;
they do not assume common maximizers of $\Phi$ and $\Sigma$.

The analytic inputs are the full classical explicit formula and its
endpoint-inclusive Stieltjes identities, [Dusart v1](https://arxiv.org/pdf/1002.0442v1)
Theorem 5.2 and Proposition 3.2,
[Platt–Trudgian's verification through height $3000175332800$](https://arxiv.org/abs/2004.09765v1),
and the Hasanalizade–Shen–Wong full zero count used in
[(F3) and (Z4) of the Polak note](../Analytic/polak2026finiterobinca.md#reusing-the-complete-residual-envelope).
Keep $H=3\cdot10^{12}$, $c_0=2+\gamma-\log(4\pi)<0.05$ and
$S_2(H)=\sum_{\Im\rho>H}m_\rho/(\Im\rho)^2<1.48\cdot10^{-12}$.
The preceding project derivations (GE1)–(GE4), (GH1), (GJ1)–(GJ2)
and (GK1)–(GK6) are used with exactly these premises.
The cited finite Robin and zero-verification computations, analytic
proofs and density-table computations are not rerun here. The
Mantovanelli, Kalyabin, Polak and Nicolas inputs retain their stated
preprint/archive status; no complete independent primary-proof audit
or fresh SevenSmooth compilation is asserted. Polak's separate huge
finite sweep is not a premise of the added interval.

### Uniform arithmetic and Gamma enclosures

Assume, for contradiction, that the same selected clock satisfies

$$
\frac72\,10^{46}<A\le\frac{403}{100}\,10^{46},\qquad
\alpha=\frac{73}{50}\,10^{23}+\frac12
       =\frac{292000000000000000000001}{2}.
\tag{GM1}
$$

Use the whole law $C\sim\operatorname{Gamma}(\text{shape }\alpha,
\text{rate }\alpha)$, not scale $\alpha$. Its mean is one,
$\mathbb E(C-1)^2=1/\alpha$ and
$M_1=\mathbb EC^{-1}=\alpha/(\alpha-1)$. The shape is noninteger
and at least $4$, as required in (GK6). With the complete coefficient
$F_A(s)=s^{-1}\int_A^\infty u^{s-2}(1+\log u)/\log^2u\,du$, put

$$
H_\alpha(s)=\frac{\Gamma(\alpha+s-1)}
 {\Gamma(\alpha)\alpha^{s-1}},\qquad
Z_\alpha(A)=\sum_\rho m_\rho H_\alpha(\rho)F_A(\rho).
$$

Every actual nontrivial zero, both ordinate signs and all multiplicities
are included. The preceding absolute-convergence arguments justify this
sum; conjugate pairing makes it real. Criticality is used only for
$|\Im\rho|\le H$; the tail retains every actual $0<\Re\rho<1$.

On the **whole** interval (GM1),

$$
L>107,\qquad 10^{23}<\sqrt A<r:=\frac{251}{125}\,10^{23},\qquad
M_1<\frac{10001}{10000},\qquad
\frac{H^2}{2(\alpha+H)}>\frac{1541}{50}.
\tag{GM2}
$$

Indeed, $\log10>2.3$ and $\log(7/2)>1.25$ give $L>107$;
$r^2=4.032064\cdot10^{46}>4.03\cdot10^{46}$.
The moment and damping bounds are direct rational comparisons at
the fixed $\alpha$, with no sampling of $A$.

Dusart's stronger Theorem 5.2 row is exactly
$k=2$, $\eta_k=0.01$, $x_k=7713133853$. It applies to **every**
$t\ge A$ in (GM1). Proposition 3.2 includes all higher prime powers,
so the decreasing right side gives

$$
\begin{aligned}
\eta_0(A)&:=\sup_{t\ge A}\frac{|\psi(t)-t|}{t}\\
&\le\frac{0.01}{L^2}+1.00007A^{-1/2}+1.78A^{-2/3}\\
&<\frac{0.01}{107^2}+\frac{1.00007}{10^{23}}
                  +\frac{1.78}{10^{30}}<10^{-6}.
\end{aligned}
\tag{GM3}
$$

This stronger constant is used with its own effective threshold;
it is not assigned to the earlier $3.965$ row.

The directed (GK6) and the absolute (GJ2) now give

$$
\begin{aligned}
-T I_\psi(A)\le{}&T Z_\alpha(A)
 +(0.52+2\eta_0(A))\frac{\sqrt A}{\alpha}
 +400\sqrt A e^{-\alpha/60000}+\frac{5M_1}{\sqrt A},\\
T|Z_\alpha(A)|<{}&M_1(1+1/L)
 \left[1.054c_0+2(1.0001)\sqrt A S_2(H)
            e^{-H^2/[2(\alpha+H)]}\right].
\end{aligned}
$$

Centering in (GK6) occurs before splitting the whole Gamma law at
$[0.99,1.01]$. Its regular part uses (GM3) for all $t\ge A$;
its local residual is nonpositive against the positive prime-power
measure, including endpoint atoms. The $c<1$ local part below $A$
uses this sign, not an unprovided prime-error bound below $A$.
All outside scales are paid by (GK5). In particular, $cA<1$ and the
finite endpoint response in (GE3) are retained; (GE4) is used only
as a directed upper bound, not an absolute bound.

For $x>0$, $e^x>\sum_{j=0}^{149}x^j/j!$. Exact rational evaluation
at $x=1541/50$ gives $e^{1541/50}>(121/50)10^{13}$.
Also $\alpha/60000>10^{18}$ and $e^x>x^3/6$ give
$e^{\alpha/60000}>10^{53}$. Substituting these and (GM2)–(GM3)
gives the following complete rational allowances:

| Contribution | Rational upper allowance | Strict outward bound |
|---|---:|---:|
| Verified head with full coefficient remainder | $(10001/10000)(108/107)(1.054)(0.05)$ | $0.0532$ |
| All heights above $H$, both signs | $2(10001/10000)^2(108/107)r(1.48\cdot10^{-12})/[(121/50)10^{13}]$ | $0.0248$ |
| Centered regular and signed local payment | $(0.520002)r/\alpha$ | $0.7152$ |
| Every outside Gamma scale | $400r/10^{53}$ | $9\cdot10^{-28}$ |
| Complete elementary/trivial response, including $cA<1$ | $5(10001/10000)/10^{23}$ | $6\cdot10^{-23}$ |

For clarity, the first three rational allowances are respectively
$142304229/2675000000$,
$25079915230749/1011484375000000$, and
$208832803200000000000000/292000000000000000000001$.
Summing the rational allowances, or their strict outward bounds, yields

$$
\boxed{-T I_\psi(A)<0.79321\quad\text{throughout (GM1)}.}
\tag{GM4}
$$

The damping exponent $t^2/[2(\alpha+t)]$ increases for $t>0$;
the full $S_2(H)$ therefore pays every height above $H$ through infinity.
No tail real part is moved to $1/2$, and no sign or coefficient remainder
is omitted in passing from $T Z_\alpha$ to its absolute upper allowance.

### Transcendental enclosures and the strict core

All decimal constants here denote exact terminating rationals. The
load-bearing logarithms can be enclosed by the convergent positive
series, with $z=(y-1)/(y+1)$ and $1\le y\le2$,

$$
q_m(y)=2\sum_{j=0}^{m-1}\frac{z^{2j+1}}{2j+1},\qquad
0\le\log y-q_m(y)
\le\frac{2z^{2m+1}}{(2m+1)(1-z^2)}.
$$

This follows by integrating the geometric series for $1/(1-z^2)$;
each omitted denominator is at least $2m+1$.
Write any rational $y\ge1$ as $2^k v$, $1\le v<2$, and add
the brackets for $v$ and $k\log2$. With $m=64$ the resulting rational
comparisons give $\log2<0.6931472$, $\log10>2.3$ and
$\log(7/2)>1.25$, as used above. Squaring positive rational endpoints
gives $1.4142135<\sqrt2<1.4142136$.
Positive Taylor prefixes through degree 149 give
$e^{17}>2\cdot10^7$ and $e^{52}>10^{22}$, as well as the damping
comparison used in (GM4). These are analytic enclosures with explicit
remainders or one-sided positive prefixes, not floating-point values.

For the existing core function $\mathcal E$ in (G7), differentiation
gives

$$
\mathcal E'(L)=\frac{(2+\log2)\sqrt2}{L^2}
-\frac{13.56}{L^3}+\frac{2.67}{6}e^{-L/6}
 +\left(L-2+\frac5{2L}+\frac5{L^2}\right)e^{-L/2}>0
\qquad(L\ge26).
$$

The first two terms have sum greater than $(2L-13.56)/L^3>0$;
the other terms are positive. Thus $L>107$ gives
$\mathcal E(L)>\mathcal E(107)$ uniformly. Since $107/6>17$ and
$107/2>52$, the outward enclosures just proved yield

$$
\begin{aligned}
\mathcal E(107)>{}&2(1.4142135)
 -\frac{(2+0.6931472)(1.4142136)}{107}
 +\frac{6.78}{107^2}-2.00014\\
&-\frac{2.67}{2\cdot10^7}
 -\frac{214+5/107}{10^{22}}>0.79328.
\end{aligned}
\tag{GM5}
$$

The last comparison is exact rational arithmetic. Together with (G6),
this is a whole-interval strict lower bound for the core at the same $N$.

### Contradiction and remaining boundary

By (G1), (GM4) and (GM5),

$$
\boxed{T\Delta(N)=T I_\psi(A)+T D^*(A)
 >0.79328-0.79321=\frac7{100000}>0
 \quad\text{throughout (GM1)}.}
\tag{GM6}
$$

This contradicts the selected source's $\Delta(N)\le0$.
Together with (GL4), it proves the conditional restriction
$\log N>(403/100)10^{46}$ for the same least global maximizer.
The open lower endpoint is supplied by (GL4), and the upper endpoint
is included by the uniform enclosures; there is no uncovered clock.

This excludes a selected-source interval, not every integer below
$\exp((403/100)10^{46})$, and gives no least-counterexample bound.
For arbitrary $n$ the exact $d_n$ remains. At surviving selected clocks,
the full signed requirement (G9), with its positive elementary
correction, remains unpaid. A substantive formal frontier is the
directed centered-Gamma transport (GK6), including the endpoint atoms,
whole mean-one law and $cA<1$ branch; scalar wrappers of the rational
budget do not close it. No such formal theorem is supplied here.
The RH/Robin research target remains active and unproved.

## Project application: every integer on the same finite clock interval

The existing effective reserve supplies a stronger quantifier on (GM1).
This application combines (GM4) with
[FIB §§249–250, especially (250.6)](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#250-无穷远锚定将有效导数预算变为点值间隔).
It is a conditional ordinary derivation from those project sources,
without a new numerical endpoint, literature-priority claim or Lean
certification. Keep the unrestricted pressure over **all** positive
integers, including one, and the actual $R(A)$ and $d_n$ defined above.

Let $n$ be **any integer** such that

$$
\frac72\,10^{46}<A=\log n\le\frac{403}{100}\,10^{46},\qquad
L=\log A,\qquad T=\sqrt A L.
\tag{GAI1}
$$

Retain the classical prime-power pressure and tail identities and all
the analytic suppliers used in (GE1)–(GE4), (GH1), (GJ1)–(GJ2) and
(GK1)–(GK6), with the explicit Dusart inputs, finite zero criticality
through $H=3\cdot10^{12}$, $c_0<0.05$ and the complete
$S_2(H)<1.48\cdot10^{-12}$ enclosure. These are the same full Gamma,
centering, dilation, convergence and actual-zero-multiset premises
stated above. The reserve also uses Dusart v1 Theorem 5.2's precise row
$(k,\eta_k,x_k)=(2,1/5,3594641)$ from FIB §249.
The source proofs and computations remain named external or
project-level analytic inputs; their complete primary verification is
not supplied by this application.

### The signed estimate does not require source selection

Although (GM1) was first introduced inside a selected-source
contradiction, its analytic estimate (GM4) holds for every real $A$
in that interval. Indeed, (GM2) is uniform arithmetic; the stronger
Dusart row $(2,0.01,7713133853)$ and Proposition 3.2 give (GM3)
for every $t\ge A$. The centered directed comparison (GK6), including
the endpoint atoms and all outside Gamma scales, and the complete
zero-response bound (GJ2) therefore give the displayed five allowances
for each such $A$. Their sum is strictly less than $0.79321$.
Neither comparison uses a CA optimizer, CNS selection, properness,
$d_n=0$ or (GM5). All actual zeros above $H$ retain their real parts,
both ordinate signs and multiplicities. Consequently

$$
-T I_\psi(A)<\frac{79321}{100000}
\quad\text{for every real }A\text{ in (GAI1)}.
\tag{GAI2}
$$

The open lower endpoint and included upper endpoint are exactly those
of (GM1); no extension below or above them has been made.

### The effective actual reserve pays this same clock

FIB (250.6) applies to the same unrestricted $R(x)$ for every
$x\ge e^{100}$. Its numerical start comes from the explicit Dusart
row and the event-safe derivative comparison in §249. The boundary
condition at infinity is paid by §93.2's finite reserve bound
$0\le R(x)\le5x^{-2/3}+2/x+1/[2(\sqrt x-1)]\to0$.
It does not require an unspecified start for the asymptotic reserve
expansion, or the sign of the common tail that cancels in (250.1).
At $x=A$, (GM2) gives $L>107>100$, hence

$$
T R(A)>2(\sqrt2-1)
 -\frac{2(\sqrt2-1)+\sqrt2\log2}{L}
 +\frac{L}{(L+2)^3}.
\tag{GAI3}
$$

The bracket being subtracted is positive. Thus replacing $L>107$
by $107$ gives a valid lower bound. Use the strict rational enclosures

$$
\rho_-:=\frac{2828427}{2000000}<\sqrt2
 <\rho_+:=\frac{1767767}{1250000},\qquad
\log2<\ell_+:=\frac{2166085}{3125000}.
$$

The root inequalities follow by exact squaring; the logarithm bound
follows by the positive series
$\log2=2\sum_{j\ge0}(1/3)^{2j+1}/(2j+1)$ with its explicit
geometric remainder. Taking the lower root in the positive term and
the upper root and logarithm in the subtracted bracket yields

$$
\begin{aligned}
T R(A)&>Q+\frac{L}{(L+2)^3},\\
Q&:=2(\rho_--1)
 -\frac{2(\rho_+-1)+\rho_+\ell_+}{107}
 =\frac{67838284064811}{83593750000000}
 >\frac{8115}{10000}.
\end{aligned}
\tag{GAI4}
$$

This preserves the additional positive barrier term. No equality
case at $L=107$ or asymptotic numerical start is being assumed.

### Retain the defect for every integer

Use the exact identity $\Delta(n)=I_\psi(A)+R(A)+d_n$ at this
integer's own clock. Since $T>0$ and $d_n\ge0$, (GAI2) and (GAI4) give

$$
\begin{aligned}
T\Delta(n)
&>\frac{1530885627311}{83593750000000}
  +\frac{L}{(L+2)^3}+T d_n\\
&>\frac{1829}{100000}+T d_n>0.
\end{aligned}
\tag{GAI5}
$$

Thus Robin's strict inequality holds for every integer in (GAI1),
under the stated analytic premises. The defect has not been set to
zero or transferred from a selected source. The known small-clock
case $n=5041$, where $I_\psi(\log5041)+R(\log5041)<-1/200$,
lies outside this interval and still requires its actual defect.

The CNS reduction, properness, exact-price CA bridge, SevenSmooth
exclusion, Kalyabin endpoint conditions, Nicolas's effective $6.78$
branch and absent-prime ladder are not premises of (GAI5).
They remain premises of the earlier argument selecting the least
global maximizer and placing its clock above $(7/2)10^{46}$.
That delivered conditional lower bound, ultimately
$\log N>(403/100)10^{46}$, retains its scope. This application proves
neither a least-counterexample bound nor an all-integer verification
below the interval; Polak's separate huge finite sweep is not used.
The full signed all-integer target beyond this finite interval, its
formal analytic suppliers and RH remain unproved.

## Project application: a seven-eighths ceiling lowers the actual-sample cut

The original full coefficient (M1), estimate (H5) and
“A smaller moving cut from joint density and zero-free support” can be
consumed on the actual first-prime event samples. With the additional
seven-eighths ceiling recorded in the
[OpenAI source interface](../Analytic/openai2026quasirh.md), this gives a
smaller complete remainder at the detector's sample-moment scale. It is a
conditional ordinary application of existing sources, with no new
zero-free theorem or Lean certification.

The extra premise is precisely

$$
\beta\le\frac78\quad\text{for every actual nontrivial zeta zero}.
\tag{ASC1}
$$

Equality remains allowed. The pinned upstream declaration is
[`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean).
Its conclusion is used as an external analytic input; its complete
transitive proof closure has not been compiled or independently certified
here. Project Lean 4.33.0 and upstream Lean 4.34.1 remain distinct. The
stronger conditional completed-probe ceiling in the linked project note
is not used.

### Every event retains its own clock and complete response

Let $\mathcal P_X$ consist of the first-prime events $p$ with
$X\le b_p<3X$, using the largest inclusive optimizer $C_{b_p}$.
Put $A_p=\log C_{b_p}$, $L=\log X$ and $T(x)=\sqrt x\log x$.
The original full-layer and PNT suppliers, as used in the
[event-state construction](../Analytic/mantovanelli2026primeworkload.md),
give, for sufficiently large $X$,

$$
A_p\in[X/2,4X],\qquad m=|\mathcal P_X|\ll X/L.
\tag{ASC2}
$$

All higher and simultaneous layers remain in $C_{b_p}$; $A_p$ is not
identified with the event price $b_p$. Keep the original complete formula
$U_p=-T(A_p)I_\psi(A_p)$ and its elementary correction $r_{A_p}$.
For $H=X^{3/10}$ use the exact split

$$
U_p=V_p(H)+e_p(H),\quad
V_p(H)=T(A_p)\sum_{|\gamma|\le H}m_\rho F_{A_p}(\rho)+r_{A_p},\quad
e_p(H)=T(A_p)\sum_{|\gamma|>H}m_\rho F_{A_p}(\rho).
\tag{ASC3}
$$

These sums range over distinct actual zeros with multiplicity $m_\rho$
exactly once. Both ordinate signs and all actual real parts are retained.
Every zero exactly at $H$ stays in the head. The full pole and trivial-zero
correction stays in $r_{A_p}$.

### Consume the existing density layer at its new endpoint

For $5/8\le\sigma\le7/8$, reuse the existing
Chourasiya–Simonič density supplier with
$d(\sigma)=3(1-\sigma)/(2-\sigma)$. Its inclusive count and exclusive
suffix give

$$
\sum_{\gamma>H,\,\beta\ge\sigma}\frac{m_\rho}{\gamma^2}
\ll H^{d(\sigma)-2}(\log H)^3,
\quad H\ge3\cdot10^{12}.
$$

Under (ASC1), the original layer decomposition, including the full-count
base layer, therefore gives, uniformly for $x\in[X/2,4X]$,

$$
\sum_{|\gamma|>H}\frac{m_\rho x^{\beta-1/2}}{\gamma^2}
\ll \frac{x^{1/8}\log H}{H}
+\log x(\log H)^3\int_{5/8}^{7/8}
 x^{\sigma-1/2}H^{d(\sigma)-2}\,d\sigma.
\tag{ASC4}
$$

Set $f(\sigma)=(\sigma-1/2)\log x+(d(\sigma)-2)\log H$.
Since $d'(\sigma)=-3/(2-\sigma)^2$, $H=X^{3/10}$ gives
$f'(\sigma)\ge(13/45)L+O(1)$ throughout this interval.
For sufficiently large $X$ it is at least $(13/90)L$.
The integral in (ASC4) is thus at most
$90e^{f(7/8)}/(13L)$. Here $d(7/8)=1/3$, so
$e^{f(7/8)}\ll X^{3/8}H^{-5/3}=X^{-1/8}$.
This cancels the displayed outer logarithm. The original complete
coefficient bound (H5), with its remainder retained, yields

$$
|e_p(H)|\ll X^{-7/40}L+X^{-1/8}L^3
\quad\text{for every actual sample }p\in\mathcal P_X.
\tag{ASC5}
$$

### The full sample remainder pays the detector scale

Using (ASC2) and $(a+b)^2\le2a^2+2b^2$ gives

$$
\sum_{p\in\mathcal P_X}|e_p(H)|^2
\ll X^{13/20}L+X^{3/4}L^5
=o\!\left(Q(X)\right),\qquad
Q(X)=\frac{X^{3/4}e^{L^{1/4}/2}}{L^2}.
\tag{ASC6}
$$

Indeed, the quotient is bounded by
$O(X^{-1/10}L^3e^{-L^{1/4}/2}+L^7e^{-L^{1/4}/2})\to0$.
For this exact split, the $1$-Lipschitz map $z\mapsto(z-1/2)_+$ gives

$$
\left|\|(U_p-1/2)_+\|_2-\|(V_p(H)-1/2)_+\|_2\right|
\le\|e(H)\|_2=o(\sqrt{Q(X)}).
\tag{ASC7}
$$

Thus all head-tail cross effects are paid at the norm level, without
decorrelation. Also $\#\{p:|e_p(H)|>\eta\}=o(Q(X))$ for each fixed
$\eta>0$. The new cut is smaller than $X^{5/16}$ by the factor
$X^{-1/80}\to0$, under the additional premise (ASC1).

The complete signed head and a sufficient one-sided actual-sample
occupancy or positive-excess bound remain unpaid. The original signed
Landau suffix (J4) is retained; its stated errors alone do not furnish
this sample-square estimate at $H=X^{3/10}$.
No growing event-dependent selector is inserted into a fixed-parameter
OpenAI correlation theorem. No numerical common starting $X$, transfer
of the $4.03\cdot10^{46}$ global-maximizer bound, least-counterexample
bound, full Robin/RH proof, or official acceptance is supplied.

## Project application: the same actual reserve extends the clock to 4.23

The global complete-response estimates (GK6) and (GJ2), together with
the actual effective reserve (GAI3)–(GAI4), extend the all-integer
interval (GAI1). This is a conditional ordinary application of the same
project sources, without a new zero computation, external zero ceiling,
numerical reserve-asymptotic start or Lean certification.

Let $n$ be any integer with its own clock

$$
\frac72\,10^{46}<A=\log n\le\frac{423}{100}\,10^{46},
\qquad L=\log A,\qquad T=\sqrt A L.
\tag{GAJ1}
$$

Retain all the analytic premises of the preceding effective-reserve
application: unrestricted pressure and tail identities, the full
classical explicit formula, endpoint-inclusive Stieltjes conventions,
convergence and PNT inputs, the complete Gamma product and whole-law
moments, and all elementary responses, including scales with $cA<1$.
The exact Dusart v1 Theorem 5.2 rows remain
$(2,0.01,7713133853)$ for the global error and
$(2,1/5,3594641)$ for the reserve, with Proposition 3.2's full
higher-prime-power correction and the coarse $k=0$ bound.
Keep criticality through $H=3\cdot10^{12}$, the positive reciprocal
identity $c_0<0.05$ and the complete $S_2(H)<1.48\cdot10^{-12}$.
The actual reserve remains the unrestricted one over all positive
integers, including one, from FIB §§249–250 and its finite §93.2
anchor. These source proofs and computations remain named analytic
premises; their complete primary certification is not supplied here.

### Evaluate the global formulas at the larger endpoint

Keep the identical noninteger shape and rate

$$
\alpha=\frac{292000000000000000000001}{2},\qquad
C\sim\operatorname{Gamma}(\text{shape }\alpha,\text{rate }\alpha).
$$

Set $r=(2057/1000)10^{23}$. Exact squaring gives
$r^2=4.231249\cdot10^{46}>4.23\cdot10^{46}$, so
$\sqrt A<r$ even at the included upper endpoint of (GAJ1).
The lower endpoint still gives $L>107$ and $\sqrt A>10^{23}$.
Thus the global domain $A\ge e^{78}$, noninteger $\alpha\ge4$ of
(GK6), and $L>78$ of the full-coefficient (GJ2), both apply.
The interval subsequently used to illustrate (GJ2) does not restrict
its global proof. In particular, the old interval estimate (GM4) is
not being extrapolated.

The unchanged shape, height and lower endpoint retain

$$
M_1<\frac{10001}{10000},\qquad
\frac{H^2}{2(\alpha+H)}>\frac{1541}{50},\qquad
\eta_0(A)<10^{-6}.
$$

Here (GM3)'s proof uses the stronger Dusart row for every $t\ge A$
and only the lower clock endpoint; it therefore remains uniform on
(GAJ1). Reuse the positive exponential-series enclosures
$e^{1541/50}>(121/50)10^{13}$ and
$e^{\alpha/60000}>10^{53}$. Inserting these into the actual global
formulas gives the complete five allowances:

| Contribution | Exact rational upper allowance |
|---|---:|
| Verified head, full coefficient | $(10001/10000)(108/107)(1.054)(0.05)$ |
| All tail heights, both signs | $2(10001/10000)^2(108/107)r(1.48\cdot10^{-12})/[(121/50)10^{13}]$ |
| Centered regular and signed local payment | $(0.520002)r/\alpha$ |
| Every outside Gamma scale | $400r/10^{53}$ |
| Full elementary response, including $cA<1$ | $5(10001/10000)/10^{23}$ |

Every terminating decimal denotes an exact rational. Let $U_{423}$
be their sum. All actual tail-zero real parts, multiplicities, heights
and ordinate signs remain, as do the coefficient remainder, endpoint
atoms and centering before the whole Gamma law is split. Consequently

$$
-T I_\psi(A)<U_{423}\quad\text{throughout (GAJ1)}.
\tag{GAJ2}
$$

### Pay the same integer with its actual reserve and defect

The unchanged (GAI4), anchored by the finite reserve bound and valid
for $L>107$, gives

$$
T R(A)>Q_R+\frac{L}{(L+2)^3},\qquad
Q_R=\frac{67838284064811}{83593750000000}.
$$

Exact subtraction of the complete five-row sum yields

$$
Q_R-U_{423}
=\frac{22837901643254399996290102708491463199999986623442401}
 {78110000000000000000000267500000000000000000000000000000}
>\frac1{4000}.
\tag{GAJ3}
$$

Use the same-clock identity
$\Delta(n)=I_\psi(A)+R(A)+d_A(n)$, with its actual
$d_A(n)\ge0$. Equations (GAJ2)–(GAJ3) therefore give

$$
\boxed{T\Delta(n)>\frac1{4000}
 +\frac{L}{(L+2)^3}+T d_A(n)>0}
\quad\text{for every integer in (GAJ1)}.
\tag{GAJ4}
$$

No CA selection, zero-defect transfer or finite sweep is needed for
this interval consequence. Under the additional unchanged original
source-selection and lower-clock chain that gives
$\log N>4.03\cdot10^{46}$ for the same least global maximizer of
$G(n)=\sigma(n)/(n\log\log n)$ over $n>5040$ under Robin failure,
(GAJ4) excludes its remaining interval up to $4.23\cdot10^{46}$.
Thus that same conditional selected restriction improves to

$$
\log N>4.23\cdot10^{46}.
\tag{GAJ5}
$$

The CNS/properness, exact-price CA, SevenSmooth, Kalyabin eligible
endpoint, Axler finite-stop, Nicolas $6.78$ and original lower-clock
ladder premises retain their original role in that preceding chain.
This is not a least-counterexample bound or all-integer verification
below the interval. The unbounded signed Robin/RH target remains unproved. This application
supplies no new Lean/kernel or complete formal analytic verification.

## Project application: bounded log-uniform smoothing reaches 7.2

This project derivation combines the original complete Robin response and
its deterministic centered kernels with a finite positive law built from
the existing uniform/sinc library. It extends the same all-integer clock
interval while preserving the actual unrestricted FIB reserve and each
integer's defect. It is a conditional ordinary proof, with the primary
analytic suppliers retained below; no Lean/kernel or full RH proof is
claimed. This supplement is project work, not an additional result
attributed to Nicolas's manuscript.

In this section **NC** denotes the preceding material in this source,
**FIB** denotes `docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md`,
and **PK** denotes `Library/Analytic/polak2026finiterobinca.md`. The
original sources and cited Fourier declarations used for this derivation
were read at project revision
`7f52221f2e23da81475058d5b5b6620e68709401`; the present supplement
reuses their definitions and conventions.

### 1. Exact theorem and premises

Write `g` for Euler's constant, to distinguish it from zero ordinates. Put

\[
 A_-=\tfrac72 10^{46},\quad A_+=\tfrac{36}{5}10^{46},\quad
 H=3\cdot10^{12},\quad k=23,\quad a=\frac5{2H}=\frac1{1200000000000}.
\]

For every real \(A_-<A\le A_+\), put \(L=\log A\), \(T=\sqrt A L\).
Under the premises below the complete signed integral satisfies

\[
 -T I_\psi(A)<U<Q_R-\frac3{1000},\qquad
 Q_R=\frac{67838284064811}{83593750000000}.
\tag{GAK1}
\]

For **each** integer \(n\) whose own clock \(A=\log n\) lies in that
interval, at its own price \(\lambda=1/(AL)\),

\[
 T\left[g+\log L-\log\frac{\sigma(n)}n\right]
 >\frac3{1000}+\frac{L}{(L+2)^3}+T d_A(n)>0.
\tag{GAK2}
\]

The required primary analytic inputs remain conditional in this conditional derivation:

1. The classical zeta explicit formula, in its endpoint-inclusive
   Stieltjes/half-value convention, and the integration and limiting
   conventions used in NC (GR5)–(GR8). Its constant term is \(-\log(2\pi)\)
   and its trivial-zero term is \(-\tfrac12\log(1-x^{-2})\). The exponential
   integral has the horizontal-from-left-infinity convention described in
   NC's Akatsuka Proposition 4.4 application. No lateral \(i\pi\) is added.
2. Effective unconditional PNT/Mertens convergence supplying the exact
   tail identity and an absolute constant \(C_\psi\) with
   \(|\psi(x)-x|\le C_\psi x/\log^2(2+x)\) for all \(x>0\), as in NC (GR3).
   These are logarithmic-error inputs, not a square-root error or an
   inferred short-interval theorem.
3. The actual nontrivial zero multiset \(\rho=\beta+i\gamma\),
   \(0<\beta<1\), with multiplicities \(m_\rho\), conjugation symmetry,
   the classical convergent zero count and identity
   \(\sum_\rho m_\rho/[\rho(1-\rho)]=c_0=2+g-\log(4\pi)<1/20\).
4. Platt–Trudgian's finite verification (through height 3000175332800)
   supplying \(\beta=1/2\) only for \(|\gamma|\le H\), and the full positive-
   ordinate bound
   \(S_2(H)=\sum_{\gamma>H}m_\rho/\gamma^2<1.48\cdot10^{-12}\).
   PK (F3), (Z4) identify the Hasanalizade–Shen–Wong zero-count supplier.
   Neither computation nor the complete primary proof is rerun here.
5. Dusart arXiv:1002.0442v1, Theorem 5.2, the exact rows
   \((2,0.01,7713133853)\) and \((2,1/5,3594641)\), and Proposition 3.2
   \(0\le\psi(t)-\vartheta(t)<1.00007\sqrt t+1.78t^{1/3}\).
   The classical Chebyshev estimate \(\vartheta(y)\le2y\) is also used;
   NC supplies it from the same source's \(k=0\) row. Finite computations
   underlying these sources remain external premises.

The complete coefficient bounds and the deterministic transport below are
derived, rather than assumed as law-general versions of Gamma results.
The reserve's numerical start and infinity anchor are also traced and
derived below. The all-integer theorem needs no CA, CNS, properness,
SevenSmooth, Kalyabin, Axler finite Robin stop or Nicolas effective
envelope premise. Those are extra conditions solely for the final
same-global-maximizer corollary in section 10.

### 2. Construct the entire positive law and compute exact moments

Use the finite product probability space of \(k\) copies of the uniform
law on \([-a,a]\). Let \(U_j\) be its coordinate variables, let
\(Y=\sum_{j=1}^k U_j\), and write

\[
 S(z)=\begin{cases}\sinh z/z&z\ne0,\\1&z=0,\end{cases}\quad
 d=k\log S(a),\quad C=e^{Y-d}.
\]

The original project uniform interval density is nonnegative, integrable
and of integral one. Its transform convention is
\(\int f(x)e^{izx}\,dx\). The existing theorem
`InfiniteSincProduct.uniformIntervalFourierLaplace_eq_complexSinc`
at frequency \(-iz\) gives

\[
 \mathbb E e^{zU_j}=\operatorname{complexSinc}(-iaz)=S(az).
\]

Alternatively the integral is \((2a)^{-1}\int_{-a}^a e^{zx}dx\), with
the removable value at \(z=0\). For each complex \(z\), its absolute
value is bounded on the finite product domain. Finite-product Fubini
and independence therefore give \(\mathbb E e^{zY}=S(az)^k\).
There is no infinite-product limit in this construction.

For \(C^z=e^{z\log C}\), with the real logarithm of \(C>0\),

\[
 H_C(s):=\mathbb E C^{s-1}
 =S(a(s-1))^k e^{-(s-1)d}.
\tag{GAK3}
\]

Every complex moment exists, and this is an entire function. In particular

\[
 \mathbb EC=1,\quad \mathbb EC^{-1}=S(a)^{2k},\quad
 \operatorname{Var} C=\mathbb E(C-1)^2
 =\frac{S(2a)^k}{S(a)^{2k}}-1=(a\coth a)^k-1.
\tag{GAK4}
\]

The last equality uses \(S(2a)=S(a)\cosh a\). The mean is exactly one
on the **whole** law, before any restriction to scales.

Let \(x=a^2\in(0,1)\). Positive series give

\[
 1\le S(a)=\sum_{n\ge0}\frac{x^n}{(2n+1)!}\le\frac1{1-x}.
\]

The coefficients in

\[
 \cosh a-S(a)=\frac{a\cosh a-\sinh a}{a}
 =\sum_{n\ge1}\frac{2n}{(2n+1)!}x^n
\]

start at \(1/3\). The ratio of coefficient \(n+1\) to coefficient
\(n\) is exactly \(1/[2n(2n+3)]\le1/10\). Thus all coefficients
are at most \(1/3\), and division by \(S(a)\ge1\) gives

\[
 0\le a\coth a-1\le\frac{x}{3(1-x)}=:b.
\]

For a nonnegative number \(b\) with \(kb<1\),
\((1+b)^k=\sum_{j=0}^k\binom kj b^j\le\sum_{j\ge0}(kb)^j\),
since \(\binom kj\le k^j\). Consequently

\[
 \operatorname{Var}C\le V_*:=\frac{kx}{3-(k+3)x},\qquad
 \mathbb EC^{-1}\le (1-x)^{-2k}\le M_*:=\frac1{1-2kx}.
\tag{GAK5}
\]

The inverse bound follows from \((1-x)^{2k}\ge1-2kx>0\), so
reciprocals have the displayed direction. All denominators are positive.

Furthermore \(0\le d\le kx/(1-x)\), because
\(-\log(1-x)=\log(1+x/(1-x))\le x/(1-x)\). Every point in the
support obeys

\[
 |\log C|\le\epsilon:=ka+\frac{kx}{1-x}<\frac1{1000}.
\]

The elementary inequalities \(e^{-\epsilon}\ge1-\epsilon\) and
\(e^\epsilon\le(1-\epsilon)^{-1}\), the latter by positive series,
give the stronger exact rational comparisons

\[
 \frac{99}{100}<1-\epsilon\le C\le\frac1{1-\epsilon}<\frac{101}{100}.
\tag{GAK6}
\]

These are support bounds, not high-probability bounds. No outside-law
event exists; in particular \(CA>1\) on the entire interval.

### 3. All-frequency sine bound and actual complex normalization

For all real \(v\) with \(|v|\ge5/2\),

\[
 \frac{|\sin v|}{|v|}\le\frac14.
\tag{GAK7}
\]

To prove it on \([5/2,\pi]\), \(\sin v/v\) is decreasing on
\((0,\pi)\): the numerator \(v\cos v-\sin v\) of its derivative
vanishes at zero and has derivative \(-v\sin v<0\). At \(5/2\),
the sine Taylor prefix through degree nine is
\(P_9=\sum_{j=0}^4(-1)^j(5/2)^{2j+1}/(2j+1)!<5/8\).
The omitted alternating tail starts negative and its terms decrease:
already the ratio from degree nine to degree eleven is
\((5/2)^2/(10\cdot11)<1\), and later ratios are smaller. This
justifies the upper bound even though the very first Taylor terms need
not decrease. On \([\pi,4]\),
\(|\sin v|\le v-\pi<v-3\le v/4\), by the derivative bound
\(|\cos v|\le1\), \(\pi>3\), and \(v\le4\). For \(v\ge4\)
use \(|\sin v|\le1\). Reflection proves the negative axis. The
classical \(3<\pi<4\) fixes these adjoining bands.

Now take the **actual** \(u=\beta-1\in(-1,0)\) and \(|\gamma|\ge H\).
The identity

\[
 |\sinh(a(u+i\gamma))|^2=\sinh^2(au)+\sin^2(a\gamma)
\]

and \(|a(u+i\gamma)|\ge|a\gamma|\ge5/2\) imply

\[
 |S(a(u+i\gamma))|
 \le\frac14+\frac25\sinh a
 \le\frac14+\frac25\frac{a}{1-x}.
\]

Here \(\sqrt{b^2+c^2}\le|b|+|c|\), \(|u|<1\), and the positive
hyperbolic series were used. The normalization is retained:
\(e^{-ud/k}=S(a)^{-u}\le S(a)\le(1-x)^{-1}\). Therefore (GAK3) gives

\[
 |H_C(\beta+i\gamma)|\le q_*^k<q^k,\quad
 q_*:=\frac{1/4+(2/5)a/(1-x)}{1-x}<q:=\frac{2501}{10000}.
\tag{GAK8}
\]

This is uniform for **all** \(0<\beta<1\) and every ordinate in the
tail, both signs. It does not substitute \(u=-1/2\).
For every zero, including the head, let \(\theta=1-\beta\in(0,1)\).
Positivity and concavity of \(t^\theta\) give

\[
 |H_C(\rho)|\le\mathbb EC^{-\theta}
 \le(\mathbb EC^{-1})^\theta\le M_*.
\tag{GAK9}
\]

This bound needs no head criticality. Criticality will be used separately
only to bound the head coefficient.

### 4. Consume the original complete coefficient and deterministic dilations

Retain

\[
 D(t)=\psi(t)-t,\quad k_0(t)=\frac{1+\log t}{t^2\log^2t},\quad
 w(t)=\frac{1+\log t}{\log^2t},\quad
 F_A(s)=\frac1s\int_A^\infty t^{s-2}w(t)dt.
\tag{GAK10}
\]

Thus \(F_A=A^{s-1}/(sL)-\operatorname{Ei}((s-1)L)\) in the source
convention. No replacement by just its leading term is made. For
\(h(t)=tw'(t)=-(\log t+2)/\log^3t\), two integrations by parts give
NC (H1), independently:

\[
 F_A(s)=\frac{w(A)A^{s-1}}{s(1-s)}
 +\frac{h(A)A^{s-1}+\int_A^\infty t^{s-1}h'(t)dt}{s(1-s)^2}.
\tag{GAK11}
\]

All boundary terms at infinity vanish for \(0<\Re s<1\),
\(h'(t)=2(\log t+3)/(t\log^4t)>0\), and
\(\int_A^\infty h'(t)dt=-h(A)\). The numerator of the second term
is consequently at most \(2|h(A)|A^{\beta-1}\) in modulus. This yields
the complete NC (GJ1) estimate

\[
 T|F_A(\beta+i\gamma)|
 \le(1+1/L)\frac{A^{\beta-1/2}}{|\rho||1-\rho|}
 \left(1+\frac{2(L+2)}{L(L+1)|1-\rho|}\right).
\tag{GAK12}
\]

NC (H5) is a compatible derived \(\gamma^{-2}\) leading-plus-error
envelope; it need not be assumed instead of (GAK11). For finite endpoints
\(R\ge A\), integration by parts using \(w'\le0\) gives

\[
 |F_{A,R}(s)|\le\frac{2w(A)A^{\beta-1}}{|s||1-s|}.
\tag{GAK13}
\]

This is NC (U2), uniform in \(R\), with the complete finite coefficient.
For \(|\gamma|\ge4\), it is at most \(2w(A)/\gamma^2\).

For a deterministic \(c>0\), define exactly the NC (GR5)–(GR7) objects

\[
 J_c(A)=-\frac1c\int_A^\infty D(cu)k_0(u)du,\quad
 Z_c(A)=\sum_\rho m_\rho c^{\rho-1}F_A(\rho),\quad r_c=J_c-Z_c.
\tag{GAK14}
\]

On our whole support, \(c\ge.99\) and \(cA>1\). The PNT premise
gives a constant independent of \(c\) with
\(|D(cu)|/c\le K u/\log^2u\) for \(u\ge A\). This follows directly
from \(\log(2+cu)\ge\log u+\log(.99)\ge\tfrac12\log u\).
After multiplication by \(k_0(u)\), the majorant is a constant times
\(1/[u\log^3u]\), which is integrable. Hence absolute Fubini proves
\(J_\mu:=\mathbb EJ_C\) exists and may be averaged inside its integral.

The entire **integrated coefficient** series can also be averaged
absolutely. Indeed (GAK13) bounds its high part uniformly by
\(2w(A)\gamma^{-2}\), since
\(c^{\beta-1}A^{\beta-1}=(cA)^{\beta-1}\le1\). The finitely many
lower zeros are uniformly bounded on the compact scale support. The
zero count supplies summability. Thus

\[
 Z_\mu:=\mathbb EZ_C
 =\sum_\rho m_\rho H_C(\rho)F_A(\rho),\quad
 J_\mu=Z_\mu+r_\mu,\quad r_\mu=\mathbb Er_C.
\tag{GAK15}
\]

This absolute exchange is for the integrated \(F_A\) series. It is
**not** an absolute interchange of the unsmoothed \(x^\rho/\rho\)
explicit-formula series with an infinite integral. For (GAK14)'s explicit
formula, take the source's finite-endpoint/truncated formula first,
then its integrated convergence and (GAK13); the uniform summable bound
pays the scale-endpoint limit, exactly as in GR7. The half-value change
at prime powers affects no Lebesgue integral. This analytic limiting
input remains one of the named premises in section 1.

Substitution \(x=cu\) in the full explicit formula gives the exact
elementary response for \(cA\ge1\):

\[
 r_c(A)=\frac{\log(2\pi)}{cAL}
 +\frac12\int_{cA}^\infty\log(1-x^{-2})
       \frac{1+\log(x/c)}{x^2\log^2(x/c)}dx.
\tag{GAK16}
\]

The second term is nonpositive and integrable. In fact our support has
\(cA\gg1\), so there is no logarithmic endpoint singularity; the
source also treats the integrable endpoint \(cA=1\). Since
\(\log(2\pi)<2\), this gives

\[
 T r_\mu\le\frac{2\mathbb EC^{-1}}{\sqrt A}
 \le\frac{5M_*}{\sqrt A}.
\tag{GAK17}
\]

The last relaxed allowance agrees with the candidate. It is directed,
not an absolute bound. The full pole/constant and trivial-zero terms
have been retained in (GAK16). NC (GE2) proves the bound for all \(c>0\),
including its separate \(cA<1\) branch using \(D(x)=-x\), GR6 and U2;
our law assigns that branch zero probability by (GAK6). GR8's unquantified
absolute constant is not used for the numerical budget.

Conjugation of actual zeros and (GAK3), (GAK10) shows \(Z_\mu\) is real.
The signed equality at \(c=1\) is \(J_1=-I_\psi(A)\), including its
original full elementary correction. The transport next compares this
entire \(J_1\) with \(J_\mu\); one must not drop or separately
double-count \(r_1\).

### 5. Derive law-centered transport, preserving all atoms

Set

\[
 h_A(t)=\frac1{\max(A,t)\log\max(A,t)},\quad
 w_c(t)=c^{-1}h_A(t/c),\quad
 a_A(t)=\begin{cases}-1/(AL)&0<t\le A,\\1/(t\log^2t)&t>A.\end{cases}
\]

NC (GP4)'s deterministic estimates give
\(\int|w_c-h_A|(d\psi+dt)\le K(c+c^{-1})/L\). For completeness,
below \(A\max(1,c)\) bound the two weights by their constants and
use \(\psi(t)\ll t\); above that point their absolute difference is

\[
 \frac{|\log c|}{t\log t\log(t/c)}
 \le\frac{|\log c|(1+|\log c|/L)}{t\log^2t}.
\]

Partial summation with \(\psi(t)\ll t\) makes the latter summable.
The constants are uniform on \([.99,1.01]\). Also
\(\int a_A dt=0\), and \(\int|a_A|(d\psi+dt)<\infty\).
Changing variables in finite integrals shows
\(\int(w_c-h_A)dt=0\); its upper endpoint difference is
\(\log\log(R/c)-\log\log R\to0\).

Integration by parts, with the PNT boundary at infinity and \(D(t)=-t\)
below 1, gives the deterministic GP5 identity

\[
 J_1-J_c=\int(w_c-h_A)d\psi=\int(w_c-h_A)dD.
\]

Only absolutely convergent differences are used. Define
\(B_c=w_c-h_A-(c-1)a_A\). Absolute Fubini and the exact **whole-law**
mean \(\mathbb E(C-1)=0\) give

\[
 J_1-J_\mu=\mathbb E\int B_C(t)dD(t).
\tag{GAK18}
\]

This is the law-general version of NC (GS6), derived before splitting.
It requires no Gamma identity.

For \(.99\le c\le1.01\), let \(e=c-1\), and split \(B_c=b_c+v_c\):

\[
 b_c(t)=\begin{cases}
 e^2/(cAL),&0<t\le A,\\
 [t(\log t-\log c)]^{-1}-(t\log t)^{-1}-e/(t\log^2t),&t>A.
 \end{cases}
\tag{GAK19}
\]

For \(t>A\), let \(v=\log t\), \(r=v-\log c\). The second
dilation derivative of \(1/[t(v-\log c)]\) and its \(t\)-derivative are

\[
 \frac{2-r}{tc^2r^3},\qquad \frac{r^2-6}{t^2c^2r^4}.
\]

Throughout the segment from 1 to \(c\), \(c\ge.99\),
\(r\ge v-.01\ge.999v\), and \(r>2\), \(r^2>6\), since
\(L>107>78\). Their moduli are at most
\(1.024/(t v^2)\) and \(1.024/(t^2v^2)\), respectively.
Taylor's integral remainder, whose weight integrates to \(e^2/2\),
therefore proves the deterministic GK2 bounds

\[
 |b_c(t)|\le\frac{.512e^2}{t\log^2t},\qquad
 |b'_c(t)|\le\frac{.512e^2}{t^2\log^2t}.
\]

Use the actual right-continuous \(D(A)\), including its atom. Partial
summation with the change of formula at \(A\) gives

\[
 \int b_c dD=
 [e^2/(cAL)-b_c(A+)]D(A)-\int_A^\infty D(t)b'_c(t)dt.
\]

The upper boundary vanishes. With
\(\eta_0(A)=\sup_{t\ge A}|D(t)|/t\), the three contributions give

\[
 \left|\int b_c dD\right|
 \le\frac{\eta_0(A)e^2}{L}
 [100/99+.512+.512/L]\le\frac{2\eta_0(A)e^2}{L}.
\tag{GAK20}
\]

Only values \(t\ge A\) of the global error were used. The contribution
below \(A\) is the constant part integrated exactly to \(D(A)\).

The residual \(v_c\) vanishes off the cutoff interval. Its exact values
are those of \(B_c-b_c\), not an arbitrary almost-everywhere version:

* For \(c>1\), on \(A<t<cA\) it equals
  \(1/(cAL)-1/[t\log(t/c)]\), and \(v_c(A)=v_c(cA)=0\).
* For \(c<1\), on \(cA<t\le A\) it equals
  \(1/[t\log(t/c)]-1/(cAL)\), and \(v_c(cA)=0\).
* For \(c=1\), it is zero everywhere.

The function \(1/[t\log(t/c)]\) decreases throughout these intervals,
so \(v_c\le0\), including its actual endpoint values. Thus the
nonnegative atomic measure \(d\psi\) gives

\[
 \int v_c dD=\int v_c d\psi-\int v_cdt\le-\int v_cdt.
\]

This retains an atom at \(A\) for \(c<1\) with its nonpositive sign;
an atom at \(cA\) has zero coefficient. For \(c>1\), the possibly
discontinuous right limit at \(A\) does not change the actual atom
value zero. There is no replacement of \(d\psi\) by a density.

On the whole cutoff interval \(t\ge.99A\),
\(\log(t/c)\ge L-.01\). Hence

\[
 \left|\frac{d}{dt}\frac1{t\log(t/c)}\right|
 \le\frac{1.034}{A^2L}.
\]

The worst ratio is bounded at \(L=78\) by
\(.99^{-2}[78/(78-.01)][1+1/(78-.01)]<1.034\); both logarithmic
factors decrease with \(L\). Since \(v_c(cA)=0\), a triangular
Lebesgue-area bound proves the deterministic GK4 inequality

\[
 \int v_c dD\le\frac{1.034(A|e|)^2}{2A^2L}<\frac{.52 e^2}{L}
\tag{GAK21}
\]

when \(e\ne0\); the non-strict form holds also at zero.
NC (GS9)'s bounded variation ensures the local integrals exist, but
its short-interval error bound is not used. In particular no error
estimate below \(A\) is needed to pay the \(c<1\) residual.

Averaging (GAK20)–(GAK21) in (GAK18), using the entire support and (GAK4), yields

\[
 T(J_1-J_\mu)\le(.52+2\eta_0(A))\sqrt A\operatorname{Var}C.
\tag{GAK22}
\]

There is no outside-scale cost and no conditional mean. We have thus
rederived the necessary GK3/GK4 averaging; NC's Gamma-specific GK1 or
GK6 is not an assumption. Combining (GAK15), (GAK17), (GAK22), and \(J_1=-I_\psi\),

\[
 -T I_\psi(A)\le T|Z_\mu(A)|
 +(.52+2\eta_0(A))\sqrt A V_*+\frac{5M_*}{\sqrt A}.
\tag{GAK23}
\]

### 6. Pay the entire actual zero spectrum and full remainder

For every zero,

\[
 \Re\frac1{\rho(1-\rho)}
 =\frac{\gamma^2+\beta(1-\beta)}{|\rho(1-\rho)|^2}>0.
\]

On the verified head it is the positive real weight
\(1/(\gamma^2+1/4)\). The classical identity for \(c_0\) therefore
bounds the head sum of absolute weights by \(c_0\); its tail cannot
cancel a positive head contribution. On the unverified tail,
\(|\rho||1-\rho|\ge\gamma^2\), so the complete tail weight is at
most \(2S_2(H)\). The factor two counts the negative ordinates by
conjugation with the same multiplicities, rather than creating another
zero population.

For \(L>78\), (GAK12)'s full remainder factor on the head is below 1.054,
since \(|1-\rho|\ge1/2\) and
\(4(L+2)/(L(L+1))\le4\cdot80/(78\cdot79)<.054\).
On the tail \(|1-\rho|\ge|\gamma|>H\), so the factor is below 1.0001.
The rational function \((L+2)/(L(L+1))\) decreases for positive \(L\).
Equations (GAK8), (GAK9), (GAK12) thus give, for the **complete** series,

\[
 T|Z_\mu(A)|<(1+1/L)
 [1.054 M_*c_0+2(1.0001)\sqrt A S_2(H)q^{23}].
\tag{GAK24}
\]

The head uses \(A^{\beta-1/2}=1\). Only there is criticality assumed.
The tail retains its actual \(\beta\), before the valid upper bound
\(A^{\beta-1/2}\le\sqrt A\). Its \(q^{23}\) already includes the
actual-real-part normalization, so no additional \(M_*\) factor is
required in that tail term. All heights through infinity are included.
This derives the replacement for the Gamma damping in GJ2; neither
GJ2 nor a Gamma moment law is invoked.

### 7. Uniform rational budget for every real clock

Use exact integer fractions throughout. For
transcendental enclosures use, for \(1\le y\le2\) and
\(z=(y-1)/(y+1)\),

\[
 q_m(y)=2\sum_{j=0}^{m-1}\frac{z^{2j+1}}{2j+1},\quad
 0\le\log y-q_m(y)
 \le\frac{2z^{2m+1}}{(2m+1)(1-z^2)}.
\tag{GAK25}
\]

This follows by integrating the geometric series for \((1-z^2)^{-1}\)
and bounding every omitted denominator by \(2m+1\). Divide a rational
\(y\ge1\) by powers of two to reach \([1,2)\), and add its multiple
of the enclosure for \(\log2\). At \(m=64\), the exact fractions give
\(\log10>2.3\) and \(\log(7/2)>1.25\). Thus on the **whole** interval,

\[
 L>46(2.3)+1.25=107.05>107,\quad \sqrt A>10^{23},\quad
 A^{2/3}>10^{30}.
\]

The stronger Dusart row applies to **every** \(t\ge A\), because even
the lower endpoint exceeds 7713133853. Proposition 3.2 and the decreasing
error functions give, independently of the upper endpoint,

\[
 \eta_0(A)\le\frac{.01}{L^2}+1.00007A^{-1/2}+1.78A^{-2/3}
 <\frac{.01}{107^2}+\frac{1.00007}{10^{23}}+
   \frac{1.78}{10^{30}}<10^{-6}.
\tag{GAK26}
\]

This is NC (GM3)'s lower-clock argument, not a restriction to its old
Gamma upper endpoint. Set \(r=(671/250)10^{23}=2.684\cdot10^{23}\).
Its square is \(7.203856\cdot10^{46}>A_+\). Hence
\(\sqrt A<r\) even at the included upper endpoint.

Define the following exact positive rational numbers:

\[
\begin{split}
 U_h&=\frac{108}{107}\frac{527}{500}\frac1{20}M_*,\\
 U_t&=2\frac{108}{107}\frac{10001}{10000}r
                \frac{37}{25\cdot10^{12}}\left(\frac{2501}{10000}\right)^{23},\\
 U_v&=\frac{260001}{500000}rV_*,\qquad
 U_e=\frac{5M_*}{10^{23}},\qquad U=U_h+U_t+U_v+U_e.
\end{split}
\tag{GAK27}
\]

Each replacement in (GAK23)–(GAK24) increases a positive allowance. All bounds
are uniform for real \(A\), not values sampled at endpoints. Exact rational substitution proves

\[
 U_h<.053193,\quad U_t<.011502,\quad U_v<.743074,\quad U_e<6\cdot10^{-23},
\]

and, using the full fractions rather than these rounded displays,

\[
 .003755<Q_R-U<.003756,
 \qquad Q_R-U>\frac3{1000}.
\tag{GAK28}
\]

The displayed allowances are exact rational definitions, so the final
comparison is an integer cross-multiplication. Positive-series enclosures
justify the logarithmic constants before this subtraction; they do not
certify the primary analytic suppliers.

### 8. Reuse the same effective unrestricted reserve

Use exactly the unrestricted pressure, including the integer one,
\[
 M(\lambda)=\max_{m\ge1}[\log(\sigma(m)/m)-\lambda\log m],
 \qquad R(x)=P_{\rm pp}(x)-\frac{\psi(x)}{x\log x}
              -M(1/(x\log x)).
\tag{GAK29}
\]
FIB §§87/98/111 provide the finite prime-prefix maximization, all ties,
and the nonnegative reserve. Its finite §93.2 bound and (250.3) give
\[
 0\le R(x)\le5x^{-2/3}+2/x+1/[2(\sqrt x-1)]\longrightarrow0.
\]
The event-safe argument in FIB §§249–250, already consumed in NC
(GAI3)–(GAI4), uses the exact Dusart reserve row
$(2,1/5,3594641)$, higher reference layers, paired left/right states,
and this zero-at-infinity anchor. Its explicit start is $x\ge e^{100}$;
it does not differentiate a reserve asymptotic or transfer the finite
Robin value at 5040. Reuse its complete conclusion (250.6):
\[
 R(x)>\frac{c_R+c_2/\log x}{\sqrt x\log x}
             +\frac1{\sqrt x(\log x+2)^3},
 \quad c_R=2(\sqrt2-1),\quad
 c_2=-2(\sqrt2-1)-\sqrt2\log2.
\tag{GAK36}
\]
At the present $x=A$, $L>107$ pays that start. Exact squaring and
(GAK25)'s positive log series certify
\[
 \rho_-=2828427/2000000<\sqrt2<\rho_+=1767767/1250000,
 \qquad \log2<\ell_+=2166085/3125000.
\]
Use the lower root in the positive term and upper root/logarithm in
the subtracted term, and then $L>107$. Thus the same actual reserve gives
\[
 TR(A)>Q_R+\frac{L}{(L+2)^3},\qquad
 Q_R=2(\rho_--1)-\frac{2(\rho_+-1)+\rho_+\ell_+}{107}
 =\frac{67838284064811}{83593750000000}.
\tag{GAK37}
\]
This is reuse of the paid lower-clock reserve, with its original full
assumptions and event conventions, rather than a new reserve theorem.

### 9. Keep each integer's actual defect

The PNT/Mertens tail identity, FIB 87.3 and NC's full-response formula,
is

\[
 I_\psi(A)=g+\log L-\frac1L-P_{\rm pp}(A)+\lambda\psi(A).
\tag{GAK38}
\]

It also follows by differentiating this continuous finite expression:
its derivative is \(-D(A)k_0(A)\), its prime-power jumps cancel,
and its limit is zero by the named PNT/Mertens input.
Define the actual nonnegative price defect

\[
 d_A(n)=M(\lambda)-W(n)+\lambda\log n\ge0.
\]

For \(A=\log n\), adding (GAK29), (GAK38) and this defect, with
\(\lambda A=1/L\), proves exactly

\[
 \Delta(n):=g+\log L-W(n)=I_\psi(A)+R(A)+d_A(n).
\tag{GAK39}
\]

The pressure and \(R(A)\) have not been replaced by a different
optimizer or a restricted maximum. Equations (GAK23)–(GAK28), (GAK37), (GAK39)
prove (GAK2), for every integer in the stated interval, including its
upper endpoint. Since \(T>0\), \(\Delta(n)>0\) is precisely
\(\sigma(n)<e^g n\log\log n\). No defect was set to zero, including
for a non-CA integer. There is no inference for every smaller integer
or for an unbounded clock interval.

### 10. Same least global maximizer corollary and remaining boundaries

For this separate corollary retain **all** original selection and
lower-clock suppliers, as spelled out in NC's section beginning at
line 6743 and its earlier G1–G9, GH/GL finite ladder:

* Under a Robin violation, CNS Theorems 4(ii), 5(iii) select the same
  least integer \(N>5040\) attaining the **global maximum** of
  \(G(n)=\sigma(n)/(n\log\log n)\), at level at least \(e^g\).
* CNS Fact 1 and GA2 give properness and \(N/p\ge4>e\) for deletion.
  Mantovanelli's archived direct tangent bridge supplies regular CA
  optimality at the exact price \(1/(A\log A)\). A support-based
  CA-family price is not substituted.
* The unrestricted-exponent SevenSmooth exclusion removes support
  index at most four. Kalyabin's stated endpoint hypotheses then give
  \(P=P^+(N)<A=\log N<P^+\), with exponent one at \(P\).
  This fixes the actual full-support minimization, \(d_A(N)=0\), and
  its core identity. None of these zero-defect statements are moved to
  arbitrary integers.
* Axler's cited finite stop through the \(K\)th primorial,
  \(K=999999476056\), supplies the initial clock. The exact Nicolas
  \(N^{(0)}\) threshold is paid by
  \(\log N^{(0)}<66(1000000007)<K/2<A\), so the effective
  6.78 branch is retained. GA2 pays the absent-prime suffix while
  keeping the primorial cutoff, support endpoint and clock distinct.
* The original Nicolas/Dusart core and finite signed-response ladder,
  including the original finite-height, density and zero-free suppliers
  where used, puts this **same** selected \(A\) above
  \((7/2)10^{46}\). Their source proofs, finite computations and
  preprint/archive statuses are unchanged conditional suppliers.

If that same \(N\) also had \(A\le7.2\cdot10^{46}\), (GAK2) would give
\(\Delta(N)>0\), contradicting its global counterexample level.
Therefore, with this complete unchanged extra chain,
\(\log N>7.2\cdot10^{46}\). This is **not** a least-counterexample
bound. The new all-integer interval argument itself does not require
this extra chain, and does not independently audit all its primary proofs.

For fixed \(a,k\), \(V_*>0\) and \(q^k>0\). Both the transport
and unverified-tail allowances grow with \(\sqrt A\). Thus the
fixed-law construction gives no unbounded signed Robin estimate,
full RH proof or official acceptance.

### 11. Library reuse and actual missing formal content

The immutable project toolchain is 4.33.0; its manifest pins Mathlib to
`db584cd6d46c92f209a44c0f1c829460d327499d`. Source inspection was of
the original three entire Lean modules, the related DyadicComplexDecay
module, and their complete Blueprints,
not their runtime evidence. The Blueprints' existing machine-check
claims are source descriptions, not new certifications by this derivation.

The reusable project declarations are:

* `InfiniteSincProduct.uniformIntervalDensity`, its nonnegativity,
  integrability and integral-one facts, and
  `uniformIntervalFourierLaplace_eq_complexSinc`, for the one-factor
  complex identity at frequency \(-iz\).
* `DyadicConvolutionDensity.dyadic_partial_convolution_fourierLaplace`
  and its tilt/convolution proof pattern, with actual nonnegativity,
  mass-one and compact-support results. The public finite theorem
  specifically uses dyadic widths and \(n+1\) factors; it is not already
  the 23 equal-width law. Its finite induction/Fubini machinery can be
  reused or factored through a general finite-width bridge. One must
  not silently instantiate equal widths in a dyadic-only signature.
* `DyadicTransformDecay.sinc_product_decay_bound` and
  `dyadic_density_transform_decay` concern the infinite dyadic density
  on **real frequencies**. They provide the existing finite-prefix
  norm argument and real sinc bounds, but do not directly prove the
  normalized finite-law bound for all actual \(\beta-1+i\gamma\).
* The related `DyadicComplexDecay.dyadic_transform_explicit_strip_decay`
  already proves explicit inverse-power decay for the infinite dyadic
  density at all complex frequencies. Its proof supplies the existing
  uniform-factor exponential/inverse bounds and the normalized-prefix
  argument. That general dyadic strip theorem should also be reused;
  its signature and constants do not themselves give the equal-width,
  mean-one law's sharper normalized factor \(.2501\) above \(H\).

Neither infinite dyadic nonvanishing nor all-order real decay is needed
as a premise of the present finite law. Do not duplicate these existing
uniform/sinc facts, or introduce an independent complex-sinc definition.

The genuinely missing consumed formal bridge comprises the finite
equal-width law and its pushforward by \(e^{Y}/S(a)^{23}\), its exact
whole-law centering and moments, the normalized complex-strip tail
bound, and the endpoint-inclusive deterministic centered transport
with absolute Fubini for the **full** \(F_A\) series and exact elementary
response. The unrestricted-pressure identity, event-safe reserve
start/infinity anchor, actual per-integer defect and conditional primary
supplier interfaces must accompany that bridge for the complete theorem.
A scalar wrapper of (GAK28), or an unproved law-general invocation of
Gamma GK6/GJ2, would not consume those obligations.

The OpenAI/math checkout at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, toolchain 4.34.1, is not a
premise of this derivation. Its differently pinned closure is not claimed
to have compiled against this project toolchain.

The reasoning discipline was to check the positive law, complete
deterministic response and same actual reserve before combining their
scalar budgets; to retain signed identities until a directed bound
permits absolute values; and to distinguish an ordinary conditional
deduction from independent certification of primary analytics.

## Project application: complete event cells sample the own-size clock

Keep (ASC1)–(ASC7), the actual first-prime sample $\mathcal P_X$,
its inclusive largest optimizers $N_p=C_{b_p}$ and their own clocks
$A_p=\log N_p$. The full event construction in the
[Mantovanelli interface](../Analytic/mantovanelli2026primeworkload.md#actual-sample-and-finite-support)
supplies the underlying states. The application below uses ordinary
bounded-variation endpoint quadrature; it is not a new quadrature,
zero-density or prime-distribution theorem. It is a conditional
project deduction, without Lean certification or a historical
originality claim.

Put $L=\log X$, $H=X^{3/10}$ and $J_X=[X/2,4X]$. For each fixed
$X$, keep $H$ fixed while varying $A\in J_X$, and define

$$
V_X(A)=\sqrt A\log A\sum_{|\operatorname{Im}\rho|\le H}
 m_\rho F_A(\rho)+r_A,
\qquad f_X(A)=(V_X(A)-1/2)_+^2.
\tag{OCQ1}
$$

Here $F_A$ is the complete coefficient (M1), and $r_A$ is the complete
elementary correction after (G9). All distinct actual zeros retain
their multiplicities and real parts; both ordinate signs and every
zero exactly at $H$ remain in the head. Conjugate pairing makes $V_X$
real. At each actual sample, $V_X(A_p)=V_p(H)$ from (ASC3).

### Use every activation layer in the size partition

If there are no layer events in $[X,3X)$, the selected sample sum
is zero and the inequality is immediate. Otherwise enumerate all
distinct event prices $e_1<\cdots<e_k$ in this band. Let $B_i=\log C_{e_i}$ be the post-event size after all
ties, and let $B_0$ be the size immediately before $e_1$. Local
finiteness and the complete activation rule give

$$
B_i-B_{i-1}=\sum_{\tau_{p,j}=e_i}\log p=:h_i>0.
\tag{OCQ2}
$$

Thus $B_0<\cdots<B_k$ is a partition in the actual size coordinate,
even though the prices need not be equally spaced. If $X$ itself
is an event, its whole jump belongs to the first cell. An event at
$3X$ is excluded. Higher-layer events and every tied layer stay in
this partition.

For a first-prime event at $e_i=b_p$, the existing calibration
$p<b_p<p+1$ gives $p\ge X-1\ge X/2$ eventually. Hence

$$
h_i\ge\log p\ge L-\log2.
\tag{OCQ3}
$$

First-prime event prices are strictly increasing in $p$, so at most
one selected sample uses a given cell. The $j$th layer price is also
strictly increasing in its prime, so a tied event has at most one
prime for each fixed $j$.

Reuse the activation cutoff from
[FIB Proposition 420.2](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#420-既有大间隙链的实际素层隔离与根位置的联合缺口):
every layer at a price below $3X$ has
$p^j<Q_X=3X\log(3X)/\log2$. In particular
$j\le d_X=\lfloor\log Q_X/\log2\rfloor$. For the complete tied jump,

$$
\mu_X:=\max_i h_i
\le\log Q_X\sum_{j=1}^{d_X}\frac1j
=O(L\log L)=O(L^2).
\tag{OCQ4}
$$

The existing full-clock estimate
$\log C_b=\psi(b)+O(\sqrt b[\log(2b)]^{5/2})$ and PNT give
$\log C_b=b+o(b)$ uniformly for $b\in[X,3X]$.
Together with (OCQ4), they put $B_0$ and every $B_i$ inside $J_X$
eventually. This uses the entire optimizer clock, not just (ASC2)'s
first-prime endpoints, and makes no substitution $A_p=b_p$.

For quadrature, directly reuse S. S. Dragomir, *The Ostrowski integral
inequality for mappings of bounded variation*, *Bulletin of the
Australian Mathematical Society* **60** (1999), 495–508,
[DOI 10.1017/S0004972700036662](https://doi.org/10.1017/S0004972700036662),
Corollary 7, equations (5.16)–(5.17), printed p. 507. Its arbitrary
partition is $(B_i)_{i=0}^k$, its sample in the $i$th cell is the
right endpoint $B_i$, and its mesh is $\mu_X$. The published error
bound is mesh times total variation; for absolutely continuous $f$,
that variation is $\int|f'|$. No generic quadrature proof is repeated.

For any nonnegative absolutely continuous $f$ on $J_X$, this supplier
and (OCQ3) give

$$
\begin{aligned}
\sum_{p\in\mathcal P_X}f(A_p)
&\le\frac1{L-\log2}\sum_{i=1}^k h_i f(B_i)\\
&\le\frac1{L-\log2}\left(
 \int_{B_0}^{B_k}f(A)\,dA+
 \mu_X\int_{B_0}^{B_k}|f'(A)|\,dA\right)\\
&\le\frac1{L-\log2}\left(
 \int_{J_X}f(A)\,dA+
 \mu_X\int_{J_X}|f'(A)|\,dA\right).
\end{aligned}
\tag{OCQ5}
$$

Both enlarged integrands are nonnegative. An empty selected sample
has left side zero; if there are no events, no partition is needed.
This estimate uses no prime-gap bound, sampling independence or
separate supremum payment for higher-layer mass: those layers supply
cells in the same partition.

### The complete moving coefficient pays the mesh error

The finite head in (OCQ1) has a fixed zero set at each $X$. Differentiating
the full (M1) integral with respect to its lower endpoint gives

$$
\partial_A F_A(\rho)
=-\frac{A^{\rho-2}(1+\log A)}{\rho\log^2A}.
\tag{OCQ6}
$$

Under the named ceiling (ASC1), directly reuse the complete
coefficient bound (GH2), the finite reciprocal-square
mass $\mathcal C_\zeta$ in (GE1), and the classical zero count
$\sum_{|\gamma|\le H}m_\rho/|\rho|=O(\log^2(2H))$. They give,
uniformly on $J_X$,

$$
|V_X(A)|=O(X^{3/8}),\qquad
|V_X'(A)|=O(X^{-5/8}L^2).
\tag{OCQ7}
$$

The full elementary response remains in this differentiation.
Its exact formula after (G9) gives
$r_A=O(A^{-1/2})$ and $r_A'=O(A^{-3/2})$, including the
trivial-zero integral. These contributions fit (OCQ7).
The positive-part square is $C^1$, including at $V_X=1/2$, with
$f_X'=2(V_X-1/2)_+V_X'$. Thus

$$
\int_{J_X}|f_X'(A)|\,dA=O(X^{3/4}L^2).
\tag{OCQ8}
$$

Substituting into (OCQ5) gives the own-clock sampling interface

$$
\boxed{\sum_{p\in\mathcal P_X}(V_p(H)-1/2)_+^2
\le\frac1{L-\log2}\int_{J_X}(V_X(A)-1/2)_+^2\,dA
 +O(X^{3/4}L^3).}
\tag{OCQ9}
$$

The coarse error is sufficient: relative to (ASC6)'s unchanged
$Q(X)$, its quotient is
$O(L^5e^{-L^{1/4}/2})\to0$. No refinement of the generic quadrature
theorem or new tail calculation is needed for this rate.

### The original fixed-exponent consumer and its remaining signed input

The proposed sufficient analytic input is still

$$
\int_{J_X}(V_X(A)-1/2)_+^2\,dA=o(LQ(X)).
\tag{OCQ10}
$$

This input is required along all sufficiently large scales carrying
the original source; a bound only on an unrelated subsequence does
not supply that quantifier. It is not established by (OCQ7), the zero ceiling, finite zero
verification, PNT or quadrature. Indeed, the unsigned bound (OCQ7)
only gives $O(X^{7/4})$ for this integral, which does not pay
(OCQ10). This route still lacks a sufficient directed estimate of the same
actual zero response; no independent phase or modified arithmetic source is
introduced.

If (OCQ10) were supplied, (OCQ9) and the already paid head-tail
norm transfer (ASC7) would give

$$
\sum_{p\in\mathcal P_X}(U_p-1/2)_+^2=o(Q(X)).
\tag{OCQ11}
$$

To identify its actual-source consumer, keep the original particular
fixed $0<\eta<1/2$ and power surplus supplied by the
[Caveney persistence application](../Arith/caveney2012sacaga.md#a-wider-actual-price-interval-for-the-same-supplied-power-excess),
where that exponent is denoted $\eta'$. Reuse the actual first-prime
count (R6) in the
[Stadlmann interface](../Analytic/stadlmann2022meansquaregaps.md#the-existing-uniform-prime-count-gives-a-stronger-source-specific-count).
On every scale carrying the same selected source, there are

$$
\gg\frac{X^{1-\eta/2}e^{L^{1/4}/2}}{L}
\tag{OCQ12}
$$

samples in $\mathcal P_X$ whose same actual $N_p=C_{b_p}$ satisfies
$\log G(N_p)-\gamma>\delta X^{-\eta}$, for the fixed positive
$\delta$ in that persistence application. The original exponent is
not decreased or reselected.

The argument does not transfer the original selected integer's
event-free, own-price, zero-defect properties to these post-event
integers. Instead consume
the already preserved unrestricted integer identity

$$
\Delta(n)=I_\psi(\log n)+R(\log n)+d_n,
\qquad d_n\ge0,
\qquad \Delta(n)=\gamma-\log G(n).
\tag{OCQ13}
$$

At $n=N_p$, its own clock and the unrestricted sufficiently large
reserve $R(A_p)>0$ supplied in (GAI3)–(GAI4) give

$$
U_p=T(A_p)\bigl(\log G(N_p)-\gamma+R(A_p)+d_{N_p}\bigr)
\ge T(A_p)\bigl(\log G(N_p)-\gamma\bigr).
\tag{OCQ14}
$$

Keep $d_{N_p}$; it is not set to zero. By (ASC2), each sample in
(OCQ12) has $U_p\gg X^{1/2-\eta}L\to\infty$ and hence $U_p\ge1$
eventually. Each contributes at least $1/4$ to (OCQ11). The ratio of
the lower count (OCQ12) to $Q(X)$ is
$\gg X^{1/4-\eta/2}L\to\infty$, contradicting (OCQ11) on the
same unbounded source scales.

Thus the displayed implication retains the original fixed-exponent
source and all post-event layers. It does not obtain (OCQ10), the
original one-sided $I_\psi$ estimate or RH. Standard quadrature and
the existing persistence count supply interfaces, not the missing
continuous signed-head bound. No new generic theorem, repeated
prime-count proof, parameter optimization or numerical replay is
claimed as mathematical progress.


## Project application: actual monotone layers at a shorter successor

This is a **repo-derived ordinary derivation**, not a compiled result. Its
substantive additional estimate is the whole weighted actual second-layer
increment and its one-sided combination below (candidate M6–M7, labelled
MS6–MS7 here to distinguish the earlier Mellin formulas). The unrestricted
pressure, packet identity, first-cutoff location and second-cutoff scale are
reused. The bounded source comparison does not certify literature priority.
The prior independent ordinary audit used the same model family; it is
design evidence, not a same-round peer review, diverse-model consensus,
Pro review, official acceptance or Lean/kernel evidence.

The original project sources are pinned at
`7f52221f2e23da81475058d5b5b6620e68709401`: this note's G1–G9 and PH
pressure section; [FIB §§85, 87, 98, 111, 247.4 and 249](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md);
and [ZE/5040's unrestricted/restricted pressure Theorem 3.2, own-price
Theorem 6.1 and equation (19), and actual-cutoff Definition 7.1/Theorem 8.1](../../docs/develop/theory/ZECKENDORF_EULER_5040.md).
The [Mantovanelli workload note](../Analytic/mantovanelli2026primeworkload.md)
identifies the primary Zenodo 22014299, version 1.0.0, manuscript SHA-256
`8208445c84c6cafc971a6f2a0637b06715a783f680de80d2ed3bb4a3be503d65`:
§4 `thm:direct-bridge`, Theorem 5.2 `thm:packet-identity`, and
Proposition 7.6 `prop:moment-workload` are existing inputs. Its packet
theorem has two regular selfmatching endpoints; the arbitrary endpoint
used here requires the retained concavity correction.

### Same actual state, finite support and endpoint correction

For \(x>1\), put

\[
f(x)=\log\log x,\qquad \lambda(x)=\frac1{x\log x},\qquad
w(x)=-\lambda'(x)=\frac{\log x+1}{x^2(\log x)^2}>0.
\]

For primes \(p\) and integers \(k\ge1\), define

\[
\beta_{p,k}=\log\left(1+\frac1{p+\cdots+p^k}\right),\quad
r_{p,k}=\frac{\beta_{p,k}}{\log p},\quad
a_p(x)=\#\{k\ge1:r_{p,k}>\lambda(x)\},
\]

\[
N_x=\prod_p p^{a_p(x)},\qquad
K_k(x)=\sum_{p:r_{p,k}>\lambda(x)}\log p,\qquad
K(x)=\sum_{k\ge1}K_k(x)=\log N_x.
\]

Every equality layer is excluded. For \(1<a\le b\), the common support
including possible ties is

\[
L_b=\{(p,k):r_{p,k}\ge\lambda(b)\}.
\]

Since \(0<r_{p,k}<1/(p^k\log p)\), membership implies

\[
p^k\log p<b\log b,\qquad p<b,\qquad 2^k\log2<b\log b.
\]

Thus \(L_b\) is finite. The decreasing price makes all actual layer sets
increase: \(K_k\) and \(K\) are finite step functions on \([a,b]\), and

\[
N_a\mid N_b,\qquad
\frac{N_b}{N_a}=\prod_p p^{a_p(b)-a_p(a)}\in\mathbb N.
\]

Finite sum/integral interchange holds on the whole interval with this
common support. Simultaneous events retain each layer's full \(\log p\)
weight; activation positions are the actual ones, not reference prime
powers.

Write \(W(n)=\log(\sigma(n)/n)\), \(G(n)=(\sigma(n)/n)/(\log\log n)\),
so \(\log G(n)=W(n)-f(\log n)\) for \(n>e\). Reuse the unrestricted
finite positive-part pressure

\[
S(\lambda)=\max_{n\ge1}(W(n)-\lambda\log n),\qquad
D(x)=\gamma+f(x)-\lambda(x)x-S(\lambda(x)).
\]

On \([a,b]\), reuse the exact finite expression

\[
S(\lambda(x))=\sum_{(p,k)\in L_b}\log p\,(r_{p,k}-\lambda(x))_+.
\]

It is absolutely continuous and gives \(D'(x)=(x-K(x))w(x)\) off the
finitely many events.
At the strict optimizer, with \(Y=K(x)>1\),

\[
\log G(N_x)=\gamma-D(x)+C_x(Y),\qquad
C_x(Y)=f(x)+\lambda(x)(Y-x)-f(Y)\ge0.
\]

Fix an actual **strict stable selfmatch** \(A>2\), meaning that \(A\) is
event-free and \(K(A)=A\), and set

\[
B=A+H,\qquad H>0,\qquad X=K(B)\ge A.
\]

Concavity gives \(C_B(X)\ge0\), with equality exactly when \(X=B\).
Integrating the existing pressure derivative yields

\[
\log\frac{G(N_B)}{G(N_A)}
=\int_A^B[K(t)-t]w(t)\,dt+C_B(X). \tag{MS0}
\]

This holds even if \(B\) is an event. If all ties at \(B\) were included,
write \(J_B=\sum_{r_{p,k}=\lambda(B)}\log p\) and \(X^+=X+J_B\).
Their reward is exactly \(\lambda(B)J_B\), giving the same integral with

\[
\log G(N_B^+)-\log G(N_B)=C_B(X^+)-C_B(X).
\]

Below the endpoint is consistently the strict \(N_B\). Neither \(X=B\)
nor zero own-price defect at the different clock \(X\) is assumed.

For any real \(A>2,H>0\), put \(\rho_A(u)=w(A+u)/w(A)\), and define

\[
\begin{aligned}
T_\theta(A,H)&=\int_0^H[\theta(A+u)-\theta(A)-u]\rho_A(u)\,du,\\
U_2(A,H)&=\int_0^H[K_2(A+u)-K_2(A)]\rho_A(u)\,du,\\
U_{\ge3}(A,H)&=\int_0^H\sum_{k\ge3}[K_k(A+u)-K_k(A)]\rho_A(u)\,du,\\
E_1(A,H)&=\int_0^H[K_1(A+u)-K_1(A)-\theta(A+u)+\theta(A)]\rho_A(u)\,du.
\end{aligned}
\]

Here \(\theta(t)=\sum_{p\le t}\log p\) uses the weak prime endpoint.
Subtracting the complete initial state \(K(A)=A\) gives the exact identity

\[
\log\frac{G(N_B)}{G(N_A)}
=w(A)[T_\theta+U_2+U_{\ge3}+E_1]+C_B(X). \tag{MS1}
\]

The literal finite \(U_{\ge3}\ge0\) follows pointwise from actual layer
monotonicity. It remains in every comparison.

The existing first cutoff solves

\[
\frac{\log(1+1/q_1(x))}{\log q_1(x)}=\lambda(x),\qquad x-1<q_1(x)<x
\quad(x>2).
\]

The inequalities follow from \(\log(1+t)<t\) and

\[
\log(1+1/(x-1))>1/x,\qquad \log(x-1)<\log x.
\]

Consequently the exact first-layer endpoint correction is

\[
\delta_1(x)=\theta(x)-K_1(x)
=\sum_{q_1(x)\le p\le x}\log p,\qquad 0\le\delta_1(x)\le\log x.
\]

The closed interval has length less than one and contains at most one
integer. A prime at either \(q_1(x)\) or \(x\) is included in this
correction. Direct differentiation gives

\[
\frac{w'(x)}{w(x)}=\frac1x\left[-2-\frac2{\log x}+\frac1{\log x+1}\right]<0,
\qquad 0<\rho_A(u)\le1.
\]

The \(E_1\) integrand is \(\delta_1(A)-\delta_1(A+u)\); hence

\[
-H\log B\le E_1(A,H)\le H\log A. \tag{MS2}
\]

Its lower loss is paid; its sign is not assumed favorable.

### Actual second cutoff and the uniform prime input

Let \(q=q_2(x)>1\) be the unique solution

\[
r_2(q)=\frac{\ell(q)}{\log q}=\lambda(x),\qquad
\ell(q)=\log\left(1+\frac1{q^2+q}\right).
\]

The smooth \(r_2\) decreases strictly from infinity to zero. Exact
differentiation and ordinary expansions give

\[
\ell'(q)=-\frac{2q+1}{(q^2+q)(q^2+q+1)},\quad
\ell(q)=q^{-2}-q^{-3}+O(q^{-4}),\quad
\ell'(q)=-2q^{-3}+3q^{-4}+O(q^{-5}).
\]

Set \(a(q)=q^2\ell(q)-1=-q^{-1}+O(q^{-2})\) and

\[
b(q)=-q^3\ell'(q)-2=-3q^{-1}+O(q^{-2}),\qquad
L=\log x,\quad l=\log q.
\]

The exact implicit equation and derivative are

\[
q^2l=(1+a(q))xL,\qquad
r_2'(q)=-\frac{q^{-3}}l\left[2+b(q)+\frac{1+a(q)}l\right],
\]

\[
q_2'(x)=\frac qx\,
\frac{(1+a(q))(1+1/L)}{2+b(q)+(1+a(q))/l}.
\]

For sufficiently large \(x\), comparison at \(\sqrt x\) and \(2\sqrt x\)
first bounds \(q\) between them. Thus \(l=L/2+O(1)\), and substitution
into these exact formulas proves

\[
q_2(x)=\sqrt{2x}[1+O(1/\log x)],\qquad
q_2'(x)=\frac1{\sqrt{2x}}[1+O(1/\log x+1/q_2(x))]. \tag{MS3}
\]

The \(1/q_2(x)\) term is smaller than \(1/\log x\). This derivative
comes from the smooth actual equation, not differentiation of a
pointwise prime-count asymptotic or an \(O(1)\) cutoff error. With common
constants for large \(A\), \(0<H\le A/2\), \(0\le u\le H\), integration
of the derivative gives

\[
v(u):=q_2(A+u)-q_2(A)
=\frac u{\sqrt{2A}}
+O\left(\frac u{\sqrt A\log A}+\frac{uH}{A^{3/2}}\right). \tag{MS4}
\]

Use **Corollary 1.3**, not the almost-all Corollary 1.4, of
[Guth–Maynard, arXiv:2405.20552v2](https://arxiv.org/html/2405.20552v2)
and its §13.2 proof; the [existing GM note](../Analytic/guthmaynard2024largevalues.md)
records this primary input. For each fixed \(\epsilon>0\) with a
nonempty range there exist constants \(C_\epsilon,Y_\epsilon>0\) such
that for **every real** \(y\ge Y_\epsilon\) and every real length

\[
y^{17/30+\epsilon}\le v\le y^{99/100},\qquad
\left|\pi(y+v)-\pi(y)-\frac v{\log y}\right|
\le C_\epsilon v e^{-(\log y)^{1/4}}.
\]

No numerical \(Y_\epsilon\) is supplied. Fix

\[
\epsilon=1/60,\quad H=A^{4/5},\quad y=q_2(A),\quad
V=v(H),\quad h_0=(2\sqrt A)^{7/12}=2^{7/12}A^{7/24}.
\]

Eventually \(y\sim\sqrt{2A}\le2\sqrt A\),

\[
y^{7/12}\le h_0\le V\sim A^{3/10}/\sqrt2,
\qquad h_0,V\le y^{99/100},\qquad y\ge Y_{1/60}.
\]

Indeed \(3/10-7/24=1/120>0\) and \(3/10<99/200\). All these
requirements are paid by one common eventual, unquantified threshold.
For \(h_0\le v\le V\), write \(n(v)=\pi(y+v)-\pi(y)\). Then

\[
0\le\theta(y+v)-\theta(y)-(\log y)n(v)
\le\log(1+v/y)n(v),\qquad n(v)\le2v/\log y
\]

eventually, uniformly. Thus multiplication of the **absolute \(\pi\)
error by \(\log y\)** gives

\[
\theta(y+v)-\theta(y)
=v+O\left(v\log y\,e^{-(\log y)^{1/4}}+\frac{v^2}{y\log y}\right).
\]

For fixed constants \(C,c>0\), use

\[
\eta_A=C\left(\log A\,e^{-(c\log A)^{1/4}}+H/A\right)\longrightarrow0,
\]

since \(V/y=O(H/A)\) and \(\log y\asymp\log A\). For \(0\le v<h_0\),
apply GM only at the enclosing length \(h_0\), then monotonicity:

\[
0\le\theta(y+v)-\theta(y)\le\theta(y+h_0)-\theta(y)\le2h_0.
\]

It follows, uniformly over **the whole** \(0\le v\le V\), that

\[
\theta(y+v)-\theta(y)=v+O(\eta_Av+h_0). \tag{MS5}
\]

GM has not been extended below its lower length. To retain both strict
second-cutoff atoms, let \(e(z)=\log z\) when \(z\) is an integer prime,
and \(e(z)=0\) otherwise. The exact formula is

\[
K_2(A+u)-K_2(A)=\theta(y+v(u))-\theta(y)+e(y)-e(y+v(u)).
\]

The initial atom has a plus sign and the final atom a minus sign. Their
difference is \(O(\log A)\) uniformly, including events at \(u=0,H\).
At a stable initial source \(e(y)=0\); the supplier does not need this.

### Whole weighted increment and retained higher layers

The exact logarithmic derivative of \(w\) gives

\[
\rho_A(u)=1+O(H/A)\quad(0\le u\le H\le A/2).
\]

Combining MS4–MS5 and the two atoms, with \(v(u)\le C u/\sqrt A\),
gives throughout \([0,H]\)

\[
K_2(A+u)-K_2(A)=\frac u{\sqrt{2A}}
+O\left(\frac u{\sqrt A\log A}+\frac{uH}{A^{3/2}}
+\eta_A\frac u{\sqrt A}+h_0+\log A\right).
\]

Integrating the entire interval, including the initial short lengths,
and paying the weight variation yields

\[
U_2(A,H)=\frac{\sqrt2}{4}\frac{H^2}{\sqrt A}
+O\left(\frac{H^2}{\sqrt A\log A}+\frac{H^3}{A^{3/2}}
+\eta_A\frac{H^2}{\sqrt A}+Hh_0+H\log A\right). \tag{MS6}
\]

In particular, put \(S_A=H^2/\sqrt A=A^{11/10}\). There exist constants
\(A_0,C,c>0\) such that for **every real \(A\ge A_0\)**, with \(H=A^{4/5}\),

\[
\left|\frac{U_2(A,H)}{S_A}-\frac{\sqrt2}{4}\right|
\le C\left(\frac1{\log A}+A^{-1/5}
+\log A\,e^{-(c\log A)^{1/4}}
+A^{-1/120}+A^{-3/10}\log A\right)=:\mathcal E(A).
\]

The constants depend on the fixed GM input and the ordinary calculus
bounds, not on \(A\) or its selfmatching status; none is given a numerical
value here. The short-range cost is exactly

\[
\frac{h_0\sqrt A}{H}=2^{7/12}A^{-1/120},\qquad
\frac{\sqrt A\log A}{H}=A^{-3/10}\log A\longrightarrow0.
\]

The first-layer loss MS2 is also paid by the latter scale. After increasing
\(C\), set \(\varepsilon_*(A)=\mathcal E(A)\ge0\), tending to zero.
The same bound gives, for every such real \(A\),

\[
U_2+E_1\ge(\sqrt2/4-\varepsilon_*(A))S_A,
\]

\[
U_2+U_{\ge3}+E_1
\ge(\sqrt2/4-\varepsilon_*(A))S_A+U_{\ge3}. \tag{MS7}
\]

Equivalently, for every \(\delta>0\) there exists \(A_\delta\) such that

\[
U_2(A,A^{4/5})+E_1(A,A^{4/5})\ge(\sqrt2/4-\delta)A^{11/10}
\quad\text{for every real }A\ge A_\delta.
\]

No actual higher layer is deleted. In contrast, integrating the old
coarse difference \(Q=K-\psi\) error

\[
O(A^{1/3}(\log A)^{7/3})
\]

would cost \(O(H A^{1/3}(\log A)^{7/3})\), or

\[
O(A^{1/30}(\log A)^{7/3})
\]

relative to \(S_A\). This need not vanish. MS7 keeps the monotone actual
higher layers instead; it does not assert a shorter-interval asymptotic
for the old signed \(Q\) difference.

For each fixed \(47/60<\alpha<199/200\), the same proof works with

\[
H=A^\alpha,\qquad 0<\epsilon<2\alpha-47/30,\qquad
h_{0,\epsilon}=(2\sqrt A)^{17/30+\epsilon}.
\]

The short-range relative exponent is \(47/60+\epsilon/2-\alpha<0\),
and the upper-range ratio is \(V/y^{99/100}=O(A^{\alpha-199/200})\to0\).
This choice also ensures \(17/30+\epsilon<99/100\). All other costs
vanish; constants and thresholds depend on the fixed \(\alpha,\epsilon\).
These are sufficient exponents, with no optimality or uniform endpoint
claim. The displayed \(4/5,1/60\) choice lies strictly inside this range.

### Actual integer consumer and the unpaid prime sign

Return to \(H=A^{4/5}\), \(B=A+H\), \(X=K(B)\). At a strict stable
selfmatch \(A\ge A_0\), suppose the same \(N_A\)
satisfies GA2 against all its multiples; in particular this holds if
\(N_A>5040\) is a global maximizer of \(G\) over integers greater than \(5040\).
Since \(N_A\mid N_B\), MS1 and MS7 imply the necessary condition

\[
T_\theta(A,H)\le-(\sqrt2/4-\varepsilon_*(A))S_A
-U_{\ge3}(A,H)-\frac{C_B(X)}{w(A)}. \tag{MS8}
\]

The exact endpoint-preserving finite prime sum is

\[
w(A)T_\theta(A,H)
=\sum_{A<p\le B}\log p\,[\lambda(p)-\lambda(B)]
-[f(B)-f(A)-H\lambda(B)]. \tag{MS9}
\]

Indeed integrate the finite indicators \(\mathbf1_{p\le t}\) against

\[
w(t),\qquad \int_p^B w=\lambda(p)-\lambda(B),\qquad
\int_A^B(t-A)w(t)\,dt=f(B)-f(A)-H\lambda(B).
\]

A prime at \(A\) is excluded; one at \(B\) has zero weight. This is the
original same-state identity, not a new standalone prime theorem.

For every fixed real \(\kappa<\sqrt2/4\), there exists a common
\(A_\kappa\ge A_0\) such that \(\varepsilon_*(A)<(\sqrt2/4-\kappa)/2\) for all
\(A\ge A_\kappa\).

At any actual strict stable selfmatch above that start, the **unproved**
condition

\[
T_\theta(A,A^{4/5})\ge-\kappa S_A \tag{MSP}
\]

would give the actual strict improvement

\[
\log\frac{G(N_B)}{G(N_A)}
\ge w(A)[(\sqrt2/4-\kappa-\varepsilon_*(A))S_A+U_{\ge3}]
+C_B(X)>0.
\]

Independently, MS6 implies \(U_2>0\) eventually, so at least one new
actual second layer is present before \(B\); thus \(N_B>N_A\). The
successor is the defined integer multiple, not an unrelated scalar witness.

MSP (candidate MP) is unpaid. GM at the \(A\)-centered first-layer scale
only permits a relative error of order \(\eta_AH^2\); the required signed
loss is of order \(H^2/\sqrt A\). The factor tending to zero in GM does
not pay the missing \(A^{-1/2}\). A general-center average or rough-shift
correlation does not establish MSP at these selected centers.

The conditional selected-source statement retains the CNS and
Mantovanelli premises in the existing notes: proper GA1/GA2 and the
direct prime-local bridge give the **same** stable selfmatching integer.
For that source one still needs MSP and \(A\ge A_\kappa\). The unbounded
stable-root chain of FIB §111 is not an unbounded family of global Robin
maxima; the separate unbounded GA2 family has no automatic stable-selfmatch
premise. No unbounded covered source family is supplied here. The
historical \(7.2\cdot10^{46}\) conclusion above remains only its existing,
separately sourced conditional context; it pays neither \(Y_{1/60}\)
nor \(A_0,A_\delta,A_\kappa\). No new finite interval, least-counterexample
bound, RH proof or new unconditional formal supplier follows.

### Reuse and formalization boundary

At the original project pin, reuse
`GoldenResourceOptimalLayerCount.positive_part_sum_finite_support`,
`positive_layers_eq_count_interval`, `optimal_layer_count_spec`,
`GoldenResourceSupremum.golden_resource_supremum_eq_positive_part_sum`,
the actual sigma objective factorization and equality-layer neutrality.
The searched D5/S3/Arith/Robin public and private declarations supply
prefix, curvature and moment facts, but not the weighted short actual
second-layer estimate MS6–MS7. This is a bounded search conclusion.

Mathlib is pinned at `db584cd6d46c92f209a44c0f1c829460d327499d`:
`Chebyshev.theta`, `theta_mono`, `theta_eq_sum_primesLE`, finite sums,
sigma prime-power/multiplicativity, interval FTC, asymptotics and implicit
function APIs are reusable. The bounded pinned NumberTheory search did not find a formal GM supplier.
OpenAI/math at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/build/qualitative/analytic-transfer.tex`,
has rough-multiplier supremum/fourth-moment and averaged correlation
statements with different variables and quantifiers. They are not
premises of this derivation and do not prove MSP.

MS6–MS7 remain ordinary, uncompiled estimates using the cited GM
analytic input. Substantive formal adoption must connect the actual
finite layer state, implicit cutoff derivative, endpoint atoms and whole
weighted integration to MS1 and MS9, and discharge GM or explicitly
retain its short-interval hypothesis. A scalar wrapper assuming the
finished supplier would not implement the missing mathematics. No axiom,
wrapper Lean declaration, current required check or kernel acceptance is
produced here. MSP, the common start/source coverage, the analytic formal
input and the substantive formal implementation remain open; the full
RH/Robin/5040 goal remains **ACTIVE**.

## Project application: full signed shorter Q drift and preloaded GA2 successors

This is a complete **ordinary mathematical derivation relative to the
published Guth–Maynard short-interval input**. Its additional analytic
content is the integrated full signed difference of actual and reference
layers at the fixed length \(H=A^{4/5}\), including a bound uniform in
the growing layer index. It then applies the already audited finite lcm
accounting to the same actual GA2 integer. No selfmatching hypothesis is
needed for that application.

The preceding MS0–MS9/MSP section is reused at the immutable project
commit `963847e45dc06ddb633295b84b2bd36d4c231eae`, NC file blob
`14f2f364318cf8f02e8b58d50ab9f61802f4764e`. In particular, MS3–MS6
supply the smooth actual second-cutoff calculation and its whole weighted
increment; MS0–MS2 and MS9 retain the actual integer, endpoint convention
and signed first-layer accounting. The original
[FIB §§85, 87, 98 and 111](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
[ZE/5040 actual layers and own-price defect](../../docs/develop/theory/ZECKENDORF_EULER_5040.md),
and [Mantovanelli workload and proper prime-local bridge](../Analytic/mantovanelli2026primeworkload.md)
remain the underlying project interfaces.

The declared completed design inputs are
`actual-higher-layer-gm-shorter-Q-candidate.md`, SHA-256
`5a967ecdb296bf5c7c64413cf9c00ddc0f7ed3868c69a7ef8375386eef39ac6f`,
and its complete ordinary proof `audit-proof.md`, SHA-256
`9f18c0fe96eafb4fe61aa2da8b6370055912c961833fe5248ce4c191aec416a3`;
and `ga2-preloaded-layer-successor-candidate.md`, SHA-256
`f99946147a279237a5515659ce73334a3ccdadd7dab1be0297d8a2806314cdc5`,
with `ordinary-audit.md`, SHA-256
`307be4ca1430efc5843323b2189fcff07ad2f3ee669db59ed1f3faa0c81c4a41`.
Their preserved results and collection receipts report ordinary approval
within those stated scopes. Those prior audits are design evidence here,
not independent current validation of this source draft. No complete
independent audit of the primary GM theorem, new compilation, Lean/kernel
verification, official acceptance or priority claim is made.

### Actual and reference inventories on one common finite support

All logarithms are natural. For real \(x>1\), set

\[
f(x)=\log\log x,\qquad
\lambda(x)=f'(x)=\frac1{x\log x},\qquad
w(x)=-\lambda'(x)=\frac{\log x+1}{x^2(\log x)^2}>0.
\]

For \(q>1\) and an integer \(k\ge1\), put

\[
S_k(q)=\sum_{j=1}^k q^j,\qquad
\ell_k(q)=\log(1+1/S_k(q)),\qquad
r_k(q)=\frac{\ell_k(q)}{\log q}.
\]

For a prime \(p\), write \(r_{p,k}=r_k(p)\) and
\(h_p=\log p\). The existing Euler stack identity is

\[
\frac{\sum_{j=0}^k p^{-j}}{\sum_{j=0}^{k-1}p^{-j}}
=1+\frac1{p+\cdots+p^k},\qquad
W(n):=\log\frac{\sigma(n)}n
=\sum_p\sum_{k=1}^{v_p(n)}r_{p,k}h_p.
\]

Each \(r_k\) is smooth and strictly decreasing from infinity to zero:
\(\ell_k>0\) decreases strictly, \(\log q>0\) increases strictly,
and their endpoint limits give the stated range. Thus there is a unique
smooth increasing \(q_k(x)>1\) with
\(r_k(q_k(x))=\lambda(x)\). Define the **strict actual** inventory by

\[
K_k(x)=\sum_{p<q_k(x)}\log p
=\sum_{r_{p,k}>\lambda(x)}\log p,\qquad
N_x=\prod_p p^{\#\{k:r_{p,k}>\lambda(x)\}},\qquad
K(x)=\sum_{k\ge1}K_k(x)=\log N_x.
\]

The reference convention is weak:

\[
\theta(y)=\sum_{p\le y}\log p,\qquad
\psi(x)=\sum_{p^k\le x}\log p
=\sum_{k\ge1}\theta(x^{1/k}),\qquad Q(x)=K(x)-\psi(x).
\]

This \(Q\) is specifically the actual-minus-reference log inventory;
it is not any other quantity called \(Q\) earlier in this source.
All prime-power pairs are counted, with their individual \(\log p\)
weights.

The exact marginal bound

\[
0<r_{p,k}<\frac1{p^k\log p}
\]

shows that every possibly active or tied actual layer on \([A,B]\)
lies in the finite set
\(L_B=\{(p,k):r_{p,k}\ge\lambda(B)\}\), since membership implies
\(p^k\log p<B\log B\) and \(p<B\). The reference support
\(\{(p,k):p^k\le B\}\) is also finite. These two fixed sets give
common support for every \(x\in[A,B]\), so all subsequent sum/integral
interchanges are finite. Equal-price actual layers are excluded from
\(N_x\). Different primes may activate simultaneously; every layer of
such an event is retained separately in the accounting.

### Exact derivative control uniform in the growing layer index

The audited candidate's H1–H5 are written QH1–QH5 here to avoid the
earlier H1–H7 labels in this file. These inequalities hold uniformly
for **every** integer \(k\ge1\), rather than for each fixed \(k\)
with unspecified dependent constants.

Writing \(z=1/S_k(q)\), exact differentiation gives

\[
\ell_k'(q)=-\frac{S_k'(q)}{S_k(q)(S_k(q)+1)},\qquad
-\frac{q\ell_k'(q)}{\ell_k(q)}
=\frac{qS_k'(q)}{S_k(q)}
\frac{z}{(1+z)\log(1+z)}. \tag{QH1}
\]

Let \(m=(k+1)/2\). Pair the terms \(j<m\) and \(k+1-j>m\)
in \(\sum_{j=1}^k(j-m)q^j\). Each pair contributes

\[
(m-j)(q^{k+1-j}-q^j)\ge0;
\]

the middle term, when present, is zero. Thus
\(qS_k'(q)/S_k(q)\ge(k+1)/2\). Also \(S_k(q)\ge k\),
so \(z\le1/k\), and \(\log(1+z)\le z\) gives

\[
\frac{z}{(1+z)\log(1+z)}\ge\frac1{1+z}\ge\frac{k}{k+1}.
\]

Consequently

\[
-\frac{qr_k'(q)}{r_k(q)}
=-\frac{q\ell_k'(q)}{\ell_k(q)}+\frac1{\log q}
\ge\frac k2. \tag{QH2}
\]

Implicit logarithmic differentiation uses
\(-\lambda'(x)/\lambda(x)=(1+1/\log x)/x\), and proves

\[
0<\frac{q_k'(x)}{q_k(x)}
\le\frac{2(1+1/\log x)}{kx}\le\frac4{kx}
\qquad(x\ge e). \tag{QH3}
\]

For \(A\ge e\), \(0\le u\le H\), \(H/A\le1/4\), integrate:

\[
0\le\log\frac{q_k(A+u)}{q_k(A)}
\le\frac4k\log(1+u/A)\le\frac{4u}{kA}\le1.
\]

Using \(e^t-1\le2t\) on \([0,1]\) therefore gives

\[
0\le q_k(A+u)-q_k(A)\le\frac{8u\,q_k(A)}{kA}. \tag{QH4}
\]

At the cutoff, \(\log(1+1/S_k)<1/S_k\le q^{-k}\), hence
\(q_k(A)^k\log q_k(A)<A\log A\). In particular, **provided
\(q_k(A)\ge2\)**,

\[
q_k(A)<R_A^{1/k},\qquad R_A=\frac{A\log A}{\log2}. \tag{QH5}
\]

No large-\(q\) expansion uniform in growing \(k\) has been assumed.
A nonempty actual layer at \(B\), or even a tie at \(B\), requires
\(2^k<R_B\); a nonempty reference layer requires \(2^k\le B\).
For sufficiently large \(A\) and \(B\le2A\), both families lie in

\[
1\le k\le D_A:=\left\lceil\frac{\log R_B}{\log2}\right\rceil
\le7\log A.
\]

This is one common \(O(\log A)\) index support, including layers
empty at \(A\) but active before \(B\). The actual layer with
\(q_k(B)=2\) is empty under the strict convention and causes no
omission. The same bounds cover all equality events in \(L_B\).

### One GM threshold, length enclosure and the logarithmic weight

Use the primary **uniform Corollary 1.3** of
[Guth–Maynard, arXiv:2405.20552v2](https://arxiv.org/html/2405.20552v2),
as recorded in the [project GM source](../Analytic/guthmaynard2024largevalues.md).
Its entire primary theorem proof is not independently audited here.
Fix, once and for all,

\[
\epsilon_{\rm GM}=1/60,\qquad
\beta=17/30+\epsilon_{\rm GM}=7/12.
\]

The published input gives constants \(C_{\rm GM},Y_0>0\) such that
for **every real** \(y\ge Y_0\) and every real length
\(y^\beta\le v\le y^{99/100}\),

\[
\left|\pi(y+v)-\pi(y)-\frac v{\log y}\right|
\le C_{\rm GM}v e^{-(\log y)^{1/4}}. \tag{QGM}
\]

Increase this single unknown start to \(Y\ge e\), so that
\(C_{\rm GM}\log y\,e^{-(\log y)^{1/4}}\le1\) for every
\(y\ge Y\). Neither \(Y_0\) nor \(Y\) is assigned a numerical
value. For a permitted length, let \(P=\pi(y+v)-\pi(y)\). Then
\(P\le2v/\log y\), and

\[
0\le\theta(y+v)-\theta(y)-(\log y)P
\le\log(1+v/y)P\le\frac{2v^2}{y\log y}.
\]

Thus the required two-sided conversion is

\[
\theta(y+v)-\theta(y)
=v+O\left(v\log y\,e^{-(\log y)^{1/4}}
+\frac{v^2}{y\log y}\right). \tag{QTC}
\]

The factor \(\log y\) multiplying the absolute \(\pi\) error
is retained. Since \(v\le y^{99/100}\le y\), the same argument
also gives \(\theta(y+v)-\theta(y)\le4v\). If
\(0\le v<y^\beta\), use monotonicity and apply GM only to the
enclosing length \(y^\beta\), which lies inside its allowed range.
Consequently, with this same \(Y\),

\[
0\le\theta(y+v)-\theta(y)\le4(v+y^\beta)
\quad(y\ge Y,\ 0\le v\le y^{99/100}). \tag{QH6}
\]

This enclosure does not extend GM below its minimum length. Small
cutoffs \(y<Y\) will instead use the fixed finite bound
\(\theta(2Y)\); they do not acquire a layer-dependent GM start.

### All higher actual and reference increments, including endpoint atoms

From now on fix exactly

\[
H=A^{4/5},\qquad B=A+H,\qquad
\rho_A(u)=\frac{w(A+u)}{w(A)},\qquad
S_A=\frac{H^2}{\sqrt A}=A^{11/10}.
\]

For \(k\ge3\), \(y=q_k(A)\ge Y\), and
\(v=q_k(A+u)-q_k(A)\), QH4–QH5 give, uniformly in \(k,u\),

\[
v\le\frac{8Hy}{kA},\qquad
\frac v{y^{99/100}}
\le\frac83 A^{-1/5}R_A^{1/300}\longrightarrow0. \tag{QH7}
\]

The last power is \(A^{-59/300}\) times a fixed logarithmic
factor. Thus one common eventual \(A\)-threshold verifies the GM
**maximum** length for every such growing-index cutoff at once.

Let \(a(z)=\log z\) if \(z\) itself is an integer prime, and zero
otherwise. The exact strict-to-weak conversion, valid also at events, is

\[
K_k(A+u)-K_k(A)
=\theta(y+v)-\theta(y)+a(y)-a(y+v).
\]

The initial strict atom has a plus sign; the final one has a minus sign.
At \(u=0\) they cancel. Because \(\log y=O(y^\beta)\), QH6
and monotonicity of the actual cutoff give

\[
0\le K_k(A+u)-K_k(A)\le C(v+y^\beta).
\]

If \(q_k(A)<Y\), QH4 instead gives \(q_k(B)\le2Y\) once
\(A\) exceeds one common threshold. Its increment is then at most
\(\theta(2Y)\), even when \(q_k(A)<2\) and the initial layer is
empty. Simultaneous activations do not change these per-layer bounds.

For the reference cutoff \(y=A^{1/k}\), exact differentiation gives
\(y'(x)/y(x)=1/(kx)\). It satisfies QH4 with a smaller constant
and \(y\le R_A^{1/k}\). Apply exactly the same large-/small-cutoff
split, the same upper-length check and the same GM \(Y\). Its weak
increment already excludes the initial prime and includes the terminal
prime, and needs no strict-atom correction.

For a large higher cutoff, \(v\le C(H/A)R_A^{1/3}\) and
\(y^\beta\le R_A^{\beta/3}\). Sum both nonnegative inventories
over their common support \(3\le k\le D_A\), absorbing
\(\theta(2Y)\) into one constant. For every sufficiently large real
\(A\), simultaneously for every \(0\le u\le H\),

\[
\begin{aligned}
&\sum_{k\ge3}[K_k(A+u)-K_k(A)]\\
&\quad+\sum_{k\ge3}
 [\theta((A+u)^{1/k})-\theta(A^{1/k})]\\
&\le C\log A\left[\frac HA R_A^{1/3}+R_A^{\beta/3}+1\right].
\end{aligned} \tag{QH8}
\]

Both sums on the left are literally nonnegative. Their signed difference
is therefore bounded in absolute value by this same right side.

The exact derivative

\[
w'(x)=-x^{-3}\left(\frac2{\log x}
+\frac3{(\log x)^2}+\frac2{(\log x)^3}\right)<0
\]

gives \(0<\rho_A(u)\le1\). Integrating on the **entire** interval
with common finite support proves

\[
\begin{aligned}
&\left|\int_0^H\rho_A(u)\sum_{k\ge3}
 \bigl[K_k(A+u)-K_k(A)
 -\theta((A+u)^{1/k})+\theta(A^{1/k})\bigr]\,du\right|\\
&\le CH\log A
 \left[\frac HA R_A^{1/3}+R_A^{\beta/3}+1\right].
\end{aligned} \tag{QH9}
\]

After division by \(S_A\), the three errors are bounded by

\[
C\left[A^{-1/6}(\log A)^{4/3}
+A^{-19/180}(\log A)^{43/36}
+A^{-3/10}\log A\right]\longrightarrow0. \tag{QH10}
\]

For example, \(1/2-4/5+\beta/3=-19/180\) and
\(1+\beta/3=43/36\). This controls short **increments**, rather
than subtracting two old pointwise
\(O(A^{1/3}(\log A)^{7/3})\) errors. Integrating the latter would
give the nonvanishing relative allowance
\(O(A^{1/30}(\log A)^{7/3})\).

### Whole second-layer integration and the reference square subtraction

Reuse MS2's actual first-cutoff enclosure \(x-1<q_1(x)<x\).
It gives

\[
0\le d_1(x):=\theta(x)-K_1(x)\le\log x,
\]

including a prime at either endpoint of \([q_1(x),x]\). The
first-layer actual-minus-reference increment is
\(d_1(A)-d_1(A+u)\), so its absolute weighted integral is at most
\(H\log B\). Its normalized cost is
\(O(A^{-3/10}\log A)\), with no assumed favorable sign.

For the fixed actual second layer, MS3–MS4 derive from the **smooth
implicit equation**, not from differentiating an asymptotic remainder,

\[
q_2(x)=\sqrt{2x}\,[1+O(1/\log x)],\qquad
q_2'(x)=\frac1{\sqrt{2x}}[1+O(1/\log x)],
\]

\[
v_2(u):=q_2(A+u)-q_2(A)
=\frac{u}{\sqrt{2A}}
+O\left(\frac{u}{\sqrt A\log A}+\frac{uH}{A^{3/2}}\right).
\]

Here the fixed-layer calculation uses exactly
\(\ell_2'(q)=-(2q+1)/[(q^2+q)(q^2+q+1)]\) and
\(q^2\log q=x\log x[1+O(1/q)]\). Comparison at
\(\sqrt x\) and \(2\sqrt x\) first traps the cutoff, and implicit
differentiation then supplies the derivative. This fixed-layer expansion
is not substituted for QH1–QH5 at growing \(k\).

The reference square has the different exact derivative and increment

\[
(\sqrt x)'=\frac1{2\sqrt x},\qquad
v_{\rm sq}(u):=\sqrt{A+u}-\sqrt A
=\frac{u}{2\sqrt A}+O\left(\frac{uH}{A^{3/2}}\right).
\]

For both starts \(y=q_2(A)\) and \(y=\sqrt A\), use the same
\(Y\) as above and the common enclosing length

\[
h_0=(2\sqrt A)^\beta=2^{7/12}A^{7/24}.
\]

Eventually \(\sqrt A\le q_2(A)\le2\sqrt A\), both starts
exceed \(Y\), and

\[
y^\beta\le h_0\le y^{99/100},\qquad
0\le v_2(u),v_{\rm sq}(u)\le CA^{3/10}
\le y^{99/100}.
\]

Also \(h_0\le v_2(H),v_{\rm sq}(H)\) eventually, since
\(3/10-7/24=1/120>0\). The maximum-length comparison has
\(3/10<99/200\). Thus the enclosing interval itself respects both
GM length restrictions, for both actual and reference starts.

For \(v\ge h_0\), use QTC; for \(v<h_0\), use monotonicity
and GM at the permitted length \(h_0\). Uniformly across the whole
range of either increment this gives

\[
\theta(y+v)-\theta(y)=v+O(\eta_Av+h_0),\qquad
\eta_A=C\left[\log A\,e^{-(c\log A)^{1/4}}+H/A\right]\to0,
\]

where a fixed \(c=1/3\) is admissible after increasing the common
\(A\)-start. The \(\log A\) factor from QTC remains. For the
actual second layer add the exact atoms \(a(y)-a(y+v)\), with
absolute cost \(O(\log A)\). The reference square uses weak
endpoints directly. Events at \(u=0,H\), and simultaneous events
of other layers, require no exceptions.

The exact logarithmic derivative

\[
\frac{w'(x)}{w(x)}
=\frac1x\left[-2-\frac2{\log x}+\frac1{\log x+1}\right]
\]

has absolute value at most \(4/x\) for \(x\ge e\); hence
\(\rho_A(u)=1+O(H/A)\) uniformly. Integrate from \(0\) to \(H\),
paying the lower-length enclosure, atoms and weight variation:

\[
\begin{aligned}
U_2&:=\int_0^H\rho_A(u)[K_2(A+u)-K_2(A)]\,du\\
&=\frac{\sqrt2}{4}S_A
+O\left(\frac{H^2}{\sqrt A\log A}+\frac{H^3}{A^{3/2}}
+\eta_AS_A+Hh_0+H\log A\right).
\end{aligned} \tag{QH11}
\]

This is MS6, with the same fixed \(4/5,1/60\) parameters. In contrast,

\[
\begin{aligned}
U_{\rm sq}&:=\int_0^H\rho_A(u)
 [\theta(\sqrt{A+u})-\theta(\sqrt A)]\,du\\
&=\frac14S_A
+O\left(\frac{H^3}{A^{3/2}}+\eta_AS_A+Hh_0\right).
\end{aligned} \tag{QH12}
\]

The factors come from \(\int_0^Hu\,du=H^2/2\): the actual
derivative \(1/\sqrt{2A}\) yields \(\sqrt2/4\), whereas the
reference derivative \(1/(2\sqrt A)\) yields \(1/4\).
The enclosing and atom costs, paid before normalization, are

\[
\frac{Hh_0}{S_A}=2^{7/12}A^{-1/120},\qquad
\frac{H\log A}{S_A}=A^{-3/10}\log A.
\]

### Precise full signed Q statement and quantified error

Define the complete signed drift

\[
S_Q(A,H)=\int_0^H[Q(A+u)-Q(A)]\rho_A(u)\,du.
\]

Its finite exact decomposition is the first-layer correction, plus
\(U_2-U_{\rm sq}\), plus the signed higher-layer integral in QH9.
Combining the preceding estimates proves

\[
S_Q(A,A^{4/5})
=\left(\frac{\sqrt2-1}{4}+o(1)\right)A^{11/10}. \tag{QH13}
\]

More precisely, there exist constants \(C>0\) and \(A_*>2\)
such that **for every real \(A\ge A_*\)**, with exactly
\(H=A^{4/5}\),

\[
\left|\frac{S_Q(A,H)}{S_A}-c_Q\right|
\le\mathcal E_Q(A):=C\mathcal F_Q(A),\qquad
c_Q=\frac{\sqrt2-1}{4}, \tag{QQE}
\]

\[
\begin{aligned}
\mathcal F_Q(A)={}&\frac1{\log A}+A^{-1/5}
+\log A\,e^{-((\log A)/3)^{1/4}}+A^{-1/120}\\
&+A^{-3/10}\log A
+A^{-1/6}(\log A)^{4/3}
+A^{-19/180}(\log A)^{43/36}.
\end{aligned}
\]

All seven terms tend to zero. Constants may depend on the fixed primary
GM input and elementary estimates, but not on \(A,u,k\), selfmatching
or GA2 status. The single \(A_*\) pays the GM \(Y\), both square
cutoffs, all growing-index upper-length checks, the small-cutoff bound,
finite support and derivative estimates simultaneously. It is unknown
and no numerical start is supplied.

Equivalently, the precise tolerance formulation is

\[
\forall\delta>0\ \exists A_\delta\ge A_*,
\ \forall A\in\mathbb R,
\quad A\ge A_\delta\Longrightarrow
\left|S_Q(A,A^{4/5})-c_QA^{11/10}\right|
\le\delta A^{11/10}. \tag{QQD}
\]

The GM epsilon stays fixed at \(1/60\); \(\delta\) is the final
normalized-error tolerance. This is an ordinary GM-relative proof for
all sufficiently large real centers, not a selected-subsequence estimate.
This appended result makes no broader-\(\alpha\) assertion. It does
not supply a numerical start, a finite Robin interval, a formal/kernel
supplier, or an RH conclusion.

### Exact connection at an arbitrary actual GA2 integer

Let \(N>e^2\) be an integer, \(A=\log N\), \(a_p=v_p(N)\),
and assume GA2 in its literal sense:

\[
G(Nm)\le G(N)\quad(m\in\mathbb N_{>0}),\qquad
G(n)=\frac{\sigma(n)/n}{\log\log n}.
\]

No deletion comparison, global maximality or equation \(K(A)=A\)
is assumed. The audited occupancy argument uses the actual next layer:

\[
r_{p,a_p+1}\log p=W(Np)-W(N)
\le f(A+\log p)-f(A)<\lambda(A)\log p.
\]

The last inequality is strict concavity of \(f\). Stack monotonicity
therefore puts **every** layer with \(r_{p,k}\ge\lambda(A)\)
in \(N\), including equality layers. Thus \(N_A\mid N\), and
the finite occupied extra inventory is

\[
E_N=\{(p,k):1\le k\le a_p,\ r_{p,k}\le\lambda(A)\},\qquad
\delta_N=A-K(A)=\log(N/N_A)=\sum_{e\in E_N}h_e\ge0.
\]

For a layer \(e=(p,k)\), write \(r_e=r_{p,k}\) and \(h_e=h_p\).

For \(x\in[A,B]\), take the literal integer and clock

\[
M_x=\operatorname{lcm}(N,N_x),\qquad Y_N(x)=\log M_x,
\qquad P_N(x)=\sum_{e\in E_N:\ r_e>\lambda(x)}h_e.
\]

The generic maximizing-multiple construction already exists in
[`GoldenFutureExtensionMaximum.lean`](../../D5/S3/Arith/GoldenFutureExtensionMaximum.lean),
especially `golden_future_extension_maximum_attained`, with the
max(base exponent, new prefix exponent) witness. The corresponding
construction also appears in
[`GoldenColossalClosure.lean`](../../D5/S3/Arith/GoldenResource/GoldenColossalClosure.lean).
We reuse it; no new generic optimizer theorem or duplicate implementation
is claimed. The relevant exact application of the audited finite layer
inventory is

\[
Y_N(x)=A+K(x)-K(A)-P_N(x),\qquad
0\le P_N(x)\le\delta_N,
\quad M_A=N,\quad Y_N(A)=A. \tag{QG1}
\]

Indeed, an activated layer already in \(E_N\) must be subtracted
from the unrestricted increment: it is not a new reward of \(M_x/N\).

The audited finite lcm identity, valid for any \(H>0\), is

\[
\log\frac{G(M_B)}{G(N)}
=\int_A^B[Y_N(t)-t]w(t)\,dt+C_B(Y_N(B)),\qquad
C_B(y)=f(B)+\lambda(B)(y-B)-f(y)\ge0. \tag{QG2}
\]

Strict concavity gives \(C_B(y)=0\) exactly when \(y=B\).

For completeness, its finite event accounting is as follows. Every
genuinely missing layer has \(r_e<\lambda(A)\), a unique
activation \(t_e>A\) with \(\lambda(t_e)=r_e\), and is added
to \(M_B/N\) precisely when \(t_e<B\). If its total mass and
Euler reward are \(L=Y_N(B)-A\) and
\(R=W(M_B)-W(N)\), finite integration gives

\[
\int_A^B[Y_N(t)-t]w(t)\,dt
=R-\lambda(B)L-[f(B)-f(A)-H\lambda(B)].
\]

Adding \(C_B(A+L)\) gives \(R+f(A)-f(A+L)\), exactly the
left side of QG2. Strict terminal ties are excluded and contribute zero
interval pressure. If a permitted subset of terminal tied layers of mass
\(J\) is deliberately added, its reward is \(\lambda(B)J\);
the integral is unchanged and the defect becomes \(C_B(Y_N(B)+J)\).
Simultaneous events keep all their separate masses. The displayed
successor is consistently the strict \(M_B\), with its **actual**
terminal clock \(Y_N(B)\), which need not equal \(B\).

Define at this same \(A\)

\[
T_\psi(A,H)=\int_0^H
 [\psi(A+u)-\psi(A)-u]\rho_A(u)\,du,\qquad
V_N(A,H)=\int_0^HP_N(A+u)\rho_A(u)\,du\ge0.
\]

Using QG1 and the exact identity \(K=\psi+Q\), the integrand is

\[
\begin{aligned}
Y_N(A+u)-(A+u)
={}&K(A+u)-K(A)-u-P_N(A+u)\\
={}&\psi(A+u)-\psi(A)-u
+Q(A+u)-Q(A)-P_N(A+u).
\end{aligned}
\]

The **complete initial \(K(A)\) cancels**. There is no selfmatch
substitution. Thus the exact desired connection is

\[
\boxed{\displaystyle
\log\frac{G(M_B)}{G(N)}
=w(A)[T_\psi(A,H)+S_Q(A,H)-V_N(A,H)]
+C_B(Y_N(B)).} \tag{QG3}
\]

Neither the preoccupied loss nor the actual terminal concavity defect
has been discarded. The identity is finite and exact independently of
GM; only the subsequent estimate for \(S_Q\) requires \(H=A^{4/5}\)
and the common sufficiently-large-real start.

### Own-price defect and below-terminal-price extra layers

Reuse the unrestricted finite pressure

\[
\mathscr S(\lambda)=\max_{n\ge1}[W(n)-\lambda\log n]
=\sum_{p,k}(r_{p,k}-\lambda)_+h_p.
\]

Because all positive own-price layers are already in \(N\), its
**own** price defect is exactly

\[
d_A(N)=\mathscr S(\lambda(A))-[W(N)-\lambda(A)A]
=\sum_{e\in E_N}(\lambda(A)-r_e)h_e\ge0. \tag{QG4}
\]

Finite integration of the preoccupied indicators gives

\[
w(A)V_N=\sum_{e\in E_N}(r_e-\lambda(B))_+h_e,
\qquad
0\le V_N\le\delta_NJ_H,\qquad
J_H=\frac{\lambda(A)-\lambda(B)}{w(A)}=\int_0^H\rho_A(u)\,du.
\tag{QG5}
\]

Here \(0<J_H<H\), and \(J_H=H[1+O(H/A)]\) when \(H=o(A)\).
An extra layer tied at \(A\) has zero initial defect but contributes
its whole price drop to \(w(A)V_N\); a tie at \(B\) contributes
zero to this latter sum.

For \(a=\lambda(A)>b=\lambda(B)\) and \(r\le a\), the exact
identity \((a-r)+(r-b)_+=(a-b)+(b-r)_+\), including equality
cases, yields

\[
\boxed{\displaystyle
d_A(N)+w(A)V_N
=(\lambda(A)-\lambda(B))\delta_N
+\sum_{e\in E_N}(\lambda(B)-r_e)_+h_e.} \tag{QG6}
\]

The residual sum is the mass-weighted price defect of occupied extras
that remain below the terminal price. It is required. Arbitrary GA2
does not imply \(\delta_N=0\), \(V_N=0\), \(d_A(N)=0\), or
vanishing of this residual. In particular the zero defect of \(N_A\)
cannot be transported to the different actual integer \(N\).

### The additional signed condition remains unproved

The exact weak-reference Lambda form of the prime-power term is

\[
w(A)T_\psi(A,H)
=\sum_{A<n\le B}\Lambda(n)[\lambda(n)-\lambda(B)]
-[f(B)-f(A)-H\lambda(B)]. \tag{QG7}
\]

This follows by finite integration of
\(\psi(t)-\psi(A)=\sum_{A<n\le t}\Lambda(n)\).
A prime-power atom at \(A\) is excluded, one at \(B\) has zero
weight, and every prime power in between has its full \(\Lambda\)
weight. QG7 is the full signed prime-power budget, not a prime-only sum.

Fix a real \(\kappa<c_Q=(\sqrt2-1)/4\). There is an unknown
common \(A_\kappa\ge A_*\) for which
\(\mathcal E_Q(A)\le(c_Q-\kappa)/2\) for all real
\(A\ge A_\kappa\). The sufficient **additional unproved**
condition, at the **same actual sources** and their same shorter interval,
is

\[
T_\psi(A,A^{4/5})-V_N(A,A^{4/5})
\ge-\kappa\frac{H^2}{\sqrt A}. \tag{QGP}
\]

If this condition held at such a source, QG3 and QQE would give

\[
\log\frac{G(M_B)}{G(N)}
\ge\frac{c_Q-\kappa}{2}\,w(A)S_A+C_B(Y_N(B))>0,
\]

for the literal integer multiple \(M_B\) of this same \(N\).
This would contradict GA2; it also forces \(M_B>N\), rather than
merely producing a scalar witness. Equivalently GA2 and the proved
supplier give only the necessary upper bound

\[
T_\psi-V_N
\le-[c_Q-\mathcal E_Q(A)]S_A-\frac{C_B(Y_N(B))}{w(A)}
\quad(A\ge A_*). \tag{QG8}
\]

This is an ordinary conditional deduction, **not** a new formal theorem
assuming its desired conclusion. QGP is not proved here, in the prior
ordinary audits, or by the imported GM estimate. At the main \(A\)
scale, GM permits an integrated relative error allowance of order
\(\eta_AH^2\); after division by \(S_A\) this is of order
\(\eta_A\sqrt A\), which is not made small by the cited
subexponential error. This diagnoses an unpaid estimate, not a failure
of the proposed actual signed condition. Actual higher-layer positivity,
almost-all centers or averaged correlations do not establish QGP or
remove \(V_N\).

### Selected global maximum, unknown start and the 5040 boundary

There is a separate zero-extra case under the original **actual proper
deletion plus insertion bridge**. The archived Mantovanelli
`thm:direct-bridge` starts with the same integer \(N>e\) satisfying

\[
N/p>e,\quad G(N)\ge G(N/p)\ (p\mid N),\qquad
G(N)\ge G(Np)\ (p\text{ prime}).
\]

It gives the strict, event-free own-price state
\(N=N_A\), \(K(A)=A\) at \(A=\log N\). Under the full
unchanged selection and properness premises in this source, it applies
to the selected least global maximizer over \(n>5040\). Consequently,
for that same properly bridged source,

\[
E_N=\varnothing,\quad\delta_N=V_N=d_A(N)=0,\quad
M_B=N_B,\quad Y_N(B)=K(B),
\]

and QG3 reduces to

\[
\log\frac{G(N_B)}{G(N_A)}
=w(A)[T_\psi+S_Q]+C_B(K(B)). \tag{QG9}
\]

Only in this separate case does QGP reduce to
\(T_\psi\ge-\kappa S_A\). The terminal defect is still retained;
neither \(K(B)=B\) nor a zero terminal own-price defect is assumed.
GA2 alone supplies insertion comparisons and **does not** supply the
proper deletion bridge or these zero-extra conclusions.

The selected hypothetical global maximizer is a **single source**.
Its existence does not ensure \(A\ge A_*\) or \(A_\kappa\).
Unbounded stable roots are not an unbounded family of global maxima.
The separately documented unbounded GA2 family does not automatically
selfmatch, satisfy QGP, or eliminate its extra inventory. An eventual
argument on that family would require QGP to cover its same members;
no such coverage is established here.

The earlier conditional \(\log N>7.2\cdot10^{46}\) concerns the
same selected least **global maximizer**, under its full previously
declared chain of suppliers. It is **not a least-counterexample bound**
and cannot pay the unknown GM or shorter-drift starts. This appended
argument neither extends that finite interval nor furnishes a numerical
replacement for the common start.

For a useful finite boundary illustration, the declared completed
ordinary 5040 audit reproduced **26 rational/integer checks**: logarithm
enclosures, strict power comparisons and exact Euler ratios. At the own
clock \(A=\log5040\), it gives

\[
N_A=2^3 3^2 5\cdot7=2520,\qquad
E_{5040}=\{(2,4)\},\qquad\delta_{5040}=\log2.
\]

One exact enclosure uses
\(z_x=(x-1)/(x+1)\),
\(L_x=2\sum_{j=0}^{23}z_x^{2j+1}/(2j+1)\) and
\(U_x=L_x+2z_x^{49}/[49(1-z_x^2)]\), for
\(x\in\{2,3,5,7\}\). The positive logarithm series gives
\(L_x<\log x<U_x\). These rational endpoints establish
\(8<A<9\), \(\log8>2\), \(\log9<20/9\), hence
\(15<A\log A<20\) and \(1/20<\lambda(A)<1/15\).
The included terminal layers and excluded next layers are certified by
the following exact integer inequalities:

| Layer | Strict power comparison | Consequence |
|---|---|---|
| \((2,3)\) | \(15^{15}>2\,14^{15}\) | \(r_{2,3}>1/15\) |
| \((3,2)\) | \(13^{15}>3\,12^{15}\) | \(r_{3,2}>1/15\) |
| \((5,1)\) | \(6^{15}>5\,5^{15}\) | \(r_{5,1}>1/15\) |
| \((7,1)\) | \(8^{15}>7\,7^{15}\) | \(r_{7,1}>1/15\) |
| \((2,4)\) | \(31^{20}<2\,30^{20}\) | \(r_{2,4}<1/20\) |
| \((3,3)\) | \(40^{20}<3\,39^{20}\) | \(r_{3,3}<1/20\) |
| \((5,2)\) | \(31^{20}<5\,30^{20}\) | \(r_{5,2}<1/20\) |
| \((7,2)\) | \(57^{20}<7\,56^{20}\) | \(r_{7,2}<1/20\) |
| \((11,1)\) | \(12^{20}<11\,11^{20}\) | \(r_{11,1}<1/20\) |

Stack monotonicity covers preceding and later layers, and strict
antitonicity of \(r_1(q)\) covers every prime \(p\ge11\).
The exact Euler values are
\(Z(2520)=26/7\), \(Z(5040)=403/105\), with ratio \(31/30\).
Therefore, without requiring a GA2 classification of 5040,

\[
d_A(5040)=\lambda(A)\log2-\log(31/30)>0,\qquad
w(A)V_{5040}=(r_{2,4}-\lambda(B))_+\log2,
\]

\[
d_A(5040)+w(A)V_{5040}
=(\lambda(A)-\lambda(B))\log2
+(\lambda(B)-r_{2,4})_+\log2.
\]

The existing
[`GoldenResource5040PriceInterval.lean`](../../D5/S3/Arith/GoldenResource5040PriceInterval.lean)
and
[`GoldenResource5040EndpointComparison.lean`](../../D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison.lean)
already give supporting-price and single-layer comparisons. A supporting
price for 5040 is different from its own clock price. This illustration
explains why a preoccupied \((2,4)\) layer cannot be paid again in a
successor; it is boundary bookkeeping, not a new prime-sign theorem,
GA2 classification, kernel claim or use of the asymptotic GM supplier at
5040.

### Reuse and remaining mathematical work

MS0–MS9/MSP are preserved. In particular their prime-only unpaid MSP
condition is not retrospectively declared proved; QGP is the stated
full-prime-power sufficient condition with the actual preoccupied loss.
The additional ordinary analytic estimate here is QH13/QQE/QQD, obtained
by controlling the signed higher increments and subtracting the paid
reference square term. QG1–QG6 apply the completed finite accounting;
the generic future optimizer, Euler layer factorization, pressure and
proper prime-local bridge are existing mathematics.

The prior pinned-library source observations identify reusable finite
support, factorization, lcm, logarithm and integration interfaces. They
do not certify a new build or a formal GM theorem. This source flight
introduces no Lean wrapper, axiom, compilation, required-check result,
formal or official acceptance. A substantive future formal implementation
must consume the uniform actual cutoff derivative, common support,
GM input or an explicitly retained analytic premise, all endpoint atoms,
whole weighted errors and the same-source finite lcm identity.

QGP, coverage of the unknown common start at the required actual sources,
and the formal analytic implementation remain open. There is no numerical
start, broader exponent claim, new finite interval, priority assertion or
RH completion. The full RH/Robin/5040 research goal remains **ACTIVE**.

## Project application: a tighter sinc allowance reaches 8

This `repo-derived` application retains the complete signed response,
positive law, deterministic transport and unrestricted reserve of the
GAK application above. Its additional estimate is a tighter sine cutoff,
consumed with different law parameters. Under the same primary analytic
premises stated in GAK section 1, it gives a strict Robin margin for
**every** integer in the larger clock interval
\[
 \frac72 10^{46}<A=\log n\le8\cdot10^{46}.
\tag{GAK40}
\]
The original margin \(3/1000\) on the original interval through
\(7.2\cdot10^{46}\) remains valid; the margin for (GAK40) is
\(2/1000\). No primary analytic proof audit, Lean/kernel certification,
least-counterexample bound or unbounded RH estimate is asserted.

### Tighter cutoff using the existing sine tools

For all real \(v\) with \(|v|\ge51/20\),
\[
 \frac{|\sin v|}{|v|}\le\frac7{32}.
\tag{GAK41}
\]
The monotonicity of sinc on \((0,\pi)\), the alternating sine remainder,
the concavity tangent bound and \(|\sin v|\le1\) are standard tools.
Here is their parameter-specific application, without a new general
sinc theorem.

Put \(b=51/20\), \(q_0=7/32\), and
\[
 P_{13}(b)=\sum_{j=0}^{6}\frac{(-1)^jb^{2j+1}}{(2j+1)!}.
\]
The omitted sine tail starts with the negative degree-fifteen term;
successive omitted absolute terms decrease, since already
\(b^2/(16\cdot17)<1\). Thus \(\sin b\le P_{13}(b)\).
Exact rational comparison gives
\[
 q_0b-P_{13}(b)>\frac1{10000}.
\tag{GAK42}
\]
Since sinc decreases on \([b,\pi]\), this pays the first band.

On \([\pi,32/7]\), use the classical bound \(\pi>157/50\) and put
\(t=v-\pi\). Then \(0\le t<501/350\) and \(v<2\pi\), so
\(|\sin v|=\sin t\). The degree-five upper prefix
\[
 P_5(t)=t-t^3/6+t^5/120
\]
has a negative first omitted term and decreasing omitted terms on this
band, and hence \(\sin t\le P_5(t)\). It is concave on
\([0,501/350]\), because \(P_5''(t)=-t+t^3/6\le0\).
With \(t_0=34/25\), exact comparisons give
\[
 \begin{split}
 q_0-P_5'(t_0)&>\frac1{1000},\\
 q_0\frac{157}{50}
   -\bigl(P_5(t_0)-t_0P_5'(t_0)\bigr)&>\frac3{1000}.
 \end{split}
\tag{GAK43}
\]
The tangent upper bound therefore satisfies
\[
 \sin t\le P_5(t)
 \le P_5(t_0)+(t-t_0)P_5'(t_0)
 <q_0(t+157/50)<q_0v.
\]
For \(v\ge32/7\), use \(|\sin v|/v\le1/v\le7/32\).
Reflection supplies the negative axis and proves (GAK41).

### Change the law parameters and retain actual zero real parts

Use the **same whole-law construction** (GAK3)–(GAK6), now with
\[
 H=3\cdot10^{12},\qquad k=21,\qquad
 a=\frac{51}{20H},\qquad x=a^2,\qquad q=\frac{219}{1000}.
\tag{GAK44}
\]
Its mean is exactly one. The parameter-dependent bounds are
\[
 M_*=\frac1{1-2kx},\qquad
 V_*=\frac{kx}{3-(k+3)x},\qquad
 \epsilon=ka+\frac{kx}{1-x}.
\tag{GAK45}
\]
Both denominators are positive, and exact substitution gives
\[
 \epsilon<1/1000,\qquad
 \frac{99}{100}<1-\epsilon\le C
 \le(1-\epsilon)^{-1}<\frac{101}{100}.
\tag{GAK46}
\]
These are full-support bounds, with no discarded scales or conditional
mean. All moment and centered transport hypotheses in GAK therefore
remain available.

For an actual tail zero \(\rho=\beta+i\gamma\), put
\(u=\beta-1\in(-1,0)\), retaining \(|\gamma|\ge H\).
The complex normalization argument of (GAK8), using (GAK41), gives
\[
 |S(a(u+i\gamma))|
 \le\frac7{32}+\frac{20}{51}\frac{a}{1-x},
\]
and consequently
\[
 |H_C(\rho)|\le q_*^{21}<q^{21},\qquad
 q_*:=\frac{7/32+(20/51)a/(1-x)}{1-x}
       <\frac{219}{1000}.
\tag{GAK47}
\]
In particular the normalization \((1-x)^{-1}\) is not omitted.
This bounds **all actual** \(0<\beta<1\), both ordinate signs, and
all tail heights. Critical-line verification is used only on the
original finite head. The head estimate (GAK9) still uses \(M_*\).

### Pay the complete response on the enlarged interval

Retain \(L=\log A\), \(T=\sqrt A L\), the full coefficient
\(F_A\) in (GAK10), all actual multiplicities and endpoint conventions.
The parameter-dependent derivations (GAK18)–(GAK24) apply to the law
(GAK44): replace their original tail damping by \(q^{21}\), and use
the new \(M_*,V_*\). No leading-term replacement or new zero
population is introduced. The signed elementary correction remains in
the complete deterministic response and its allowance.

The lower-clock bounds \(L>107\), \(\sqrt A>10^{23}\) and
\(\eta_0(A)<10^{-6}\) in (GAK25)–(GAK26) are independent of the
upper endpoint. Put
\[
 r=\frac{2829}{1000}10^{23},\qquad
 r^2=8.003241\cdot10^{46}>8\cdot10^{46}.
\tag{GAK48}
\]
Thus \(\sqrt A<r\) throughout (GAK40), including its upper endpoint.
Define exact positive rational allowances
\[
 \begin{split}
 U_h&=\frac{108}{107}\frac{527}{500}\frac1{20}M_*,\\
 U_t&=2\frac{108}{107}\frac{10001}{10000}r
        \frac{37}{25\cdot10^{12}}\left(\frac{219}{1000}\right)^{21},\\
 U_v&=\frac{260001}{500000}rV_*,\qquad
 U_e=\frac{5M_*}{10^{23}},\qquad U=U_h+U_t+U_v+U_e.
 \end{split}
\tag{GAK49}
\]
These increase each positive cost in (GAK23)–(GAK24). They pay the
entire head, infinite tail, centered transport and elementary correction,
respectively. In particular \(A^{\beta-1/2}\le\sqrt A\) is applied
only after retaining the actual tail \(\beta\) in (GAK47).
The reused estimates therefore give \(-T I_\psi(A)<U\).

For the original reserve constant
\[
 Q_R=\frac{67838284064811}{83593750000000},
\]
exact rational substitution in (GAK49) yields
\[
 0.002407<Q_R-U<0.002408,\qquad Q_R-U>\frac2{1000}.
\tag{GAK50}
\]
For orientation only, the rounded contributions are
\(U_h\approx0.0531925234\), \(U_t\approx0.0119215981\),
\(U_v\approx0.7440015715\); the comparison (GAK50) uses the exact
fractions, including \(U_e\).

Reuse (GAK37) and **each integer's actual defect** in (GAK39), at
\(A=\log n\) and \(\lambda=1/(AL)\). It follows that
\[
 \sqrt A\log A\,\Delta(n)
 >\frac2{1000}+\frac{\log A}{(\log A+2)^3}
   +\sqrt A\log A\,d_A(n)>0.
\tag{GAK51}
\]
This proves the stated conditional Robin conclusion on (GAK40), with
no CA hypothesis and without setting \(d_A(n)=0\).

For the separate **same least global maximizer** corollary, retain every
selection, own-price CA, properness, SevenSmooth, Kalyabin,
Axler/Nicolas lower-clock and finite signed-response supplier listed in
GAK section 10. That complete extra chain places the same selected
\(A\) above \((7/2)10^{46}\); (GAK51) then excludes
\(A\le8\cdot10^{46}\). Only under that unchanged extra chain does
the same selected least global maximizer satisfy
\(\log N>8\cdot10^{46}\). This is not a bound for the least Robin
counterexample, or a transfer to an unbounded selected family.

### Reuse, certificates and the remaining unbounded gap

The positive law, full-response exchange, deterministic transport,
reserve and integer-defect identity are reused from GAK. Standard sine
tools supply the cutoff calculation; no new general theorem or global
originality claim is made. The actual gain over the original GAK
parameters is quantitative: at (GAK48), their same rational allowance
exceeds \(Q_R\), while (GAK49) pays it with margin (GAK50).

The parameter-specific
[exact rational program and results](https://github.com/the-omega-institute/trureturing-experiments/tree/0f4e4f1e8c1f1923dfbccc1903257d698d6db49f/experiments/robin-sinc-clock-8e46)
check the sine-prefix and tangent comparisons, denominator positivity,
whole support, actual-real-part normalization, square-root endpoint and
complete allowance. Their 20 comparisons use rational arithmetic;
decimal displays are not evidence. They do not certify the named
external analytic inputs or the full analytic inference in Lean.

For this fixed law \(V_*>0\) and \(q^{21}>0\). Its positive
transport and unverified-tail allowances still grow with \(\sqrt A\).
Thus (GAK51) supplies a finite interval improvement only. The original
unbounded same-source signed-tail estimate and RH remain open.

## Project application: terminal values and all-branch actual-source error budgets

This section uses the actual objective and the unrestricted pressure of
[FIB §§85, 87 and 98](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md),
the finite-tail formula in [ZE, “定理 1.1：尾积分的有限算式” and
“定理 1.2：压力余量的精确二分解”](../../docs/develop/theory/ZECKENDORF_EULER_5040.md),
and the complete shorter-successor result (QH13), (QQE), (QQD) and
(QG1)–(QG8) above. In particular, the proof of the full signed shorter
$Q$ drift is reused. The additional estimate is a uniform all-branch
quadrature and literal-competitor error budget at the last prime label of
the same actual integer. Its consumers below are an exact terminal
$\Xi$ identity and a finite comparison with a legal integer competitor.

All arithmetic values $G(n)$ and $F(n)$ below have $n\ge3$; every use
of $f(x)$, $\lambda(x)$ or $w(x)$ has $x>1$. Write
\[
Z(n)=\frac{\sigma(n)}n,\qquad W(n)=\log Z(n),\qquad
G(n)=\frac{Z(n)}{\log\log n},\qquad
F(n)=\log G(n)=W(n)-f(\log n),
\]
\[
f(x)=\log\log x,\qquad \lambda(x)=\frac1{x\log x},\qquad
w(x)=-\lambda'(x)=\frac{\log x+1}{x^2(\log x)^2}.
\tag{AVB01}
\]
Thus $f(\log n)=\log\log\log n$. Direct differentiation gives
$f''=-w<0$ and
\[
w'(x)=-x^{-3}\left(\frac2{\log x}+
 \frac3{(\log x)^2}+\frac2{(\log x)^3}\right)<0.
\]
The constant $\gamma$ throughout is the original Euler constant. The full
signed target remains
\[
\boxed{\quad
\forall n\in\mathbb N,\quad n>5040\Longrightarrow
 I_\psi(\log n)+R(\log n)+d_{\log n}(n)>0.
\quad}
\tag{AVB02}
\]
It is active and unproved. This section proves ordinary mathematical
estimates relative to the stated analytic source inputs.

### Actual attainment, strict inventories and the terminal value

For a prime $p$ and $k\ge1$, retain the Euler layer notation
\[
h_p=\log p,\qquad
\ell_{p,k}=\log\left(1+\frac1{p+\cdots+p^k}\right),\qquad
r_{p,k}=\frac{\ell_{p,k}}{h_p},\qquad c_p=\ell_{p,1}.
\]
Finite Euler telescoping gives $W(n)=\sum_{(p,k)\text{ occupied}}\ell_{p,k}$.
The prices decrease strictly with $k$, first prices decrease strictly
with $p$, and $0<r_{p,k}<1/(p^k\log p)$. Use the strict inventory
\[
N_x=\prod_p p^{\#\{k\ge1:r_{p,k}>\lambda(x)\}},\qquad
K(x)=\log N_x,\qquad
\psi(x)=\sum_{p^k\le x}\log p,\qquad Q(x)=K(x)-\psi(x).
\tag{AVB03}
\]
The actual inventory is strict, whereas $\psi$ is weak and
right-continuous. For each $x>1$ the inventory is finite, and $N_x$
increases by divisibility. These are the existing FIB §98.1–98.2 and
(QG1) conventions, with the actual layer cutoffs of ZE Definition 7.1,
equation (20), and the [existing actual-state definition](#same-actual-state-finite-support-and-endpoint-correction)
above.

An actual GA2 integer $q\ge3$ satisfies $G(qm)\le G(q)$ for every positive
integer $m$. Let $\mathcal D_m$ be all positive multiples of $m\ge3$.
The ordinary source input used to supply actual attainment is
\[
(U)\qquad \forall X>0\ \exists q\ge3\text{ actual GA2},\quad \log q\ge X.
\tag{AVB04}
\]
Caveney–Nicolas–Sondow, *On SA, CA, and GA numbers*,
[arXiv:1112.6010v2, Theorem 5(iii)](https://arxiv.org/abs/1112.6010v2),
supplies this input under RH failure. The family used here is conditional
on that source supply.

For clarity, the reused attainment argument concerns actual $G$, rather
than the fixed-price objective. If $m\mid q$ and $q$ is actual GA2, then
for any $n\ge3$, the legal multiple $L=\operatorname{lcm}(q,n)$ satisfies
$Z(n)\le Z(L)$ and $L\le qn$. Since all log-log denominators are positive,
\[
G(n)\le G(q)\frac{\log\log(qn)}{\log\log n}
 \le G(q)\left(1+\frac{\log q}{\log n\,\log\log n}\right).
\tag{AVB05}
\]
If some member of $\mathcal D_m$ has value strictly above $G(q)$, this
vanishing tail bound puts all sufficiently late class members strictly
below that value, and a nonempty finite initial piece attains the full
class maximum. Otherwise $q$ already attains it. Input $U$ supplies a
divisible witness for each $m$: choose a price below every occupied price
of $m$ and use GA2 insertion at a sufficiently large $q$.
Indeed insertion implies
\[
r_{p,v_p(q)+1}h_p
 \le f(\log q+h_p)-f(\log q)<\lambda(\log q)h_p,
\]
so every layer with $r_{p,k}\ge\lambda(\log q)$ is occupied.

For every attaining $N\in\mathcal D_m$, including all ties, insertion
and deletion above a forced exponent give, at $A=\log N$,
\[
r_{p,v_p(N)+1}<\lambda(A),\qquad
v_p(N)>v_p(m)\Longrightarrow r_{p,v_p(N)}>\lambda(A).
\]
Deletion is legal because $m\mid N/p$ and $N/p\ge m\ge3$. Its clock
$A-h_p$ is consequently greater than $1$, and strict concavity gives the
second strict inequality. Stack monotonicity yields the characterization
\[
N=\operatorname{lcm}(m,N_A).
\tag{AVB06}
\]
Every such attaining integer is actual GA2.

For prime $p\ge29$, define $N_p$ as the least attaining natural number
on $\mathcal D_{5040p}$, and put $A_p=\log N_p$, $v(p)=F(N_p)$.
Here $N_p\ge5040p$ gives $A_p>11$. The forced 5040 core is strictly
active at every $x>11$: its terminal prices satisfy
$r_{2,4}>1/22$, $r_{3,2}>2/39$, $r_{5,1}>1/12$ and
$r_{7,1}>1/16$, while $\lambda(x)<1/22$.
These inequalities follow respectively from
$(31/30)^{22}>1+22/30+231/900+1540/27000>2$,
$\log(13/12)>1/13$, $\log3<3/2$, and
$\log5,\log7<2$. Earlier layers have larger prices. Thus (AVB06)
at $m=5040p$ becomes, for every maximizer in that class,
\[
N=\operatorname{lcm}(p,N_A),\qquad
E_N:=\{(q,k)\text{ occupied in }N:r_{q,k}\le\lambda(A)\}
 \subseteq\{(p,1)\}.
\tag{AVB07}
\]
The extra is either empty or precisely the forced first $p$-layer.
The lower bound $A_p>11$ follows, for example, from
$5040>2^{12}$, $\log2>2/3$, $p\ge29>3^3$ and $\log3>1$.

Use Gronwall in its original normalization: the limiting upper and
lower envelopes concern $G(n)/e^\gamma$. This is the
$\mathrm{robinRatio}$ normalization in
[PaddingRatio](../../D5/S3/Arith/Robin/PaddingRatio.lean);
the interfaces are
[gronwall_lower_envelope](../../D5/S3/Weil/GronwallLowerEnvelope.lean)
and [gronwall_upper_envelope](../../D5/S3/Weil/GronwallUpperEnvelope.lean).
The ordinary lower envelope at arbitrarily large $n$, combined with
(AVB05), gives $G(q)\ge e^\gamma$ for every actual GA2 $q\ge3$.
Since $N_p\ge5040p\to\infty$, the upper envelope now implies
\[
G(N_p)\longrightarrow e^\gamma,\qquad
v(p)\ge\gamma,\qquad v(p)\longrightarrow\gamma.
\tag{AVB08}
\]
The final limit uses positivity and continuity of the real logarithm.
Neither zero nor $1$ is the terminal $F$ value.

Strict excess uses the additional ordinary input
\[
(U^+)\qquad
\forall X>0\ \exists q\ge3\text{ actual GA2},\quad
 \log q\ge X,\quad G(q)>e^\gamma.
\tag{AVB09}
\]
It follows under RH failure from the positive oscillation on CA integers
and tail-maximizer construction in CNS, pp.15–16: for every integer
$T\ge5041$, choose $n_0\ge T$ with $G(n_0)>e^\gamma$.
Gronwall's upper envelope makes all sufficiently late values strictly
smaller than $G(n_0)$, so the full tail $n\ge T$ attains a maximum
strictly above $e^\gamma$ in a finite initial piece. Its maximizer is
GA2 because every positive multiple stays in that tail.
Taking $T\ge e^X$ proves $U^+$.

For fixed $p\ge29$, use $U^+$ with $\log q\ge p+1$ and
\[
r_{p,1}>\frac1{(p+1)\log p}>\lambda(p+1).
\]
GA2 insertion and the active 5040 core give $5040p\mid q$.
Actual maximality in $\mathcal D_{5040p}$ then gives $v(p)>\gamma$.
This is the only use of $U^+$ here. The error budgets below need
$v(p)-\gamma\ge0$ and the terminal limit in (AVB08), and do not use
strict excess or transport a signed estimate from this witness $q$.

### Canonical order and legal brackets on every branch

The finite Euler identity for $g=\gcd(X,Y)\ge3$ and
$l=\operatorname{lcm}(X,Y)$ is $W(g)+W(l)=W(X)+W(Y)$.
With $z=\log g>1$, $u=\log(X/g)$ and $v=\log(Y/g)$,
\[
F(g)+F(l)-F(X)-F(Y)
 =\int_0^u\int_0^v w(z+s+t)\,dt\,ds\ge0.
\tag{AVB10}
\]
Equality holds exactly when $u=0$ or $v=0$, that is, when the integers
are nested by divisibility. This is finite Euler min/max modularity and
strict concavity on the displayed positive-log rectangle.

For nested imposed classes $m\mid d$, the meet of an $m$-maximizer
and a $d$-maximizer is a legal $m$-competitor, and their join a legal
$d$-competitor. Summed maximality and (AVB10) force nesting and equality
of both value comparisons. If the $m$-maximizer is least, its meet is
itself. Hence it divides every attaining $d$-maximizer. Least attainment
is essential for this canonical conclusion.

Fix primes $29\le p<r$, set $\delta=\log(r/p)>0$,
$A=A_p$ and $C=A_r$. If $p\mid N_r$, their meet is a legal
$\mathcal D_{5040p}$ competitor and their join a legal
$\mathcal D_{5040r}$ competitor. Applying the same argument gives
$N_p\mid N_r$, $A\le C$ and $v(p)\ge v(r)$.
The fact that a meet contains 5040 alone would not justify the
$p$-class comparison.

If $p\nmid N_r$, (AVB07) and first-price antitonicity give
$N_r=rV$, $V=N_C$, with $p,r$ absent from $V$ and $5040\mid V$.
The completed integer $pV$ is legal in $\mathcal D_{5040p}$, and
\[
F(pV)-F(rV)=c_p-c_r+f(C)-f(C-\delta)>0.
\]
Thus $v(p)>v(r)$, and $r\nmid N_p$, since otherwise $N_p$ would be
a legal $r$-class competitor. Put $k=v_p(N_p)\ge1$. The two completed
replacements $rN_p/p$ and $pN_r/r$ are legal in their opposite classes;
both retain the full 5040 core, and their clocks $A+\delta,C-\delta$
exceed $1$. Their combined Euler increment is exactly
$c_p-\ell_{p,k}\ge0$, not a first-layer removal when $k>1$.
If $A+\delta>C$, these two replacement clocks are strictly more
spread with the same sum than $A,C$. Strict concavity decreases the
summed $f$ values, so the summed $F$ values strictly increase, contradicting
the two actual maximality comparisons. Consequently $C-A\ge\delta$.
Only now can one deduce $N_A\mid N_C$, $p\nmid N_A$, and $k=1$.
Thus on this nonnested branch
\[
N_p=pU,\quad N_r=rV,\quad U=N_A\mid V=N_C,\quad
p,r\nmid V,\quad D=\log(V/U)=C-A-\delta\ge0.
\tag{AVB11}
\]
The literal legal competitors $pV$ and $rU$ give
\[
c_p-c_r+f(C)-f(C-\delta)
 \le v(p)-v(r)
 \le c_p-c_r+f(A+\delta)-f(A).
\tag{AVB12}
\]
The lower bracket is used only on this branch.

The upper bracket holds on every branch. When $r\nmid N_p$, comparison
with $rN_p/p$ gives
\[
v(p)-v(r)
 \le\ell_{p,k}-c_r+f(A+\delta)-f(A)
 \le c_p-c_r+f(A+\delta)-f(A).
\tag{AVB13}
\]
When $r\mid N_p$, value order and feasibility give equality of values.
The preceding nonnested argument excludes $p\nmid N_r$, so
$N_p\mid N_r$. Least attainment in the $r$-class gives $N_r\le N_p$,
and therefore $N_r=N_p$. The zero drop obeys (AVB13).
This proves both canonical clock order and
\[
A_p\le A_r,\quad v(p)\ge v(r),\qquad
N_p=N_r\ \Longleftrightarrow\ r\mid N_p.
\tag{AVB14}
\]

A repeated-source plateau has $E_N=\varnothing$, since (AVB07)
puts that same extra set in each of two distinct singleton labels.
A distinct-clock equal-value transition is nested, but is retained.
Its arriving source also has empty extra: otherwise $N_r=rV$ with
$p\mid V$, $5040p\mid V$, and $c_r\le\lambda(C)\log r$.
The legal $p$-competitor $V$ has clock $C-\log r>1$, and strict
concavity gives
\[
F(V)-F(N_r)=f(C)-f(C-\log r)-c_r>0,
\]
contradicting $F(N_r)=v(p)$. No existence of such transitions is assumed.

On every nested edge $p\mid N_r$, the distinct labels and (AVB07)
put $p$ in $N_C$. Thus
$\lambda(C)<r_{p,1}<\lambda(p)$, whence
\[
C>p.
\tag{AVB15}
\]
In particular the active price at a nested arrival is
$\lambda(C)<\lambda(p)$. This includes plateaus and will pay their
toll without applying the nonnested lower bracket.

### Convergence before subtraction and the actual competitor deficiencies

Let $p_0=29<p_1<\cdots$ be consecutive ordinary primes.
Write $N_i=N_{p_i}$, $A_i=\log N_i$, $v_i=v(p_i)$,
$c_i=c_{p_i}$, $\delta_i=\log(p_{i+1}/p_i)$ and
$\Delta v_i=v_i-v_{i+1}\ge0$.
For a starting index $j$ set $e_j=v_j-\gamma\ge0$.
By (AVB08), $\sum_{i\ge j}\Delta v_i=e_j$.
Initially define the nonnegative extended sum
\[
L_j=\sum_{i\ge j}\delta_i\lambda(A_{i+1}).
\tag{AVB16}
\]
On nonnested edges, the lower bracket (AVB12) implies
$\delta_i\lambda(A_{i+1})\le\Delta v_i$.
On every other edge (AVB15) bounds the summand by
$\delta_i\lambda(p_i)$.

Bertrand gives $p_{i+1}<2p_i$ and $\delta_i\le\log2$.
On $u\in[\log p_i,\log p_{i+1}]$,
\[
\frac{e^{-\log p_i}/\log p_i}{e^{-u}/u}
 \le2\left(1+\frac{\log2}{\log29}\right)<3.
\]
These consecutive intervals cover the entire logarithmic prime tail.
Therefore
\[
\sum_{i\ge j}\delta_i\lambda(p_i)
 \le3\int_{\log p_j}^\infty\frac{e^{-u}}u\,du
 \le\frac3{p_j\log p_j}.
\tag{AVB17}
\]
It follows first that $L_j\le e_j+3/(p_j\log p_j)<\infty$.
Monotonicity and cofinality of $A_i$ then give
\[
0\le\sum_{i\ge j}\delta_i
 [\lambda(A_i)-\lambda(A_{i+1})]
 \le(\log2)\lambda(A_j).
\tag{AVB18}
\]
This is a full nonnegative telescope, including zero plateau increments.
In particular $\sum_{i\ge j}\delta_i\lambda(A_i)$ is finite.
Only with these convergences established do we sum (AVB13), using
$c_i\to0$ and $v_i\to\gamma$, to obtain
\[
-\frac3{p_j\log p_j}\le e_j-L_j
 \le c_j+(\log2)\lambda(A_j).
\tag{AVB19}
\]

Define the actual upper-bracket allowance and slack by
\[
b_i=f(A_i+\delta_i)-f(A_i)
 =\int_0^{\delta_i}\lambda(A_i+t)\,dt,\qquad
\tau_i=c_i-c_{i+1}+b_i-\Delta v_i\ge0.
\tag{AVB20}
\]
Here $0\le b_i\le\delta_i\lambda(A_i)$, so its sum converges.
At a finite endpoint $m$ the exact identity is
\[
\sum_{i=j}^m\tau_i
 =c_j-c_{m+1}+\sum_{i=j}^m b_i-e_j+e_{m+1}.
\]
Passing to infinity in these convergent terms gives
\[
e_j=c_j+\sum_{i\ge j}b_i-\sum_{i\ge j}\tau_i,\qquad
0\le\sum_{i\ge j}\tau_i
 \le c_j+\frac3{p_j\log p_j}+(\log2)\lambda(A_j).
\tag{AVB21}
\]
For the inequality, use $\sum b_i\le L_j+(\log2)\lambda(A_j)$ and
$L_j-e_j\le3/(p_j\log p_j)$. There is no subtraction of divergent
positive series.

Choose a literal legal successor-class competitor on every edge:
\[
X_i=
 \begin{cases}
 N_i,&p_{i+1}\mid N_i,\\
 p_{i+1}N_i/p_i,&p_{i+1}\nmid N_i,
 \end{cases}
\qquad
\eta_i=v_{i+1}-F(X_i)\ge0.
\tag{AVB22}
\]
The first case is precisely a plateau by (AVB14), with $\eta_i=0$
and $\tau_i=c_i-c_{i+1}+b_i$.
In the second case let $k_i=v_{p_i}(N_i)$.
Finite Euler subtraction, removing the actual terminal $k_i$-layer,
gives exactly
\[
\tau_i=\eta_i+c_i-\ell_{p_i,k_i}.
\tag{AVB23}
\]
Thus $0\le\eta_i\le\tau_i$ on every edge, including distinct nested
arrivals. The kth-layer correction and the plateau allowance are
retained; $\eta_i$ is a deficiency of a legal completed integer.

### Last label, uniform constants and the actual Stieltjes representation

Fix a source $N=N_p$, put $A=\log N$ and $s=P^+(N)$.
Since $s\ge p\ge29$ and $5040s\mid N$, feasibility gives
$v(s)\ge F(N)=v(p)$; value order gives equality.
Least attainment gives $N_s\le N$, while canonical clock order gives
$A_s\ge A_p$. Hence $N_s=N$.
More generally, the labels whose clocks are at most $A$ are exactly
the primes $29\le r\le s$. For $r\le p$ use clock order.
For $p<r\le s$, either this case is empty because the extra is nonempty
and $s=p$, or $N=N_A$ and the first-layer prime prefix gives $r\mid N$.
The legal meet comparison gives $N_r\mid N$, hence $A_r\le A$.
If $r>s$, clock order gives $A_r\ge A$, and equality would give
$N_r=N$, contradicting $r\mid N_r$ and $r\nmid N$.
Thus $s$ is the last label producing this integer. Plateau labels form
a consecutive finite block, whose last label is $s$; a nonempty extra
has only its own label.

The real first-layer cutoff $q_1(A)$ solves
$r_{q_1(A),1}=\lambda(A)$ as in ZE Definition 7.1.
The elementary strict bounds
$r_{A-1,1}>1/[A\log(A-1)]>\lambda(A)$ and
$r_{A,1}<\lambda(A)$ give
\[
A-1<q_1(A)<A.
\]
If the extra is nonempty, $s=p$ and $r_{p,1}\le\lambda(A)$.
The inequality $r_{p,1}>1/[(p+1)\log p]$ excludes $p\le A-1$,
so $s>A-1$.
If it is empty, $N=N_A$. Put $m=\lfloor(A-1)/2\rfloor\ge5$.
Bertrand gives a prime $m<q<2m\le A-1<q_1(A)$, so $q\mid N_A$.
In both cases,
\[
s>\frac A3;
\qquad
\text{in the empty-extra case }
s\ge q>m\ge\frac{A-3}2>\frac A3,\quad s<A.
\tag{AVB24}
\]
The comparison $(A-3)/2>A/3$ uses $A>11$, and $s<A$ uses
$\lambda(A)<r_{s,1}<\lambda(s)$.
An extra prime is not bounded above by $A$.

Relabel the same tail by choosing $j$ with $p_j=s$ and write
$e_s=e_j$, $L_s=L_j$, $u_s=e_s-L_s$.
Since $c_s<1/s<3/A$, $3/(s\log s)\le9/A$, and
$(\log2)\lambda(A)<1/A$, (AVB19)–(AVB23) imply
\[
\boxed{\quad |v(s)-\gamma-L_s|=|u_s|\le\frac9A,\qquad
 \sum_{i\ge j}\eta_i\le\sum_{i\ge j}\tau_i\le\frac{13}A.\quad}
\tag{AVB25}
\]
The upper side of (AVB19) is already less than $4/A$.
With $S_A=A^{11/10}$,
\[
\frac{1/A}{w(A)S_A}
 =A^{-1/10}\frac{(\log A)^2}{1+\log A}\longrightarrow0.
\tag{AVB26}
\]
The bound depends only on $A$, so its supremum over all actual sources
with clocks at least a real $T$ tends to zero as $T\to\infty$.
These are paid errors at the consumed scale. Neither $e_s$ nor $L_s$
is asserted individually small at that scale.

For this terminal tail, denote its cumulative logarithmic label mass by
\[
J_s(t)=\sum_{\substack{i\ge j\\A_{i+1}\le t}}\delta_i
 \quad(t\ge A).
\tag{AVB27}
\]
This local $J_s(t)$ has a real clock argument; the divisor deficit
$J_s(d)$ near the beginning of this note is a different function.
Last-label characterization proves $A_{i+1}>A$ for every $i\ge j$,
so $J_s(A)=0$. The function is right-continuous and locally finite:
$A_{i+1}\le t$ implies $p_{i+1}\le e^t/5040$, leaving only finitely
many labels on every compact interval. Simultaneous future clocks,
including repeated future plateaus, have one aggregated atom of mass
$\sum_{A_{i+1}=t}\delta_i$.

If $p_k$ is the last included successor label, telescoping gives
$J_s(t)=\log(p_k/s)$; if there are no included labels the mass is zero.
Since $5040p_k\le e^t$ and $5040s\le e^A$,
\[
0\le J_s(t)\le t-\log5040-\log s,\qquad
\lambda(t)J_s(t)\longrightarrow0.
\tag{AVB28}
\]
Finite Stieltjes integration by parts, with atoms in $(A,T]$, gives
\[
\int_{(A,T]}\lambda(t)\,dJ_s(t)
 =\lambda(T)J_s(T)+\int_A^T J_s(t)w(t)\,dt.
\]
The left side increases to the already proved convergent $L_s$ in
(AVB16)–(AVB18). Equation (AVB28) removes the boundary at infinity.
Consequently the actual representation is
\[
\boxed{\quad
L_s=\int_{(A,\infty)}\lambda(t)\,dJ_s(t)
    =\int_A^\infty J_s(t)w(t)\,dt<\infty.
\quad}
\tag{AVB29}
\]
This convergence follows from the all-branch value bound before the
integration-by-parts limit. The crude estimate $J_s(t)\le t$ would
not establish it, since $\int^\infty t\,w(t)\,dt$ diverges.

### Weighted nonnested jump width and its limitation

On a nonnested consecutive edge retain (AVB11), with
$N_i=p_iU_i$, $N_{i+1}=p_{i+1}V_i$,
$D_i=\log(V_i/U_i)$, $A=A_i$, $\delta=\delta_i$ and
$C=A_{i+1}=A+D_i+\delta$.
The two literal competitors define distinct nonnegative deficiencies
\[
\alpha_i=v_i-F(p_iV_i),\qquad
\beta_i=v_{i+1}-F(p_{i+1}U_i)=\eta_i.
\]
The equality with $\eta_i$ uses $k_i=1$ on this branch.
The exact comparisons are
\[
\begin{aligned}
\Delta v_i&=c_i-c_{i+1}+f(C)-f(C-\delta)+\alpha_i,\\
\Delta v_i&=c_i-c_{i+1}+f(A+\delta)-f(A)-\beta_i.
\end{aligned}
\]
Subtracting gives the complete bracket width
\[
\alpha_i+\beta_i
 =\int_0^\delta\int_0^{D_i}w(A+x+t)\,dt\,dx
 =\int_0^\delta[\lambda(A+x)-\lambda(A+D_i+x)]\,dx.
\tag{AVB30}
\]
Decrease of $w$ yields the lower bound $w(C)\delta D_i$.
Also $f(C)-f(C-\delta)\ge\delta\lambda(C)$ and
$f(A+\delta)-f(A)\le\delta\lambda(A)$, so the width is at most
$\delta[\lambda(A)-\lambda(C)]$. Enlarging the nonnegative subset sum
to the full telescope (AVB18) proves
\[
\sum_{\substack{i\ge j\\\text{nonnested}}}
 w(A_{i+1})\delta_iD_i
 \le\sum_{\substack{i\ge j\\\text{nonnested}}}(\alpha_i+\beta_i)
 \le(\log2)\lambda(A_j).
\tag{AVB31}
\]
This does not telescope over only the selected edges.

If $D_i=0$, the width forces $\alpha_i=\beta_i=0$.
If $D_i>0$, the legal integer $p_{i+1}U_i$ is strictly smaller than
the least attaining $N_{i+1}$, so $\beta_i>0$.
Least attainment provides no quantitative lower separation of their
real values. The distinction between $\alpha_i$, $\beta_i$ and the
all-branch $\eta_i$ matters: the $13/A$ budget controls replacement
deficiencies $\eta_i$, whereas $\alpha_i$ is controlled here by the
width, and is not that replacement deficiency.

For fixed $A,\delta$, the width in (AVB30) increases with $D$ to the
finite value $f(A+\delta)-f(A)$ as $D\to\infty$, whereas
$w(A+D+\delta)\delta D\to0$.
Thus (AVB31) weights remote jumps weakly and provides no clock mesh.
Nested branches, including distinct equal-value arrivals, remain outside
the nonnested width identity and are still included in (AVB25).

### Correct centered coupling with the original complement

Retain every prime-power reference weight and the unrestricted pressure:
\[
P(x)=\sum_{q^k\le x}\frac1{kq^k},\qquad
\mathscr S(c)=\sum_{q,k}(r_{q,k}-c)_+\log q,\qquad
R(x)=P(x)-\lambda(x)\psi(x)-\mathscr S(\lambda(x)).
\tag{AVB32}
\]
The pressure argument has $c>0$. Here $(z)_+=\max(z,0)$; a positive
part is multiplied by $\log q$.
The sums defining $P$ and the positive pressure are finite at each
admitted point. This is FIB §87.3 and §98.1, with the same pressure
as (QG4) and the original $R$ in (GAK39). The reference coefficient is
$1/(kq^k)$, whereas a $\psi$ or $\Lambda$ atom has mass $\log q$.
They have different roles.

On every compact interval $[a_0,b_0]\subset(1,\infty)$, a positive
minimum price and $r_{q,k}<1/(q^k\log q)$ give one common finite support
for all possible pressure terms and activation ties. There are also
only finitely many reference prime-power atoms.
At $x=q^k$ the jump of $P$ is exactly
$1/(kq^k)=\lambda(q^k)\log q$, so the jump of $\lambda\psi$
cancels it. Between atoms $(P-\lambda\psi)'=\psi w$.
The finite positive-part pressure is continuous at activation ties,
locally absolutely continuous, and has derivative $Kw$ almost
everywhere. Strict choices at the events do not change that derivative.
Thus $R$ is locally absolutely continuous and, for arbitrary endpoint
events and $B>A>1$,
\[
R(B)-R(A)=-\int_A^B Q(t)w(t)\,dt.
\tag{AVB33}
\]
No differentiation of an untruncated infinite pressure series is involved.

Let $H=B-A$, $a=\lambda(A)$, $b=\lambda(B)$ and
$\rho_A(u)=w(A+u)/w(A)$. Keep the original centered definitions
\[
T_\psi(A,H)=\int_0^H[\psi(A+u)-\psi(A)-u]\rho_A(u)\,du,
\quad
S_Q(A,H)=\int_0^H[Q(A+u)-Q(A)]\rho_A(u)\,du.
\]
The original effective-PNT/Mertens normalization of (GAK38) and FIB
§87.3 gives
\[
I_\psi(x)=\int_x^\infty(\psi(t)-t)w(t)\,dt
 =\gamma+f(x)-P(x)+\lambda(x)(\psi(x)-x).
\tag{AVB34}
\]
The convergent tail and its original Euler constant are retained.
Subtracting its tails over $[A,B]$ and then its initial centered value
gives the required identity with the full price-drop factor:
\[
\boxed{\quad
w(A)T_\psi(A,H)
 =I_\psi(A)-I_\psi(B)-(\psi(A)-A)(a-b).
\quad}
\tag{AVB35}
\]
Indeed the centered integrand is
$(\psi(t)-t)-(\psi(A)-A)$ and $\int_A^B w=a-b$.
Similarly (AVB33) yields
\[
w(A)S_Q(A,H)=R(A)-R(B)-Q(A)(a-b).
\tag{AVB36}
\]
These finite centered subtractions preserve the weak-reference initial
atom convention and do not assume an additional infinite-tail limit.

For the same actual source $N=N_s$ at $A=\log N$, write
\[
\delta_N=A-K(A)=\sum_{e\in E_N}h_e,\qquad
d_A(N)=\mathscr S(a)-W(N)+aA
       =\sum_{e\in E_N}(a-r_e)h_e.
\]
Use exactly the (QG1), (QG5) preoccupied inventory and loss:
\[
P_N(x)=\sum_{\substack{e\in E_N\\r_e>\lambda(x)}}h_e,\qquad
V_N(A,H)=\int_0^H P_N(A+u)\rho_A(u)\,du,
\]
\[
w(A)V_N=\sum_{e\in E_N}(r_e-b)_+h_e,\qquad
R_{\rm term}(N,B)=\sum_{e\in E_N}(b-r_e)_+h_e.
\tag{AVB37}
\]
Since every $r_e\le a$, scalar positive-part algebra gives, including
own-price and terminal ties,
\[
d_A(N)+w(A)V_N=(a-b)\delta_N+R_{\rm term}(N,B).
\tag{AVB38}
\]
This is exactly (QG6); the terminal residual is retained.

At its own clock, the unrestricted finite identity (GAK39), also
(OCQ13), gives
\[
I_\psi(A)+R(A)+d_A(N)=\gamma-F(N)=-e_s.
\tag{AVB39}
\]
It concerns this actual integer $N$, not just its subinventory $N_A$.
Adding (AVB35) and (AVB36), using
$\psi(A)-A+Q(A)=K(A)-A=-\delta_N$, and subtracting $w(A)V_N$,
then gives
\[
\begin{aligned}
w(A)(T_\psi+S_Q-V_N)
 &=I_\psi(A)+R(A)-I_\psi(B)-R(B)+(a-b)\delta_N-w(A)V_N\\
 &=-e_s-I_\psi(B)-R(B)-R_{\rm term}(N,B).
\end{aligned}
\tag{AVB40}
\]
Immediately consume (AVB25) and (AVB29), at the same last label
$s=P^+(N)$, by defining
\[
\Xi_s(B)=L_s+I_\psi(B)+R(B)+R_{\rm term}(N,B).
\]
The exact result is
\[
\boxed{\quad w(A)(T_\psi+S_Q-V_N)=-\Xi_s(B)-u_s,\qquad
 |u_s|\le9/A,\quad u_s=o(w(A)S_A)\text{ uniformly}.\quad}
\tag{AVB41}
\]
This pays the replacement of the actual terminal excess by its
actual Stieltjes integral. It does not pay $L_s$, $e_s$, the original
tail, $R(B)$ or the terminal residual separately.

For explicit singleton bookkeeping let $r=r_{s,1}$ and $h=\log s$.
The literal strict successor and clock are
$M_B=\operatorname{lcm}(N,N_B)$ and $Y=Y_N(B)=\log M_B$.
In both extra branches the exact formulas are
\[
\begin{aligned}
Y&=K(B)+\mathbf1_{r\le b}h, &
d_A(N)&=(a-r)_+h,\\
w(A)V_N&=\mathbf1_{r\le a}(r-b)_+h,&
R_{\rm term}(N,B)&=(b-r)_+h.
\end{aligned}
\tag{AVB42}
\]
The indicator in $V_N$ excludes an already active first layer.
When the extra is empty $r>a$ and all the displayed extra terms vanish.
At $r=a$ the forced extra has zero own-price defect but its full
$w(A)V_N=(a-b)h$. At $r=b$ it remains in $Y$ although both its
$V_N$ contribution and terminal residual vanish. At $r<b$ it remains
in $Y$ and has positive terminal residual. Missing neutral terminal
layers are excluded by $N_B$; deliberately adding them would change
the literal $Y$ and its terminal cost.

### A finite actual competitor consumes the jump budget at the same cost

Reuse the exact (QG3) finite identity for the same $N$:
\[
F(M_B)-F(N)=w(A)(T_\psi+S_Q-V_N)+C_B(Y),\qquad
C_B(y)=f(B)+b(y-B)-f(y)\ge0\quad(y>1).
\tag{AVB43}
\]
Here $Y=\log\operatorname{lcm}(N,N_B)$ is literal and need not equal $B$;
strict concavity gives $C_B(y)=0$ exactly when $y=B$.
The existing maximizing-multiple construction
[GoldenFutureExtensionMaximum](../../D5/S3/Arith/GoldenFutureExtensionMaximum.lean),
in particular golden_future_extension_maximum_attained, and
[GoldenColossalClosure](../../D5/S3/Arith/GoldenResource/GoldenColossalClosure.lean),
maximizes $W-b\log n$ over multiples of $N$ by installing all missing
positive-price layers. It is the fixed-price construction used in
(QG1)–(QG3), not an actual-$G$ optimization assertion.

Take a nonnested consecutive edge starting at $N=N_i=p_iU_i$.
Here the departing extra is nonempty, so its last label is $s=p_i$.
Let the literal integer $Z=p_iV_i$ have clock $z=A+D_i$.
Since $U_i\mid V_i$, $Z$ is a multiple of the same $N$, and
$F(Z)=F(N)-\alpha_i$. Fixed-price maximality gives
$W(M_B)-bY\ge W(Z)-bz$.
The identity
$W(X)-b\log X=F(X)+f(B)-bB-C_B(\log X)$
then gives
\[
F(M_B)-F(N)\ge-\alpha_i+C_B(Y)-C_B(A+D_i).
\tag{AVB44}
\]
The $C_B(Y)$ here is exactly the one in (AVB43). Cancelling that
same cost yields the finite, original-objective comparison
\[
T_\psi(A,H)\ge-S_Q(A,H)+V_N(A,H)
 -\frac{\alpha_i+C_B(A+D_i)}{w(A)}.
\tag{AVB45}
\]
From (AVB31) at $j=i$, $\alpha_i\le(\log2)\lambda(A)$, and
$\lambda(A)/w(A)=A\log A/(1+\log A)<A$. Therefore
\[
\boxed{\quad
T_\psi(A,H)\ge-S_Q(A,H)+V_N(A,H)
 -(\log2)A-\frac{C_B(A+D_i)}{w(A)}.
\quad}
\tag{AVB46}
\]
This is a real finite consumer of the weighted nonnested jump estimate.
To consume the actual competitor budget as well, let $\Omega_i$ denote
the width in (AVB30). On this edge $\alpha_i=\Omega_i-\eta_i$, so
(AVB45) is equivalently the bound
\[
T_\psi\ge-S_Q+V_N-\frac{\Omega_i+C_B(A+D_i)}{w(A)}
 +\frac{\eta_i}{w(A)},\qquad
0\le\frac{\eta_i}{w(A)}\le\frac{13}{A\,w(A)}=o(S_A).
\tag{AVB46C}
\]
The last estimate is uniform by (AVB25)–(AVB26). Thus the finite
comparison retains the actual replacement correction, and its omission
costs at most the paid $13/[A\,w(A)]$ allowance.
This uses $\beta_i=\eta_i$ only on the nonnested branch, and does not
replace $\alpha_i$ by $\eta_i$.
The nonnegative cost $C_B(A+D_i)/w(A)$ is still unpaid, and cofinality
does not provide nonnested departures beyond every required common
start. Even if that source supply and an $o(w(A)S_A)$ cost were supplied,
the $O(A)=o(S_A)$ error in (AVB46) would leave only the critical
coefficient $c_Q$, not any fixed $\kappa<c_Q$.
The strict $\beta_i>0$ at $D_i>0$ supplies no such uniform margin.

### Full shorter-Q quantifiers and the unpaid actual-source sign

For the remaining comparison specialize to the existing shorter scale
$H=A^{4/5}$, $B=A+H$ and $S_A=A^{11/10}=H^2/\sqrt A$.
Retain the ordinary GM input exactly as in (QGM): fixed
$\epsilon_{\rm GM}=1/60$, $\beta_{\rm GM}=7/12$, and constants
$C_{\rm GM},Y_0$ for which
\[
|\pi(y+v)-\pi(y)-v/\log y|
 \le C_{\rm GM}v e^{-(\log y)^{1/4}},\qquad
y\ge Y_0,\quad y^{7/12}\le v\le y^{99/100}.
\]
It is an absolute prime-counting error uniform in that range.
The conversion to $\theta$ retains
$O(v\log y\,e^{-(\log y)^{1/4}}+v^2/(y\log y))$, including its logarithmic
factor. The common finite support and growing-index derivative controls
of (QH1)–(QH10), the strict atom correction
$+\operatorname{atom}(y)-\operatorname{atom}(y+v)$, all higher actual
and reference layers, and the actual/reference square coefficients
$\sqrt2/4$ and $1/4$ are those already paid in (QH11)–(QH13).
They give (QQE), with one unknown common all-real start $A_*$:
\[
\left|\frac{S_Q(A,A^{4/5})}{S_A}-c_Q\right|
 \le C\mathcal F_Q(A),\qquad c_Q=\frac{\sqrt2-1}{4},
 \qquad A\ge A_*,
\]
\[
\begin{aligned}
\mathcal F_Q(A)={}&\frac1{\log A}+A^{-1/5}
 +\log A\,e^{-((\log A)/3)^{1/4}}+A^{-1/120}\\
 &+A^{-3/10}\log A+A^{-1/6}(\log A)^{4/3}
 +A^{-19/180}(\log A)^{43/36}.
\end{aligned}
\tag{AVB47}
\]
All seven terms tend to zero. One common start pays the GM threshold,
both square cutoffs, support, all growing-index length tests and the
error tolerance for every sufficiently large real $A$.
No numerical common start is supplied by this estimate.
Its control of $S_Q$ does not supply the main-scale signed $T_\psi$ input:
an absolute GM allowance there, divided by $S_A$, has size
$\sqrt A\log A\,e^{-c(\log A)^{1/4}}$ for a fixed $c>0$,
which is not $o(1)$. The exponent
$(\log A)/2-c(\log A)^{1/4}+\log\log A$ tends to $+\infty$.
This diagnoses an unpaid allowance, not the size or sign of the true
arithmetic error.

The singleton loss is uniform even when the forced prime is much larger
than $A$. If $V_N>0$, its sole extra has $b<r_{s,1}\le a$.
Since $r_{s,1}<\lambda(s)$ and $\lambda$ decreases, $s<B$.
Equation (AVB37) gives
$w(A)V_N\le(a-b)\log s<(a-b)\log B$.
Also $(a-b)/w(A)=\int_0^H\rho_A(u)\,du<H$, since $w$ decreases.
The zero-loss case is immediate. Thus, without a bound $\log s\le\log A$,
\[
0\le V_N(A,A^{4/5})<A^{4/5}\log(2A)
 =g(A)S_A,\qquad
g(A)=A^{-3/10}\log(2A)\longrightarrow0.
\tag{AVB48}
\]
This pays a uniform preoccupied loss. It does not pay a signed
$T_\psi$ allowance.

Combining (AVB41) and (AVB43) exposes the exact GA2 orientation:
\[
\boxed{\quad
\Xi_s(B)+u_s=F(N)-F(M_B)+C_B(Y)
 \ge C_B(Y)\ge0.
\quad}
\tag{AVB49}
\]
The inequality is actual GA2 at the same literal multiple $M_B$.
Reversing it would introduce the missing favorable sign.
In particular the paid $9/A$ and $13/A$ errors do not make
$\Xi_s(B)$ favorably negative.

The exact (QG7) finite Lambda kernel, at that same real $A$, is
\[
k_A(n)=\mathbf1_{A<n\le B}
       \frac{\lambda(n)-\lambda(B)}{w(A)},\qquad
D_0(A)=\frac{f(B)-f(A)-H\lambda(B)}{w(A)},\qquad
T_\psi=\sum_{n\ge1}\Lambda(n)k_A(n)-D_0(A).
\tag{AVB50}
\]
Its initial atom is excluded and its terminal atom has zero weight.
Every prime power $n=q^k$ has its full $\Lambda(n)=\log q$ mass.
Finite integration of
$\psi(t)-\psi(A)=\sum_{A<n\le t}\Lambda(n)$ proves the displayed
formula, including
$D_0(A)=\int_0^H u\rho_A(u)\,du$.
For any real $\kappa$ the exact same-source equivalence is
\[
T_\psi(A,A^{4/5})\ge-\kappa S_A
\ \Longleftrightarrow\
\Xi_s(B)+u_s\le w(A)[\kappa S_A-S_Q(A,H)+V_N(A,H)].
\tag{AVB51}
\]
When $\kappa<c_Q$ is fixed, the right side is
$-(c_Q-\kappa+o(1))w(A)S_A$, a strictly negative margin eventually.
Equation (AVB49) exhibits the opposite GA2 orientation. The desired
contradiction therefore still requires the following actual arithmetic
source-and-sign input:
\[
\boxed{\quad
\exists\text{ fixed }\kappa<c_Q\ \forall\text{ required real }T_0\
 \exists p\ge29\text{ prime}:\quad
 A_p\ge T_0,\qquad
 \sum_{n\ge1}\Lambda(n)k_{A_p}(n)
 \ge D_0(A_p)-\kappa A_p^{11/10}.
\quad}
\tag{AVB52}
\]
This input is unproved. The required start includes a common (QQD)
tolerance start, the uniform (AVB48) tolerance start and every additional
analytic transfer start. Clock cofinality from $N_p\ge5040p$ can pass
each unknown finite start, but it does not supply the favorable sign
in (AVB52).

For its precise consumer let $\varepsilon=(c_Q-\kappa)/4$.
Beyond the common starts, (AVB47)–(AVB48) give
$S_Q\ge(c_Q-\varepsilon)S_A$ and $V_N\le\varepsilon S_A$.
If (AVB52) supplied the additional $T_\psi\ge-\kappa S_A$ there,
then
\[
T_\psi+S_Q-V_N\ge\frac{c_Q-\kappa}{2}S_A,\qquad
F(M_B)-F(N)\ge\frac{c_Q-\kappa}{2}w(A)S_A+C_B(Y)>0.
\tag{AVB53}
\]
The contradiction is at a literal integer multiple of the selected
actual $N$; it uses no standalone theorem with the missing sign
silently assumed as a proved conclusion.

A finite positive average is an equivalent selection interface only
with the same source coverage. Precisely, for every required $T_0$,
take a finite set of actual labels with $A_p\ge T_0$ and nonnegative
weights $a_p$ of positive total weight. A proved inequality
\[
\sum_p a_p\sum_n\Lambda(n)k_{A_p}(n)
 \ge\sum_p a_p[D_0(A_p)-\kappa A_p^{11/10}]
\tag{AVB54}
\]
forces at least one positive-weight label to satisfy (AVB52), since
otherwise the finite sum of its strict failures is negative.
Conversely a single qualifying source gives this finite interface.
Neither inequality is supplied by cofinality or scalar means.
Duplicate plateau labels aggregate weight at one integer and create
no independent samples.

For clarity about an alternative transfer route, the actual weak-$\psi$
stability estimate for $X\ge1024$, $A,C\in[X,2X]$ and
$d=|C-A|\le X^{4/5}/2$ is
\[
|T_\psi(A,A^{4/5})-T_\psi(C,C^{4/5})|
 \le120X^{4/5}(d+1)\log X.
\tag{AVB55}
\]
One direct derivation writes
$Q_a(t)=\psi(t)-\psi(a)-(t-a)$ and $R_a(t)=w(t)/w(a)$ on
$I_a=[a,a+a^{4/5}]$. Put $L=X^{4/5}$ and $\ell_0=\log(3X)$.
The full prime-power count gives
$0\le\psi(v)-\psi(u)\le(v-u+1)\ell_0$ for $X\le u\le v\le3X$,
so $|Q_a(t)|\le5L\ell_0$.
For $C\ge A$, the symmetric-difference length of $I_A,I_C$ is at most
$3d$, including the full upper-endpoint motion. Its cost is at most
$15Ld\ell_0$. On their intersection,
$Q_C-Q_A=d-[\psi(C)-\psi(A)]$, costing at most $4L(d+1)\ell_0$.
Finally $|w'/w|\le4/X$ gives
$0\le R_C-R_A\le4d/X$, costing at most
$40dL^2\ell_0/X\le40dL\ell_0$.
Adding and using $\ell_0\le2\log X$ proves (AVB55).
The $+1$ retains an initial prime-power jump and cannot be removed
merely by continuity of the remaining weights.

Dividing (AVB55) by $X^{11/10}$ shows that
$d=o(X^{3/10}/\log X)$ would suffice for vanishing normalized transfer
error. A fixed-margin favorable center at cofinally many scales together
with paired actual clocks at that distance and all common starts would
therefore suffice. The favorable centers and their paired actual-source
coverage are both unpaid. This sufficient pairing is not inserted as a
premise of (AVB25), (AVB41), (AVB46) or (AVB52).
Bertrand label gaps, the weighted width and monotone cofinal clocks give
no such mesh; no stronger uniform mesh is asserted or required here.

### Source scope and the remaining full target

Euler factorization, positive-price prefix optimization, scalar strict
concavity, Bertrand, Gronwall and finite Stieltjes integration by parts
are standard inputs. The original pressure, $I_\psi$, $R$, same-integer
defect and finite lcm consumer are the existing FIB/ZE/NC interfaces
cited above. The project-derived addition is (AVB19)–(AVB25), the
all-branch actual-value and accumulated literal-competitor error package,
with (AVB29) and (AVB31) making its actual measure and weighted jump
content explicit. Its immediate substantive uses are (AVB41) and
(AVB45)–(AVB46). No global novelty or primary-proof claim is made.

The own-clock event sampling (OCQ1)–(OCQ14) above retains its own
post-event source $N_p=C_{b_p}$ and its separate unproved continuous
signed-head condition (OCQ10). Its (OCQ13) all-integer defect identity
is reused in (AVB39); its sample choice, seven-eighths zero ceiling
and conditional (OCQ14) consumer do not supply (AVB52).
The $N_p$ of this section instead denotes the least actual maximizer
on $\mathcal D_{5040p}$, as explicitly defined above.
No identification of those two source families is used.
Seven-eighths nonvanishing, almost-all centers and bounded multiplicative
correlations likewise supply no stated same-actual-source Lambda sign.

The conditional finite real-clock interval (GAK40)–(GAK51), through
$A=8\cdot10^{46}$, retains its original source/material premises and
each integer's defect in (GAK39). It is a finite interval and source
corollary. Neither it nor the earlier $7.2\cdot10^{46}$ interval is an
unbounded family start, a least-counterexample bound, or payment of
the unknown GM/QQE starts. A separately selected least global maximizer,
a least counterexample, and the cofinal forced-prime family are not
interchangeable sources.

All separate deletion comparisons here occur above the forced exponent
and stay in their stated multiple class with integer at least $3$.
Completed prime replacements are compared only after insertion and
in their legal opposite forced class; no bare forced-prime deletion
comparison is used. The proper-deletion bridge used for a global $n>5040$ source has its own full hypotheses:
a deletion that merely remains above $e$ need not remain above $5040$.
Restricted comparisons cannot replace that bridge, and no integer
replacement is imported from the wrong domain.

The paid errors are $u_s$ and the sum of actual $\eta_i$, at uniform
$o(w(A)S_A)$ precision. The unpaid estimates are the signed cancellation
in (AVB51)–(AVB52), its every-start source coverage, and, for the
nonnested finite-competitor route, source supply, the literal cost
$C_B(A+D_i)$ and a strict coefficient gain beyond the critical $c_Q$.
Formal analytic suppliers and their dependency verification are separate
from this ordinary exposition. No estimate here proves the full
every-$n>5040$ signed target (AVB02), which remains active and unproved.
## Project application: forced windows and exact pairing of actual maximizing multiples

Use the strict inventories, Euler layers, \(f,\lambda,w,K,\psi,Q\),
\(T_\psi,S_Q,V_N\) and concavity cost \(C_t\) of QH1–QH13 and
QG1–QG8. Write \(N_t^{\rm str}\) for that section's strict actual
integer \(N_t\), to distinguish it from a maximizing multiple. Thus
\(K(t)=\log N_t^{\rm str}\), actual equality layers are excluded, and
the reference \(\psi(t)=\sum_{q^k\le t}\log q\) is weak and includes
every prime power. All compact positive-price intervals have one common
finite layer support, including actual ties and reference atoms.

For \(n\ge3\), put \(F(n)=\log G(n)=W(n)-f(\log n)\). For an ordinary
prime \(p\ge29\), let
\[
\mathscr M_p=\mathop{\rm argmax}_{5040p\mid n,\ n\in\mathbb N_{>0}}F(n),
\quad v(p)=\max_{5040p\mid n}F(n),\quad
N_p^{\rm mult}=\min\mathscr M_p,\quad A_p^{\rm mult}=\log N_p^{\rm mult}.
\]
These are maxima of the **actual Robin ratio over the entire multiples
class**. They are distinct from the earlier event-indexed fixed-price
integers \(N_p=C_{b_p}\).

The completed all-branch deductions supply the following intermediate
inputs: actual attainment under RH failure; for every maximizing tie
over multiples of \(m\ge3\), with clock \(A\),
\[
N=\operatorname{lcm}(m,N_A^{\rm str});
\]
the strict activation of all 5040 layers when \(m=5040p,\ p\ge29\);
and consequently
\[
N=\operatorname{lcm}(p,N_A^{\rm str}),\qquad
E_N\subseteq\{(p,1)\}.
\]
They also supply the global clock/value ordering of the **least**
sources, their finite constant-integer blocks, and the last-label bounds
used below. These all-branch and E1–E8 inputs are reused as recorded in
the [completed forced-window proof, §§2, 8–9](trureturing2026extrawindowpairing.md).
Global least-source ordering does not assert global ordering of arbitrary
ties. The finite positive-prefix optimizer at an arbitrary positive price
is the existing
[golden_future_extension_maximum_attained](../../D5/S3/Arith/GoldenFutureExtensionMaximum.lean);
its private prefix construction realizes
\(\operatorname{lcm}(N,N_t^{\rm str})\) at price \(\lambda(t)\).
[GoldenColossalClosure](../../D5/S3/Arith/GoldenResource/GoldenColossalClosure.lean)
also has the exponent-max construction, at its base threshold. Neither
fixed-price result is substituted for actual-\(G\) attainment.

### Fixed ordinary suppliers and the forced window

Assume RH is false. The CNS oscillation input on CA integers, with
\(\Theta=\sup_{\rho\text{ a nontrivial zero of }\zeta}\Re\rho\),
supplies **one fixed**
\[
1-\Theta<b<\tfrac12,\qquad d>0,
\]
and arbitrarily large actual integer witnesses \(m\), with \(X=\log m\),
such that \(F(m)\ge\gamma+dX^{-b}\). Here \(0<b<1/2\), since
\(\Theta\le1\). This is the log-converted form of CNS
[arXiv:1112.6010v2](https://arxiv.org/abs/1112.6010v2), printed p.15,
whose underlying oscillation citation is **Robin 1983, [15], p.241**,
not the separate Robin 1984 criterion.

CNS equation (2), printed p.2, supplies the positive upper envelope.
Using the upper rounding \(0.6483\) also printed on p.15, let
\(K_R=0.6483e^{-\gamma}>0\). For every \(n\ge3\), \(A=\log n>1\),
\[
F(n)-\gamma\le\frac{K_R}{(\log A)^2}.
\]
This is an upper envelope with a positive error. Both published inputs
are ordinary suppliers; their underlying analytic proofs are not
reproved here.

Use QGM with its fixed \(\epsilon_{\rm GM}=1/60\) and
\(\beta=7/12\), for all real starts and only lengths
\(y^\beta\le h\le y^{99/100}\). Enlarge its unknown common start so
that its relative counting error is at most \(1/2\). Then every permitted
interval contains a prime, and eventually the next ordinary prime after
\(p\) is at most \(p+p^\beta\). This remains a label-spacing input.

For each qualifying witness \(X\), define
\[
\ell_X=\frac d8X^{1-b}\log X,\qquad
R_X=\exp\!\left(\sqrt{\frac{2K_R}{d}}X^{b/2}\right),\qquad
\mathcal P_X=\{p\text{ prime}:e^{\ell_X}\le p\le e^{2\ell_X}\}.
\tag{FW0}
\]
\(R_X\) is the **window clock ceiling**, distinct from the original
Robin residual \(R(t)\). In the local proofs abbreviate
\(\ell=\ell_X,\ R=R_X\).

**Theorem N1 (uniform full-domain confinement and label uniqueness).**
There is an unknown witness start \(X_0\) such that for every qualifying
\(X\ge X_0\), every \(p\in\mathcal P_X\), and **every**
\(N\in\mathscr M_p\), with \(A=\log N\),
\[
v(p)\ge\gamma+\frac d2X^{-b},\qquad
\ell\le A\le R,\qquad
N=pN_A^{\rm str},\qquad E_N=\{(p,1)\},\qquad P^+(N)=p.
\tag{FW1}
\]
The same actual integer cannot be a maximizing tie for a different
ordinary label \(q\ge29\), including a label outside this window.
For each fixed \(M>0\),
\[
\frac{e^\ell}{R^M}\longrightarrow\infty
\tag{FW2}
\]
along the witnesses; its eventual start is independent of \(p\) and tie.

*Proof.* Set \(m_0=\operatorname{lcm}(5040,m)\),
\(d_0=\log(m_0/m)\in[0,\log5040]\), and take the literal integer
\(D_p=pm_0\). This is a legal multiple of \(5040p\), even when \(p\)
already divides \(m_0\). With \(k=v_p(m_0)\), exact Euler telescoping gives
\[
F(D_p)-F(m)=W(m_0)-W(m)+\ell_{k+1}(p)
 -[f(X+d_0+\log p)-f(X)].
\]
The two Euler increments are nonnegative. Since \(\lambda\) decreases,
the last cost is at most
\[
\frac{d_0+\log p}{X\log X}
\le\frac d4X^{-b}+\frac{\log5040}{X\log X}
\le\frac d2X^{-b}
\]
eventually, uniformly over the window. Thus \(F(D_p)\) has the required
floor. This uses the \((k+1)\)-st layer, not an absent-prime assumption.

For any integer with clock \(A>R\), the upper envelope is strictly below
that floor, since \(K_R/(\log R)^2=(d/2)X^{-b}\). In particular \(D_p\)
has clock at most \(R\). The nonempty finite set of multiples of
\(5040p\) with clock at most \(R\) therefore attains the entire
infinite-domain maximum, and contains all its ties. The lower clock
bound follows from \(N\ge5040p\); equality at the upper bound is retained.

Write \(a_R=\sqrt{2K_R/d}\). Then
\[
\frac{\ell}{\log R}
=\frac d{8a_R}X^{1-3b/2}\log X\longrightarrow\infty.
\]
Hence \(\ell-M\log R\to\infty\) for every fixed \(M\), proving FW2.
In particular \(p>2R\) eventually. For any tie, \(A\le R<p\), so
\(r_1(p)<\lambda(p)<\lambda(A)\). The reused strict 5040 activation
and all-branch characterization give \(N=pN_A^{\rm str}\), with exactly
one strictly inactive occupied extra. Every prime of \(N_A^{\rm str}\)
is \(<A\le R\), so \(P^+(N)=p\). If the same integer maximized another
label \(q\), its same own-clock nonempty extra set would be contained
in both \(\{(p,1)\}\) and \(\{(q,1)\}\), forcing \(q=p\). ∎

### One finite literal core and all choices of window ties

Define the common finite set and its real-parameter envelope by
\[
\mathcal C_X=\{u\in\mathbb N_{>0}:5040\mid u,\ \log u\le R,\
       \forall q\text{ prime},\ q\mid u\Rightarrow q\le R\},
\qquad
\mathcal V_X(h)=\max_{u\in\mathcal C_X}\{W(u)-f(\log u+h)\}
\quad(\ell\le h\le2\ell).
\tag{FW3}
\]
The set is nonempty eventually, since it contains 5040.

**Theorem N2 (exact envelope and all-choice ordering).**
For every sufficiently large qualifying witness and every
\(p\in\mathcal P_X\),
\[
v(p)=c_p+\mathcal V_X(\log p),\qquad c_p=\ell_1(p).
\tag{FW4}
\]
Multiplication by \(p\) is a bijection from **all** active cores at
\(\log p\) to \(\mathscr M_p\), preserving leastness.
The envelope is strictly decreasing and convex. If \(h_1<h_2\), every
active core clock at \(h_1\) is at most every active core clock at \(h_2\).
In particular, for any choices
\(N=pU\in\mathscr M_p,\ N'=rV\in\mathscr M_r\) at \(p<r\) in the window,
\[
A=\log N<C=\log N',\qquad U\mid V,\qquad
C-A=\log(V/U)+\log(r/p).
\tag{FW5}
\]
At a real \(h\), if active core clocks have extrema \(a_{\min},a_{\max}\),
the left/right derivatives and subgradient interval are
\[
\mathcal V'_{X,-}(h)=-\lambda(h+a_{\min}),\qquad
\mathcal V'_{X,+}(h)=-\lambda(h+a_{\max}),\qquad
\partial\mathcal V_X(h)=
[-\lambda(h+a_{\min}),-\lambda(h+a_{\max})].
\tag{FW6}
\]

*Proof.* FW1 puts every full-domain tie in the form
\(pN_A^{\rm str}\), whose core lies in \(\mathcal C_X\), including all
5040 layers. Conversely every \(u\in\mathcal C_X\) makes \(pu\) legal;
\(p>R\) makes \(p\) absent from that core, so its Euler factor is exactly
\(c_p\). Taking maxima proves both the identity and the full tie
bijection, rather than replacing the multiples domain by a restriction.

Each summand of FW3 has derivative \(-\lambda(\log u+h)<0\) and
second derivative \(w(\log u+h)>0\). Its finite maximum is convex and
strictly decreasing. If \(\log u>\log v\), the derivative of the
\(u\)-summand minus the \(v\)-summand is
\(\lambda(\log v+h)-\lambda(\log u+h)>0\). If \(u\) is active at
\(h_1\), that difference is strictly positive at \(h_2>h_1\);
\(v\) cannot be active there. This proves the all-choice order.
At actual labels, \(C>A\) follows after adding the strictly larger
label clock. Since \(U=N_A^{\rm str}\) and \(V=N_C^{\rm str}\),
monotonicity of strict inventories gives \(U\mid V\) and FW5.

The one-sided derivatives of a finite convex maximum are respectively
the minimum and maximum active derivatives, giving FW6. Actual active
cores remain a finite set of literal integers; intermediate subgradients
need not be clocks of integer cores. No assertion identifying different
ties at one parameter is used. ∎

### Literal replacements and their arriving-scale deficiencies

Let \(p<r\) be consecutive ordinary primes, both in \(\mathcal P_X\),
and choose any of their maximizing ties. Use
\[
N=pU,\quad N'=rV,\quad A=\log N,\quad C=\log N',\quad
\delta=\log(r/p)>0,\quad D=\log(V/U)\ge0,
\]
\[
Z=pV,\quad z=\log Z=A+D=C-\delta,\quad
\varepsilon=F(N)-F(Z),\quad
\varepsilon_r=F(N')-F(rU).
\tag{FW7}
\]
\(Z\) is a literal multiple of the **same original** \(N\).

**Theorem N3 (rectangle identity and uniform arrival errors).**
The sources \(N,N'\) are distinct and neither divides the other.
Both deficiencies in FW7 are nonnegative, and
\[
\varepsilon+\varepsilon_r
=\int_0^\delta\int_0^D w(A+s+t)\,dt\,ds
\le\delta\lambda(A).
\tag{FW8}
\]
Their cross-label value drop satisfies
\[
0<v(p)-v(r)\le\delta[1/p+\lambda(A)].
\tag{FW9}
\]
Put \(E_X=e^{-5\ell/12}\). Uniformly over these pairs and all tie choices,
\[
0<\delta\le E_X,\qquad
0\le\varepsilon\le\frac{E_X}{\ell\log\ell},
\tag{FW10}
\]
\[
\frac{\varepsilon}{w(C)},\ \frac{\varepsilon}{w(z)}
\le\frac{E_XR^2\log R}{\ell\log\ell}\longrightarrow0,
\qquad
\frac{\varepsilon}{w(C)C^{11/10}},\
\frac{\varepsilon}{w(z)z^{11/10}}
\le\frac{E_XR^{9/10}\log R}{\ell\log\ell}\longrightarrow0.
\tag{FW11}
\]
For each fixed \(M>0\), \(\delta R^M\) and \(\varepsilon R^M\)
tend uniformly to zero. No hypothesis controlling \(C/A\) is needed.

*Proof.* Both cores have primes at most \(R<p<r\), so each source
lacks the other's label prime. FW5 gives \(U\mid V\), making \(Z=pV\)
legal in \(N\)'s multiples class, and \(rU\) legal in the \(r\)-class.
Actual maximality gives the nonnegative deficiencies. The two label Euler
factors cancel in their sum, leaving
\[
f(A+D)-f(A)-f(A+D+\delta)+f(A+\delta).
\]
Twice integrating \(f''=-w\) gives FW8; integrating the inner curvature
over its full half-line bounds it by
\(\int_0^\delta\lambda(A+s)\,ds\le\delta\lambda(A)\).
Also
\[
F(pV)-F(rV)=c_p-c_r+f(C)-f(C-\delta)>0.
\]
Comparing with the legal \(rU\) bounds the drop by
\(c_p-c_r+f(A+\delta)-f(A)\).
The exact identity
\[
c_p-c_r=\int_{\log p}^{\log r}\frac{du}{e^u+1}\le\delta/p
\]
proves FW9.

GM is applied at length \(p^\beta\), inside its permitted range; thus
\(r\le p+p^\beta\) and
\(\delta\le p^{-5/12}\le E_X\). This gives FW10. For every
\(t\in[\ell,R]\),
\[
w(t)\ge\frac1{R^2\log R},\qquad
w(t)t^{11/10}\ge\frac1{R^{9/10}\log R}.
\]
Together with \(A\le z<C\le R\), these give the explicitly expanded
arrival estimates FW11. All their ceilings vanish because
\(\log R=o(\ell)\), as do the fixed-\(M\) bounds. The cross-label
drop itself has normalized bound
\[
\frac{v(p)-v(r)}{w(C)C^{11/10}}
\le E_XR^{9/10}\log R
       \left[e^{-\ell}+\frac1{\ell\log\ell}\right]\longrightarrow0.
\]
Thus its strictness supplies no fixed normalized gain. If \(D=0\),
\(Z=N\) and both deficiencies vanish. When \(D>0\),
\(\varepsilon=0\) may still be a same-domain tie; choosing the least
arrival gives \(\varepsilon_r>0\), without a quantitative margin. ∎

### Exact integer rigidity and the signed compensated contact

**Theorem N4 (literal pairing without clock-ratio control).**
For every sufficiently large qualifying window and every FW7 pair,
\[
M_z=\operatorname{lcm}(N,N_z^{\rm str})=Z,\qquad
\log M_z=z,\qquad
N_t^{\rm str}=V\quad(z\le t\le C).
\tag{FW12}
\]
In particular the original arriving clock \(C\) is exactly
\(\delta\) after this optimizer clock. \(Z\) need not be GA2 or a
canonical maximizing source.

For the **canonical least sources**, let \(p=p_j\) be the departure's
last label and reuse the E1–E8 right-continuous arriving-clock sum
\[
J_p(t)=\sum_{\substack{i\ge j\\ A_{p_{i+1}}^{\rm mult}\le t}}
             \log(p_{i+1}/p_i),
\]
where \(p_i\) run through successive ordinary prime labels. Then
\[
J_p(t)=0\quad(A\le t<C),\qquad J_p(C)=\delta.
\tag{FW13}
\]
With \(Y_N(t)=\log\operatorname{lcm}(N,N_t^{\rm str})\), the compensated
endpoint and the preceding integral are exactly
\[
Y_N(C)-C+J_p(C)=0,\qquad
\int_z^C[Y_N(t)-t+J_p(t)]w(t)\,dt=-C_C(z)<0.
\tag{FW14}
\]

*Proof.* Monotonicity and FW5 give
\(U\mid N_z^{\rm str}\mid V\). The label \(p>C\) is absent from these
cores. Thus \(M_z=pN_z^{\rm str}\mid Z=pV\), and its clock \(y\)
satisfies \(A\le y\le z\).

Reuse the literal finite positive-prefix optimizer at price \(\lambda(z)\).
Its deficiency against this same \(Z\) is
\[
\Delta_z=[W(M_z)-\lambda(z)y]-[W(Z)-\lambda(z)z]\ge0.
\]
Directly at these integers, with
\(C_z(y)=f(z)+\lambda(z)(y-z)-f(y)\), one obtains
\[
\varepsilon=[F(N)-F(M_z)]+C_z(y)+\Delta_z.
\tag{FW15}
\]
All three terms are nonnegative: \(M_z\) is an actual multiple of the
actual-GA2 integer \(N\), the cost is concave-tangent cost, and the last
term is fixed-price deficiency. For \(y\le z\),
\[
C_z(y)=\int_y^z(t-y)w(t)\,dt\ge\tfrac12w(z)(z-y)^2.
\]
Consequently the *actual common ceiling* in FW11 gives
\[
(z-y)^2\le
\frac{2E_XR^2\log R}{\ell\log\ell}\longrightarrow0.
\tag{FW16}
\]
Eventually \(z-y<\log2\), uniformly. Since \(Z/M_z\) is a positive
integer, any failure of equality would give \(Z/M_z\ge2\), contradicting
FW16. Therefore \(M_z=Z\) exactly. Cancelling the literal common factor
\(p\) gives \(N_z^{\rm str}=N_C^{\rm str}=V\).
Monotonicity gives equality on the **closed** interval \([z,C]\).
A missing equality layer at \(z\) would become strictly active before
\(C\), contradicting it. A missing tie at \(C\) remains excluded and has
zero terminal pressure.

For canonical sources, FW1 makes both label blocks singletons, including
possible labels outside the window. Their global least-source clock
order, and consecutiveness of \(p,r\), give no arriving-clock atom in
\([A,C)\) and exactly the mass \(\delta\) at \(C\). A later label at
the same clock would produce the same integer as \(N'\), contradicting
FW1's label uniqueness. This proves FW13 with weak arrival indexing;
no general plateau masses are omitted.

On \([z,C]\), \(Y_N(t)=z\). Before \(C\) the compensated integrand is
\(z-t\), and at \(C\) it jumps to \(z-C+\delta=0\). Its integral is
\(-\int_z^C(t-z)w(t)\,dt=-C_C(z)<0\).
The single endpoint atom has zero ordinary integration measure.
The uncorrected envelope integrals from \(A\) to \(z\) and to \(C\),
using the existing finite lcm identity, are respectively
\(-\varepsilon\) and \(-\varepsilon-C_C(z)\).
No divergent tail integrals are subtracted.

The small retained cost also satisfies
\[
0<C_C(z)\le\tfrac12w(z)\delta^2,\qquad
\frac{w(z)}{w(C)}\le e^{4\delta/z}\longrightarrow1.
\]
Here the bound \(|w'/w|\le4/t\) applies once \(t\ge e\). Hence eventually
\[
\frac{C_C(z)}{w(C)C^{11/10}}
\le\frac{\delta^2}{C^{11/10}}\longrightarrow0,
\qquad C_C(z)\le\tfrac12w(\ell)E_X^2.
\]
These uniform estimates retain the negative sign in FW14. ∎

### Cofinal literal forward successors and real-base transport

**Theorem N5 (cofinal exact pairing and a nontrivial forward integer).**
For every finite common start \(T\), and every finite collection of
supplier or tolerance starts, there is a sufficiently large qualifying
window and a canonical FW7 pair with \(A,z,C\) beyond all these starts.
For each such pair put
\[
h=z^{4/5},\quad B_z=z+h,\quad
L=pN_{B_z}^{\rm str},\quad Y=\log L.
\]
Then, eventually and uniformly,
\[
N\mid Z\mid L,\qquad L>Z\ge N,\qquad
V_Z(z,z^{4/5})=0,\qquad V_{N'}(C,C^{4/5})=0.
\tag{FW17}
\]
Applying the existing exact QG accounting at this same \(Z\), and then
subtracting its deficiency against this same original \(N\), gives
\[
F(L)-F(N)
=w(z)[T_\psi(z,z^{4/5})+S_Q(z,z^{4/5})]
       +C_{B_z}(Y)-\varepsilon.
\tag{FW18}
\]
The actual terminal clock \(Y\) and its full nonnegative cost are retained.
At the arriving original source \(N'\), its own literal successor is
\(rN_{C+C^{4/5}}^{\rm str}\).

*Proof.* GM at the real start \(e^\ell\), length \(e^{\beta\ell}\),
gives a prime \(p\) just above \(e^\ell\); GM at \(p\) gives its next
prime \(r\). Eventually \(r<4e^\ell<e^{2\ell}\), so both belong to
\(\mathcal P_X\). Since \(A,z,C\ge\ell\to\infty\), the unbounded
actual witness clocks pass any finite collection of starts together.
These are the original canonical maximizing integers, not the oscillation
seed \(m\) or its padded comparator \(D_p\). FW1 supplies cofinal
extra-bearing canonical source blocks.

FW12 gives \(N_z^{\rm str}=V\), so \(Z=pV\) divides \(L\).
Since \(p>2R\) and \(B_z<2z\le2R\), its unique occupied extra remains
strictly below the price throughout \([z,B_z]\). Thus its entire
preoccupied loss is exactly zero. The same argument with \(r,C\) proves
the arriving source's zero loss. The finite QG2–QG3 accounting only
requires \(N_z^{\rm str}\mid Z\), the strict initial core and the actual
literal successors; GA2 of \(Z\) is not needed. It therefore gives FW18.
All initial \(K(z)\) terms cancel as in QG3; \(K(z)=z\) is not assumed.

For strict nontriviality apply GM at the real start \(z+h/3\) with length
\(h/3\). Its permitted-length inequalities hold eventually because
\(7/12<4/5<99/100\). There is a prime
\[
z+h/3<q\le z+2h/3.
\]
Its first layer is absent from \(N_z^{\rm str}\), since \(q>z\).
Eventually \(q<B_z-1<q_1(B_z)\), by MS2's strict first cutoff enclosure,
so that layer belongs to \(N_{B_z}^{\rm str}\). Also \(q<p\).
Thus \(q\mid L/Z\), proving \(L>Z\) independently of any favorable sign.
This does not imply \(Z>N\), a positive \(D\), or GA2 of either forward
integer.

The Lambda term in FW18 is precisely QG7 evaluated at \((z,h)\):
it sums **every** prime power in \((z,B_z]\), with weight
\(\Lambda(n)[\lambda(n)-\lambda(B_z)]\), and subtracts
\(f(B_z)-f(z)-h\lambda(B_z)\). Its initial atom is excluded and its
terminal atom has zero weight. No prime-only or balanced-tent replacement
is made. If terminal equality layers of mass \(J\) are deliberately
installed, their Euler reward is \(\lambda(B_z)J\), the pressure integral
is unchanged, and the cost becomes \(C_{B_z}(Y+J)\). FW18 consistently
uses the strict successor with its original \(Y\). ∎

The completed real-base \(C_0=120\) estimate applies to **every real**
\(x\ge1024\), centers \(a,c\in[x,2x]\), and
\(|c-a|\le x^{4/5}/2\):
\[
|T_\psi(c,c^{4/5})-T_\psi(a,a^{4/5})|
\le120x^{4/5}(|c-a|+1)\log x.
\]
Reuse this estimate with the **actual real base** \(x=z\), \(a=z\),
\(c=C=z+\delta\). Eventually all its comparable-base hypotheses hold,
since \(\delta\le E_X\le1\). It yields the new uniform partner transfer
\[
\frac{|T_\psi(C,C^{4/5})-T_\psi(z,z^{4/5})|}{C^{11/10}}
\le240z^{-3/10}\log z
\le240\ell^{-3/10}\log\ell\longrightarrow0,\qquad
\frac{C^{11/10}}{z^{11/10}}\longrightarrow1.
\tag{FW19}
\]
The moving upper endpoint, weight normalization and initial prime-power
jumps are included in the reused estimate. Its indispensable \(+1\)
is retained even when \(\delta\) is tiny; \(\log Z\) is not assumed to
be a power of two. This applies to the full discontinuous \(\psi\),
not a Lipschitz surrogate.

### Consuming the cofinal extras at every fixed ratio

Enumerate the distinct canonical source blocks in label order as
\(\mathcal N_j\), with clocks \(\mathcal A_j\), last labels
\(p_j=P^+(\mathcal N_j)\), and next ordinary primes \(r_j\).
Let \(\mathcal C_j=A_{r_j}^{\rm mult}=\mathcal A_{j+1}\).
The reused all-branch replacement is the same-source literal integer
\[
\mathcal Z_j=\operatorname{lcm}(\mathcal N_j,N_{\mathcal C_j}^{\rm str}),
\qquad
\mathcal A_j\le\mathcal z_j=\log\mathcal Z_j\le\mathcal C_j.
\]
This definition preserves all branches, including zero-extra blocks.
Finite blocks and unbounded labels give
\(\mathcal A_j,p_j\to\infty\). The reused **departure last-label**
bounds are
\[
\mathcal A_j<3p_j,\qquad
E_{\mathcal N_j}=\varnothing\ \Longrightarrow\ p_j<\mathcal A_j.
\]
They are not applied at a small arrival label inside a zero-extra plateau.

**Theorem (cofinal geometry consumed from N1 and N5).**
Under the same ordinary RH-false suppliers,
\[
\forall q>1\ \forall T\
\exists j:\quad
T\le\mathcal A_j<\mathcal C_j\le q\mathcal A_j,\qquad
\mathcal A_j\le\mathcal z_j\le\mathcal C_j.
\tag{FW20}
\]
Here \(q\) is fixed first; starts may depend on it. Moreover every
sufficiently large qualifying witness window contains a canonical FW7
pair with \(C\le qA\).

*Proof.* Fix \(q>1\), and choose \(\rho=(1+q)/2\in(1,q)\).
If a zero-extra departure is followed by an extra arrival, that arrival
has the unique label \(r_j\). Its extra first layer cannot have
\(r_j\le\mathcal C_j-1\), by the strict first cutoff enclosure.
Consequently \(\mathcal C_j<r_j+1\). Label spacing and the zero-extra
departure's **last** label give
\[
\mathcal C_j<r_j+1\le p_j+p_j^\beta+1
 <\mathcal A_j+\mathcal A_j^\beta+1<q\mathcal A_j
\]
eventually.

Suppose the edges in FW20 were not cofinal. In a tail every
\(\mathcal C_j>q\mathcal A_j\), so no zero-extra block there can be
followed by an extra block. A zero-extra block would therefore force all
subsequent blocks to have zero extra, contrary to N5's cofinal extras.
This tail must consist wholly of extra blocks. Each arrival then has a
unique label, so \(p_{j+1}=r_j\) are consecutive ordinary primes.
Enlarge the tail until \(p_{j+1}\le\rho p_j\).
For all \(k\ge1\), iteration and the last-label bound would give
\[
q^k\mathcal A_j<\mathcal A_{j+k}<3p_{j+k}\le3\rho^kp_j,
\]
impossible since \(q/\rho>1\). This proves the cofinal assertion.

For the window assertion take
\[
k_X=\left\lfloor\frac{\log(R/\ell)}{\log q}\right\rfloor+1,
\qquad q^{k_X}\ell>R.
\]
The initial \(p_0\) constructed in N5 has
\(\log p_0\le\ell+\log2\). Its actual successive primes satisfy
\[
\log p_i\le\ell+\log2+iE_X<2\ell
\qquad(0\le i\le k_X)
\]
by induction using GM at each permitted label and \(k_XE_X\to0\).
The inequality simultaneously justifies their window membership.
FW1 gives \(k_X+1\) distinct canonical clocks in \([\ell,R]\).
If all their consecutive edges had \(C>qA\), the last clock would exceed
\(q^{k_X}\ell>R\). At least one edge has \(C\le qA\), and \(A\ge\ell\)
makes these edges cofinal. N4's ratio-free rigidity did not require this
additional geometry. ∎

In particular FW20 with \(q=2\) pays the premise of the completed
two-price cofinal geometry consumer recorded in the ordinary proof §8.
Its existing all-branch projection
\(\mathcal y_j=\log\operatorname{lcm}(\mathcal N_j,N_{\mathcal z_j}^{\rm str})\)
therefore obeys, cofinally,
\[
0\le\mathcal C_j-\mathcal y_j
\le8\,3^{5/24}\mathcal A_j^{7/24}\sqrt{\log\mathcal A_j}
      +\log(8\mathcal A_j)
=o\!\left(\frac{\mathcal A_j^{3/10}}{\log\mathcal A_j}\right).
\tag{FW21}
\]
Here \(\mathcal A_j\le\mathcal y_j\le\mathcal z_j\le\mathcal C_j
\le2\mathcal A_j\), so its real comparable base is
\(x=\mathcal y_j\). The same \(C_0=120\) estimate gives transfer
\(o(\mathcal C_j^{11/10})\). This consumes the existing conditional
consumer; its projection estimate is not reproved as a new theorem.
It is separate from the exact, ratio-free window pairing FW12.
FW20 is a fixed-ratio cofinal statement, not convergence on every edge
or a shrinking-rate mesh.

### The remaining full signed obligation

QQE/QQD, with all seven errors and their one unknown all-real tolerance
start, apply at the cofinal clocks just constructed:
\[
S_Q(z,z^{4/5})=(c_Q+o(1))z^{11/10},\qquad
c_Q=(\sqrt2-1)/4.
\]
This is reused FullQ, with both actual and reference higher powers and
the reference square subtraction intact. FW11 pays the same original
source's deficiency at the **arriving** scale, FW17 pays the occupied
loss exactly, and FW19 pays transport without discarding its atom cost.
Actual GA2 of \(N\), however, makes FW18 only the necessary **upper**
comparison
\[
w(z)[T_\psi(z,z^{4/5})+S_Q(z,z^{4/5})]
\le\varepsilon-C_{B_z}(Y).
\tag{FW22}
\]
No favorable lower coefficient follows.

The unchanged selected-source debt is one fixed \(\kappa<c_Q\) such that,
beyond **every** required common start \(T\), some original canonical
\(N_p^{\rm mult}\) has \(A_p^{\rm mult}\ge T\) and
\(T_\psi(A_p^{\rm mult},(A_p^{\rm mult})^{4/5})
\ge-\kappa(A_p^{\rm mult})^{11/10}\).
For this route its support may be confined to the proved cofinal window
sources; that favorable estimate on them is still unpaid. Alternatively
one owes a fixed positive normalized lower margin for the complete
\(w(z)(T_\psi+S_Q)-\varepsilon\) on cofinal proved partners.
FW19 would transport a supplied fixed favorable partner coefficient with
strict slack to the arriving original source; it supplies no such sign.

The existing E1–E8 last-label error budgets \(9/A\) and \(13/A\),
their already proved convergence, and the complete compensation are
unchanged. In particular the corrected E7 identity is reused:
\[
w(A)T_\psi=I_\psi(A)-I_\psi(B)
-(\psi(A)-A)[\lambda(A)-\lambda(B)].
\]
Its necessary comparison and the compensation do not make FW14's
negative local integral positive. No favorable finite nonzero
same-family weighted Lambda/tent average or positive localized
Tauberian estimate is obtained. Neither cofinal \(D>0\) or \(Z>N\),
nor the balanced-left placement \(z-z^{4/5}\ge A\), is supplied.
When a tent extends left of \(A\), its whole occupied crossing sum
remains; FW18 uses the valid forward interval instead.

All analytic starts here remain unknown; the source's separate
conditional finite interval through \(8\cdot10^{46}\) cannot pay them.
The literal sources, endpoint costs and full Lambda sign have not been
replaced by relaxed cores or different integers. The deductions above
are ordinary supplier-relative mathematics and carry no priority claim.
The full signed target
\[
\forall n\in\mathbb N,\quad n>5040\ \Longrightarrow\
I_\psi(\log n)+R(\log n)+d_{\log n}(n)>0
\]
remains **ACTIVE_UNPROVED**.

## Project application: cofinal additive edges and the exact constant core

Under RH failure, the CNS positive-oscillation and Robin upper-envelope
suppliers, the uniform Guth--Maynard Corollary 1.3 input, and the
[FW0--FW22/N1--N5 suppliers](trureturing2026extrawindowpairing.md), this
appendix proves cofinal additive edges, exact constant cores, and their
finite forward consumer. It follows that full forced-window section and
uses the same original integer family, the factor \(5040\), and the same
Robin objective. These are project deductions relative to those ordinary
mathematical suppliers; they are not attributed to Nicolas or to the
cited analytic authors.

### Definitions and the supplier interface

For \(x>1\) put

\[
 f(x)=\log\log x,\qquad \lambda(x)=f'(x)=\frac1{x\log x},
 \qquad w(x)=-\lambda'(x)=\frac{\log x+1}{x^2(\log x)^2}.
\]

Thus \(f''=-w<0\), and \(w\) is positive and decreasing.  For an integer
\(n\ge3\), write

\[
 W(n)=\log\frac{\sigma(n)}n,\qquad F(n)=W(n)-f(\log n),
 \qquad G(n)=e^{F(n)}.
\]

For a prime \(q\) and \(k\ge1\), define the Euler-layer data

\[
 h_q=\log q,\quad
 \ell_{q,k}=\log\left(1+\frac1{q+\cdots+q^k}\right),\quad
 r_{q,k}=\frac{\ell_{q,k}}{h_q}.
\]

Finite Euler telescoping gives

\[
 W(n)=\sum_{(q,k)\,\mathrm{occupied\ in}\,n}\ell_{q,k}.
\]

The \(r_{q,k}\) decrease strictly in \(k\), and

\[
 0<r_{q,k}<\frac1{q^k\log q},\qquad r_{q,1}<\lambda(q).
\]

The strict actual inventory and its clock are

\[
 N_t^{\rm str}=\prod_q q^{\#\{k:r_{q,k}>\lambda(t)\}},
 \qquad K(t)=\log N_t^{\rm str},
\]

whereas the reference Chebyshev--von Mangoldt clock is weak:

\[
 \psi(t)=\sum_{q^k\le t}\log q,
 \qquad Q(t)=K(t)-\psi(t).
\]

Every compact interval in \((1,\infty)\) has a common finite support of actual layers,
actual equality layers, and reference prime powers.  These conventions are
the finite inventory and endpoint conventions of [FIB §§85, 87, 98](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md) and [ZE/5040, Definition 7.1, “各指数层的素数截止值”](../../docs/develop/theory/ZECKENDORF_EULER_5040.md).  Equality layers are
excluded from \(N_t^{\rm str}\); reference atoms at their endpoint are
kept with their weak convention.

The analytic suppliers used here are the following.  Under RH failure,
put \(\Theta=\sup_{\rho\text{ a nontrivial zero of }\zeta}\Re\rho\), and
fix one \(1-\Theta<b<1/2\) and one \(d>0\) supplied by the positive
oscillation on CA integers of Caveney--Nicolas--Sondow. Since
\(1/2<\Theta\le1\), this gives \(0<b<1/2\). The primary is
[arXiv:1112.6010v2, printed p.15](https://arxiv.org/abs/1112.6010v2),
whose cited oscillation input is Robin 1983, [15], p.241.  The stable project source is the [CNS source note](../Arith/caveney2012sacaga.md).  There are arbitrarily large
actual witness integers \(m\), with \(X=\log m\), for which
\[
 F(m)\ge\gamma+dX^{-b}.
\]
The same original Robin upper envelope, in the normalization used by the
comparison file, supplies a constant \(K_R=0.6483e^{-\gamma}\) with
\[
 F(n)-\gamma\le\frac{K_R}{(\log\log n)^2}
 =\frac{K_R}{(\log(\log n))^2}
 \qquad(n\ge3).
\]
Writing \(A=\log n\), the denominator in the last display is
\((\log A)^2\).  No proof of either published analytic input is repeated.

We also use the uniform Corollary 1.3 of Guth--Maynard, as recorded in the [project GM source note](../Analytic/guthmaynard2024largevalues.md),
[arXiv:2405.20552v2](https://arxiv.org/html/2405.20552v2), with
\(\epsilon=1/60\) and \(\beta=7/12\): for every sufficiently large real
\(y\) and every \(y^\beta\le v\le y^{99/100}\),
\[
 \left|\pi(y+v)-\pi(y)-\frac v{\log y}\right|
 \le C_{\rm GM}v\exp\!\bigl(- (\log y)^{1/4}\bigr).
\]
Increase its one unknown common start until
\(C_{\rm GM}\log y\exp(- (\log y)^{1/4})\le1/2\) for every later real
\(y\). Then every permitted interval contains a prime.  That is the only use of this supplier in the counting
argument.

For a qualifying witness define
\[
 \ell=\frac d8X^{1-b}\log X,
 \qquad
 R=\exp(a_RX^{b/2}),\quad a_R=\sqrt{2K_R/d},
 \qquad
 \mathcal P_X=\{p\text{ prime}:e^\ell\le p\le e^{2\ell}\}.
\]
Here \(R\) is a window clock ceiling, not the original signed residual
\(R(t)\).  The accepted FW/N1 supplier says that, after one common
unknown start, every \(p\in\mathcal P_X\) and every maximizing tie in
the full class of positive multiples of \(5040p\) has
\[
 \ell\le A=\log N\le R,\qquad N=pN_A^{\rm str},\qquad
 E_N=\{(p,1)\},\qquad P^+(N)=p,
\]
and that no such integer is a maximizing tie for a different ordinary
label.  The accepted N2 supplier gives, for \(p<r\) in the same window
and any choices of maximizing ties,
\[
 N=pU,\quad N'=rV,\quad A=\log N<C=\log N',\quad U\mid V,
 \quad C-A=\log(V/U)+\log(r/p).
\]
For \(p\ge29\), denote the full multiples class and its canonical source by
\[
 \mathscr M_p=\mathop{\rm argmax}_{5040p\mid n,\ n\in\mathbb N_{>0}}F(n),
 \qquad N_p^{\rm mult}=\min\mathscr M_p,
 \qquad A_p^{\rm mult}=\log N_p^{\rm mult}.
\]
All cofinal and global source conclusions below use these **least
full-domain maximizers**. The N2 all-choice ordering inside a qualifying
window applies, in particular, to these canonical choices; it is not a
global order assertion for arbitrary ties. Each source is actual GA2,
because every positive integer multiple remains in its full \(5040p\)
class. The reused global least-source order and the N1 label uniqueness
make each window source a singleton label block, with last label
\(P^+(N_p^{\rm mult})=p\). Thus consecutive ordinary primes in a window
produce genuine consecutive last-label blocks of the original canonical
family. These are actual maximizers, not fixed-price optimizers or
oscillation padding integers.

The elementary padding behind the window statement is recalled for
source clarity.  Let \(m_0=\operatorname{lcm}(5040,m)\),
\(d_0=\log(m_0/m)\le\log5040\), and \(D_p=pm_0\).  If
\(k=v_p(m_0)\), then
\[
 F(D_p)-F(m)=W(m_0)-W(m)+\ell_{p,k+1}
 -[f(X+d_0+\log p)-f(X)].
\]
The Euler increments are nonnegative and the last term is at most
\((d_0+\log p)/(X\log X)\).  Since \(\log p\le2\ell\), this is at most
\(dX^{-b}/2\) for all sufficiently large witnesses.  Hence every
\(p\)-class has a member above the floor
\(\gamma+dX^{-b}/2\).  The Robin envelope is below that floor once
\(A>R\), because \(K_R/(\log R)^2=dX^{-b}/2\).  The finite part
\(A\le R\) therefore contains every full-domain maximizing tie.  Finally
\[
 \frac{\ell}{\log R}=\frac d{8a_R}X^{1-3b/2}\log X\longrightarrow\infty,
\]
so \(e^\ell/R^M\to\infty\) for every fixed \(M>0\), uniformly over the
window.  In particular \(p>2R\) eventually.

Under these same RH-false suppliers, the finite arithmetic conclusions
to be proved are

\[
\boxed{\begin{gathered}
 \text{for every fixed }\alpha>0\text{ there are cofinally many canonical}\\
 \text{original-source edges }0<C-A\le A^\alpha,\\
 \text{and cofinally many such edges }0<C-A<\log2\text{ with }U=V.
\end{gathered}}
\tag{CW0}
\]

The rest of the appendix proves this box and its exact consumer.

### Membership before counting

The next lemma is the point at which the prime count is used.  It is
proved before either the fixed-\(\alpha\) or the \(\log2\) pigeonhole
count, so no prime is counted merely because it was presumed to lie in
the window.

At \(y=e^\ell\) and \(v=e^{\beta\ell}\), the uniform GM estimate gives a
prime \(p_0\) with
\[
 e^\ell<p_0\le e^\ell+e^{\beta\ell},
 \qquad \log p_0\le\ell+\log2
\]
for large \(\ell\).  Let \(p_{i+1}\) be the actual next ordinary prime
after \(p_i\).  Whenever \(p_i\ge e^\ell\), apply GM at \(y=p_i\) with
\(v=p_i^\beta\).  This interval is permitted and contains a prime, so
\[
 0<\delta_i:=\log\frac{p_{i+1}}{p_i}
 \le\log(1+p_i^{\beta-1})
 \le p_i^{-5/12}\le E,
 \qquad E=e^{-5\ell/12}.
\]
For every specified finite \(k\), induction gives
\[
 \log p_i\le\ell+\log2+iE\qquad(0\le i\le k).
\]
Indeed the successor remains at least \(e^\ell\), and the displayed
bound is precisely the logarithm of the multiplicative successor
estimate.  If \(kE\to0\), choose the witness after the supplier starts
and with \(\ell>\log2+kE\).  Then all \(p_0,\ldots,p_k\) lie in
\([e^\ell,e^{2\ell})\), before any counting conclusion is drawn.  This
finite induction does not assert that an infinite sequence remains in one
fixed window.

For later use, the estimate \(ER^M\to0\) follows directly from
\(\log R=o(\ell)\).  It is uniform for each fixed \(M\), but no uniformity
in a moving \(M\) is claimed.

### The fixed-\(\alpha\) cofinal edge

Fix \(\alpha>0\) before choosing the witness.  Put
\[
 k_\alpha=\left\lceil\frac R{\ell^\alpha}\right\rceil+1.
\]
Then
\[
 k_\alpha E\le E\left(\frac R{\ell^\alpha}+2\right)\longrightarrow0.
\]
The preceding finite induction therefore puts \(p_0,\ldots,p_{k_\alpha}\)
inside \(\mathcal P_X\). Let \(N_i=N_{p_i}^{\rm mult}=p_iU_i\) and
\(A_i=\log N_i\) be the corresponding canonical least maximizers.  By the accepted N2
ordering, \(A_i<A_{i+1}\le R\), \(U_i\mid U_{i+1}\), and
\[
 A_{i+1}-A_i=\log(U_{i+1}/U_i)+\log(p_{i+1}/p_i)>0.
\]
If all \(k_\alpha\) edges had \(A_{i+1}-A_i>A_i^\alpha\), then, since
\(A_i\ge\ell\),
\[
 A_{k_\alpha}>A_0+k_\alpha\ell^\alpha>R,
\]
contradicting \(A_{k_\alpha}\le R\).  Thus one of these distinct
consecutive-label edges satisfies the claimed upper bound.  Since
\(\ell\to\infty\) along the CNS witnesses, choosing \(\ell\ge T\) gives
one with \(A\ge T\) for every finite \(T\).  This proves
\[
\begin{gathered}
 \forall\alpha>0\ \forall T\in\mathbb R\ \exists\text{ a consecutive}\\
 \text{canonical original-source edge with }A\ge T
 \text{ and }0<C-A\le A^\alpha.
\end{gathered}
\tag{CW1}
\]

The quantifiers in this statement are fixed-alpha quantifiers: the start
may depend on \(\alpha\) and on the supplier constants.  It does not say
that every edge has this spacing, that all \(\alpha\)'s work at one common
start, or that any long window has a mesh estimate.

### Exact \(\log 2\) rigidity

Now put
\[
 k_2=\left\lceil\frac{2R}{\log2}\right\rceil+1.
\]
The same membership induction applies because

\[
 k_2E\le\left(\frac{2R}{\log2}+2\right)E\longrightarrow0.
\]

Thus the \(k_2+1\) actual sources associated with
\(p_0,\ldots,p_{k_2}\) are all in the same admitted window.  If each of
the \(k_2\) edges had \(C_i-A_i\ge\log2\), telescoping would give
\[
 A_{k_2}\ge A_0+k_2\log2>2R,
\]
which contradicts \(A_{k_2}\le R\).  Select an edge with
\[
 0<C-A<\log2.
\]
For this edge \(U\mid V\), so \(j=V/U\) is a positive integer.  If
\(j\ge2\), then
\[
 C-A=\log j+\log(r/p)\ge\log2+\log(r/p)>\log2,
\]
which is impossible.  Consequently \(j=1\), and the exact arithmetic
identities are
\[
 U=V,\qquad D:=\log(V/U)=0,\qquad Z:=pV=pU=N,
 \qquad z:=\log Z=A,
\qquad \varepsilon:=F(N)-F(Z)=0.
\tag{CW2}
\]

The same choice can be made beyond every finite collection of analytic
or tolerance starts: choose a sufficiently large qualifying witness with
\(\ell\) above their maximum and satisfying the membership inequalities.
Thus the unchanged-core edges are cofinal in the original canonical
least-source family. Their sources remain distinct: \(N=pU\) and
\(N'=rU\), with \(p<r\). In fact \(C-A=\log(r/p)\le E\) on each
selected edge.  This proves a cofinal exact constant core, not a whole-window
common core, an every-edge equality, a long constant-core run, or a
cofinal assertion that \(D>0\) or \(Z>N\).

For reference, the counting argument is robust under a genuinely supplied
tolerance \(E_c=e^{-c\ell}\), \(c>0\): if the actual prime recurrence
gives \(\delta_i\le E_c\) and \(\log R=o(\ell)\), then
\(k_2E_c\to0\) and, for every fixed \(\alpha>0\),
\(k_\alpha E_c\to0\), so the same membership and both counting proofs
apply. This conditional observation
does not improve the supplied GM exponent and is not used as an input.

### The exact forward successor on the same original integer

Take one of the selected canonical constant-core edges. Its distinct
original integers are \(N=pU\) and \(N'=rU\), with \(p<r\); they share
only the core \(U=N_A^{\rm str}=N_C^{\rm str}\). Put
\[
 h=A^{4/5},\qquad B=A+h,\qquad
 L=pN_B^{\rm str},\qquad Y=\log L.
\]
Since \(B<2A\le2R<p\), the forced layer \((p,1)\) is absent from
\(N_t^{\rm str}\) throughout \([A,B]\).  Since \(U=N_A^{\rm str}\)
and strict inventories are divisibility-monotone,
\[
 N\mid L,\qquad 5040\mid L,
 \qquad L=\operatorname{lcm}(N,N_B^{\rm str}).
\]

The successor is genuinely larger.  Apply GM at the real point
\(A+h/3\) with length \(h/3\).  Eventually
\((A+h/3)^\beta\le h/3\le(A+h/3)^{99/100}\), so there is a prime

\[
 A+h/3<q\le A+2h/3.
\]

The first actual cutoff satisfies \(B-1<q_1(B)<B\).  Hence, for large
\(A\), \(q<B-1<q_1(B)\), so \((q,1)\) is absent from \(N_A^{\rm str}\)
and present in \(N_B^{\rm str}\).  Also \(q<p\), because \(q<B<2R<p\).
Therefore \(q\mid L/N\), and
\[
 L>N=Z.
\]
This is a literal integer successor retaining the full \(5040\) factor;
it is not a scalar relaxed competitor and is not asserted to be GA2.

The unique occupied extra of \(N\) is \((p,1)\), and

\[
 d_A(N)=(\lambda(A)-r_{p,1})\log p>0,
 \qquad
 R_{\rm term}(N,B)=(\lambda(B)-r_{p,1})\log p>0.
\]

Its occupied pressure loss is nevertheless exactly zero:
\[
 P_N(t)=0\ (A\le t\le B),
 \qquad V_N(A,h)=\int_0^hP_N(A+u)\frac{w(A+u)}{w(A)}\,du=0.
\]
The zero loss is caused by strict inactivity of the extra, while the own
defect remains positive.  These are different terms in the exact identity.

More generally, let \(N\ge3\) be an integer, \(A=\log N>1\),
\(h>0\), \(B=A+h\), and \(N_A^{\rm str}\mid N\). Let \(E_N\) be
its finite set of occupied layers excluded from \(N_A^{\rm str}\), and put
\[
 P_N(t)=\sum_{e\in E_N:\ r_e>\lambda(t)}h_e,
 \qquad
 Y_N(t)=\log\operatorname{lcm}(N,N_t^{\rm str}).
\]
The literal lcm clock is
\[
 Y_N(t)=A+K(t)-K(A)-P_N(t).
\]
With \(\rho_A(u)=w(A+u)/w(A)\), define
\[
 T_\psi(A,h)=\int_0^h[\psi(A+u)-\psi(A)-u]\rho_A(u)\,du,
 \quad
 S_Q(A,h)=\int_0^h[Q(A+u)-Q(A)]\rho_A(u)\,du,
 \quad V_N(A,h)=\int_0^hP_N(A+u)\rho_A(u)\,du.
\]
With \(Y=Y_N(B)>1\), the finite strict-lcm identity is
\[
 F(\operatorname{lcm}(N,N_B^{\rm str}))-F(N)
 =w(A)[T_\psi(A,h)+S_Q(A,h)-V_N(A,h)]+C_B(Y),
\]
where
\[
 C_B(Y)=f(B)+\lambda(B)(Y-B)-f(Y)\ge0.
\tag{CW3}
\]

Here \(C_B\) is the actual terminal concavity cost, not a fixed-price
objective term.  The selected branch has \(\operatorname{lcm}(N,N_B^{\rm str})=L\)
and \(V_N=0\).

For completeness, the proof is finite. On \([A,B]\), take one common
support containing all actual layers, equality layers, and reference
atoms. A missing actual layer has \(r_e\le\lambda(A)\) and an activation
\(t_e\ge A\) with \(\lambda(t_e)=r_e\). It is added to the strict
terminal lcm exactly when \(t_e<B\). Its integrated pressure is
\[
 \int_A^B\mathbf1_{t_e<t}h_ew(t)\,dt
 =(r_e-\lambda(B))_+h_e.
\]
A missing tie at \(A\) activates immediately to the right and has this
same weight; a missing tie at \(B\) is excluded and has zero weight.
Write \(\Delta=Y-A\) and
\(\mathcal W=W(\operatorname{lcm}(N,N_B^{\rm str}))-W(N)\). Finite
layer summation and one integration by parts give
\[
 \int_A^B[Y_N(t)-t]w(t)\,dt
 =\mathcal W-\lambda(B)\Delta-[f(B)-f(A)-h\lambda(B)].
\]
Adding \(C_B(A+\Delta)\) gives
\(\mathcal W+f(A)-f(A+\Delta)\), precisely the left side of CW3.
The clock formula and \(K=\psi+Q\) give, pointwise,
\[
 Y_N(A+u)-(A+u)
 =\psi(A+u)-\psi(A)-u+Q(A+u)-Q(A)-P_N(A+u),
\]
which yields its right side. The initial \(K(A)\) cancels without
assuming \(K(A)=A\). Reference atoms retain their weak convention:
\(\psi(t)-\psi(A)=\sum_{A<n\le t}\Lambda(n)\), with the initial
reference atom excluded and the terminal atom carrying zero pressure
weight. Simultaneous actual events retain every separate layer mass.
If missing terminal equality layers of total mass \(J\) are deliberately
installed, their reward is \(\lambda(B)J\); the pressure integral is
unchanged, but the clock and cost become \(Y+J\) and \(C_B(Y+J)\).
CW3 uses the strict successor and its actual \(Y\). No infinite-tail
subtraction is used.

The complete reference term, including every prime power, is
\[
 w(A)T_\psi(A,h)
 =\sum_{A<n\le B}\Lambda(n)[\lambda(n)-\lambda(B)]
 -[f(B)-f(A)-h\lambda(B)].
\tag{CW4}
\]
Indeed integrate each step function \(\mathbf1_{n\le t}\) over
\([A,B]\): its weight is
\(\int_n^B w(t)\,dt=\lambda(n)-\lambda(B)\), while the linear term has
integral \(f(B)-f(A)-h\lambda(B)\).  A prime power \(n=q^k\) carries
the full \(\Lambda(n)=\log q\) weight.  A reference atom at \(A\) is
excluded by the open lower endpoint and one at \(B\) has zero weight.
All simultaneous actual events retain their separate layer masses.

Because \(N\) is an actual GA2 integer and \(L\) is a positive multiple,
\(F(L)-F(N)\le0\).  On the selected edge the exact identity therefore
gives the necessary upper comparison
\[
 w(A)[T_\psi(A,A^{4/5})+S_Q(A,A^{4/5})]
 \le -C_B(Y)\le0.
\tag{CW5}
\]
The [full-Q supplier QH1--QH13/QQE/QQD](nicolas2025comparison.md#precise-full-signed-q-statement-and-quantified-error)
gives, for every sufficiently large real center,
\(S_Q(A,A^{4/5})=(c_Q+o(1))A^{11/10}\), where
\[
 c_Q=\frac{\sqrt2-1}{4}>0.
\]
More precisely, there are \(C_Q>0\) and one unknown \(A_*>2\) such that
for every real \(A\ge A_*\),
\[
 \left|\frac{S_Q(A,A^{4/5})}{A^{11/10}}-c_Q\right|
 \le C_Q\mathcal F_Q(A),
\]
\[
\begin{aligned}
 \mathcal F_Q(A)={}&\frac1{\log A}+A^{-1/5}
 +\log A\,e^{-((\log A)/3)^{1/4}}+A^{-1/120}\\
 &+A^{-3/10}\log A+A^{-1/6}(\log A)^{4/3}
 +A^{-19/180}(\log A)^{43/36}.
\end{aligned}
\]
All seven errors tend to zero. The actual square coefficient
\(\sqrt2/4\), the subtracted reference square coefficient \(1/4\),
both higher-layer inventories, and the strict endpoint correction
\(+\operatorname{atom}(y)-\operatorname{atom}(y+v)\) remain in this
supplier. Equivalently, for every fixed tolerance \(\eta>0\), there is
one unknown \(A_\eta\ge A_*\) such that
\(\left|S_Q(A,A^{4/5})-c_QA^{11/10}\right|\le\eta A^{11/10}\) for
**every real** \(A\ge A_\eta\). The cofinal canonical sources pass
each such start; no numerical start is supplied.
The displayed direction is an upper direction forced by GA2.  It is not a
favorable lower bound for \(T_\psi\).

### Scope of the project deductions

Under the same RH-false CNS/Robin, uniform GM, and full FW/N1--N5
suppliers, the results proved here are the cofinal additive edge for every
fixed \(\alpha>0\), the cofinal exact unchanged-core edge with
\(0<C-A<\log2\), the conditional tolerance generalization when an actual
\(E_c\) recurrence is supplied, and the exact same-original full-\(\Lambda\)
consumer with its necessary GA2 upper direction. The cofinal sources
are canonical least full-domain maximizers with their original last
labels and clocks. The generalization supplies no new prime estimate.

The mathematical dependencies and remaining obligations are:

| input or result | hypotheses and mathematical use |
|---|---|
| CNS positive oscillation and Robin envelope | RH failure supplies fixed \(1-\Theta<b<1/2\), \(d>0\), unbounded actual witnesses; the unconditional envelope gives the upper clock ceiling |
| Guth--Maynard Corollary 1.3 | one unknown all-real start, fixed \(\beta=7/12\), admitted lengths through \(y^{99/100}\); used for actual successor primes and the nontrivial forward integer |
| [FW0--FW22/N1--N5](trureturing2026extrawindowpairing.md) | full-domain attainment and label uniqueness for all ties, finite-window all-choice ordering, and global ordering of canonical least sources |
| membership, cofinality, rigidity, and CW3--CW5 | proved above on that same source family; strict inventories, full \(\Lambda\), occupied loss, and actual terminal cost are retained |
| [QH1--QH13/QQE/QQD](nicolas2025comparison.md#precise-full-signed-q-statement-and-quantified-error) | full signed \(Q\)-drift for every sufficiently large real center, with all seven errors and endpoint/higher-layer terms |
| [finite_signed_response_identity](../../D5/S3/Arith/Robin/ActualVonMangoldtBandCompensation.lean) | distinct finite centered-dilation identity; its kernel, theta premise, and finite boundary require a bridge to this forward consumer |
| [OpenAI/math](../Analytic/openai2026quasirh.md), [Mantovanelli/rough-shift](../Analytic/mantovanelli2026primeworkload.md), and [short-uniformity](../Analytic/shortuniformity2026robininterfaces.md) interfaces | their distinct zero-free, shift, weight, model, or testing hypotheses have not been instantiated for these selected full-\(\Lambda\) weights |
| full RH/Robin/5040 statement | \(I_\psi(\log n)+R(\log n)+d_{\log n}(n)>0\) for every actual integer \(n>5040\); remains ACTIVE_UNPROVED |

The formal-source consumer just named is
`D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation.finite_signed_response_identity`,
under its actual real-parameter hypotheses \(A\ge e^{78}\),
\(99/100\le c\le101/100\), \(A<R_{\rm cut}\), and
\(cA\le R_{\rm cut}\). Here \(R_{\rm cut}\) denotes that theorem's
finite cutoff parameter, distinct from both the window ceiling and the
original residual.
Its conclusion has the form
\[
 \mathrm{finiteResponse}
 =\mathrm{smoothBoundary}+\mathrm{bandVolume}
 -\mathrm{actualCompensation}.
\]
Its companion `finite_signed_response_upper_of_theta_increment_lower`
additionally requires \(H>0\), \(0\le\epsilon<1\), and
\(\mathrm{ThetaIncrementLower}(99A/100,H,\epsilon)\): for every
\(99A/100\le u<v\le198A/100\) with \(H\le v-u\),
\[
 (1-\epsilon)(v-u)\le\theta(v)-\theta(u).
\]
Its conclusion retains
\(\mathrm{smoothBoundary}+\epsilon\,\mathrm{bandVolume}
+(1-\epsilon)\,\mathrm{shortAllowance}\).
This kernel has a different finite boundary normalization from the
\(T_\psi\) kernel above; the required theta premise and the bridge to
the displayed full-\(\Lambda\) forward consumer remain unpaid.

The selected-source signed obligation for this route remains **one fixed**
\(\kappa<c_Q\) such that, beyond **every** required common unknown finite
start \(T\), there is an original canonical least source
\(N_p^{\rm mult}\) in the proved cofinal window family, with
\(A=A_p^{\rm mult}\ge T\), satisfying
\[
 T_\psi(A,A^{4/5})\ge-\kappa A^{11/10},
\]
or an equivalent fixed positive lower margin for the complete same-source
quantity.  Neither cofinality, zero occupied loss, exact \(Z=N\), positive
\(Q\)-drift, nor least attainment supplies that sign.  In particular, no
finite interval through \(8\cdot10^{46}\) pays an unknown asymptotic start,
and no finite common-start substitution is made.

No every-edge convergence and no every-edge \(A^{4/5}\)-scale spacing is
claimed.  Cofinal original-source \(A^\alpha\)-scale edges are proved for
each fixed \(\alpha>0\), and cofinal exact unchanged-core edges are proved
with \(0<C-A<\log2\), all under the same RH-false suppliers and on
canonical least full-domain sources. The original full signed lower input
remains unpaid. The unchanged all-integer target is
\[
 \forall n\in\mathbb N,\quad n>5040\ \Longrightarrow
 I_\psi(\log n)+R(\log n)+d_{\log n}(n)>0,
\]
and remains **ACTIVE_UNPROVED**. Here \(R(t)\) is the original signed
residual, not the window clock ceiling.

# Integrated weights of the original selected family

Let \(3\le\ell\le\mathcal R\), and let \(S\subset[\ell,\mathcal R]\)
be measurable, of mass \(M=|S|>0\). In the original source application,
\(S\) is the **complete** union of unchanged-core intervals of consecutive
window labels belonging to the canonical least full-domain maximizers
\[
 N_p=\min\operatorname*{argmax}_{5040p\mid n} \left[
 \log(\sigma(n)/n)-\log\log\log n\right].
\]
Nothing in the following weight construction changes these integers.
Put
\[
 f(x)=\log\log x,\quad\lambda(x)=1/(x\log x),\quad
 w(x)=-\lambda'(x),\quad H_t=t^{4/5},\quad B_t=t+H_t.
\]
Define the real kernel by
\[
 k_t(x)=\begin{cases}
 [\lambda(x)-\lambda(B_t)]/[w(t)t^{11/10}],&t<x\le B_t,\\
 0,&\text{otherwise}.
 \end{cases}
\]
Thus no price is evaluated at \(x\le1\). Set
\[
 \mathcal W(x)=\int_S k_t(x)\,dt,\qquad
 a(t)=\frac{f(B_t)-f(t)-H_t\lambda(B_t)}{w(t)t^{11/10}},
 \quad \mathcal D=\int_S a(t)\,dt,
\]
\[
 b(t)=\frac{\lambda(t)-\lambda(B_t)}{w(t)t^{11/10}},
 \qquad\mathcal B=\int_S b(t)\,dt.
\]

For the source geometry, the strict inventory means
\[
 r_{q,k}=\frac{\log(1+1/(q+\cdots+q^k))}{\log q},\quad
 \mathcal N(t)=\prod_{q\ \mathrm{prime}}
 q^{\#\{k\ge1:r_{q,k}>\lambda(t)\}},\quad K(t)=\log\mathcal N(t).
\]
Every compact clock interval has one finite set of potentially active or
tied actual layers, since \(r_{q,k}<1/(q^k\log q)\). Equal-price
layers are excluded from the strict inventory.

**Proposition.** The weight \(\mathcal W\) is nonnegative, compactly
supported, and absolutely continuous. Its derivative is, almost everywhere,
\[
 \mathcal W'(x)=\mathbf1_S(x)b(x)
 -w(x)\int_{\substack{t\in S\\t<x<B_t}}
           \frac{dt}{w(t)t^{11/10}}.
\tag{A1}
\]
In (A1) the two nonnegative densities are defined on \(x>1\) and
are extended by zero on \(x\le1\), without evaluating a price there.
Both densities have integral \(\mathcal B\), and
\[
 \mathcal B\le M\ell^{-3/10},\quad
 \operatorname{Var}(\mathcal W)\le2\mathcal B,\quad
 0\le\mathcal W\le\mathcal B,\quad
 \int_0^\infty\mathcal W(x)\,dx=\mathcal D.
\tag{A2}
\]

*Proof.* Since \(w\) decreases,
\(b(t)\le H_t/t^{11/10}=t^{-3/10}\). For every real \(x\),
\[
 k_t(x)=b(t)\mathbf1_{x>t}
 -\frac1{w(t)t^{11/10}}\int_t^{B_t}\mathbf1_{s<x}w(s)\,ds.
\]
This representation also holds at both endpoints. Integrating in \(t\)
and applying Tonelli expresses \(\mathcal W\) as the difference of the
indefinite integrals of the two integrable densities in (A1). Each has
integral \(\mathcal B\). Absolute continuity and the variation bound
follow. Also \(0\le k_t\le b(t)\), and all kernels vanish outside
\([\ell,2\mathcal R]\). Finally direct integration gives
\(\int k_t=a(t)\); Tonelli proves the last identity. No estimate for
the number of connected components of \(S\) is used. \(\square\)

Let \(\psi(x)=\sum_{n\le x}\Lambda(n)\) use the full von Mangoldt
function, and put
\[
 \Phi(t)=t^{-11/10}\int_0^{H_t}
  [\psi(t+u)-\psi(t)-u]\frac{w(t+u)}{w(t)}\,du,
 \quad\mathcal I=\int_S\Phi(t)\,dt,
 \quad J=\lfloor2\mathcal R\rfloor.
\]

**Corollary (discrete centering with absolute small error).**
With \(\Lambda(1)=0\),
\[
 \mathcal I=\sum_{n=1}^J(\Lambda(n)-1)\mathcal W(n)+e_S,
\quad
 e_S=\int_0^\infty(\{x\}-1/2)\mathcal W'(x)\,dx,
\quad |e_S|\le M\ell^{-3/10}.
\tag{A3}
\]
Equivalently,
\[
 \mathcal I=\sum_{d=1}^J\mu(d)
       \sum_{m=1}^{\lfloor J/d\rfloor}\log m\,\mathcal W(dm)
       -\mathcal D.
\tag{A4}
\]
Every reference power \(q^k\) is present with mass \(\log q\).

*Proof.* The finite step identity for \(\psi\) gives
\(\Phi(t)=\sum_{n=2}^J\Lambda(n)k_t(n)-a(t)\).
An initial atom \(n=t\) is excluded, and an included terminal atom
\(n=B_t\) has zero weight. Finite interchange gives
\(\mathcal I=\sum\Lambda(n)\mathcal W(n)-\mathcal D\).
Integration by parts against \(\lfloor x\rfloor\) and against \(x\)
gives
\[
 \sum_n\mathcal W(n)-\int\mathcal W
 =\int\{x\}\mathcal W'(x)\,dx
 =\int(\{x\}-1/2)\mathcal W'(x)\,dx.
\]
The boundary terms vanish, and (A2) bounds its absolute value by
\(\operatorname{Var}(\mathcal W)/2\le\mathcal B\). This proves (A3).
For (A4), use \(\Lambda=\mu*\log\) and regroup only pairs with
\(dm\le J\). Indeed the coefficient of \(\log p\) in
\(\sum_{d\mid n}\mu(d)\log(n/d)\) is
\((1-1)^{\omega(n)-1}\) for each prime dividing \(n>1\): it is
one for a prime power and zero otherwise. At \(n=1\) the logarithm
vanishes. Thus this regrouping retains every power and every divisor
scale. \(\square\)

For any real or complex sequence indexed by positive integers, \(a_n\), let \(A_a(x)=\sum_{n\le x}a_n\).
The exact testing interface is
\[
 \sum_{n=1}^J a_n\mathcal W(n)
 =-\int_0^\infty A_a(x)\mathcal W'(x)\,dx
 =\int_S\frac1{w(t)t^{11/10}}
     \int_t^{B_t}[A_a(x)-A_a(t)]w(x)\,dx\,dt.
\tag{A5}
\]
The first identity is finite Abel summation. The second uses (A1) and
\(b(t)=\int_t^{B_t}w(x)\,dx/[w(t)t^{11/10}]\); it cancels the
same initial prefix, without changing any integer endpoint.

In particular, if \(C\ge0\), \(c\ge0\), and a supplied ordinary
prefix estimate is
\(|A_a(x)|\le Cx/(\log x)^c\) for every real \(x\ge3\), then
\[
 \left|\sum_n a_n\mathcal W(n)\right|
 \le3C\int_S\frac{t^{7/10}}{(\log t)^c}\,dt.
\tag{A6}
\]
To prove this, bound the jump part of (A1) by
\(b(t)Ct/(\log t)^c\), and its descending part by
\(b(t)2Ct/(\log t)^c\), since \(t\le x\le B_t<2t\).
When \(|a_n|\le1\), positivity and (A3) also give the elementary
bound \(\mathcal D+\mathcal B\); one may take the minimum of the two
allowances.

The pinned OpenAI/math ordinary affine Liouville supplier, at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, gives precisely the prefix
premise of (A6) for
\(a_n=\lambda_L(a_1n+b_1)\lambda_L(a_2n+b_2)\), with fixed
\(a_1,a_2\ge1\), \(b_1,b_2\ge0\), and
\(a_1b_2-a_2b_1\ne0\). Here \(\lambda_L\) is Liouville, not the
price \(\lambda\). The exponent is absolute and the constant depends
on these fixed forms. Thus (A6) is a genuine ordinary, supplier-relative
application to the original selection weight, even though that weight is
not multiplicative. The source is the ordinary preprint's quantitative
affine theorem and the actual `OAI/NumberTheory/TwoPointCorrelations/FinalMain.lean`
entry, not the `sorry` comparator interface. No external formal validation
is asserted. Neither this large allowance nor its minimum with the
elementary bound gives the required absolute \(O(M)\) signed estimate.

For every cofactor \(m\), including moving ones, (A5) applied to the
dilated weight gives
\[
 \sum_{d\le\lfloor J/m\rfloor}\mu(d)\mathcal W(md)
 =-\int_0^\infty M_\mu(x/m)\mathcal W'(x)\,dx
 =\int_S\frac1{w(t)t^{11/10}}
       \int_t^{B_t}[M_\mu(x/m)-M_\mu(t/m)]w(x)\,dx\,dt.
\tag{A7}
\]
No factor \(m\) remains: the derivative of the dilated weight cancels
the change-of-variable Jacobian. Its elementary bound is
\(\mathcal D/m+\mathcal B\). A qualitative Mertens supplier gives,
for each fixed \(m\), the alternative bound
\[
 \frac{3\eta_\mu(\ell/m)}m\int_S t^{7/10}\,dt,
 \quad\eta_\mu(s)=\sup_{y\ge s}|M_\mu(y)|/y\longrightarrow0.
\]
This does not provide a uniform small allowance when \(m\) grows up
to \(J\). The full sum in (A4) still needs all its logarithms and rows.

The original good-edge geometry also has an exact continuous comparison.
Let its endpoint sources be \(pU,rU\), with clocks \(A<C\), both
GA2 against all positive multiples, and suppose the strict inventory
\(\mathcal N(t)\) equals \(U\) on the closed interval \([A,C]\).
For sufficiently late original witnesses, both labels exceed
\(2\mathcal R\), whereas all primes in \(V_t=\mathcal N(B_t)\)
are below \(B_t<2\mathcal R\). Also \(U\mid V_t\) and
\(5040\mid U\); hence \(rV_t\) is a legal integer multiple
of \(rU\) retaining 5040. Put
\(D_t=\log(V_t/U)\), \(Y_t=t+D_t\), and
\[
 C_B(Y)=f(B)+\lambda(B)(Y-B)-f(Y)\ge0.
\]
Then, with \(Q=\log\mathcal N-\psi\) and the full signed
\(S_Q(t,H)=\int_0^H[Q(t+u)-Q(t)]w(t+u)/w(t)\,du\),
\[
 w(t)[t^{11/10}\Phi(t)+S_Q(t,H_t)]+C_{B_t}(Y_t)
 \le-\int_t^C[\lambda(s)-\lambda(s+D_t)]\,ds\le0.
\tag{A8}
\]
To prove it, freeze \(V_t\) and differentiate
\[
 W(V_t)-W(U)-f(s+D_t)+f(s),\qquad W(n)=\log(\sigma(n)/n).
\]
Here \(V_t\) and \(D_t\) are frozen while \(s\) varies. Its
derivative is \(\lambda(s)-\lambda(s+D_t)\ge0\), and its value
at \(C\) is \(F(rV_t)-F(rU)\le0\). Finite layer integration between
\(U\) and \(V_t\) identifies its value at \(t\) with the left side
of (A8): an activation at \(t\) is initially absent and integrated on
its right, and an activation tied at \(B_t\) is excluded with zero
integrated weight. Adding the displayed terminal cost cancels the linear
terms. At \(t=A\), \(Y_t\) is the actual original lcm-successor
clock; other real centers are scalar interpolations of that legal
endpoint comparison, not newly claimed integer maximizers.

For the complete original family, the full-Q supplier gives
\(S_Q(t,H_t)/t^{11/10}\to c_Q=(\sqrt2-1)/4\), uniformly beyond
an unknown every-real tolerance start. Integrating (A8) preserves the
interpolated cost and nonnegative comparison slack. Independently, the
actual departures retain their discrete terminal costs. Thus (A3)
provides an absolute \(o(M)\) bridge to the same weighted
\(\Lambda-1\) lower obligation. A fixed lower coefficient
\(\kappa<c_Q\), available on cofinally many complete original
families after every common start, is still **unproved**. All-integer
RH/Robin/5040 remains **ACTIVE_UNPROVED**.


## Full-family quantifiers, reference powers and finite source maps

These additions are ordinary project deductions relative to the same
completed source-localization, corrected CW and FW suppliers and the
immutable sources named below. They preserve the same original integers,
the complete original selected set, and every reference and divisor row.

In the original RH-false application, one fixes the CNS/Robin constants
\(1-\Theta<b<1/2\), \(d>0\) before the unbounded witness clocks
\(X\). The suppliers give
\[
 \ell=(d/8)X^{1-b}\log X,\quad
 \mathcal R=\exp(\sqrt{2K_R/d}X^{b/2}),\quad
 E=e^{-5\ell/12},\quad K_R=0.6483e^{-\gamma},
\]
\[
 \ell-(2+\mathcal R/\log2)E\le M_X\le\ell,
 \quad M_X\sim\ell,\quad \log\mathcal R=o(\ell).
\]
The source-window all-choice ordering applies to the canonical least
full-domain maximizers; no global arbitrary-tie assertion is substituted.
The ordinary window labels are exactly primes
\(p\in[e^\ell,e^{2\ell}]\), and consecutive good edges have
\(N_i=p_iU_i\), \(U_i=U_{i+1}\),
\(C_i-A_i=\delta_i=\log(p_{i+1}/p_i)\in(0,E]\).
Here every sum indexed by \(i\) is over all these good edges.
Every full selected interval has closed strict inventory \(U\), with
its half-open version used only for disjoint integration. The unknown
uniform GM and full-Q starts are retained.

For an actual departure \(A_i\), put
\(L_i=p_i\mathcal N(B_{A_i})\), \(Y_i=\log L_i\), and retain
the actual discrete cost
\[
 \mathcal C_X=\sum_i
 \frac{\delta_i C_{B_{A_i}}(Y_i)}{w(A_i)A_i^{11/10}}\ge0.
\]
The finite lcm identity and actual GA2 yield, for every fixed tolerance
\(\eta>0\) beyond the common starts,
\[
 \mathcal I_X\le-(c_Q-\eta)M_X-\mathcal C_X+\varepsilon_X,
 \quad\varepsilon_X=30E\mathcal R^{7/10}\log(2\mathcal R)=o(1).
\tag{A9}
\]
The whole-interval comparison (A8) independently yields
\[
 \mathcal I_X\le-(c_Q-\eta)M_X-
 \widetilde{\mathcal C}_X-\mathcal H_X,
\]
\[
 \widetilde{\mathcal C}_X=\sum_i\int_{A_i}^{C_i}
 \frac{C_{B_t}(t+D_t)}{w(t)t^{11/10}}dt,\quad
 \mathcal H_X=\sum_i\int_{A_i}^{C_i}
 \frac{\int_t^{C_i}[\lambda(s)-\lambda(s+D_t)]ds}
 {w(t)t^{11/10}}dt.
\tag{A10}
\]
Both costs are retained; they are not identified with one another.
GM at real \(t+H_t/3\), length \(H_t/3\), supplies a prime
between \(t+H_t/3\) and \(t+2H_t/3\) once the permitted relative
counting error is below \(1/2\). The admitted length ratios follow from
\(7/12<4/5<99/100\). Using \(x-1<q_1(x)<x\), its first layer
is absent at \(t\) and strictly present at \(B_t\), uniformly for
\(t\ge\ell\). Thus \(D_t>0\) eventually. The explicit slack
satisfies
\[
 0<\mathcal H_X\le EM_X\ell^{-1/10}=o(1),
\tag{A11}
\]
because \(C_i-t\le E\), the inner integral is at most
\(E\lambda(t)\), and \(\lambda(t)/w(t)<t\). This is an upper
bound for that specific slack; it gives no fixed favorable margin.
Pointwise (A8) also gives
\(\int_S\Phi^2\ge(c_Q-\eta)^2M_X\) for \(0<\eta<c_Q\).

The exact sufficient lower obligation is
\[
 \exists\text{ one fixed }\kappa<c_Q\quad
 \forall\text{ finite common starts }T\quad
 \exists\text{ qualifying original witness with }\ell\ge T:
 \quad\mathcal I_X\ge-\kappa M_X.
\tag{A12}
\]
The selected set is the **complete** original family for that witness.
Fix \(\eta=(c_Q-\kappa)/2\) first. Then (A9) contradicts (A12)
for a sufficiently late such witness, since it would require
\((c_Q-\kappa)M_X/2+\mathcal C_X\le\varepsilon_X\).
This proves the implication, not the lower bound.
The discrete departure mean differs by \(\varepsilon_X/M_X=o(1)\).
A favorable full mean gives a favorable departure atom after fixing
slack; a single favorable atom does not imply the full family mean.
An original cofinal atom would separately suffice for the GA2
contradiction, but has not been obtained.

The exact baseline in (A2) has the quantitative size
\[
 \frac12(1+\ell^{-1/5})^{-4}\int_S\sqrt t\,dt
 \le\mathcal D\le\frac12\int_S\sqrt t\,dt.
\tag{A13}
\]
This uses \(|w'/w|\le4/t\) and direct integration of
\(u\,w(t+u)/(w(t)t^{11/10})\). Replacing \(\mathcal D\) by its
leading term need not have absolute \(o(M)\) error. The \(d=1\)
row in (A4), by itself, is at least
\((\log\ell)(\mathcal D-\mathcal B)\); divided by \(M\) it
diverges by (A13). It cannot be deleted and paid by its own absolute
\(O(M)\) mass. No sign for a regrouped nonrough remainder is inferred.

### Reference powers at the exact first-moment scale

With \(\theta(x)=\sum_{q\le x}\log q\), define the analogous
\(\Phi_\theta\) by replacing \(\psi\) in \(\Phi\) with
\(\theta\). Finite step integration gives exactly
\[
 \Phi(t)-\Phi_\theta(t)
 =\sum_{q^k,\ k\ge2}\log q\,k_t(q^k)\ge0.
\tag{A14}
\]
At project pin `fe5fd5fbd2ef0072806ad77b3d10fcd8f2e46fa2`,
`Library/ArithSums/nicolas2025comparison.md` QH12 integrates the full
reference-square increment and gives its normalized value
\(1/4+o(1)\) for every sufficiently large real center. Its exact
derivative is \(1/(2\sqrt t)\), whereas the actual second-cutoff
derivative is \(q_2'(t)=(1/\sqrt{2t})[1+O(1/\log t)]\), giving the
distinct leading coefficient \(\sqrt2/4\). The lower-length enclosure
\(h_0=(2\sqrt t)^{7/12}\) costs
\(H_th_0/t^{11/10}=2^{7/12}t^{-1/120}\).

QH8 bounds the **sum of the two nonnegative** actual and reference
higher-increment inventories, on a common growing support
\(k\le7\log t\); hence it also bounds the reference increments
alone. QH9–QH10 give their integrated normalized allowance
\[
 C[t^{-1/6}(\log t)^{4/3}
 +t^{-19/180}(\log t)^{43/36}+t^{-3/10}\log t].
\]
This uses one common GM threshold, permitted enclosing intervals for
increments shorter than the GM minimum, and a finite small-cutoff bound;
GM is never applied below its minimum. The complete QQE error function is
\[
\begin{aligned}
 \mathcal F_Q(t)={}&1/\log t+t^{-1/5}
 +\log t\,e^{-((\log t)/3)^{1/4}}+t^{-1/120}\\
 &+t^{-3/10}\log t+t^{-1/6}(\log t)^{4/3}
 +t^{-19/180}(\log t)^{43/36}.
\end{aligned}
\]
Both square calculations, every growing higher layer, strict initial
actual atoms, excluded strict terminal atoms and weak reference endpoints
remain in that supplier. It has one unknown every-real tolerance start.
Consequently
\[
 \mathcal I_X=\int_S\Phi_\theta(t)dt+\tfrac14M_X+o(M_X).
\tag{A15}
\]
With fixed slack, an equivalent theta formulation of the open lower
obligation has coefficient strictly below
\(c_Q+1/4=\sqrt2/4\). This equivalence concerns existence of a fixed
strict coefficient, not equality at the unbuffered boundary. Under the
same RH-false suppliers the necessary upper bound is instead
\(\int_S\Phi_\theta\le-\sqrt2 M_X/4+o(M_X)\).
No favorable theta estimate replaces the all-power target.

### Full centered covariance and a genuine rough-block application

For each selected center put
\[
 Z_t(d)=\sum_{m\le J/d}\log m\,k_t(dm),\quad
 \Gamma(d,e)=\int_SZ_t(d)Z_t(e)dt,\quad
 b_1(d)=\int_Sa(t)Z_t(d)dt,\quad c_1=\int_Sa(t)^2dt.
\]
The exact finite convolution gives the complete centered expansion
\[
\begin{aligned}
 \int_S\Phi^2={}&\sum_d\mu(d)^2\Gamma(d,d)
 +2\sum_{z=1}^{J-1}\sum_{r=1}^{J-z}
 \mu(r)\mu(r+z)\Gamma(r,r+z)\\
 &-2\sum_d\mu(d)b_1(d)+c_1.
\end{aligned}
\tag{A16}
\]
This keeps the diagonal, all logarithmic cofactor rows, shifts, linear
term and baseline. For \(\Gamma_z(r)=\Gamma(r,r+z)\), extended by
zero past its support, and
\(S_r(z)=\sum_{d=1}^r\mu(d)\mu(d+z)\), exact Abel telescoping is
\[
 \sum_r\mu(r)\mu(r+z)\Gamma_z(r)
 =\sum_{r=1}^JS_r(z)[\Gamma_z(r)-\Gamma_z(r+1)],
 \quad\Gamma_z(J+1)=0.
\tag{A17}
\]
The actual qualitative source gives \(S_r(z)=o_z(r)\) for fixed
positive \(z\); it gives no uniform conclusion for all growing shifts.

Fix \(C_0\ge1\), \(1<\tau<2\), \(\epsilon=10^{-4}\) and a
large \(B\) beyond the named common supplier start. Let
\[
 P_0=e^{B^{1-\epsilon}},\quad
 P_0/\tau\le M_0\le e^{C_0B},\quad D=\lceil M_0\rceil,
\]
and let \(Z\subset(M_0,\tau M_0]\) be a finite set of positive
\(P_0\)-rough integers. Set
\[
 \omega_r=\max_{z\in Z}z|\Gamma_z(r)-\Gamma_z(r+1)|,\quad
 c_r(z)=z[\Gamma_z(r)-\Gamma_z(r+1)]/\omega_r
\]
when the row is nonzero, and set zero for empty sets or zero rows.
Then \(|c_r(z)|\le1\), and these coefficients are fixed before
the dummy sum over \(d\le r\). Thus
\[
 O_Z=\sum_{z\in Z}\sum_d\mu(d)\mu(d+z)\Gamma_z(d)
 =\sum_{r=1}^J\omega_r\sum_{z\in Z}c_r(z)S_r(z)/z.
\tag{A18}
\]

The actual ordinary preprint `build/qualitative/analytic-transfer.tex`,
lemma `lem:rough-multiplier`, at external pin
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, permits arbitrary fixed
bounded coefficients on this exact support. Its fixed multiplier integer
is \(h=1\) here. It gives
\[
 \|Q\|_\infty\ll B^{-1+\epsilon}\log B,\quad
 \int_{\mathbb T}|Q|^4\ll
 M_0^{-1}B^{-4+4\epsilon}(\log B)^6,
 \quad Q(\alpha)=\sum_Zc(z)e(z\alpha)/z.
\]
The source proof depends only on the rough support; no dependence of
coefficients on the averaging integer is permitted. Dependence on the
fixed row and original selected family is permitted.

The finite FQ/MRT derivation in the project pin's
`Library/Analytic/mantovanelli2026primeworkload.md` combines this premise
with named MRT Theorem 1.7 and the quantitative Möbius distance bound.
It retains exactly
\[
 \mathcal M_\mu(r,Q)=\inf_{|u|\le r,q\le Q,\chi\bmod q}
 \sum_{p\le r}\frac{1-\Re(\mu(p)\overline{\chi(p)p^{iu}})}p,
 \quad Q_H(r)=\min((\log r)^{1/125},(\log H)^5),
\]
and the frequency supremum outside the short-interval average.
For windows \(D,3D\), the exact early and late overlap triangles
have total absolute mass \(D(D-1)\), costing \((D-1)h_Z\) after
division by \(D\), where \(h_Z=\sum_Z1/z\le1\).
The complete finite allowance is
\[
 F_B(0)=0,\quad F_B(r)=rh_Z\quad(1\le r<3D),
\]
\[
\begin{aligned}
 F_B(r)={}&C_{20}r[B^{-1-\epsilon}
 +B^{-2+10\epsilon}(\log B)^8\\
 &+B^{-1+9\epsilon}(\log B)^7(\log r)^{-1/700}]
 +(D-1)h_Z\quad(r\ge3D).
\end{aligned}
\]
Here \(C_{20}\) is fixed, and the common supplier start is unknown.
The eventual simpler range is
\(r\ge\lceil\max(e^B,DB^2)\rceil\), with the actual rounded
\(D\). Applying this finite estimate to every fixed row of (A18)
proves the valid ordinary supplier-relative bound
\[
 |O_Z|\le\sum_{r=1}^J\omega_rF_B(r).
\tag{A19}
\]
The full exact budget, all small rows, nonrough shifts, diagonal, linear
term and baseline in (A16) remain necessary. Neither a small centered
energy bound nor a favorable first-moment sign follows. The covariance
of the different largest-optimizer sample in Mantovanelli is not
identified with this \(\Gamma\).

### Precise remaining analytic input and other source boundaries

The actual affine source permits \(\mu\): it is 1-bounded and
multiplicative, and its prime values, hence pretentious distances, equal
Liouville's. Its full growing-height nonpretentiousness is supplied by
the source's MRT Appendix C and fixed-modulus PNT argument. Applying the
qualitative binary result to \(\mu(n)\cdot1(n+1)\) gives the
classical \(M_\mu(x)=o(x)\), used in (A7). In all rows (A7), the
prefix is evaluated at \(x/m\), not at \(x\) or \(e^t\).
Qualitative decay for fixed \(m\) supplies neither a uniform small
bound for \(m\le J\) nor a paid sum with every \(\log m\).

Actual `DirichletL/Nonvanishing.lean` retains only strict
\(\Re s>7/8\), positive moduli and the principal-pole exception;
it is not RH. Its detector has ideal-character, modulus, width and
capacity hypotheses distinct from (A4). Ideal Möbius on the Eisenstein
ring does not become integer Möbius under norm: the inert prime ideal
\((2)\) has norm 4 and Möbius \(-1\), whereas \(\mu(4)=0\).
No ideal/detector transport to (A4) is claimed.

The separate D5 `finite_signed_response_identity` retains
\(A\ge e^{78}\), \(99/100\le c\le101/100\),
\(A<R_{\rm cut}\), \(cA\le R_{\rm cut}\). Its upper companion
also needs \(H>0\), \(0\le\epsilon<1\) and every admitted theta
increment on \([99A/100,198A/100]\) of length at least \(H\).
Its smooth boundary, volume and short allowance are not this kernel's
forward baseline. The short-uniformity sources likewise retain their
models, fixed testing complexity or well-factorable hypotheses and total
prime baseline. None has been silently instantiated as the missing sign.

The remaining input is (A12), or equivalently (A4)'s complete double sum
at least \(\mathcal D_X-\kappa M_X\), with one fixed
\(\kappa<c_Q\), after every common unknown start. By (A3), a proved
lower coefficient strictly below \(c_Q\) for the **same** weighted
\(\Lambda-1\) sum transfers using fixed slack. The negative selected
initial excursion does not bound its coupled forward tail; tiny future
Stieltjes errors do not bound the whole terminal comparison. No fixed
\(\kappa\), source sign, RH, stronger external formal closure or
all-integer Robin/5040 proof is supplied. The original signed target for
every \(n>5040\) remains **ACTIVE_UNPROVED**.

## Project application: density-weighted order-nine transport reaches 3e47

This `repo-derived` quantitative application consumes the complete zero-mass
bound already established in [Polak (W5), (X1)–(X2)](../Analytic/polak2026finiterobinca.md#keep-the-coupled-logarithmic-exponent-in-the-complete-density-tail)
inside the existing GAK positive-law transport. The density theorem,
whole-law construction, coefficient remainder and unrestricted reserve
are reused. Their proofs and finite zero computations are not repeated.
The additional step is to retain the density-weighted mass before choosing
the smoothing order. Under the five primary analytic premises listed in
GAK section 1, together with Chourasiya–Simonič's
[arXiv:2507.15184v2](https://arxiv.org/pdf/2507.15184v2), Corollary 1 and
Table 1, the resulting signed allowance applies uniformly on

$$
8\cdot10^{46}<A\le3\cdot10^{47},\qquad
L=\log A,\quad T_A=\sqrt A L.
\tag{GAD1}
$$

The cited density rows and finite-height verification remain external
premises. This is an ordinary analytic application, without a full
primary-proof audit, a Lean/kernel proof or a worldwide priority claim.

### Retain the actual real-part layers in the complete zero mass

Keep $H=3\cdot10^{12}$, $h=\log H$ and $s=\log(Hh)$. Reuse Polak's
positive-ordinate mass, including every actual zero with analytic
multiplicity,

$$
B_2(A)=\sum_{\gamma>H}m_\rho
 \frac{A^{\beta-1/2}+A^{1/2-\beta}}{\gamma^2},\qquad
\alpha(\sigma)=\frac{1+\sigma}{2-\sigma}.
$$

Its already established (X2) consequence is

$$
B_2(A)<2A^{1/4}S_2(H)
 +144Lh^4\int_{3/4}^1
    A^{\sigma-1/2}(Hh)^{-\alpha(\sigma)}\,d\sigma
 +30000H^{-2}(\sqrt A-A^{1/4}).
\tag{GAD2}
$$

This integrates the actual reflected population through every height
above $H$. In particular it does not substitute a finite-height ceiling
for a full-tail count. Its density source and parameter correspondence
are those of Polak (W1), (W2), (W5), (X1).

GAK25 gives $L>107$ on (GAD1). The same rational logarithm enclosure
gives $\log3<1.099$ and $\log10<2.303$, hence $h<28.74<29$.
The positive exponential prefix
$\sum_{j=0}^{10}(84/25)^j/j!>1437/50$ gives
$\log28.74<3.36$. Therefore $s<32.1$.

For $f_A(\sigma)=L(\sigma-1/2)-s\alpha(\sigma)$,

$$
f_A'(\sigma)=L-\frac{3s}{(2-\sigma)^2}\ge L-3s>0
\qquad(3/4\le\sigma\le1).
$$

Integrating this derivative lower bound from $\sigma$ to $1$ yields
$f_A(\sigma)\le f_A(1)-(L-3s)(1-\sigma)$. Thus

$$
\int_{3/4}^1e^{f_A(\sigma)}\,d\sigma
 <\frac{e^{L/2-2s}}{L-3s}.
$$

Since $h^4e^{-2s}=h^2/H^2$, (GAD2) gives the useful uniform envelope

$$
B_2(A)<2A^{1/4}S_2(H)
 +\frac{144h^2\sqrt A}{H^2}\frac{L}{L-3s}
 +\frac{30000\sqrt A}{H^2}.
\tag{GAD3}
$$

Set $r=5478\cdot10^{20}$. Then
$r^2=3.0008484\cdot10^{47}>3\cdot10^{47}$, so $\sqrt A<r$
and $A^{1/4}<10^{12}$. Also $L/(L-3s)<10$, because $L>107$,
$3s<96.3$ and $107/(107-96.3)=10$. Reuse
$S_2(H)<37/(25\cdot10^{12})$ to obtain

$$
B_2(A)<2(10^{12})\frac{37}{25\cdot10^{12}}
 +\frac{144(29)^2r}{H^2}\,10+\frac{30000r}{H^2}
 =\frac{9442616}{125}<76000.
\tag{GAD4}
$$

Reflection at fixed positive ordinate preserves multiplicity, and
conjugation supplies negative ordinates. Consequently

$$
B_2(A)=\sum_{|\gamma|>H}
       \frac{m_\rho A^{\beta-1/2}}{\gamma^2}.
\tag{GAD5}
$$

No further factor of two belongs in the complete high-zero response.

### Consume the complete mass with a lower-variance whole law

Use GAK3–GAK6 with the changed order $k=9$, leaving
$\delta=51/(20H)$ and $q=219/1000$. Put $x=\delta^2$ and reuse

$$
M_*=(1-2kx)^{-1},\qquad V_*=\frac{kx}{3-(k+3)x}.
$$

All denominators are positive; the whole support lies in $(.99,1.01)$
and the mean is exactly one. GAK41 and GAK47's actual-real-part
normalization give $|H_C(\rho)|<q^9$ for every $|\gamma|>H$;
the head bound remains $M_*$. The scalar normalization base in GAK47
is independent of $k$, so only its power changes.

Retain the original complete coefficient $F_A$ of GAK10, including
GAK12's remainder, in $Z_C(A)=\sum_\rho m_\rho H_C(\rho)F_A(\rho)$.
GAK24's head and tail remainder factors $527/500$ and $10001/10000$,
together with (GAD4)–(GAD5), imply

$$
T_A|Z_C(A)|<U_h+U_t,
$$

$$
\begin{aligned}
U_h&=\frac{108}{107}\frac{527}{500}\frac1{20}M_*,\\
U_t&=\frac{108}{107}\frac{10001}{10000}q^9(76000),\\
U_v&=\frac{260001}{500000}rV_*,\qquad
U_e=\frac{5M_*}{10^{23}}.
\end{aligned}
\tag{GAD6}
$$

GAK26's bound $\eta_0(A)<10^{-6}$ is independent of the upper
endpoint, and $\sqrt A>10^{23}$ still holds. GAK23 therefore gives
the original uncentered signed integral, retaining its cutoff atoms and
full elementary response,

$$
-T_AI_\psi(A)<U_h+U_t+U_v+U_e<\frac{19}{25}.
\tag{GAD7}
$$

The sufficient exact rational comparisons are
$U_h<.0532$, $U_t<.0889$, $U_v<.6175$ and
$U_e<6\cdot10^{-23}$. Their sum is less than $.76$.
No class average, favorable class selection or zero-phase sign is used.

### Keep the actual integer defect and the selected-source distinction

For each integer $n$ whose own clock $A=\log n$ satisfies (GAD1),
reuse its own nonnegative $d_A(n)$ and the exact identity GAK39.
GAK37's same unrestricted reserve obeys
$T_AR(A)>Q_R+L/(L+2)^3$, with the unchanged
$Q_R=67838284064811/83593750000000$ and $Q_R-19/25>1/20$.
Consequently, under the stated analytic premises,

$$
T_A\Delta(n)>
\frac1{20}+\frac{L}{(L+2)^3}+T_A d_A(n)>0.
\tag{GAD8}
$$

This bounded all-integer clock conclusion sets no defect to zero and
requires no CA or maximizer condition. It does not establish Robin
for every smaller integer up to this upper endpoint.

For the separate least-global-maximizer corollary, retain every extra
selection and lower-clock supplier in GAK section 10 and the corollary
following GAK51. That full existing chain already puts the same
selected $N$ above $\log N=8\cdot10^{46}$. Equation (GAD8) then
excludes $\log N\le3\cdot10^{47}$ for that same selected source.
This conditional consequence is not a bound for the least counterexample.

The parameter-specific
[rational program and results](https://github.com/the-omega-institute/trureturing-experiments/tree/fbe2ee18cadc21f30afc368a29a5604fdb44e8b5/experiments/robin-density-transport-3e47)
check the changed logarithm,
exponential prefix, density mass, support, normalization and complete
allowances. It does not certify the external analytic suppliers or the
full inference in Lean. For this fixed $H$ and order-nine law,
$V_*>0$ and the positive transport allowance grows with $\sqrt A$.
The original unbounded signed estimate and RH remain open.


## Complete higher-prime-power transport on an unlimited clock range

This application retains the GAK kernel, actual prime-power counting
functions and a single whole probability law. The inputs are the existing
GAK36–GAK39 pressure reserve and identity, and
[Dusart arXiv:1002.0442v1](https://arxiv.org/pdf/1002.0442v1),
Lemma 3.3 and Theorem 5.2. The square-root main term, convexity and
prime-counting estimates are published suppliers. The application below
pays the complete $k\ge2$ transport for this kernel; the first-power
prime transport and full smoothed signed response remain unpaid.
No additional all-integer Robin interval or global RH conclusion follows.

### The same whole law and complete counting function

Write $L=\log A$, $T_A=\sqrt A L$ and retain

$$
K(u)=\frac{1+\log u}{u^2\log^2u},\qquad
P_{\ge2}(t)=\psi(t)-\vartheta(t)
=\sum_{k\ge2}\vartheta(t^{1/k}).
$$

Let $\mu$ be any whole probability law satisfying
$99/100\le C\le101/100$ almost surely and $\mathbb EC=1$.
This includes the original GAK and GAD laws; no conditioning or
separate choice of law for different components is made. Define

$$
\begin{aligned}
J_c^{\ge2}(A)&=-\frac1c\int_A^\infty P_{\ge2}(cu)K(u)\,du,\\
\mathcal T_{\ge2}(A,\mu)&=J_1^{\ge2}(A)-\mathbb E J_C^{\ge2}(A),\\
m_\mu&=\mathbb EC^{-1/2},\qquad
V_\mu=\mathbb E(C-1)^2,\\
B(A)&=T_A\int_A^\infty\sqrt u K(u)\,du.
\end{aligned}
\tag{GPP1}
$$

The counting function retains every actual atom $p^k$, $k\ge2$, of
mass $\log p$, with $p^k\le t$ at endpoints. It is not replaced by a
density in the definition of either response.

### Uniform full-tail comparison

Put

$$
s=\frac{99A}{100}>(3594641)^2,\qquad
\epsilon(s)=\frac4{5\log^2s}+\frac{89}{50}s^{-1/6}.
$$

Dusart Lemma 3.3 gives
$0\le P_{\ge2}(t)-\vartheta(\sqrt t)<1.777745t^{1/3}$ for every
$t>0$. Theorem 5.2's row $(k,\eta_k,x_k)=(2,1/5,3594641)$ gives
$|\vartheta(y)-y|<y/(5\log^2y)$ for $y\ge3594641$.
Consequently, for $t\ge s$,

$$
|P_{\ge2}(t)-\sqrt t|
\le\sqrt t\left[\frac4{5\log^2t}+\frac{89}{50}t^{-1/6}\right]
\le\epsilon(s)\sqrt t.
\tag{GPP2}
$$

These are applications of the fixed primary statements; their underlying
finite computations and analytic proofs are external inputs.
Since every $cu\ge s$ for $u\ge A$, the same bound controls all scales
and the whole infinite tail. Positivity of $K$ and the integrable
square-root majorant justify exchanging expectation and integration.
Subtracting the two responses gives

$$
\mathcal T_{\ge2}
=\int_A^\infty
\left[\mathbb E\frac{P_{\ge2}(Cu)}C-P_{\ge2}(u)\right]K(u)\,du.
$$

The square-root main term is $(m_\mu-1)\sqrt u$; the error is at most
$(m_\mu+1)\epsilon(s)\sqrt u$. Thus

$$
\left|T_A\mathcal T_{\ge2}-B(A)(m_\mu-1)\right|
\le B(A)(m_\mu+1)\epsilon(s).
\tag{GPP3}
$$

Integration by parts, with the upper boundary zero, gives

$$
B(A)=2-T_A\int_A^\infty\frac{du}{u^{3/2}\log^2u},\qquad
2-\frac2L\le B(A)<2.
\tag{GPP4}
$$

For $f(c)=c^{-1/2}$, $0<f''(c)=3c^{-5/2}/4<1$ throughout the support.
Convexity and Taylor's bound, using the exact whole-law mean, imply

$$
0\le m_\mu-1\le\frac{V_\mu}{2}\le\frac1{20000}.
$$

If $A>e^{107}$, then $s>e^{106}$, so
$4/(5\log^2s)<1/14000$ and $(89/50)s^{-1/6}<1/70000$.
The second comparison follows from $e>2$ and $106/6>17$.
Hence $\epsilon(s)<3/35000<1/10000$ and $m_\mu+1<201/100$.
Combining these bounds with GPP3–GPP4 proves

$$
\left|T_A\mathcal T_{\ge2}(A,\mu)\right|
<2\left[\frac1{20000}+\frac{201}{100}\frac1{10000}\right]
=\frac{251}{500000}<\frac1{1000}
\qquad(A>e^{107}).
\tag{GPP5}
$$

This is uniform for all such real clocks, with no upper endpoint,
and allows the whole law to vary with $A$ within the stated conditions.

### Fixed-law sign and the original reserve consumer

For a fixed law, GPP3–GPP4 and $\epsilon(.99A)\to0$ give

$$
T_A\mathcal T_{\ge2}(A,\mu)\longrightarrow2(m_\mu-1).
\tag{GPP6}
$$

For a fixed nondegenerate mean-one law, strict convexity makes this
limit strictly positive. This is eventual positivity; GPP5 does not
assert positivity for every $A>e^{107}$, or for a varying law.
In particular, the negative local square atoms from GAK21 cannot
be recorded as extra reserve without their regular companions:
the complete higher-power contribution eventually has the opposite sign.

Let $J_c^\vartheta$ retain the GAK definition with
$\vartheta(cu)-cu$ in place of $\psi(cu)-cu$, and set
$\mathcal T_\vartheta=J_1^\vartheta-\mathbb E J_C^\vartheta$.
Then $J_c^\psi-J_c^\vartheta=J_c^{\ge2}$ exactly.
For each integer's own clock $A=\log n>e^{107}$, GAK39 therefore gives

$$
\Delta(n)=R(A)+d_A(n)-J_\mu^\psi(A)
-\mathcal T_\vartheta(A,\mu)-\mathcal T_{\ge2}(A,\mu).
$$

Retain every analytic premise and event convention of GAK36–GAK39.
The original unrestricted reserve bound GAK37 requires only its lower
clock, so it still applies on this unlimited range. Using GPP5 yields

$$
\begin{aligned}
T_A\Delta(n)>&\ Q_R-\frac1{1000}
+\frac{L}{(L+2)^3}+T_A d_A(n)\\
&-T_AJ_\mu^\psi(A)-T_A\mathcal T_\vartheta(A,\mu),\\
Q_R={}&\frac{67838284064811}{83593750000000}.
\end{aligned}
\tag{GPP7}
$$

The actual nonnegative defect of this same integer is retained; it is
not replaced by zero or by the defect of a selected optimizer.
GPP7 pays the complete higher-prime-power transport with an explicit
small budget on an unlimited range. It supplies no upper bound for
the remaining combined $J_\mu^\psi+\mathcal T_\vartheta$ at the same
source. The full signed response still includes all actual zeros,
real parts, coefficients and elementary terms. These ordinary
applications are not new prime-counting theorems or Lean-certified
results; the all-integer Robin inequality and RH remain open.


## A classical positive xi law pays the smoothed response on an unlimited range

This application directly reuses the distribution in
[Biane–Pitman–Yor, arXiv:math/9912170v1](https://arxiv.org/pdf/math/9912170v1),
§2.2, Proposition 1(i) and equation (20). The positive xi law and its
functional equation are classical results, not new constructions here.
The xi null-vector mechanism is also already used in the
[Weil comparison application](../Weil/frankliebseiringer2006hardy.md);
its vanishing at actual zeros is not a new result. The present consumer
is the original Robin response, whose integrability, broad-law transport
and reserve must be paid separately.
The other inputs are this note's all-scale remainder estimate GE2,
integrated coefficient bound GAK13, complete higher-power comparison
GPP2–GPP4, and same-integer identity and reserve GAK37–GAK39. Their
analytic premises, finite-verification inputs and endpoint conventions
are retained. No new zero computation or prime-counting theorem is used.

The law below has unbounded support. It does not satisfy GPP1's narrow
support hypothesis, so that section's uniform transport budget cannot
be applied to it. The estimates below instead pay both small scales and
the whole higher-power tail for this one law. They leave the original
first-prime transport unbounded and do not prove RH or the strict Robin
inequality for every integer greater than 5040.

### Reuse the published law with the consumer's mean normalization

Use the usual completed function
$\xi(s)=s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)/2$.
The cited proposition supplies a positive random variable $Y$ with

$$
\mathbb EY^s=2\xi(s)\qquad(s\in\mathbb C).
$$

In particular all real moments exist and $\mathbb EY=1$. Equation (20)
identifies $Y^{-1}$ with the size-biased law of $Y$.
Put

$$
m=2\xi(2)=\frac\pi3,\qquad C=\frac1{mY},\qquad
\mu=\operatorname{Law}(C).
$$

The published functional equation $\xi(s)=\xi(1-s)$ gives exactly

$$
\mathbb EC=1,\qquad
H_C(s):=\mathbb EC^{s-1}=2m^{1-s}\xi(s).
\tag{XLR1}
$$

Thus $H_C(\rho)=0$ for every actual nontrivial zero, with no assumption
about its real part. This uses a fixed positive probability law, not a
choice of signs or a deletion of a zero tail. The moments needed below
are

$$
\begin{aligned}
\mathbb EC^{-1}&=m,\\
M_4:=\mathbb EC^{-4}&=\frac{2\pi^2}{15}m^4<2,\\
1\le m_{1/2}:=\mathbb EC^{-1/2}
&=\sqrt m\,\mathbb E\sqrt Y\le\sqrt m<\frac{128}{125}.
\end{aligned}
\tag{XLR2}
$$

For the last line use convexity with $\mathbb EC=1$, then Cauchy–Schwarz
with $\mathbb EY=1$. The rational bounds follow from $\pi<22/7$:
$m<22/21$, $(22/21)^4<5/4$, $\pi^2<10$, and
$22/21<(128/125)^2$.

### Average the actual full response, including scales below the cutoff

Keep $L=\log A$, $T_A=\sqrt A L$, the GPP kernel $K$ and the actual
$J_c^\psi$ of GAK14. In this section $A>e^{107}$.
The expectation of its infinite integral is absolutely justified as
follows. At each $u\ge A$, divide the law into
$G_u=\{C\ge u^{-1/2}\}$ and its complement.
On $G_u$, $Cu\ge\sqrt u$ and the existing unconditional logarithmic PNT
input gives

$$
\frac{|\psi(Cu)-Cu|}{C}
\le\frac{4C_\psi u}{\log^2u}.
$$

On the complement, $\psi(t)\le t\log t$ for $t\ge1$, and $\psi(t)=0$
for $t<1$. Markov's inequality and XLR2 give

$$
\begin{aligned}
\mathbb P(C<u^{-1/2})&\le M_4u^{-2},\\
\mathbb E\left[\frac{\psi(Cu)}C;\ C<u^{-1/2}\right]
&\le\tfrac12M_4u^{-1}\log u<u^{-1}\log u,\\
\mathbb E\left[\frac{|\psi(Cu)-Cu|}C;\ C<u^{-1/2}\right]
&<u^{-1}(\log u+2).
\end{aligned}
\tag{XLR3}
$$

Both bounds become integrable after multiplication by $K(u)$.
Consequently $\mathbb E|J_C^\psi|<\infty$, and absolute Fubini permits
expectation inside its full infinite integral. No portion with $Cu<1$
is discarded.

The integrated zero series can likewise be averaged absolutely.
For $0<\beta<1$,
$\mathbb EC^{\beta-1}\le1+\mathbb EC^{-1}=1+m$.
Taking the endpoint limit in GAK13, and using $A^{\beta-1}\le1$, yields

$$
\sum_\rho m_\rho\mathbb E
 \left|C^{\rho-1}F_A(\rho)\right|
\le 2w(A)(1+m)\mathcal C_\zeta<\infty.
$$

Here $w(A)=(1+\log A)/\log^2 A$, and $\mathcal C_\zeta$ is the same
complete absolute zero weight used in GE1. This is an exchange of the
integrated coefficient series, not of the unsmoothed explicit formula.
XLR1 and GAK14–GAK15 therefore give

$$
Z_\mu(A)=\sum_\rho m_\rho H_C(\rho)F_A(\rho)=0,
\qquad J_\mu^\psi(A)=\mathbb Er_C(A).
$$

GE2 applies to every positive $c$, including $cA<1$. Averaging its
one-sided bound gives the actual signed estimate

$$
T_AJ_\mu^\psi(A)<\frac{5m}{\sqrt A}<\frac1{1000}
\qquad(A>e^{107}).
\tag{XLR4}
$$

Integrability of $r_C=J_C-Z_C$ follows from the two preceding absolute
bounds. XLR4 is an upper bound, not an absolute estimate. All pole,
constant and trivial-zero corrections are still included in $r_C$.

### Pay the complete higher-prime-power transport for this same law

Use the actual $P_{\ge2}=\psi-\vartheta$ and
$\mathcal T_{\ge2}$ of GPP1, now with this unbounded $\mu$.
On $G_u$, use GPP2 with $s=\sqrt A$; it applies because $Cu\ge\sqrt u$.
On its complement, XLR3 also bounds $P_{\ge2}(Cu)/C$, and

$$
\sqrt u\,\mathbb E[C^{-1/2};\ C<u^{-1/2}]
\le M_4u^{-5/4}<2u^{-5/4}.
$$

The good-scale square-root comparison, these two small-scale tails,
and GPP2 for $P_{\ge2}(u)$ give

$$
\begin{split}
\left|\mathbb E\frac{P_{\ge2}(Cu)}C-P_{\ge2}(u)
 -(m_{1/2}-1)\sqrt u\right|
\le{}&(m_{1/2}+1)\epsilon(\sqrt A)\sqrt u\\
&+u^{-1}\log u+2u^{-5/4}.
\end{split}
\tag{XLR5}
$$

These same bounds justify the nonnegative Tonelli exchange and its
finiteness. With the unchanged $B(A)$ of GPP4, integration gives

$$
\begin{split}
\left|T_A\mathcal T_{\ge2}
 -B(A)(m_{1/2}-1)\right|
\le{}&B(A)(m_{1/2}+1)\epsilon(\sqrt A)\\
&+L A^{-3/2}+2A^{-7/4}.
\end{split}
\tag{XLR6}
$$

Indeed $T_A\int_A^\infty u^{-1}\log u K(u)du\le L A^{-3/2}$,
and $T_A\int_A^\infty2u^{-5/4}K(u)du<2A^{-7/4}$, by
$(1+\log u)/\log u\le2$ and $\log u\ge L$.

For the constants, $\sqrt A>e^{48}$ and $e>8/3$ give $e^8>2500$ and

$$
\epsilon(\sqrt A)
<\frac1{2500}+\frac{89}{125000}<\frac1{500}.
$$

Also $L A^{-3/2}+2A^{-7/4}<1/1000$: both terms decrease with $L>107$,
and $e^L>2^L$ with $L<e^{L/2}$ bounds their sum by
$e^{-L}+2e^{-7L/4}<3\cdot2^{-107}<1/1000$.
Using GPP4's $B(A)<2$ and XLR2 now gives

$$
\left|T_A\mathcal T_{\ge2}(A,\mu)\right|
<\frac6{125}+\frac{506}{62500}+\frac1{1000}
<\frac3{50}.
\tag{XLR7}
$$

This covers all actual powers $k\ge2$, their endpoints, the entire
positive law and the whole infinite integral. Together with XLR4 it pays
one combined actual quantity on the unlimited range:

$$
T_A\bigl[J_\mu^\psi(A)+\mathcal T_{\ge2}(A,\mu)\bigr]
<\frac{61}{1000}\qquad(A>e^{107}).
\tag{XLR8}
$$

### Consume the bound at the original integer and state the unpaid term

Define $\mathcal T_\vartheta=J_1^\vartheta-\mathbb EJ_C^\vartheta$
using this same $\mu$. The preceding integrability bounds also pay this
expectation. For each integer's own clock $A=\log n>e^{107}$, the
unchanged exact GAK39 identity reads

$$
\Delta(n)=R(A)+d_A(n)-J_\mu^\psi(A)
 -\mathcal T_\vartheta(A,\mu)-\mathcal T_{\ge2}(A,\mu).
$$

Combining XLR8 with the original reserve GAK37 gives

$$
\begin{aligned}
T_A\Delta(n)>{}&Q_R-\frac{61}{1000}
 +\frac{L}{(L+2)^3}+T_A d_A(n)-T_A\mathcal T_\vartheta(A,\mu)\\
>{}&\frac34+\frac{L}{(L+2)^3}
 +T_A d_A(n)-T_A\mathcal T_\vartheta(A,\mu),
\end{aligned}
\tag{XLR9}
$$

where the last strict inequality uses the existing exact
$Q_R=67838284064811/83593750000000>811/1000$.
The nonnegative defect belongs to this same integer and the original
unrestricted pressure; no optimizer substitution is made.

XLR8 is an estimate for the actual combined smoothed response and
higher-power transport. XLR9 has only the first-prime transport left
unbounded. No sufficient upper bound for that term is established here.
Indeed $J_\mu^\psi+\mathcal T_\vartheta+\mathcal T_{\ge2}=J_1^\psi$
exactly: annihilating the smoothed zero series does not annihilate the
unsmoothed arithmetic error. The first-prime transport keeps the
remaining oscillation, and its wide-scale cancellations have not been
bounded at this reserve. This application is paper mathematics using
published and existing inputs, with no Lean certification or literature
priority claim. RH and strict Robin for every integer $n>5040$ remain
unproved.

## A full-response budget for logarithmically growing signed xi clocks

This application reuses XLR1's published Biane–Pitman–Yor law, the
integrated explicit formula GAK10–GAK16, GPP2–GPP4 and the original
same-integer account GAK37–GAK39. It is a repo-derived application controlling a changing family of
signed clocks; the fixed positive-law allowance XLR8 is not applied
to that family. The interpolation algebra is standard, and no
literature priority or Lean certification is claimed.

The additional classical inputs are
[Johnston–Yang, arXiv:2204.01980v2](https://arxiv.org/pdf/2204.01980v2),
Lemma 2.7, already recorded as
[PK (Z1)](../Analytic/polak2026finiterobinca.md#the-additional-published-input),
and [DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9) and
[25.2.10](https://dlmf.nist.gov/25.2.E10).
The latter formula with $n=1$ gives
$\zeta(\sigma+it)=O((1+|t|)^3)$ uniformly for $0\le\sigma\le1/2$:
the periodic-Bernoulli integral is uniformly absolutely bounded
there, and its coefficient is a cubic polynomial. Vertical-strip
Stirling and the entire continuation of $\xi$ consequently give
rapid vertical decay for XLR1's
$h(s)=2m^{1-s}\xi(s)$ on this strip. These are published inputs and
their parameter correspondence, rather than new zeta estimates.

### One signed family and a common degree cap

Put $m=\pi/3$ and retain the whole law $\mu$ of XLR1, with
$h(s)=\int c^{s-1}\,d\mu(c)$. For an integer $k\ge1$ define

$$
Q(z)=(1-z)(1-z/m),\qquad
P_k(z)=1-Q(z)^k=\sum_{j=1}^{2k}p_{k,j}z^j,
$$

$$
\nu_k=\sum_{j=1}^{2k}p_{k,j}\mu^{*j},\qquad
H_k(s)=\int c^{s-1}\,d\nu_k(c)=P_k(h(s)).
\tag{GPC1}
$$

Here convolution is multiplicative. The signed mass, first moment
and inverse first moment are all one, since
$h(0)=m$ and $h(1)=h(2)=1$. Also $H_k(\rho)=0$ at every actual
nontrivial zero, with no critical-line assumption. The usual
polynomial interpolation gives vanishing derivatives of $H_k-1$
through order $k-1$ at $s=0,1$. These algebraic identities provide
neither positivity of $\nu_k$ nor Jensen's inequality.

For real $t$ let $b_t=\int c^t\,d\mu(c)$ and
$R_t=(1+b_t)(1+b_t/m)$. All these moments are finite. The
coefficient absolute-value envelope gives

$$
M_t(k):=\int c^t\,d|\nu_k|(c)\le1+R_t^k.
\tag{GPC2}
$$

Fix $\eta=1/24$. Choose one $\kappa>0$ so that
$\kappa\log R_t\le\eta$ for every
$t\in\{0,-1,-4,-2/3,1/3\}$. For $1\le k\le\kappa\log A$,

$$
M_t(k)\le2A^\eta
\qquad(t\in\{0,-1,-4,-2/3,1/3\},\ A\ge1).
\tag{GPC3}
$$

The same $\kappa$ is decreased below to control the complete zero
spectrum. No bounded-total-variation or fixed-degree limit is assumed.

Write $\rho=\beta+i\gamma$, $\delta_\rho=1-\beta$. The classical
zero-free region, together with the existing finite verification for
$|\gamma|<2$, gives

$$
\delta_\rho\ge\frac{a_0}{\log(2+|\gamma|)},\qquad
a_0=\min\{1/5.5666305,\ (\log2)/2\}>0.
$$

Only this finite head uses verified criticality. Rapid vertical
decay supplies $B_0<\infty$ with
$|h(\rho/2)|\le B_0/(1+|\gamma|)^2$. Since

$$
\log_+|Q(z)|
\le(1+1/m)|z|,
$$

there is a fixed $B>0$ with
$\log_+|Q(h(\rho/2))|\le(B/a_0)\delta_\rho$.
Reduce $\kappa$ so that $\kappa B/a_0\le1/4$. Then, simultaneously
for all actual zeros and all $k\le\kappa\log A$,

$$
A^{\beta/2-1/2}|H_k(\rho/2)|
\le2\exp\!\left(-\frac{\delta_\rho\log A}{4}\right).
\tag{GPC4}
$$

Indeed $|H_k|\le1+|Q(h)|^k\le2A^{\delta_\rho/4}$.
This bounds filter growth and the zero-free gap on the same zero.
No numerical value of $\kappa$ or common starting point is supplied.

### Uniform full smoothed response

Keep $L=\log A$, $T_A=\sqrt A L$, and the unchanged $K,F_A,J_c^\psi$.
In particular $J_1^\psi=-I_\psi$; the integrated zero coefficient in
$J_c^\psi$ has the positive sign $c^{\rho-1}F_A(\rho)$.
The following assertions hold uniformly through the common degree cap:

$$
\begin{aligned}
\sup_{1\le k\le\kappa L}T_A|J_{\nu_k}^\psi(A)|&\longrightarrow0,\\
\sup_{1\le k\le\kappa L}
\left|T_A\mathcal T_{\ge2}(A,\nu_k)
 -B(A)(H_k(1/2)-1)\right|&\longrightarrow0.
\end{aligned}
\tag{GPC5}
$$

Here $J_\nu^\psi=\int J_c^\psi\,d\nu(c)$ and the actual transport is

$$
\mathcal T_{\ge2}(A,\nu)
=\int_A^\infty
 \left[\int\frac{P_{\ge2}(cu)}c\,d\nu(c)-P_{\ge2}(u)\right]K(u)\,du.
$$

All powers, all positive clocks and the entire infinite tail remain.
We establish absolute integrability against $|\nu_k|$ before using
any signed cancellation.

Put $E_A=\{c<A^{-1/2}\}$ and abbreviate $M_t=M_t(k)$. The absolute
measure satisfies

$$
\begin{aligned}
|\nu_k|(E_A)&\le A^{-2}M_{-4},\\
\int_{E_A}c^{-1}\,d|\nu_k|&\le A^{-3/2}M_{-4},\\
\int_{E_A}c^{-1/2}\,d|\nu_k|&\le A^{-7/4}M_{-4}.
\end{aligned}
\tag{GPC6}
$$

For absolute integrability of $J_\nu^\psi$, apply XLR3 to
$|\nu_k|$, splitting at $c=u^{-1/2}$ for each $u$.
Above that cut the logarithmic PNT gives
$O(M_0u/\log^2u)$; below it the trivial
$\psi(t)\le t\log_+t$ gives $O(M_{-4}u^{-1}(1+\log u))$.
Both are $K$-integrable. For the actual contribution of the fixed
$E_A$, split again at $u^{-1/2}$. The upper part costs
$O(M_{-4}A^{-3/2}/L)$ after multiplication by $T_A$, and the lower
part costs $O(M_{-4}L A^{-3/2})$.

On $E_A^c$ one has $cu\ge\sqrt A$. The finite-endpoint integrated
explicit formula and GAK13 therefore apply. The zero count makes
$\mathcal S_1=\sum_\rho m_\rho/(|\rho||1-\rho|)$ finite.
Replacing the complementary Mellin integral by the full
$H_k(\rho)=0$ leaves only $E_A$; GPC6 bounds its normalized cost
by $O(M_{-4}\mathcal S_1/A)$. The constant and trivial-zero terms
have absolute normalized cost $O(M_{-1}/\sqrt A)$:
their integral is $O(M_{-1}/(AL))$, using
$|\log(1-(cu)^{-2})|\le2(cu)^{-2}$ on the good set.

All constants here are independent of $k$. GPC3 makes each allowance
vanish, proving the first line of GPC5. This uses absolute elementary
remainders, not a one-sided positive-law estimate for signed $\nu_k$.

### The square term with every zero retained

Define

$$
S_\nu(A)=\int_A^\infty\int
 \frac{\psi(\sqrt{cu})-\sqrt{cu}}c\,d\nu(c)K(u)\,du.
$$

On $E_A$, $c<1$ and the absolute integrand before multiplication
by $K$ is at most
$\sqrt u\,c^{-1/2}(1+\log u)$. GPC6 bounds its normalized tail
by $O(M_{-4}L^2 A^{-7/4})$.

For the whole square integral,
$c^{-1/2}(1+\log_+c)\le C(1+c^{-1})$ supplies an absolute
large-clock majorant; its small-clock part is covered by GPC6.
On $E_A^c$, $\sqrt{cu}\ge A^{1/4}$. The same finite-endpoint
explicit-formula argument, now with $s=\rho/2$, has zero coefficient

$$
-\frac12c^{\rho/2-1}F_A(\rho/2).
$$

The factor $1/2$ follows from the original $1/\rho$ coefficient;
it is not absorbed into the zero multiplicity. GAK13 gives a
summable finite-endpoint majorant. The constant and trivial-zero
terms again cost $O(M_{-1}/\sqrt A)$ after normalization, using
$|\log(1-(cu)^{-1})|\le2/(cu)$.
Completing the complementary Mellin moment to $H_k(\rho/2)$ costs
$O(M_{-4}A^{-3/2}\mathcal S_2)$, where

$$
\mathcal S_2=\sum_\rho\frac{m_\rho}{|\rho||1-\rho/2|}<\infty.
$$

For the complete full-law sum, GAK13 and GPC4 give the common
normalized majorant

$$
C\sum_\rho
 \frac{m_\rho}{|\rho||1-\rho/2|}
 \exp\!\left(-\frac{\delta_\rho\log A}{4}\right)
 \longrightarrow0.
\tag{GPC7}
$$

Both ordinate signs and actual multiplicities occur in these sums.
The convergence follows from the summable $\mathcal S_2$ majorant
and $\delta_\rho>0$ at each actual zero; GPC4 makes it independent
of the changing $k$. This proves
$\sup_{k\le\kappa L}T_A|S_{\nu_k}(A)|\to0$.
It does not exchange an unsmoothed zero series absolutely.

### Every remaining prime power

For every $t>0$ there is the exact finite-sum identity

$$
\begin{aligned}
P_{\ge2}(t)&=\psi(\sqrt t)+R_3(t),\\
R_3(t)&=\sum_{j\ge3}\vartheta(t^{1/j})-P_{\ge2}(\sqrt t).
\end{aligned}
$$

The global Chebyshev bound and the number of admissible exponents
give $|R_3(t)|\le C t^{1/3}(1+\log_+t)^2$. Below the first prime
power both sides vanish; no small-$t$ singularity is introduced.
For $u\ge A\ge e$,

$$
\int\frac{|R_3(cu)|}{c}\,d|\nu_k|(c)
\le C u^{1/3}(1+\log u)^2(M_{-2/3}+M_{1/3}).
$$

Here $(1+\log_+(cu))^2\le C(1+\log u)^2(1+c)$.
The full normalized $K$-tail is
$O(A^{\eta-1/6}L^2)\to0$, uniformly in $k$.
This also supplies absolute Fubini for the complete remainder.
Separately GPP2 pays the reference
$P_{\ge2}(u)-\sqrt u=o(\sqrt u)$ on the entire $u\ge A$ tail,
with no growing total-variation multiplier on that reference.
The square main term is
$\sqrt u\int c^{-1/2}\,d\nu_k=\sqrt u\,H_k(1/2)$.
Combining these facts proves the second line of GPC5.

### The original integer's account and the unpaid estimate

XLR2 gives $b=h(1/2)\in[1,\sqrt m]$ and
$-1<Q(b)\le0$. For even $k$,
$H_k(1/2)-1=-Q(b)^k\le0$. Thus GPC5 supplies one
$\epsilon_*(A)\to0$, independent of even $k$ in the cap, such that

$$
T_A[J_{\nu_k}^\psi(A)+\mathcal T_{\ge2}(A,\nu_k)]
\le\epsilon_*(A).
\tag{GPC8}
$$

For any integer-valued $k(A)\to\infty$ within the cap, this combined
expression tends to zero in absolute value; parity is unnecessary
for that limit. No convergence to a positive law or to $\delta_1$
is asserted.

Use the centered response
$J_c^\vartheta=-c^{-1}\int_A^\infty[\vartheta(cu)-cu]K(u)\,du$
and $\mathcal T_\vartheta=J_1^\vartheta-\int J_c^\vartheta\,d\nu_k$.
Their integrability follows from the preceding $\psi$ and
proper-power bounds. For each integer's own $A=\log n>e^{107}$,
mass one preserves the exact account

$$
\Delta(n)=R(A)+d_A(n)-J_{\nu_k}^\psi
 -\mathcal T_\vartheta(A,\nu_k)-\mathcal T_{\ge2}(A,\nu_k).
$$

GAK37 and GPC8 therefore imply, eventually and uniformly for even
$2\le k\le\kappa L$,

$$
T_A\Delta(n)>
 Q_R+\frac{L}{(L+2)^3}+T_A d_A(n)
 -T_A\mathcal T_\vartheta(A,\nu_k)-\epsilon_*(A).
\tag{GPC9}
$$

The nonnegative defect and unrestricted pressure still belong to
this same integer. GPC5–GPC9 admit clocks with an increasing number
of exact logarithmic moment cancellations while paying the full
smoothed and higher-power response. They do not bound the
remaining first-prime transport against that defect. In particular,
$J_{\nu_k}^\psi+\mathcal T_\vartheta+\mathcal T_{\ge2}=J_1^\psi$
still holds exactly. No mean-one price normalization, signed Jensen
inequality, new finite verification interval or RH/Robin proof follows.

## Exact nonlinear price calibration with adjacent growing xi clocks

This repo-derived application reuses GPC1–GPC9 and XLR1, including
the published BPY law, all real moments and the complete growing-family
response budget. Adjacent-error extrapolation, polynomial
interpolation and Gamma integrals are standard tools. The additional
calculation concerns their full-law, moving-degree price error and
the actual small-clock cutoff. No literature priority, Lean
certification or signed Jensen inequality is claimed.

### The same source and the actual price observation

Retain $m=\pi/3$, $h$, $Q$, $\nu_j$ and $H_j$ of GPC1.
Write $L=\log A$, $T_A=\sqrt A L$, and choose

$$
k=k(A)=\lfloor L^{1/3}\rfloor,\qquad
\chi_A(c)=\max(c,e/A),\qquad
\lambda(x)=\frac1{x\log x}\quad(x\ge e).
$$

The normalized price observation is

$$
y_A(c)=\frac{\lambda(A\chi_A(c))}{\lambda(A)}
 =\frac{AL}{A\chi_A(c)\log(A\chi_A(c))}.
\tag{APC1}
$$

For all $c>0$, $y_A(c)\le L/c$. Thus its integral against each
$|\nu_j|$ is finite. Define

$$
Y_{A,j}=\int y_A(c)\,d\nu_j(c),\qquad
E_{A,j}=1-Y_{A,j}\qquad(j=k,k+1).
$$

The original source and its image under $\chi_A$ remain distinct.
The effect of this cutoff on the prime responses is estimated below.

All real moments justify differentiating $h$ near zero. The elementary
$\log c\le c-1$ gives
$h'(0)=\int c^{-1}\log c\,d\mu\le1-m<0$. Consequently

$$
\alpha=-\frac{m-1}{m}h'(0)>0,\qquad
g(u)=Q(h(-u))=\alpha u\exp(O(u)).
\tag{APC2}
$$

Here $Q'(m)=(m-1)/m$. Choose a fixed $u_0\in(0,1)$ and $D<\infty$
so that $g(u)>0$ and
$|\log(g(u)/(\alpha u))|\le Du$ for $0<u\le u_0$.
Neither constant depends on $A$ or $j$.

### The complete price error from a finite Laplace interval

Use only the truncated function

$$
f_A(c)=Lc^{-1}\int_0^{u_0}e^{-u(L+\log c)}\,du.
$$

This integral also defines the value when $L+\log c=0$.
No full half-line Laplace integral is interchanged with the clock law.
Put $\tau=e/A$. For $c\ge\tau$,

$$
|y_A(c)-f_A(c)|
 =y_A(c)e^{-u_0(L+\log c)}
 \le L A^{-u_0}c^{-1-u_0}.
$$

For $c<\tau$,

$$
|f_A(c)|\le Lu_0[c^{-1}+A^{-u_0}c^{-1-u_0}],
\qquad y_A(c)=AL/e.
$$

Using GPC2's absolute moments
$M_t(j)=\int c^t\,d|\nu_j|$ and
$\int_{c<\tau}c^{-q}\,d|\nu_j|\le\tau^{4-q}M_{-4}(j)$
for $q=0,1,1+u_0$ proves the whole-law bound

$$
\left|Y_{A,j}-\int f_A\,d\nu_j\right|
 \le L A^{-u_0}M_{-1-u_0}(j)
       +C L A^{-3}M_{-4}(j).
\tag{APC3}
$$

All $c>0$, including $Ac\le1$, occur in this estimate.
Absolute Fubini on $[0,u_0]$ follows from
$M_{-1}(j)+M_{-1-u_0}(j)<\infty$. Therefore

$$
\int f_A\,d\nu_j
 =L\int_0^{u_0}e^{-Lu}H_j(-u)\,du
 =1-e^{-u_0L}-L\int_0^{u_0}e^{-Lu}g(u)^j\,du.
$$

For $j=k,k+1$, GPC2 gives $M_t(j)=\exp(O(j))$ at every fixed $t$.
Since $j=O(L^{1/3})$, APC3 implies, for one fixed $c_0>0$,

$$
E_{A,j}=I_{L,j}+O(e^{-c_0L}),\qquad
I_{L,j}=L\int_0^{u_0}e^{-Lu}g(u)^j\,du.
\tag{APC4}
$$

The cutoff and truncation have thus been controlled before taking a
relative asymptotic.

### Moving order and the separated adjacent errors

For $L>2Dj$, APC2 bounds $I_{L,j}$ between

$$
\alpha^jL\int_0^{u_0}e^{-(L+Dj)u}u^j\,du
\quad\hbox{and}\quad
\alpha^jL\int_0^{u_0}e^{-(L-Dj)u}u^j\,du.
$$

The corresponding full Gamma integrals are
$\alpha^jL j!/(L\pm Dj)^{j+1}$. The fraction beyond $u_0$ is at most
$(j+1)/[(L\pm Dj)u_0]$, by the first moment of the normalized positive
Gamma integral. As $j=k,k+1$, one has $j^2/L\to0$, so

$$
I_{L,j}=\frac{\alpha^j j!}{L^j}
       \left(1+O\!\left(\frac{j^2}{L}\right)\right).
$$

Moreover $\log(\alpha^j j!L^{-j})=-O(j\log L)=o(L)$.
The absolute error in APC4 is therefore negligible relative to this
main term. This proves the full-law, moving-order formula

$$
E_{A,j}=\frac{\alpha^j j!}{L^j}
       \left(1+O\!\left(\frac{j^2}{L}\right)\right),
\qquad j=k,k+1.
\tag{APC5}
$$

In particular the two errors are positive eventually, and their
actual ratio satisfies

$$
r_A=\frac{E_{A,k+1}}{E_{A,k}}
 =\frac{\alpha(k+1)}L
       \left(1+O\!\left(\frac{k^2}{L}\right)\right)\longrightarrow0.
\tag{APC6}
$$

Thus $0<r_A<1/2$ eventually. No numerical common starting point or
numerical error constant is supplied; no fixed-order expansion has
been applied to a changing order.

### Exact calibration and the source properties it preserves

Apply the standard adjacent-error extrapolation to the actual errors:

$$
\sigma_A=\frac{\nu_{k+1}-r_A\nu_k}{1-r_A},
\qquad
\bar\sigma_A=(\chi_A)_\#\sigma_A.
\tag{APC7}
$$

The first is the full source measure; the second is the actual
clamped clock measure. By definition of $r_A$,

$$
\int y_A\,d\sigma_A
 =\frac{Y_{A,k+1}-r_AY_{A,k}}{1-r_A}=1.
$$

For $\sigma_A$, mass, first clock moment and inverse clock moment
are all one. Its Mellin transform vanishes at every actual xi zero.
At $s=0,1$, all derivatives of $H_{\sigma_A}-1$ through order $k-1$
vanish, since both adjacent transforms have these properties.
For each fixed real $t$,

$$
N_t(A):=\int c^t\,d|\sigma_A|(c)
 \le\frac{M_t(k+1)+r_AM_t(k)}{1-r_A}
 =\exp(O(k))=A^{o(1)}.
\tag{APC8}
$$

These exact Mellin, jet and clock-moment properties refer to
$\sigma_A$ before the cutoff. They are not asserted for
$\bar\sigma_A$. The latter has mass one and exact nonlinear price
mean $\int\lambda(Ac)\,d\bar\sigma_A(c)=\lambda(A)$.
Neither measure is asserted positive or ordered by Jensen's inequality.

### Pay the complete original response after the cutoff

Since $k,k+1\to\infty$ and eventually $k+1\le\kappa L$,
GPC5 and its limit along growing orders give

$$
T_A|J_{\sigma_A}^\psi(A)|
 +T_A|\mathcal T_{\ge2}(A,\sigma_A)|\longrightarrow0.
$$

This uses linearity on mass-one signed measures and bounded mixing
coefficients. In particular
$H_j(1/2)-1=-Q(h(1/2))^j\to0$; no uniform absolute limit for all
fixed orders is assumed.

It remains to pay the actual cutoff, which need not preserve exact
Mellin zeros. Since $\tau=e/A<A^{-1/2}$ eventually, GPC's absolute
small-clock argument gives

$$
T_A\int_{c<\tau}|J_c^\psi(A)|\,d|\sigma_A|(c)
 =O(N_{-4}(A)L A^{-3/2}).
$$

Also $J_\tau^\psi(A)=O(L)$. On $A\le u\le A^2$, the trivial
$\psi(t)\le t\log_+t$ bounds its integrand before $K$ by $u(L+2)$,
and $\int_A^{A^2}uK(u)\,du=O(1)$. On $u\ge A^2$,
$\tau u\ge\sqrt u$, so the existing logarithmic PNT gives an
integrable $O(u/\log^2u)$ bound. Finally
$|\sigma_A|(\{c<\tau\})\le\tau^4N_{-4}(A)$. Hence

$$
T_A|J_{\bar\sigma_A}^\psi-J_{\sigma_A}^\psi|
 \le C N_{-4}(A)
       [L A^{-3/2}+L^2 A^{-7/2}]\longrightarrow0.
$$

GPP2 and its bounded initial interval give
$P_{\ge2}(t)\le C\sqrt t$ for all $t>0$. Both laws have mass one,
so the reference $P_{\ge2}(u)$ cancels in their transport difference.
The complete small-clock and cutoff terms consequently cost

$$
\begin{aligned}
T_A|\mathcal T_{\ge2}(A,\bar\sigma_A)
       -\mathcal T_{\ge2}(A,\sigma_A)|
&\le CB(A)\left[
 \int_{c<\tau}c^{-1/2}\,d|\sigma_A|
 +\tau^{-1/2}|\sigma_A|(\{c<\tau\})\right]\\
&\le C N_{-4}(A)A^{-7/2}\longrightarrow0.
\end{aligned}
$$

The error estimates include every original clock value, every prime
power and the entire $u\ge A$ tail. They also prove absolute integrability
of the modified responses. Thus the actual price-calibrated clock
law has the full component budget

$$
T_A|J_{\bar\sigma_A}^\psi(A)|
 +T_A|\mathcal T_{\ge2}(A,\bar\sigma_A)|\longrightarrow0.
\tag{APC9}
$$

No one-sided positive-law constant has been transferred to a signed law.

### Original pressure and the same integer

For each original integer's $A=\log n$, put
$\lambda_A=1/(AL)$ and
$\Lambda_A(c)=\lambda(A\chi_A(c))$.
The same source satisfies $\int\Lambda_A\,d\sigma_A=\lambda_A$
exactly. The actual unrestricted pressure is integrable:
its existing asymptotic
$M(\lambda(x))=\gamma+\log\log x-1/\log x+O(1/\log^2x)$,
together with the cutoff $x\ge e$, bounds it by $C_A(1+c)$ on this
source; APC8 supplies the required absolute moment.

Keep $d_\lambda(n)=M(\lambda)-W(n)+\lambda\log n$ and define
$G_A=\int M(\Lambda_A(c))\,d\sigma_A-M(\lambda_A)$.
Exact calibration gives the same-integer identity

$$
\int d_{\Lambda_A(c)}(n)\,d\sigma_A(c)=d_A(n)+G_A.
\tag{APC10}
$$

The nonnegativity of each individual defect does not supply a sign
for this signed integral or for $G_A$.

Define $\mathcal T_\vartheta$ using $\bar\sigma_A$ and the centered
response of GPC9. APC9 pays its integrability and leaves the original
exact account intact:

$$
\Delta(n)=R(A)+d_A(n)-J_{\bar\sigma_A}^\psi
 -\mathcal T_\vartheta(A,\bar\sigma_A)
 -\mathcal T_{\ge2}(A,\bar\sigma_A).
$$

The unchanged GAK37 reserve therefore gives, eventually, one
$\epsilon(A)\to0$ such that

$$
T_A\Delta(n)>
 Q_R+\frac{L}{(L+2)^3}+T_A d_A(n)
 -T_A\mathcal T_\vartheta(A,\bar\sigma_A)-\epsilon(A).
\tag{APC11}
$$

This instantiates the original account with an explicitly calibrated
price family, unbounded source moment-cancellation order and paid
cutoff error. The remaining comparison between first-prime transport
and this same integer's defect is unproved. Generic fixed-family
Jensen obstructions are not removed by the construction; no pressure
sign, new finite verification interval or RH/Robin proof follows.

## Actual pressure order of the calibrated growing family

Retain exactly the source, cutoff, degree and calibration of APC1–APC11.
The following repo-derived application estimates their actual unrestricted
pressure correction $G_A$. It reuses the BPY law, the complete pressure
identity, the published PNT input and standard Laplace/Gamma asymptotics.
The earlier fixed-family signed Jensen tests do not supply this
moving-degree relative estimate. No literature priority, numerical common
starting threshold, Lean certification or RH/Robin proof is claimed.

### The complete actual-pressure remainder

Put

$$
B(x)=\gamma+\log\log x-\frac1{\log x}\qquad(x\ge e).
$$

GAK29 and GAK38 already give
$M(\lambda(x))=B(x)-I_\psi(x)-R(x)$, with the unrestricted pressure
and every prime power retained. Reuse
[Johnston–Yang, arXiv:2204.01980v2](https://arxiv.org/pdf/2204.01980v2),
Theorem 1.1, equation (1.3), as recorded in the
[existing supplier note](../Weil/johnstonyang2022pnt.md):

$$
|\psi(u)-u|\le9.39u(\log u)^{1.515}
 e^{-0.8274\sqrt{\log u}}\qquad(u\ge2).
$$

After $v=\log u$, its contribution to $|I_\psi(x)|$ is bounded by a
constant times
$\int_{\log x}^\infty(1+v)v^{-0.485}e^{-0.8274\sqrt v}\,dv$.
Absorbing the polynomial into a smaller exponential, and using the
existing whole-reserve upper $R(x)=O(x^{-1/2})$, gives fixed $C,b>0$ with

$$
|M(\lambda(x))-B(x)|\le C e^{-b\sqrt{\log x}}
\qquad(x\ \text{sufficiently large}).
\tag{ACP1}
$$

This is an application of the published theorem, without rerunning its
computations or independently certifying its whole proof. The difference
on the left is continuous, bounded on compact subsets of $[e,\infty)$,
and tends to zero, so it is globally bounded there.

For $j=k,k+1$, split the whole source at $c=A^{-1/2}$. Above this cut,
$A\chi_A(c)\ge\sqrt A$; below it use the global bound and
$|\nu_j|(c<A^{-1/2})\le A^{-2}M_{-4}(j)$. GPC2 consequently gives

$$
\int|M(\lambda(A\chi_A(c)))-B(A\chi_A(c))|\,d|\nu_j|(c)
\le e^{-b_1\sqrt L+O(j)}+e^{-2L+O(j)}
\tag{ACP2}
$$

for a fixed $b_1>0$. Arbitrarily small and clamped clocks are included.
The same allowance applies to the value at $x=A$ and to the bounded
adjacent mixture.

### The other interpolation node and the finite Laplace calculation

Since $\mu$ is a probability law with $\int c\,d\mu=1$, the strict
inequality $\log c<c-1$ away from $c=1$ gives $h'(1)<0$.
The law is nontrivial because $h(0)=m>1$. Define

$$
\beta_1=-\frac{m-1}{m}h'(1)>0,\qquad
v(u)=Q(h(1-u))=-\beta_1u\exp(O(u)).
\tag{ACP3}
$$

Here $Q'(1)=-(m-1)/m$; $\beta_1$ belongs to node $1$, whereas
APC2's positive $\alpha$ belongs to node $0$. All real moments justify
the derivatives. Choose fixed $u_0\in(0,1)$ and $D<\infty$ so that
$v(u)<0$ and $|\log[-v(u)/(\beta_1u)]|\le Du$ for $0<u\le u_0$.

For one clamped clock put $z=\log(A\chi_A(c))\ge1$. The standard
logarithm and reciprocal-logarithm formula is

$$
B(A\chi_A(c))-B(A)
=\int_0^\infty(e^{-Lu}-e^{-zu})(1/u+1)\,du.
$$

Only $[0,u_0]$ is interchanged with the signed source. The absolute
remaining tail is at most $C(e^{-u_0L}+e^{-u_0z})$, whose source
integral is at most $CA^{-u_0}[M_0(j)+M_{-u_0}(j)]$.
Near zero, absolute Fubini uses the cancelling difference and

$$
\frac{|1-\chi_A(c)^{-u}|}{u}
\le|\log\chi_A(c)|[1+\chi_A(c)^{-u_0}].
$$

Its absolute integral is finite by neighboring fixed real moments;
clamping a clock below $e/A<1$ decreases its absolute logarithm.
No two divergent $1/u$ integrals are separated.

Write $\tau=e/A$. For $c<\tau$ and $0<u\le u_0$,

$$
\frac{|\tau^{-u}-c^{-u}|}{u}
\le\log(\tau/c)c^{-u_0}
\le C\tau^{4-u_0}c^{-4}.
$$

The last bound follows from
$\sup_{0<t<1}t^{4-u_0}\log(1/t)<\infty$. It pays the complete
replacement of the truncated clamped Mellin factor by $H_j(1-u)$.
Thus, for some fixed $c_0>0$,

$$
S_{A,j}:=\int[B(A\chi_A(c))-B(A)]\,d\nu_j(c)
=\int_0^{u_0}e^{-Lu}v(u)^j(1/u+1)\,du
 +O(e^{-c_0L+O(j)}).
\tag{ACP4}
$$

### Moving degree, actual pressure and exact calibration

The integral in ACP4 has sign $(-1)^j$. Its magnitude lies between

$$
\beta_1^j\int_0^{u_0}e^{-(L+Dj)u}(u^{j-1}+u^j)\,du
$$

and the same expression with $L-Dj$. The full Gamma integrals have
leading value $\beta_1^j(j-1)!/L^j$. The $u^j$ term and the removed
Gamma tails cost $O(j/L)$ relatively; changing $L$ to $L\pm Dj$
costs $O(j^2/L)$. Since $j=k,k+1$ and $k=\lfloor L^{1/3}\rfloor$,

$$
S_{A,j}=\frac{(-\beta_1)^j(j-1)!}{L^j}
 \left(1+O\!\left(\frac{j^2}{L}\right)\right).
\tag{ACP5}
$$

The logarithm of this main magnitude is $-O(j\log L)$, and
$j\log L=o(\sqrt L)$. Therefore the whole actual-pressure allowance
ACP2 and the cutoff remainder ACP4 are negligible relatively, including
the $\exp(O(j))$ variation cost. The actual individual gap satisfies

$$
F_{A,j}:=\int M(\lambda(A\chi_A(c)))\,d\nu_j(c)-M(\lambda(A))
=\frac{(-\beta_1)^j(j-1)!}{L^j}
 \left(1+O\!\left(\frac{j^2}{L}\right)\right).
\tag{ACP6}
$$

This transfers a moving-order calculation to the actual unrestricted
pressure; it is neither a fixed-order substitution nor a smooth-only
sign claim.

Use the unchanged actual ratio $r_A$ from APC6. In
$G_A=(F_{A,k+1}-r_AF_{A,k})/(1-r_A)$, the two numerator main terms
have the same sign, so their coefficients add. Equations APC6 and ACP6 give

$$
G_A=(-1)^{k+1}
 \frac{\beta_1^k(k-1)![\beta_1k+\alpha(k+1)]}{L^{k+1}}
 \left(1+O\!\left(\frac{k^2}{L}\right)\right).
\tag{ACP7}
$$

The denominator $1-r_A=1+O(k/L)$ is absorbed in this relative error.
Consequently $G_A>0$ for odd $k$ and $G_A<0$ for even $k$, eventually
in both parity sectors. Stirling at this actual degree gives

$$
\log|G_A|=-\left(\frac23+o(1)\right)L^{1/3}\log L,
\qquad G_A\to0,
\qquad \sqrt A\log A\,|G_A|\to\infty.
\tag{ACP8}
$$

These are the actual gap's sign and magnitude, rather than growth
inferred from an upper allowance.

### What the comparison supplies at the original integer

Put $V_A=\int M(\lambda(A\chi_A(c)))\,d\sigma_A(c)$.
The same mixture of ACP5 and ACP2 proves

$$
V_A-B(A)=G_A(1+o(1)),\qquad R(A)=o(|G_A|).
\tag{ACP9}
$$

The second assertion uses the valid whole-reserve upper
$R(A)=O(A^{-1/2})$. It does not treat a reserve lower constant as an
upper budget. For odd $k$ the actual pressure upper
$M(\lambda(A))<V_A$ holds eventually, but $V_A>B(A)$ with a shift
larger than the root scale. For even $k$, $V_A<B(A)$ but
$M(\lambda(A))>V_A$. Thus this single comparison does not give the
proposed sufficient pressure upper $M(\lambda(A))<B(A)$ on either
sector. It determines neither the sign of $M(\lambda(A))-B(A)$ nor
the outcome of a compensated argument.

For every original integer $n$ with its own $A=\log n$, the exact target is

$$
\Delta(n)=B(A)-M(\lambda(A))+d_A(n)>0
\quad\Longleftrightarrow\quad
 d_A(n)>M(\lambda(A))-B(A).
\tag{ACP10}
$$

The stronger pressure upper is sufficient, not necessary. Retain APC10's
same-integer identity unchanged:
$\int d_{\lambda(A\chi_A(c))}(n)\,d\sigma_A(c)=d_A(n)+G_A$.
ACP7 now estimates its previously unspecified correction. Pointwise
nonnegative defects do not imply a nonnegative signed average, and no
other optimizer replaces $n$. No existence of an own-price zero-defect
integer in a specified parity sector is asserted.

APC9–APC11 still pay the complete smoothed and proper-power responses.
The comparison of first-prime transport with this same integer's defect
remains unproved. Exact price calibration and a favorable pressure
comparison do not by themselves remove the larger averaged benchmark
shift; no RH or all-integer Robin conclusion follows.

## An observation transport with a root-scale averaged-pressure margin

The following application reuses the whole BPY law, GPC's original
response estimates, APC's absolute cutoff bounds and the same actual
reserve. It changes the clock observation by an explicit signed
Stieltjes kernel. Standard integration by parts supplies the transport;
the additional application pays its variation and infinite clock tail
and estimates the resulting actual pressure average. No literature
priority, numerical common threshold, Lean certification, pressure-order
inequality or RH/Robin proof is claimed.

### Keep the two response kernels distinct

Retain $K(x)=(1+\log x)/(x^2\log^2x)$,
$\lambda(x)=1/(x\log x)$ and ACP's
$B(x)=\gamma+\log\log x-1/\log x$ for $x\ge e$.
Their derivatives are $\lambda'=-K$ and $B'=xK$. The original response is

$$
J_c^\psi(A)=-\frac1c\int_A^\infty[\psi(cu)-cu]K(u)\,du.
$$

In general $I_\psi(Ac)\ne-J_c^\psi(A)$: scaling also changes the
logarithmic kernel. The construction below transports this observation
explicitly instead of identifying the two integrals.

The actual pressure still satisfies
$M(\lambda(x))=B(x)-I_\psi(x)-R(x)$. Directly reuse the expansion of
this same reserve in
[FIB §247.3, (247.8)](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md#2473-实际双候选储备的二项展开):

$$
R(x)=\frac{c_R}{\sqrt x\log x}
 +O\!\left(\frac1{\sqrt x\log^2x}\right),
\qquad c_R=2(\sqrt2-1)>0.
\tag{KTO1}
$$

Its existing proof uses the actual two-candidate reserve and effective
unconditional PNT. No new reserve or PNT theorem is asserted.
The existing pressure and tail identities make $R$ and $I_\psi$ bounded
on $[e,\infty)$, with both tending to zero.

### A slower source and a paid inverse-moment correction

Use $R_t$ and $\nu_j$ from GPC2. Put $L=\log A$, $T_A=\sqrt A L$ and

$$
\mathcal T=\{0,-4,-3/4,-1/4,1/4\},\qquad
\epsilon=\frac1{8(1+\max_{t\in\mathcal T}\log R_t)},\qquad
k=\max\{1,\lfloor\epsilon\log L\rfloor\}.
$$

This degree differs from APC/ACP's $\lfloor L^{1/3}\rfloor$.
It depends only on the owned clock moments. GPC2 gives, eventually,

$$
M_t(k)\le C L^{1/4}\quad(t\in\mathcal T),\qquad
\int\bigl[|\log c|+c^{-1/2}(1+|\log c|)\bigr]\,d|\nu_k|(c)
\le C L^{1/4}.
\tag{KTO2}
$$

Indeed $\epsilon\log R_t\le1/8$, and neighboring quarter moments
bound both logarithmic factors. Also $k\to\infty$ and
$k\le\kappa L$ eventually, within GPC's common response cap.

Let $\tau=e/A$, $\bar\nu=(\chi_A)_\#\nu_k$, and define

$$
\delta_A=\int c^{-1}\,d\bar\nu(c)-1,\qquad
\eta_A=\bar\nu-2\delta_A(\delta_1-\delta_2).
\tag{KTO3}
$$

Then $\eta_A$ has mass one, inverse clock moment exactly one and support
$c\ge\tau$ for large $A$. The whole small-clock estimate is
$|\delta_A|\le2\tau^3M_{-4}(k)=O(A^{-3}L^{1/4})$.
Clamping decreases the needed negative weighted logarithms; its positive
quarter-moment change is bounded by $\tau^{1/4}M_0(k)$.
Thus the selected absolute and logarithmic moments of $\eta_A$ retain
the bounds KTO2. GPC and APC's absolute cutoff estimates, followed by
the negligible two-atom correction, give

$$
T_A\left|\int J_c^\psi(A)\,d\eta_A(c)\right|\longrightarrow0.
\tag{KTO4}
$$

The fixed-clock responses at $c=1,2$ are bounded by the existing PNT
bounds; their correction cost after multiplication by $T_A$ tends to
zero. All prime powers, zero heights and infinite response tails remain.
Exact xi zeros and source jets belong to $\nu_k$; cutoff and correction
errors for $\eta_A$ are paid rather than declared zero.

### A finite-variation observation kernel

For $c\ge\tau$ and $v\ge c$ define

$$
r_A(v,c)=\frac{c^{-2}K(Av/c)}{K(Av)},\qquad a_A(c)=r_A(c,c),
$$

$$
d\kappa_{A,c}(v)=a_A(c)\delta_c(dv)
 +\mathbf1_{v>c}\,\partial_v r_A(v,c)\,dv.
\tag{KTO5}
$$

The cumulative function is zero below $c$ and $r_A(v,c)$ above it.
Every kernel argument is at least $e$. With $g(z)=(1+z)/z^2$,
$r_A(v,c)=g(\log(Av)-\log c)/g(\log(Av))$ and
$a_A(c)=g(L)/g(L+\log c)$. Since
$g'/g=1/(z+1)-2/z$ is increasing, $r_A$ decreases to one for $c>1$
and increases to one for $c<1$. Consequently $\kappa_{A,c}$ has mass one;
it is positive for $c<1$, while for $c>1$ its atom is followed by a
negative density. Its variation satisfies

$$
\|\kappa_{A,c}-\delta_c\|_{\rm TV}=2|a_A(c)-1|,
\quad |a_A(c)-1|\le\frac{2|\log c|}{L},
\quad \|\kappa_{A,c}\|_{\rm TV}\le C(1+\log_+c/L).
\tag{KTO6}
$$

The middle bound uses $g(L)\le2/L$ and the $1$-Lipschitz function
$z^2/(z+1)$ on $z\ge1$.

At a finite endpoint $V\ge c$, Stieltjes integration by parts gives
three expressions, respectively:

$$
\begin{aligned}
\int_{[c,V]}\lambda(Av)\,d\kappa_{A,c}
 &=\lambda(AV)r_A(V,c)+\frac1c\int_A^{AV/c}K(u)\,du,\\
\int_{[c,V]}B(Av)\,d\kappa_{A,c}
 &=B(AV)r_A(V,c)-B(AV/c)+B(A),\\
\int_{[c,V]}I_\psi(Av)\,d\kappa_{A,c}
 &=I_\psi(AV)r_A(V,c)
   +\frac1c\int_A^{AV/c}[\psi(cu)-cu]K(u)\,du.
\end{aligned}
$$

The price and tail boundary terms vanish as $V\to\infty$.
Moreover $r_A(V,c)-1=O_c(1/\log(AV))$, so the benchmark boundary
difference also vanishes. Including the atom in KTO5 is essential.
The resulting exact observations are

$$
\int\lambda(Av)\,d\kappa_{A,c}=\frac{\lambda(A)}c,
\qquad \int B(Av)\,d\kappa_{A,c}=B(A),
\qquad \int I_\psi(Av)\,d\kappa_{A,c}=-J_c^\psi(A).
\tag{KTO7}
$$

These integrals are absolute. Price and $I_\psi$ are bounded on
$[e,\infty)$. For $B$, its lower bound and the positive kernel for
$c<1$ control the absolute integral by a constant depending on $A$.
For $c\ge1$, the single-sign density and the benchmark calculation
bound it by $C_A[1+(\log_+c)^2]$. The moments in KTO2 make all these
bounds integrable against $|\eta_A|$.

Define the actual signed clock measure by the absolutely integrable kernel

$$
\omega_A(E)=\int\kappa_{A,c}(E)\,d\eta_A(c).
$$

It has mass one, support $v\ge\tau$ and
$\|\omega_A-\eta_A\|_{\rm TV}=O(L^{-3/4})$. Absolute kernel Fubini,
KTO3 and KTO7 prove

$$
\int\lambda(Av)\,d\omega_A=\lambda(A),\qquad
\int B(Av)\,d\omega_A=B(A),\qquad
\int I_\psi(Av)\,d\omega_A=-\int J_c^\psi(A)\,d\eta_A(c).
\tag{KTO8}
$$

Thus the actual shifted-tail average is $o(1/T_A)$ by KTO4.
Positive power moments and exact Mellin zeros are not assumed for
$\omega_A$. Its new infinite clock tail has finite variation and the
absolute observation bounds just proved.

### Transport the same actual reserve at root scale

First KTO1–KTO3 imply

$$
T_A\int R(Ac)\,d\eta_A(c)=c_RH_k(1/2)+o(1).
\tag{KTO9}
$$

For completeness, before the tiny correction the original-source integral
is $\int R(A\chi_A(c))\,d\nu_k(c)$. Split that source at
$c<A^{-1/2}$ and retain this clamped integrand on the small-clock set.
Bounded $R$ and $M_{-4}(k)$ pay its entire contribution
by $O(L^{5/4}A^{-3/2})$. On the complement, $z=\log c$ and
$L+z\ge L/2$, so KTO1 gives

$$
T_A R(Ac)=c^{-1/2}
 \left[\frac{c_RL}{L+z}+O\!\left(\frac L{(L+z)^2}\right)\right].
$$

Its difference from $c_Rc^{-1/2}$ is at most
$(C/L)c^{-1/2}(1+|\log c|)$, costing $O(L^{-3/4})$ by KTO2.
The missing reference moment is at most $A^{-7/4}M_{-4}(k)$, and
the tiny KTO3 atoms cost $o(1)$ after root normalization. This uses
the quantitative reserve remainder, not a bare $o(1)$ multiplied by
growing signed variation.

For $c\ge A^{-1/2}$, the support of $\kappa_{A,c}$ lies in $v\ge c$,
and KTO1 bounds the whole later reserve by
$C/(\sqrt{Ac}\log(Ac))$. KTO6 therefore gives

$$
T_A\left|\int R(Av)\,d\kappa_{A,c}(v)-R(Ac)\right|
\le\frac C L c^{-1/2}|\log c|.
$$

Its $|\eta_A|$ integral is $O(L^{-3/4})$. For
$\tau\le c<A^{-1/2}$ the kernel is positive of mass one; bounded $R$
and the complete small-clock mass again cost
$O(L^{5/4}A^{-3/2})$. Hence

$$
T_A\int R(Av)\,d\omega_A(v)
=c_RH_k(1/2)+o(1)\longrightarrow c_R>0.
\tag{KTO10}
$$

Here $H_k(1/2)=1-Q(h(1/2))^k\to1$ by XLR2/GPC8.
No positivity of a general signed average was used, and the kernel's
entire infinite tail remains.

### Actual pressure and the same integer's remaining defect

The observation bounds establish absolute pressure integrability through
$M=B-I_\psi-R$. Integrating this exact identity and using KTO4,
KTO8 and KTO10 yields

$$
V_A:=\int M(\lambda(Av))\,d\omega_A(v)
=B(A)-\frac{c_R}{\sqrt A\log A}
 +o\!\left(\frac1{\sqrt A\log A}\right).
\tag{KTO11}
$$

In particular $V_A<B(A)-c_R/(2T_A)$ eventually.
This is an actual averaged-pressure margin for the transported
observation; it supplies no ordering of $M(\lambda(A))$ and $V_A$.
ACP's older two-degree pressure comparison retains its own observation
and remains unchanged.

For every original integer $n$ with its own $A=\log n$, keep the
pointwise defect $d_\lambda(n)=M(\lambda)-W(n)+\lambda\log n$ and define
$D_A(n)=\int d_{\lambda(Av)}(n)\,d\omega_A(v)$.
Exact mass and price mean give $D_A(n)=V_A-W(n)+1/L$, and therefore

$$
\Delta(n)=D_A(n)+B(A)-V_A,\qquad
T_A\Delta(n)=T_AD_A(n)+c_R+o(1).
\tag{KTO12}
$$

The same original integer is used throughout. The signed average
$D_A(n)$ has no proved lower bound sufficient to settle Robin.
All prime powers occur in the complete $\psi$ response, actual reserve,
actual pressure and exact account. GPC's original response is used at
its legitimate source, with the new observation transported by KTO7.
The compensated defect estimate, RH and strict Robin for all $n>5040$
remain unproved.

## A joint lower bound for the complete distant first-prime sector

This application combines the whole signed source before estimating a
prime sector. It reuses KTO's observer, GPC's moments, ACP's node-$1$
slope and Gamma comparison method, and the standard effective
unconditional PNT. The new lower bound concerns the actual distant
first-layer defect of the same original integer, including occupied
primes. Its complementary signed defect remains uncontrolled. No
literature priority, numerical common threshold, Lean certification or
RH/Robin proof is claimed.

### The actual sector and absolute clock budget

Keep KTO's $A=\log n$, $L=\log A$, $T_A=\sqrt A L$ and
$k=\max\{1,\lfloor\epsilon\log L\rfloor\}$. Put

$$
P=A^{16},\qquad Z=\log P=16L,\qquad
\mathcal C_A=[A^{-1/2},A^8],\qquad
r_p=\frac{\log(1+1/p)}{\log p},
$$

$$
F_P(q)=\sum_{p>P}\log p\,(r_p-q)_+,\qquad
U_A=\int F_P(\lambda(Av))\,d\omega_A(v),\qquad
H_A=\frac{\beta_1^k(k-1)!}{(16L)^k}.
\tag{JPT1}
$$

Here $\beta_1>0$ is ACP3's slope at node $1$. Each $F_P(q)$ is a
finite nonnegative sum bounded by the actual unrestricted pressure
$M(q)$. The sum over all $p>P$ after integration will be kept complete.
The real moments in GPC2 and KTO2, and the other side of ACP3's
analytic expansion, give

$$
M_t(k)\le CL^{1/4}\quad(t=0,-4,1/4),\qquad
\int|\log c|\,d|\nu_k|(c)\le CL^{1/4},
$$

$$
w(u):=Q(h(1+u))=\beta_1u\exp(O(u))>0
\quad(0<u\le u_0),\qquad 0<u_0\le1/16.
\tag{JPT2}
$$

Choose fixed $D$ with
$|\log(w(u)/(\beta_1u))|\le Du$ on that interval. These are
identities and bounds for the original source $\nu_k$; no Mellin
identity is assigned to $\eta_A$ or $\omega_A$.

The bounded $I_\psi,R$ in KTO allow a fixed $C_*$ such that
$0\le M(\lambda(x))\le F(x):=B(x)+C_*$ and $F(x)\ge1$ for $x\ge e$.
For $c<1$, positivity of $\kappa_{A,c}$ and KTO7 give
$\int F(Av)\,d|\kappa_{A,c}|=F(A)$. For $c\ge1$, the atom and
single-sign density give exactly

$$
\int F(Av)\,d|\kappa_{A,c}|=2a_A(c)F(Ac)-F(A).
$$

Use $a_A(c)\le1+2\log c/L$ and
$F(Ac)\le C+\log L+\log c/L$. Consequently

$$
\int F_P(\lambda(Av))\,d|\kappa_{A,c}|(v)
\le C(1+\log L)[1+(\log_+c)^2].
\tag{JPT3}
$$

This proves absolute kernel/source Fubini and, by Tonelli against
total variation, absolute interchange of the complete prime sum.
No positive power moment of $\omega_A$ is used.

Below $c=A^{-1/2}$, the clamped source has mass at most
$A^{-2}M_{-4}(k)$; the correction atoms $1,2$ are outside this set
for large $A$. Its full JPT3 cost is
$O(A^{-2}L^{1/4}(1+\log L))$. Above $c=A^8$, $\eta_A=\nu_k$ and

$$
1+\log^2c\le Cc^{1/8},\qquad c^{1/8}\le A^{-1}c^{1/4}.
$$

Thus the complete high-clock cost is
$O(A^{-1}L^{1/4}(1+\log L))$. On $\mathcal C_A$ the clamp is inactive;
replacing $\eta_A$ by $\nu_k$ costs
$O(|\delta_A|(1+\log L))$ at the two correction atoms. With
$G_A(c)=\int F_P(\lambda(Av))\,d\kappa_{A,c}(v)$, these bounds yield

$$
U_A=\int_{\mathcal C_A}G_A(c)\,d\nu_k(c)
 +O(A^{-1}L^{1/4}(1+\log L)).
\tag{JPT4}
$$

The displayed error is both $o(H_A)$ and $o(1/T_A)$. The comparison
with $H_A$ is justified by the moving-degree estimate below.

### Keep the actual activation and the infinite prime tail

Let $x_p$ solve $\lambda(x_p)=r_p$ for large $p$. Elementary logarithm
expansion and the explicit derivative of $\lambda$ give
$x_p>p$ and $x_p=p+O(1)$: the price difference at $p$ is
$O(1/(p^2\log p))$, the solution lies in $[p,2p]$ eventually, and the
mean-value denominator there is comparable to $1/(p^2\log p)$.
For $c\in\mathcal C_A$ and $p>P$, $x_p/A>A^{15}>c$, so the kernel
atom sees zero hinge. Finite-endpoint integration by parts gives

$$
\int(r_p-\lambda(Av))_+\,d\kappa_{A,c}(v)
=r_p-\frac1c\lambda(x_p/c)
=-\frac{\log c}{x_p\log x_p\log(x_p/c)}.
\tag{JPT5}
$$

The endpoint at infinity is $r_p$, since the cumulative kernel tends
to one. All arguments in this calculation exceed $e$. Its sign for
$c<1$ differs from its sign for $c>1$; neither is separately carried
through the signed source.

Put $z=\log c$, so $-L/2\le z\le8L$ and $\log p\ge16L$.
Replacing $x_p$ by $p$ in the $\log p$-weighted sum JPT5 costs at most
$C|z|\sum_{p>P}1/(p^2\log p)\le C|z|/(P\log P)$.
The reference summand is $-z/[p(\log p-z)]$.
Reuse the standard effective unconditional PNT in the form
$\pi(t)=\operatorname{li}(t)+O(t\exp(-a\sqrt{\log t}))$.
Partial summation applies uniformly because $|z|/\log t\le1/2$
for $t\ge P$, and the weight derivative is bounded by
$C|z|/(t^2\log t)$. The endpoint and complete infinite error tail are
$O(|z|\exp(-a_1\sqrt Z))$ for some fixed $a_1>0$.
The continuous integral is exactly

$$
-z\int_P^\infty\frac{dt}{t\log t(\log t-z)}
=\log(1-z/Z).
$$

Therefore, uniformly on $\mathcal C_A$,

$$
G_A(c)=\log(1-\log c/Z)
 +O\!\left(|\log c|e^{-a_1\sqrt Z}
             +\frac{|\log c|}{P\log P}\right).
\tag{JPT6}
$$

Its source-integrated error is
$O(L^{1/4}e^{-a_1\sqrt Z}+L^{1/4}/(P\log P))=o(H_A)$.
The PNT error is not asserted to be $o(1/T_A)$; relative control is
sufficient to determine this sector's sign.

### Combine the whole signed source before estimating

On $\mathcal C_A$ use

$$
\log(1-z/Z)=-\int_0^\infty e^{-Zu}(e^{zu}-1)\,\frac{du}{u}.
$$

Only $[0,u_0]$ is interchanged with the source. The removed tail is
bounded by $C\exp[-u_0(Z-\max(z,0))]\le Ce^{-8u_0L}$.
The bound $|(c^u-1)/u|\le|\log c|(1+c^{u_0})$ supplies absolute
Fubini. No two divergent $1/u$ terms are separated.
Extending this truncated expression from $\mathcal C_A$ to the
whole $\nu_k$ costs $O(A^{-2}LM_{-4}(k))$ below $A^{-1/2}$ and
$O(A^{-1}M_{1/4}(k))$ above $A^8$. For the former, use the maximum
of $c^4|\log c|$ on the small-clock set; for the latter use
$|\log c|(1+c^{u_0})\le Cc^{1/8}$.
Exact source mass and its Mellin identity now give

$$
\int_{\mathcal C_A}\log(1-\log c/Z)\,d\nu_k(c)
=\int_0^{u_0}e^{-Zu}Q(h(1+u))^k\,\frac{du}{u}+o(H_A).
\tag{JPT7}
$$

In particular the source factor is evaluated at $1+u$, whereas
ACP4 used $1-u$. The main integral here is positive for every $k$.

Apply the Gamma comparison method of ACP4–ACP5 with the explicit new
parameters $Z=16L$ and $k=O(\log L)$. JPT2 bounds the integral between
truncated Gamma integrals with rates $Z+Dk$ and $Z-Dk$.
Here $k^2/Z\to0$ and $k\log Z=o(Z)$, so the rate change costs
$O(k^2/Z)$ relatively, and the removed Gamma tails are exponentially
smaller. Hence

$$
\int_0^{u_0}e^{-Zu}w(u)^k\,\frac{du}{u}
=\frac{\beta_1^k\Gamma(k)}{Z^k}
 \left(1+O\!\left(\frac{k^2}{Z}\right)\right)
=H_A(1+o(1)).
\tag{JPT8}
$$

Stirling at this actual degree gives
$\log H_A=-\epsilon(\log L)^2+O(\log L\log\log L)$.
Thus every error in JPT4, JPT6 and JPT7 is $o(H_A)$, including the
whole source variation and prime tail. Combining them proves

$$
U_A=H_A(1+o(1))>0,\qquad T_AH_A\longrightarrow\infty.
\tag{JPT9}
$$

### The same integer's occupied and absent first layers

Let $D_{\mathrm{far},A}(n)$ average the complete first-layer defect
at primes $p>P$, including both occupied and absent primes:

$$
D_{\mathrm{far},A}(n)=\int\left[
 \sum_{\substack{p>P\\p\nmid n}}\log p\,(r_p-\lambda(Av))_+
 +\sum_{\substack{p>P\\p\mid n}}\log p\,(\lambda(Av)-r_p)_+
 \right]d\omega_A(v).
$$

This is an actual pointwise part of the same integer's defect; absolute
integration follows from the complete defect bounds in KTO.
The scalar hinge identity, exact mass and exact price mean give

$$
D_{\mathrm{far},A}(n)
=U_A+\sum_{\substack{p>P\\p\mid n}}
        (\lambda(A)-r_p)\log p.
\tag{JPT10}
$$

Every occupied-prime correction is nonnegative because
$r_p<\lambda(p)<\lambda(A)$ for $p>P>A$. Consequently, uniformly
for every original $n$ at its own $A=\log n$,

$$
D_{\mathrm{far},A}(n)\ge U_A\ge H_A/2>0
\quad\text{eventually}.
\tag{JPT11}
$$

No optimizer, CA/GA hypothesis or bound on the prime support of $n$
replaces this original integer. Define $E_A(n)$ by averaging the exact
complementary defect part: every first layer $p\le P$ and every higher
exponent layer at every prime remains in it. Then

$$
D_A(n)=D_{\mathrm{far},A}(n)+E_A(n)\ge E_A(n)+H_A/2,
$$

$$
T_A\Delta(n)=T_AE_A(n)+T_AD_{\mathrm{far},A}(n)+c_R+o(1).
\tag{JPT12}
$$

The complementary signed average $E_A(n)$ has no proved sufficient
lower bound. Its pointwise nonnegative integrand does not imply that
its signed average is nonnegative. The positive far-tail credit alone supplies no lower bound for this
complementary signed term. Discarding this tail in a lower bound is
justified after the complete signed average, not kernel by kernel.
No positivity of the complete defect, new total Robin upper or RH
proof follows.

## Growing source moments move the paid first-prime boundary

This application extends JPT's actual first-layer lower bound to a
moving cutoff whose logarithm is asymptotic to $\log A$. It keeps the
same KTO observer and degree. GPC's source moments, xi reflection,
positive-real Stirling, JPT's actual activation calculation and the
standard effective unconditional PNT are reused. The retained
application is the additional signed arithmetic band lower and its
same-integer consumer; the intermediate moment and Gamma estimates
are not separate new results. No literature priority, numerical
common threshold, Lean certification or RH/Robin proof is claimed.

### Uniform growing moments of the unchanged source

Keep $A=\log n$, $L=\log A$, $T_A=\sqrt A L$ and
$k=\max\{1,\lfloor\epsilon\log L\rfloor\}$ from KTO. Its original
source has

$$
h(s)=2m^{1-s}\xi(s),\qquad m=\pi/3,\qquad
Q(z)=(1-z)(1-z/m),\qquad H_k(s)=1-Q(h(s))^k.
$$

The clamped and calibrated source and its transported observer remain
$\eta_A=(\chi_A)_\#\nu_k-2\delta_A(\delta_1-\delta_2)$ and
$\omega_A=\int\kappa_{A,c}\,d\eta_A(c)$, with
$|\delta_A|=O(A^{-3}L^{1/4})$. Exact mass and price mean are still
$\int d\omega_A=1$ and
$\int\lambda(Av)\,d\omega_A(v)=\lambda(A)$.
All Mellin identities below belong to $\nu_k$.

GPC2 gives, for every real $t$ and integer $k\ge1$,
$M_t(k)=\int c^t\,d|\nu_k|(c)\le1+R_t^k$, where
$R_t=(1+b_t)(1+b_t/m)$ and $b_t=h(1+t)$.
For $t\ge2$, xi reflection gives
$b_t=2m^{-t}\xi(1+t)$ and $b_{-t}=2m^t\xi(t)$.
Use the standard positive-real log-Gamma Stirling expansion
([DLMF 5.11.1](https://dlmf.nist.gov/5.11.E1)) in
$\xi(s)=s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)/2$, for real
$s\ge2$, together with $\zeta(s)\le\zeta(2)$.
There is a fixed $C_m\ge1$ such that

$$
\log R_t,\ \log R_{-t}\le C_mt\log(t+2),\qquad
M_t(k)+M_{-t}(k)\le4e^{C_mkt\log(t+2)}
\quad(t\ge2,\ k\ge1).
\tag{GMW1}
$$

The constant is uniform in growing real $t$ and growing degree $k$.
No fixed-$t$ implicit constant or bounded-strip vertical Stirling
estimate is substituted at a growing real argument.

### A logarithmic clock window and its relative tail budget

For sufficiently large $A$, put

$$
t_A=\log L\ge4,\qquad
\ell_A=4(C_m+1)k\log(t_A+2),\qquad
\mathcal C'_A=[e^{-\ell_A},e^{\ell_A}],
$$

$$
P_A=Ae^{2\ell_A},\qquad Z_A=\log P_A=L+2\ell_A,\qquad
\widetilde H_A=\frac{\beta_1^k(k-1)!}{L^k}.
\tag{GMW2}
$$

Here $\beta_1>0$ is the same node-$1$ slope as in ACP3 and JPT2.
Retain JPT2's fixed $0<u_0\le1/16$ and
$w(u)=Q(h(1+u))=\beta_1u\exp(O(u))>0$ on $(0,u_0]$.
Since $k=O(t_A)$,
$\ell_A=O(t_A\log(t_A+2))=o(L)$ and $k\ell_A/L\to0$.
The clamp level $\tau=e/A$ is below $e^{-\ell_A}$ eventually, and
the correction atoms $1,2$ lie inside $\mathcal C'_A$.
In particular

$$
\frac{\log P_A}{\log A}\longrightarrow1,\qquad
P_A=A\exp\!\bigl(O(\log\log A\,\log\log\log A)\bigr)
 < A^{16}\quad\text{eventually}.
$$

This does not assert $P_A/A\to1$.
For $t=t_A\ge4$ and real $z$,
$(1+z^2)e^{u_0|z|}\le Ce^{t|z|/2}$ with an absolute constant
independent of $t$. On $|z|>\ell_A$, this is at most
$Ce^{-t\ell_A/2}e^{t|z|}$.
Integrating $c^t+c^{-t}$ with GMW1 gives

$$
\int_{|\log c|>\ell_A}(1+\log^2c)e^{u_0|\log c|}
       \,d|\nu_k|(c)
\le C\exp\!\bigl(-(C_m+2)kt_A\log(t_A+2)\bigr)
=:E_A^{\mathrm{clock}}.
\tag{GMW3}
$$

Stirling at the actual slow degree yields
$\log\widetilde H_A=-\epsilon(\log L)^2+
O(\log L\log\log L)$, whence
$(1+t_A)E_A^{\mathrm{clock}}=o(\widetilde H_A)$.
This is a relative error statement; these growing-window errors are
not asserted to be $o(1/T_A)$.

### The actual complete prime tail at the moving cutoff

Keep JPT's $r_p=\log(1+1/p)/\log p$ and the actual activation
$\lambda(x_p)=r_p$, with $x_p>p$ and $x_p=p+O(1)$. Define

$$
F_{P_A}(q)=\sum_{p>P_A}\log p\,(r_p-q)_+,\qquad
U'_A=\int F_{P_A}(\lambda(Av))\,d\omega_A(v).
\tag{GMW4}
$$

JPT3's global bound, valid at every cutoff because $F_{P_A}\le M$,
gives

$$
\int F_{P_A}(\lambda(Av))\,d|\kappa_{A,c}|(v)
\le C(1+\log L)[1+(\log_+c)^2].
$$

Thus absolute kernel/source integration retains the complete infinite
prime tail. GMW3 pays both excluded clock sets. Clamping only
decreases the low-clock logarithmic weight and keeps excluded low
clocks below $e^{-\ell_A}$; moreover
$|\chi_\#\nu_k|\le\chi_\#|\nu_k|$. On high clocks
$\eta_A=\nu_k$, and both correction atoms are inside the window.
Their replacement cost is
$O(|\delta_A|(1+\log L))=o(\widetilde H_A)$.
With $G'_A(c)=\int F_{P_A}(\lambda(Av))\,d\kappa_{A,c}(v)$,

$$
U'_A=\int_{\mathcal C'_A}G'_A(c)\,d\nu_k(c)
       +o(\widetilde H_A).
\tag{GMW5}
$$

The new tail budget is $O((1+t_A)E_A^{\mathrm{clock}})$; JPT4's
polynomial-window root-error assertion is not used outside its range.

For $c\in\mathcal C'_A$ and $p>P_A$, one has
$x_p/A>e^{2\ell_A}>c$, so the actual activation lies beyond the
kernel atom, as required in JPT5. Also
$|\log c|/\log p\le\ell_A/(L+2\ell_A)<1/2$.
These verified domain conditions permit JPT5's same finite-endpoint
calculation and JPT6's actual-activation replacement and effective-PNT
partial summation. They give, uniformly on the new window,

$$
G'_A(c)=\log(1-\log c/Z_A)
 +O\!\left(|\log c|e^{-a_1\sqrt{Z_A}}
          +\frac{|\log c|}{P_A\log P_A}\right),
\tag{GMW6}
$$

for a fixed $a_1>0$. The exact nonhomogeneous kernel, its atom,
actual prime thresholds and infinite tail are unchanged.
By KTO2, $\int|\log c|\,d|\nu_k|\le CL^{1/4}$.
Since $Z_A\sim L$ and $\sqrt L$ dominates $(\log L)^2$, the
source-integrated error in GMW6 is $o(\widetilde H_A)$, without a
root-smallness claim.

### Source cancellation and the moving Gamma comparison

On the new window set $z=\log c$ and use

$$
\log(1-z/Z_A)=-\int_0^\infty e^{-Z_Au}(e^{zu}-1)\,\frac{du}{u}.
$$

Only the finite interval $[0,u_0]$ is interchanged with the source.
The removed $u\ge u_0$ tail is at most
$Ce^{-u_0(Z_A-\max(z,0))}\le Ce^{-u_0(L+\ell_A)}$;
its source cost, including total variation $O(L^{1/4})$, is
$o(\widetilde H_A)$.
On the retained interval,
$|(c^u-1)/u|\le|\log c|(1+c^{u_0})$.
GMW3 therefore pays extension of this truncated expression to all
of $\nu_k$ with cost $O(E_A^{\mathrm{clock}})$.
Keep $c^u-1$ intact before Fubini; no divergent $1/u$ pieces are
separated. Exact source mass and its Mellin identity then give

$$
\int_{\mathcal C'_A}\log(1-\log c/Z_A)\,d\nu_k(c)
=\int_0^{u_0}e^{-Z_Au}Q(h(1+u))^k\,\frac{du}{u}
 +o(\widetilde H_A).
\tag{GMW7}
$$

Reuse the standard Gamma comparison of ACP4--ACP5 and JPT8 with
rates $Z_A\pm Dk$, where JPT2 supplies fixed $D$.
Here $k^2/Z_A\to0$ and $k\log Z_A=o(Z_A)$, so the integral is
$\beta_1^k\Gamma(k)Z_A^{-k}(1+o(1))$.
Moreover
$(L/Z_A)^k=\exp[-k\log(1+2\ell_A/L)]=1+o(1)$ because
$k\ell_A/L\to0$. Combining the actual tail, clock and source
errors proves

$$
U'_A=\widetilde H_A(1+o(1))>0,\qquad
T_A\widetilde H_A\longrightarrow\infty.
\tag{GMW8}
$$

### The additional paid band of the same original integer

For the same observer, $A$ and $k$, JPT9 gives the old actual tail
$U_A^{(16)}=16^{-k}\widetilde H_A(1+o(1))$ beyond $A^{16}$.
Since $k\to\infty$ and $P_A<A^{16}$ eventually, the actual
intervening band satisfies

$$
U_A^{\mathrm{band}}:=U'_A-U_A^{(16)}
=\int\sum_{P_A<p\le A^{16}}\log p\,(r_p-\lambda(Av))_+
            \,d\omega_A(v)
=\widetilde H_A(1+o(1))>0.
\tag{GMW9}
$$

Both terms use one realization and one clock; no separately optimized
sources are combined. For the same original integer $n$ at its own
$A=\log n$, let $D_A^{\mathrm{band}}(n)$ be the signed observer
average of the complete first-layer defect in $P_A<p\le A^{16}$:
absent primes contribute $\log p\,(r_p-\lambda(Av))_+$ and
occupied primes contribute $\log p\,(\lambda(Av)-r_p)_+$.
The scalar hinge identity, exact mass and exact price mean give

$$
D_A^{\mathrm{band}}(n)
=U_A^{\mathrm{band}}
 +\sum_{\substack{P_A<p\le A^{16}\\p\mid n}}
       (\lambda(A)-r_p)\log p
\ge U_A^{\mathrm{band}}
\ge\widetilde H_A/2>0\quad\text{eventually}.
\tag{GMW10}
$$

The occupied-prime correction is nonnegative because $p>P_A>A$.
This lower bound holds uniformly for every original integer at its
own clock. It pays an actual band previously inside JPT's
complementary defect, with no CA/GA assumption, prime-support bound
or optimizer substitution. The complete new far-first-layer sector
$p>P_A$ likewise has its nonnegative occupation correction and a
lower bound $\widetilde H_A/2$ eventually. These positive lower
bounds depend on $A$; they are not fixed positive constants.

Let $E'_A(n)$ average the exact remaining defect: all first layers
$p\le P_A$ and every higher exponent layer at every prime.
Writing $D_{\mathrm{far},A}^{(16)}(n)$ for the old JPT far sector,
the disjoint account is

$$
D_A(n)=E'_A(n)+D_A^{\mathrm{band}}(n)
                +D_{\mathrm{far},A}^{(16)}(n).
\tag{GMW11}
$$

One may instead combine the last two terms into the new far sector;
that overlapping sector is not counted again. KTO12's original
Robin margin remains

$$
T_A\Delta(n)=T_AE'_A(n)+T_AD_A^{\mathrm{band}}(n)
                 +T_AD_{\mathrm{far},A}^{(16)}(n)+c_R+o(1).
\tag{GMW12}
$$

No sufficient lower bound for $E'_A(n)$ is supplied. Its integrand is
pointwise nonnegative but its observer average is signed. The new
first-layer boundary and positive band do not prove complete-defect
positivity, RH or strict Robin for every $n>5040$.

## A root-small debit for the complete actual higher-layer defect

This application bounds every actual exponent layer $j\ge2$ of the
same original integer under the unchanged KTO observer. It reuses
the actual second cutoff MS3, the ordinary integral GPP4, KTO's
quantitative root-tail transport and the standard effective
unconditional PNT. These supporting estimates are not separate new
results. The application concerns the complete higher-layer defect;
the earlier reference prime-power transport is not assumed to bound
that defect. No literature priority, numerical common threshold,
Lean certification or RH/Robin proof is claimed.

For the classical actual-cutoff and full-exponent bookkeeping, see
Akatsuka, [arXiv:2411.19259v1, §3](https://arxiv.org/html/2411.19259v1#S3),
Lemma 3.1, Proposition 3.2 and (3.6)--(3.8), (3.11).
The correspondence is $\kappa=1$, the paper's price
$\varepsilon=\lambda(x)$, first cutoff $x_1(\varepsilon)$, and
higher cutoffs $y_j(x_1(\varepsilon))$.
These are the actual ratio thresholds used here, rather than reference
prime powers. Those source statements concern CA products and their
full-layer remainders; they do not state the signed-observer defect
lower bound consumed below. No claim of priority is attached to the
intermediate higher-pressure asymptotic.

### The actual higher pressure and its finite limit

Keep KTO's $A=\log n$, $L=\log A$, $T_A=\sqrt A L$,
$k=\max\{1,\lfloor\epsilon\log L\rfloor\}$, sources
$\nu_k,\eta_A$ and observer $\omega_A$.
Its mass is exactly one and its price mean is exactly $\lambda(A)$.
Keep $\lambda(x)=1/(x\log x)$ and $K(x)=-\lambda'(x)$.
Use the same actual increments

$$
\beta_{p,j}=\log\left(1+\frac1{p+\cdots+p^j}\right),\qquad
r_{p,j}=\frac{\beta_{p,j}}{\log p}.
$$

Define the full higher pressure and its tail by

$$
\mathcal M_{\ge2}(q)=\sum_p\sum_{j\ge2}\log p\,(r_{p,j}-q)_+,
\qquad C_2=\sum_p\sum_{j\ge2}\beta_{p,j}=\log\zeta(2),
$$

$$
F_2(x)=C_2-\mathcal M_{\ge2}(\lambda(x)),\qquad
\mathcal A_{\ge2}(x)=
 \sum_{\substack{p,\ j\ge2\\r_{p,j}>\lambda(x)}}\log p.
\tag{HLD1}
$$

The constant uses the ordinary telescope
$\sum_{j\ge2}\beta_{p,j}=-\log(1-p^{-2})$ and the convergent
Euler product for $\zeta(2)$. In particular $F_2$ is nonnegative,
bounded and decreases to zero on $[e,\infty)$.
Tonelli for nonnegative scalar hinges, followed by $q=\lambda(t)$,
gives the exact account

$$
F_2(x)=\sum_p\sum_{j\ge2}
       \min\{\beta_{p,j},\lambda(x)\log p\}
     =\int_x^\infty\mathcal A_{\ge2}(t)K(t)\,dt.
\tag{HLD2}
$$

The actual active set is finite at every finite $t$. The strict
threshold convention remains unchanged; isolated equality values do
not affect this ordinary integral.

### Insert the owned actual second cutoff and retain every higher layer

MS3 gives the actual second cutoff
$q_2(t)=\sqrt{2t}(1+O(1/\log t))$.
The effective PNT, including the possible strict endpoint atom
$O(\log t)$, therefore gives

$$
\sum_{p:r_{p,2}>\lambda(t)}\log p
=\vartheta(q_2(t)-)
=\sqrt{2t}+O(\sqrt t/\log t).
$$

For all growing indices $j\ge3$, reuse the owned activation bound
$p^j\log p<t\log t$. Put $X=t\log t/\log2$.
Then $j<\log X/\log2$ and $p<X^{1/j}$.
The elementary bound $\vartheta(y)\le y\log y$ yields

$$
\sum_{j\ge3}\sum_{p:r_{p,j}>\lambda(t)}\log p
\le\sum_{3\le j\le\log X/\log2}\vartheta(X^{1/j})
=O\!\left(X^{1/3}(\log X)^2\right)
=O\!\left(t^{1/3}(\log t)^3\right).
\tag{HLD3}
$$

This is uniform over the entire growing index range. Every actual
layer and its full weight remains; reference prime-power thresholds
are not substituted. The short-interval GM estimates elsewhere in
the MS3 application are not needed here.

Insert these bounds in HLD2 and reuse GPP4's integral estimate
$\int_x^\infty\sqrt tK(t)\,dt
=2/(\sqrt x\log x)+O(1/(\sqrt x\log^2x))$.
The second-layer error integrates to
$O(1/(\sqrt x\log^2x))$.
The entire $j\ge3$ term is $O(x^{-2/3}\log^2x)$, smaller than
that error. Consequently the actual pressure tail satisfies

$$
F_2(x)=\frac{2\sqrt2}{\sqrt x\log x}
       +O\!\left(\frac1{\sqrt x\log^2x}\right).
\tag{HLD4}
$$

### Use the same quantitative root-tail transport

Apply KTO9--KTO10's root-tail argument with $F_2$ in place of $R$
and $2\sqrt2$ in place of $c_R$, keeping the same sources,
degree and observer. The required input is HLD4 with its quantitative
extra logarithm, together with boundedness on $[e,\infty)$.
The correspondence of error bounds is as follows.

Below $c=A^{-1/2}$, the clamped bounded integrand and source mass
$A^{-2}M_{-4}(k)$ cost $O(A^{-3/2}L^{5/4})$ after multiplication
by $T_A$. On $c\ge A^{-1/2}$ put $z=\log c$, so $L+z\ge L/2$.
HLD4 gives

$$
T_AF_2(Ac)=c^{-1/2}
 \left[\frac{2\sqrt2 L}{L+z}
       +O\!\left(\frac L{(L+z)^2}\right)\right].
$$

Its difference from $2\sqrt2c^{-1/2}$ is bounded by
$(C/L)c^{-1/2}(1+|\log c|)$.
KTO2 makes its full source integral $O(L^{-3/4})$.
The omitted source reference moment is at most
$A^{-7/4}M_{-4}(k)$, and the same two correction atoms are negligible.
This gives
$T_A\int F_2(Ac)\,d\eta_A(c)
=2\sqrt2H_k(1/2)+O(L^{-3/4})$.

For $c\ge A^{-1/2}$ the entire kernel support has $v\ge c$.
HLD4 bounds every later $F_2(Av)$ by
$C/(\sqrt{Ac}\log(Ac))$. KTO6 therefore gives

$$
T_A\left|\int F_2(Av)\,d\kappa_{A,c}(v)-F_2(Ac)\right|
\le\frac C L c^{-1/2}|\log c|.
$$

Its $|\eta_A|$ integral is $O(L^{-3/4})$.
On the remaining small clocks the kernel is positive of mass one;
bounded $F_2$ and the same small-clock mass pay its complete infinite
tail. Thus the reused root-tail transport yields

$$
T_A\int F_2(Av)\,d\omega_A(v)
=2\sqrt2H_k(1/2)+O(L^{-3/4}).
\tag{HLD5}
$$

All source Mellin identities remain on $\nu_k$.
No positive-power moment of $\omega_A$ is used.
Bounded $F_2$ and finite variation also give absolute integration.

Since $\omega_A$ has exact mass one, HLD4--HLD5 imply the actual
higher-pressure gap

$$
\mathcal J_2(A):=
\int\mathcal M_{\ge2}(\lambda(Av))\,d\omega_A(v)
       -\mathcal M_{\ge2}(\lambda(A)),
$$

$$
T_A\mathcal J_2(A)
=2\sqrt2[1-H_k(1/2)]+O(L^{-3/4})
=2\sqrt2Q(h(1/2))^k+O(L^{-3/4})=o(1).
\tag{HLD6}
$$

Here $|Q(h(1/2))|<1$ by XLR2/GPC8.
No Jensen sign is asserted. In particular, for a fixed sufficiently
large $C$, put
$\varepsilon_A=C(|Q(h(1/2))|^k+L^{-3/4})\to0$;
then $|\mathcal J_2(A)|\le\varepsilon_A/T_A$ eventually.

### Compare with the same integer's nonnegative own-price defect

For the original integer $n$, let $a_p=v_p(n)$ and put
$W_2(n)=\sum_p\sum_{2\le j\le a_p}\beta_{p,j}$ and
$L_2(n)=\sum_p(a_p-1)_+\log p$.
Its pointwise complete higher-layer defect is

$$
d_2(n,q)=\mathcal M_{\ge2}(q)-W_2(n)+qL_2(n)
 =\sum_p\sum_{2\le j\le a_p}\log p\,(q-r_{p,j})_+
  +\sum_p\sum_{j\ge\max\{2,a_p+1\}}
                 \log p\,(r_{p,j}-q)_+\ge0.
\tag{HLD7}
$$

Every active and occupied sum at $q>0$ is finite.
This retains all higher layers and the original integer's exact
occupation pattern. Its observer average is absolute: the higher
pressure is bounded, $W_2(n),L_2(n)$ are finite, and KTO owns the
absolute price integral.
Define $D_{2,A}(n)=\int d_2(n,\lambda(Av))\,d\omega_A(v)$.
Exact mass and exact price mean give

$$
D_{2,A}(n)=d_2(n,\lambda(A))+\mathcal J_2(A)
\ge-\frac{\varepsilon_A}{T_A},\qquad
\varepsilon_A\longrightarrow0.
\tag{HLD8}
$$

The lower bound is uniform for every original integer at its own
$A=\log n$. It compares to the nonnegative defect at the original
price; it does not carry pointwise positivity through signed averaging
or replace $n$ by an optimizer. All remaining observer error depends
on $n$ only through $A$.

### The first-layer consumer and the remaining full target

Let $N_A(n)$ average the complete actual first-layer defect for
$p\le P_A$, with GMW2's cutoff and unchanged observer.
Let $D_{\mathrm{far,new},A}(n)$ average the first-layer complement
$p>P_A$. The disjoint account is

$$
D_A(n)=N_A(n)+D_{\mathrm{far,new},A}(n)+D_{2,A}(n),
$$

$$
D_{\mathrm{far,new},A}(n)
=D_A^{\mathrm{band}}(n)+D_{\mathrm{far},A}^{(16)}(n)
\ge\widetilde H_A/2>0\quad\text{eventually}.
\tag{HLD9}
$$

No overlapping GMW sector is counted twice.
KTO12, GMW and HLD8 therefore give

$$
\begin{aligned}
T_A\Delta(n)
&\ge T_AN_A(n)+T_AD_{\mathrm{far,new},A}(n)
                       +c_R-\varepsilon_A+o(1)\\
&\ge T_AN_A(n)+T_A\widetilde H_A/2+c_R-o(1).
\end{aligned}
\tag{HLD10}
$$

Every actual higher layer has a root-small possible debit.
The remaining signed estimate concerns the same integer's first
layers $p\le P_A$ and their joint compensation with the paid far
sector. No sufficient lower bound for $N_A(n)$ is supplied.
Complete-defect positivity, strict Robin for every $n>5040$ and RH
remain unproved.

## Root-scale localization of the remaining first-prime defect

This application controls the complete low-first-prime defect of the
same original integer under the unchanged KTO observer. It reuses
GMW1's uniform real-order source moments, the exact KTO kernel and
mass/price calibration, GMW's far-first-layer lower and HLD's complete
higher-layer lower. The new consumer leaves only a moving first-prime
window unpaid at root scale. The intermediate moment and affine
identities are supporting steps, not separate new results.
No literature priority, numerical common threshold, Lean certification
or RH/Robin proof is claimed.

### Use the same source with a larger negative moment order

Keep $A=\log n$, $L=\log A$, $T_A=\sqrt A L$,
$k=\max\{1,\lfloor\epsilon\log L\rfloor\}$ and the same
$\nu_k,\eta_A,\omega_A$ from KTO.
In particular the clamp is $\chi_A(c)=\max\{c,e/A\}$ and the
source correction atoms are $1,2$.
GMW1 has a fixed $C_m\ge1$ valid for every real moment order
$t\ge2$. For the lower prime cut use $t=L\ge4$ and put

$$
b_A=4(C_m+1)k\log(L+2),\qquad
Y_A=Ae^{-2b_A},\qquad a_A^{\mathrm{low}}=2Y_A/A=2e^{-2b_A},
$$

$$
\rho_A=4\exp\!\bigl(-(3C_m+4)kL\log(L+2)\bigr).
\tag{CPW1}
$$

Since $k=O(\log L)$, one has
$b_A=O((\log L)^2)=o(L)$.
Thus $Y_A\to\infty$, $\log Y_A/\log A\to1$,
$2Y_A<A$ and
$e/A<a_A^{\mathrm{low}}\le e^{-b_A}<1$ eventually.
Moreover

$$
\log(T_A\rho_A)=\log4+L/2+\log L
                    -(3C_m+4)kL\log(L+2)\longrightarrow-\infty,
\qquad T_A\rho_A\longrightarrow0.
\tag{CPW2}
$$

The changed moment order and buffer specify the lower prime cut;
the signed source, observer and slow degree remain unchanged.

### The actual low-prime pressure is affine above a common activation

Keep $r_p=\log(1+1/p)/\log p$ and $\beta_p=r_p\log p$.
For the finite set $p\le Y_A$, write
$\vartheta_Y=\sum_{p\le Y_A}\log p$ and
$S_Y=\sum_{p\le Y_A}\beta_p$, and define

$$
F_Y(q)=\sum_{p\le Y_A}\log p\,(r_p-q)_+,\qquad
B_Y(q)=\sum_{p\le Y_A}\log p\,(q-r_p)_+.
$$

The exact finite hinge identity gives

$$
F_Y(q)=S_Y-q\vartheta_Y+B_Y(q)\qquad(q\ge0).
\tag{CPW3}
$$

For every prime $p\le Y_A$, including $2$, the elementary actual
inequality $\log(1+1/p)>1/(p+1)$ gives

$$
r_p>\frac1{(p+1)\log p}
\ge\frac1{(Y_A+1)\log Y_A}
>\lambda(2Y_A)>\lambda(A)
\quad\text{eventually}.
\tag{CPW4}
$$

Thus $B_Y(\lambda(A))=0$, and
$B_Y(\lambda(Av))=0$ whenever $v\ge a_A^{\mathrm{low}}$.
No large-prime approximation to an activation point is applied to
small primes.

KTO5's entire kernel is supported on $v\ge c$.
For $c\ge a_A^{\mathrm{low}}$, its $B_Y$ observation is therefore
exactly zero, including arbitrarily high clocks and the signed
kernel density. For $e/A\le c<a_A^{\mathrm{low}}<1$, the kernel
is positive by KTO6. The exact KTO7 price observation yields

$$
0\le\int B_Y(\lambda(Av))\,d\kappa_{A,c}(v)
\le\vartheta_Y\int\lambda(Av)\,d\kappa_{A,c}(v)
=\frac{\vartheta_Y\lambda(A)}c.
\tag{CPW5}
$$

Positivity here concerns only these low-$c$ kernels. Neither the
source nor the final observer is assigned positivity.

### Pay the complete inverse-price-weighted low-clock tail

Put $J_{\mathrm{low}}(A)=
\int B_Y(\lambda(Av))\,d\omega_A(v)$.
The two source correction atoms lie outside
$c<a_A^{\mathrm{low}}$. Total variation decreases under pushforward,
and the clamp increases $c$, decreasing its inverse weight.
Using $a_A^{\mathrm{low}}\le e^{-b_A}$ and GMW1 at the actual
growing order $L$, one obtains

$$
\begin{aligned}
|J_{\mathrm{low}}(A)|
&\le\vartheta_Y\lambda(A)
       \int_{c<a_A^{\mathrm{low}}}c^{-1}\,d|\eta_A|(c)\\
&\le\vartheta_Y\lambda(A)
       \int_{c<a_A^{\mathrm{low}}}c^{-1}\,d|\nu_k|(c)\\
&\le e^{-2b_A}e^{-(L-1)b_A}M_{-L}(k)\\
&\le4\exp\!\bigl(-(L+1)b_A+C_mkL\log(L+2)\bigr)\\
&\le\rho_A=o(1/T_A).
\end{aligned}
\tag{CPW6}
$$

Here $\vartheta_Y\le Y_A\log Y_A$ gives
$\vartheta_Y\lambda(A)\le e^{-2b_A}$, and on $c<e^{-b_A}$,
$c^{-1}\le e^{-(L-1)b_A}c^{-L}$.
This proves absolute kernel/source Fubini as well: the integrand is
zero on the full support of every $c\ge a_A^{\mathrm{low}}$ kernel,
and the displayed positive-kernel bound controls all remaining clocks.
No inverse-price singularity, clamped source contribution or infinite
kernel tail is dropped. The uniform real-order input is GMW1;
no fixed-order implicit constant or weaker $u_0$-weighted clock
estimate is substituted at order $L$.

### Retain the same integer's actual missing low primes

For the original $n$, set
$W_{\mathrm{low}}(n)=\sum_{p\le Y_A,\ p\mid n}\beta_p$,
$L_{\mathrm{low}}(n)=\sum_{p\le Y_A,\ p\mid n}\log p$ and
$d_{\mathrm{low}}(n,q)=F_Y(q)-W_{\mathrm{low}}(n)+qL_{\mathrm{low}}(n)$.
This is exactly its complete first-layer defect on $p\le Y_A$:
occupied primes contribute $\log p(q-r_p)_+$ and absent primes
contribute $\log p(r_p-q)_+$.
By CPW4 its original-price baseline is

$$
G_{\mathrm{low},A}(n):=d_{\mathrm{low}}(n,\lambda(A))
=\sum_{\substack{p\le Y_A\\p\nmid n}}
             (\beta_p-\lambda(A)\log p)\ge0.
\tag{CPW7}
$$

Let $D_{\mathrm{low},A}(n)=
\int d_{\mathrm{low}}(n,\lambda(Av))\,d\omega_A(v)$.
Exact mass and exact price mean applied to CPW3 give

$$
D_{\mathrm{low},A}(n)
=G_{\mathrm{low},A}(n)+J_{\mathrm{low}}(A)
\ge G_{\mathrm{low},A}(n)-\rho_A\ge-\rho_A,
\qquad T_A\rho_A\longrightarrow0.
\tag{CPW8}
$$

This is uniform for every original integer at its own $A=\log n$.
The error depends on $n$ only through $A$; actual low-prime occupancy
is preserved in $G_{\mathrm{low},A}(n)$.
The finite prime set and KTO's absolute mass/price bounds give
absolute defect integration. No other integer, optimizer or
pointwise positivity transported through a signed measure is used.

### A disjoint central-window consumer

Retain GMW's upper cutoff
$P_A=Ae^{2\ell_A}$, where
$\ell_A=4(C_m+1)k\log(\log L+2)$, and its complete actual far-first
lower $D_{\mathrm{far,new},A}(n)\ge\widetilde H_A/2>0$ eventually.
Retain HLD's complete actual higher-layer lower
$D_{2,A}(n)\ge-\varepsilon_A/T_A$, with $\varepsilon_A\to0$.
All components use the same source, observer, degree and original $n$.

Let $C_A(n)$ average only the complete actual first-layer defect
on $Y_A<p\le P_A$. The exact disjoint account is

$$
D_A(n)=D_{\mathrm{low},A}(n)+C_A(n)
                  +D_{\mathrm{far,new},A}(n)+D_{2,A}(n).
\tag{CPW9}
$$

KTO12 and the three lower bounds yield

$$
\begin{aligned}
T_A\Delta(n)
&\ge T_AC_A(n)+T_AG_{\mathrm{low},A}(n)
 +T_AD_{\mathrm{far,new},A}(n)
 +c_R-\varepsilon_A-T_A\rho_A+o(1)\\
&\ge T_AC_A(n)+T_AG_{\mathrm{low},A}(n)
 +T_A\widetilde H_A/2+c_R-o(1).
\end{aligned}
\tag{CPW10}
$$

No far sector or higher layer is counted twice.
Both $\log Y_A/\log A$ and $\log P_A/\log A$ tend to one.
The logarithmic width of the unpaid prime window relative to
$\log A$ therefore tends to zero; the multiplicative window is not
claimed to shrink, and neither endpoint divided by $A$ is claimed
to tend to one.
No sufficient joint lower for
$C_A(n)+G_{\mathrm{low},A}(n)+D_{\mathrm{far,new},A}(n)$ is supplied.
Complete-defect positivity, RH and strict Robin for every $n>5040$
remain unproved.

## An actual integer family consumes the enlarged far-prime credit

The following application gives a cofinal family of actual integers
whose complete central first-layer debit cancels GMW's enlarged far
credit to leading order. It uses MS's strict actual products, the
owned effective PNT, HLD's full higher inventory and the unchanged
KTO/GMW/CPW observation. This is an obstruction to retaining a fixed
positive fraction of that credit through separate sector estimates.
It supplies no root-scale lower for the full defect, literature-priority
claim, Lean certification or RH/Robin proof.

### A complete pressure balance at the unchanged observation

Keep $A=\log n$, $L=\log A$, $T_A=\sqrt A L$, the same slow degree,
source and observer, and the exact cuts $Y_A,P_A$ from CPW and GMW.
Keep $\widetilde H_A=\beta_1^k(k-1)!/L^k$ and the actual far
pressure $U'_A$ from GMW4. KTO1 and KTO11 give

$$
\mathcal J(A):=V_A-M(\lambda(A))
=I_\psi(A)+o(1/T_A).
\tag{ACC1}
$$

Let
$F_{\mathrm{cen}}(q)=\sum_{Y_A<p\le P_A}\log p\,(r_p-q)_+$ and
$\mathcal J_{\mathrm{cen}}(A)
=\int F_{\mathrm{cen}}(\lambda(Av))\,d\omega_A(v)
-F_{\mathrm{cen}}(\lambda(A))$.
The original-price far pressure is zero: $p>P_A>A$ implies
$r_p<1/(p\log p)<\lambda(A)$.
CPW3 and exact mass/price identify the low pressure gap with
$J_{\mathrm{low}}(A)$; HLD6 retains the complete higher gap.
The disjoint pressure account therefore gives

$$
\mathcal J_{\mathrm{cen}}(A)
=I_\psi(A)-U'_A+o(1/T_A)
=-\widetilde H_A(1+o(1)).
\tag{ACC2}
$$

Here the effective PNT input used in ACP1 bounds
$|I_\psi(A)|\le Ce^{-a\sqrt L}=o(\widetilde H_A)$ for fixed
$C,a>0$. GMW8 and $T_A\widetilde H_A\to\infty$ pay the other
relative errors. No root-smallness of $U'_A$ is asserted.
All pressure integrals are absolute by KTO, GMW, HLD and CPW.
This balance alone concerns pressure: the complete central defect
still retains its nonnegative original-price baseline.

### Use actual strict products at their own size

Reuse MS's actual products

$$
N_x=\prod_p p^{a_p(x)},\qquad
 a_p(x)=\#\{j\ge1:r_{p,j}>\lambda(x)\},\qquad
 A_x=\log N_x.
$$

All equality layers are excluded. The owned finite-layer pressure
formula gives

$$
W(N_x)=M(\lambda(x))+\lambda(x)A_x.
\tag{ACC3}
$$

Every active first prime has $p<x$. Conversely, $p\le x-1$ gives
$r_p>1/((p+1)\log p)>\lambda(x)$. Thus the first active mass lies
between $\vartheta(x-1)$ and $\vartheta(x)$.
Use the same effective PNT, including the endpoint allowance
$O(\log x)$, and HLD3/MS3's bound $O(\sqrt x)$ for the complete
higher active mass. For some fixed $a>0$,

$$
A_x=x+O\!\left(xe^{-a\sqrt{\log x}}\right),\qquad A_x\sim x.
\tag{ACC4}
$$

This retains every growing exponent layer. In particular the actual
integers $N_x$ are unbounded. It does not assert $A_x=x$ or zero
defect at their own-size price.

For large $x$, put $A=A_x$, $s_y=y\log y$ and
$h_x=|s_A/s_x-1|$. ACC4 gives
$h_x=O(e^{-a\sqrt{\log x}})$ and hence $h_x\le1/4$ eventually.
The full-layer capacity application (NPC1) below gives the same
integer's original-price defect bound

$$
\begin{aligned}
0\le d_{A_x}(N_x)
&=M(\lambda(A_x))-M(\lambda(x))
       +(\lambda(A_x)-\lambda(x))A_x\\
&\le\frac{24A_xh_x^2+32\sqrt{A_x}h_x}{A_x\log A_x}\\
&=O\!\left(\frac{e^{-2a\sqrt{\log x}}}{\log x}\right)
=o(\widetilde H_{A_x}).
\end{aligned}
\tag{ACC5}
$$

The last comparison uses GMW2--GMW3's
$\log\widetilde H_A=-\epsilon(\log L)^2+
O(\log L\log\log L)$; $\sqrt L$ dominates $(\log L)^2$.
The capacity input is the existing arbitrary-host CA benefit bound,
not Proposition 5's additional superabundant localization. All
higher layers and both strict and weak threshold ties are retained.
This unconditional allowance still does not give
$d_{A_x}(N_x)=o(1/T_{A_x})$.

### The complete central debit and far credit are jointly realized

Put $n=N_x$ and $A=A_x$ in all unchanged cuts and observations.
Since $A\sim x$, one has $P_A>x$ and $2Y_A<x$ eventually.
Every prime factor of $N_x$ is below $x$, so the exact far occupation
correction vanishes. CPW4 gives
$r_p>\lambda(2Y_A)>\lambda(x)$ for every $p\le Y_A$;
hence all low primes divide this same $N_x$. Consequently

$$
D_{\mathrm{far,new},A}(N_x)=U'_A
=\widetilde H_A(1+o(1)),\qquad
G_{\mathrm{low},A}(N_x)=0.
\tag{ACC6}
$$

The original-price central and higher baselines are nonnegative
parts of the full $d_A(N_x)$ and are each bounded by ACC5.
Exact mass and price mean, ACC2, HLD8 and CPW8 now give

$$
C_A(N_x)=-\widetilde H_A(1+o(1)),\qquad
D_{\mathrm{low},A}(N_x)=o(1/T_A),\qquad
D_{2,A}(N_x)=o(\widetilde H_A).
\tag{ACC7}
$$

These are the complete occupied-and-absent defect contributions,
not just their pressure terms. In particular the disjoint CPW9
account yields

$$
D_A(N_x)-D_{\mathrm{far,new},A}(N_x)
=-\widetilde H_A(1+o(1)),\qquad
D_A(N_x)=o(\widetilde H_A).
\tag{ACC8}
$$

Thus, for every fixed real $\alpha<1$, eventually along this cofinal
actual integer family, with the threshold allowed to depend on the
fixed $\alpha$,

$$
\begin{aligned}
C_A(N_x)+\alpha D_{\mathrm{far,new},A}(N_x)&<0,\\
[D_A(N_x)-D_{\mathrm{far,new},A}(N_x)]
       +\alpha D_{\mathrm{far,new},A}(N_x)&<0.
\end{aligned}
\tag{ACC9}
$$

Uniform separate-sector estimates that leave a fixed positive fraction
of the enlarged far credit cannot hold on all original integers.
The same actual integers realize both sides of the cancellation;
no separately optimized configurations are combined.
The intermediate pressure balance and near-price estimates are used
only to establish this actual-integer obstruction.

The surviving target remains the root-scale compensated account
$T_A\Delta(N_x)=T_Ad_A(N_x)+T_AI_\psi(A)+c_R+o(1)$.
Neither term on the right has been bounded here sufficiently at that
scale. No sign of $D_A(N_x)$, $\Delta(N_x)$ or a Robin violation is
inferred. A joint arithmetic estimate preserving the root reserve
can still succeed; RH and strict Robin for every $n>5040$ remain
unproved.


## A finite upper benefit bound at the same strict inventory's own price

The existing [arbitrary-host benefit and thin-layer capacity
TC.1](erdosnicolas1975repartition.md#an-explicit-thin-layer-capacity-for-the-same-arbitrary-host)
can bound the complete own-price defect of ACC's actual $N_x$.
This applies a classical benefit calculation to two specified prices;
it introduces no new capacity or prime-distribution theorem. The
capacity's Yamada and Dusart inputs remain external, and this
application has no Lean certification or literature-priority claim.

Use the same strict integer $N_x$, $A=\log N_x$, $s_y=y\log y$ and
$\lambda(y)=1/s_y$. Suppose $x>1$, $A\ge16$, and put

$$
h=\left|\frac{s_A}{s_x}-1\right|\le\frac14.
$$

Let $C_A$ be the **maximal** optimizer at $\lambda(A)$, so it includes
every layer with $r_{p,j}\ge\lambda(A)$. The source $N_x$ includes
exactly the layers with $r_{p,j}>\lambda(x)$. For each prime, let
$\mathscr J$ contain exactly the positive layers lying between these
two actual exponent counts:

$$
\mathscr J=
\{(p,j):p\text{ prime},\
 \min(v_p(C_A),v_p(N_x))<j\le
 \max(v_p(C_A),v_p(N_x))\}.
$$

This is finite. If a layer belongs to $\mathscr J$, its marginal
lies between $\lambda(A)$ and $\lambda(x)$, with the appropriate
endpoint inclusion. Therefore every crossed layer satisfies

$$
|s_A r_{p,j}-1|\le h,\qquad
|r_{p,j}-\lambda(A)|\le h/s_A.
$$

In particular a layer tied at $\lambda(A)$ has zero benefit cost,
while a layer tied at $\lambda(x)$ is still inside the same weak band.
The bound does not require $N_x$ to be superabundant, GA1, GA2,
or optimal at its own-size price.

The classical layerwise benefit identity at the **own-size** price is

$$
\begin{aligned}
d_A(N_x)
&=M(\lambda(A))-W(N_x)+\lambda(A)A\\
&=\sum_{(p,j)\in\mathscr J}
       \log p\,|r_{p,j}-\lambda(A)|.
\end{aligned}
$$

TC.1 with parameter $a=A$ bounds the full weak-band resource by
$24Ah+32\sqrt A$. Since $\mathscr J$ is a subset of that band,

$$
\boxed{
0\le d_A(N_x)
\le\frac{24Ah^2+32\sqrt A\,h}{A\log A},\qquad
T_A d_A(N_x)\le24\sqrt A\,h^2+32h.
}
\tag{NPC1}
$$

This is a finite bound with an explicit hypothesis on the two actual
prices. It accounts for every changed prime-power layer.

For ACC4's unconditional family, $A\sim x$ and the mean-value theorem
for $y\log y$ gives $h=O(e^{-a\sqrt{\log x}})$. Consequently (NPC1)
gives the estimate used in ACC5: the first term is
$O(e^{-2a\sqrt{\log x}}/\log x)$, and the second is
$O(e^{-a\sqrt{\log x}}/(\sqrt x\log x))$, which is smaller.
The PNT and the constant $a$ are the same as in ACC4. The normalized
allowance still contains $O(\sqrt x e^{-2a\sqrt{\log x}})$;
its growth prevents this allowance from paying a root-scale defect
bound on the whole unconditional family. No lower bound on the
actual defect is inferred from that growth. The original signed
Robin integral remains unpaid.


### A conditional root-scale transfer for the same actual integers

Let $x$ range over any unbounded family of real prices for which

$$
\delta_x:=|A_x-x|=o(x^{3/4}).
\tag{NPC2}
$$

This condition implies $A_x\sim x$. The mean-value theorem for
$y\log y$ on the interval with endpoints $x,A_x$ gives
$h_x=O(\delta_x/x)$, with one common constant once
$A_x\in[x/2,2x]$. In particular the finite hypotheses of (NPC1)
hold eventually along the entire specified family, and

$$
0\le T_{A_x}d_{A_x}(N_x)
=O\!\left(\frac{\delta_x^2}{x^{3/2}}+
                 \frac{\delta_x}{x}\right)=o(1).
\tag{NPC3}
$$

There is no substitution of $x$ for the source's own clock $A_x$ in
the defect or its normalization. The exponent $3/4$ here comes from
the quadratic capacity allowance; it is a sufficient condition, not
a necessity or an optimal exponent.

Use KTO1's existing complete pressure identity and two-candidate
reserve at $A=A_x$:

$$
M(\lambda(A))
=\gamma+\log\log A-\frac1{\log A}-I_\psi(A)-R(A),
\qquad
T_AR(A)=c_R+O(1/\log A),\quad c_R=2(\sqrt2-1).
$$

Since $\lambda(A)\log N_x=1/\log A$, the same integer has the
exact margin account

$$
\Delta(N_x)=d_A(N_x)+I_\psi(A)+R(A),\qquad A=A_x.
$$

Thus (NPC2), with the cited reserve and capacity inputs, gives

$$
\boxed{
T_{A_x}\Delta(N_x)
=T_{A_x}I_\psi(A_x)+c_R+o(1).
}
\tag{NPC4}
$$

For example, on such a family a lower bound
$\liminf T_{A_x}I_\psi(A_x)>-c_R$ would imply eventual strict
Robin there; an upper bound
$\limsup T_{A_x}I_\psi(A_x)<-c_R$ would imply eventual violations
there. Neither signed premise is supplied. An asymptotic comparison
at equality with $-c_R$ does not decide strict Robin.

ACC4's unconditional PNT allowance does not imply (NPC2): its ratio
to $x^{3/4}$ grows. The existing full-real inventory normal form
$A_x=\psi(x)+(\sqrt2-1)\sqrt x+o(\sqrt x)$, cited in
[the workload note](../Analytic/mantovanelli2026primeworkload.md#the-full-real-normal-form-also-controls-strict-inventory-at-events),
identifies (NPC2) with $\psi(x)-x=o(x^{3/4})$ on this same family.
This gives a checkable condition on the actual prime error; it does
not establish that condition at every large price or at the unknown
counterexample-selected prices.

The finite upper benefit estimate and this conditional transfer reuse
the classical CA benefit, the already derived thin-layer capacity,
and the existing reserve and inventory normal form. No new signed
prime estimate or assumption of RH is introduced. The full original
same-source signed budget, strict Robin for every integer above 5040,
and RH remain unresolved; this application has no Lean verification.
