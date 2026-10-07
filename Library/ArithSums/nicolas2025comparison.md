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

Fiori–Jaskari, *Explicit bounds for the prime number theorem*, [arXiv:2609.23222v1](https://arxiv.org/abs/2609.23222v1), Theorem 1.1 and Table 1, state for $u\ge e^3$ that

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
A selected counterexample would instead have to satisfy
$\sqrt A\log A\,I_\psi(A)<-\mathcal E(\log A)$.
The new allowance is weaker as a tail requirement than the existing
$-D_{\rm lb}(A)$ requirement; neither signed tail bound has been proved.
The full integral over $[A,\infty)$ remains in (G9).
This paper-level improvement does not prove RH, and finite source
checks and source inspection do not certify its external premises.

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
