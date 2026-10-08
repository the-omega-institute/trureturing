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
