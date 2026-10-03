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
