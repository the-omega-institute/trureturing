---
bibkey: hircheguantomamichel2023renyicombining
authors: Christoph Hirche; Xinyue Guan; Marco Tomamichel
year: 2023
title: "Chain Rules for Rényi Information Combining"
doi: 10.1109/ISIT54713.2023.10206941
url: https://arxiv.org/abs/2305.02589v1
claim: "Conjecture V.5 asserts equality in both BSC-PSC branches at orders two and three for independent binary classical-quantum inputs; Proposition V.3, equation V.13, proves order two, and the remark after Proposition V.4 leaves the explicit order-three expression to be calculated."
strata_touched:
  - D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree
license: citation-only
triage: anchor
---

# Hirche, Guan and Tomamichel: Rényi information combining

## Verified locator

DOI: 10.1109/ISIT54713.2023.10206941

Source: https://arxiv.org/abs/2305.02589v1

The proceedings version appears in IEEE ISIT 2023, pp. 204–209. Page numbers below
refer to the arXiv v1 PDF.

## Definitions and source statements

Section IV, p. 4, defines the sandwiched conditional Rényi entropy:

$$
\widetilde H^\downarrow_\alpha(A|B)_\rho
=\frac{1}{1-\alpha}\log\operatorname{tr}
  \left(\rho_B^{\frac{1-\alpha}{2\alpha}}\rho_{AB}
  \rho_B^{\frac{1-\alpha}{2\alpha}}\right)^\alpha.
$$

The identity on the unconditioned system is implicit in the source's matrix
products. In Lean it is explicit, and powers use continuous functional calculus.
Negative powers vanish on the kernel and act as inverse powers on the support.
Logarithms are natural logarithms. Section IV describes quantum states as
“normalized positive semidefinite matrices”; the reused `IsDensity` is precisely
positive semidefiniteness and trace one.

Section V, p. 5, uses independent equiprobable binary inputs

$$
\rho^{X_iB_i}_i=\frac12|0\rangle\langle0|\otimes\sigma^{B_i}_0
+\frac12|1\rangle\langle1|\otimes\sigma^{B_i}_1.
$$

Its sentence introducing the combined state is:

> After applying a CNOT gate to the classical systems we have the joint state

$$
\tau^{(X_1+X_2)X_2B_1B_2}
=\sum_{z,x_2}\frac14|z\oplus x_2\rangle\langle z\oplus x_2|
\otimes|x_2\rangle\langle x_2|\otimes\sigma^{B_1}_z\otimes\sigma^{B_2}_{x_2}.
$$

`Fin 2` addition encodes XOR. The index ordering is
`((X1 + X2, X2), (B1, B2))`; `traceOutX2` sums over the second classical
index before evaluating the conditional entropy.

Conjecture V.5, Section V, p. 7, states:

> Let $H_1=\widetilde H_\alpha^\downarrow(X_1|B_1)_{\rho_1}$ and
> $H_2=\widetilde H_\alpha^\downarrow(X_2|B_2)_{\rho_2}$.
> For $\alpha\in(0,2]\cup[3,\infty)$,

$$
\widetilde H_\alpha^\downarrow(X_1+X_2|B_1B_2)_\tau\geq
\begin{cases}
h_\alpha(h_\alpha^{-1}(H_1)\ast h_\alpha^{-1}(H_2)),
&H_1+H_2\leq\log2,\\
H_1+H_2-\log2+
h_\alpha(h_\alpha^{-1}(\log2-H_1)\ast h_\alpha^{-1}(\log2-H_2)),
&H_1+H_2\geq\log2.
\end{cases}
$$

> For $\alpha\in[2,3]$ the same holds with $\geq$ exchanged by $\leq$ and
> for $\alpha\in\{2,3\}$ the above holds with equality.

Here $h_\alpha$ denotes binary Rényi entropy, its inverse is restricted to
probabilities in $[0,1/2]$, and $p\ast q=p(1-q)+(1-p)q$.
Page 2, before Theorem I.1, fixes the name:

> In the following, we denote the binary Rényi entropy as hα.

The Lean claim specializes only the equality clause at order three and includes
both branches, each with the printed guard. Both guards apply at the boundary.

## Neighbouring results and the order-three mechanism

Proposition V.3, equation (V.13), proves the order-two equality. It is cited here, not proved by
the order-three module. Expanding the square of the sandwiched blocks gives the
quadratic counterpart of the cubic calculation. Proposition V.4 gives the
corresponding equality for the dual entropy at order one half. The following
remark, p. 7, reads:

> We remark that an equality expressions such as the ones above should also hold
> in the case of $\alpha=3$, however calculating it explicitly seems more difficult.

The order-three proof uses $r=(\sigma_0+\sigma_1)/2$,
$A=r^{-1/3}\sigma_0r^{-1/3}/2$, $B=r^{-1/3}\sigma_1r^{-1/3}/2$,
$S=A+B$ and $D=A-B$. Cyclicity of the trace gives
$K=e^{-2H}=(1+3\operatorname{tr}(SD^2))/4$ and $S^3=r$.
For independent inputs the XOR moment is the product of their two moments,
including singular marginals. Thus

$$
H_{\mathrm{out}}=-\frac12\log
\frac{4K_1K_2-K_1-K_2+1}{3}.
$$

The module proves the two order-three branches for arbitrary finite dimensions;
it assumes neither commuting inputs nor full rank. The other-order inequality
clauses of Conjecture V.5 and possible closed forms at other integer orders
remain open. No change to the paper's independently proved chain rules is claimed.

## Numerical supporting evidence

The independent experiment entry is
[`docs/reports/hirche-guan-tomamichel-2023-renyi-order-three-xor/check.py`](https://github.com/the-omega-institute/trureturing-experiments/blob/7847a3ca3e7432801ff09b0db12c8d2b9ffa9616/docs/reports/hirche-guan-tomamichel-2023-renyi-order-three-xor/check.py)
in `the-omega-institute/trureturing-experiments`, at commit
`7847a3ca3e7432801ff09b0db12c8d2b9ffa9616`, SHA-256
`f5936cfa8d9def03e4c21033e0027d6b067ee06cb2528312df3b8a2ea43bf746`.
The supplied reading for `python3 check.py 7` is exit 0,
`trials=400 max_abs_err=1.343e-14`. It tests noncommuting and rank-deficient
inputs in dimensions one through four. This is numerical evidence, separate
from the Lean proof.
