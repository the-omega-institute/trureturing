---
bibkey: simnacher2021separable
authors: Timo Simnacher; Jakub Czartowski; Konrad Szymański; Karol Życzkowski
year: 2021
title: "Confident entanglement detection via the separable numerical range"
doi: 10.1103/PhysRevA.104.042420
url: https://arxiv.org/abs/2107.04365v1
claim: "For Hermitian A_1, ..., A_k the restricted numerical range L_X(A_1, ..., A_k) is the set of vectors (Tr rho A_1, ..., Tr rho A_k) over states rho in X; L is the numerical range over all states and L_Sep the separable numerical range. The minimal volume ratio mu_{n,d,k} is the minimum over A_1, ..., A_k of vol L_Sep / vol L (Definition 2). Proposition 7 proves mu_{2,1} >= sqrt(2) - 1, and Conjecture 8 states that for a single measurement on a two-qubit system the minimal volume ratio is mu_{2,1} = 1/2, which the projector onto (|00> + |11>)/sqrt(2) attains."
strata_touched:
  - D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio
license: citation-only
triage: anchor
---

# Confident entanglement detection via the separable numerical range

Timo Simnacher, Jakub Czartowski, Konrad Szymański, Karol Życzkowski,
Phys. Rev. A 104, 042420 (2021), arXiv:2107.04365v1 (quant-ph). Quotations
are from the arXiv v1 source.

Definition 1:

> Let $A_1,\dots,A_k$ be Hermitian operators.
> Then, the set

followed by the display
$L_X(A_1,\dots,A_k) = \{ (\trace\rho A_1, \dots, \trace\rho A_k) \in \dR^k \,|\, \rho \in X \}$,
and

> is called the \textit{joint (restricted) numerical range} of $A_1,\dots,A_k$ where the set $X$ restricts the accessible states.
> If $X$ is the set of all quantum states, $L$ is simply the (joint) numerical range of $A_1,\dots,A_k$;
> if it is the set of all separable quantum states, $L_\Sep$ is called the separable (joint) numerical range of $A_1,\dots,A_k$.

The next sentence:

> Furthermore, the Euclidean volume of $L_X(A_1,\dots,A_k)$ is denoted by $\vol L_X$.

Definition 2:

> For $k$ independent measurements on a quantum system consisting of $n$ particles and local dimensions $\bm{d} = (d_1,\dots,d_n)$, we denote the minimal volume ratio of the separable numerical range compared to the standard numerical range as

followed by the display
$\mu_{n,\bm{d},k} = \min_{A_1,\dots,A_k} \frac{\vol L_\Sep(A_1,\dots,A_k)}{\vol L(A_1,\dots,A_k)}$,
and

> If $d_1 = \dots = d_n = d$, we just write $d$ instead of $\bm{d}$.
> Further, if $n=2$, we omit the corresponding subscript.

Proposition 7:

> It holds that $\mu_{2,1} \ge \sqrt{2} - 1 \approx 0.41$. Moreover, this is the best bound achievable when only absolutely separable states are considered.

Conjecture 8:

> For a single measurement on a two-qubit system, the minimal volume ratio is $\mu_{2,1} = \frac{1}{2}$.

The sentences after it:

> This value is for example reached by $A = \ket{\phi^+}\bra{\phi^+}$ with eigenvalues 0 and 1, being the projector onto the maximally entangled state $\ket{\phi^+} = \frac{1}{\sqrt{2}}(\ket{00}+\ket{11})$.

and

> Thus, it follows that $\mu_{2,1} \le \frac{1}{2}$.

The encoding reads a two-qubit state as a positive semidefinite matrix of
trace $1$ indexed by `Fin 2 × Fin 2`, a separable state as a finite sum of
Kronecker products of positive semidefinite $2\times2$ factors with trace
$1$, the Euclidean volume of a subset of $\mathbb R$ as its Lebesgue
measure, and the minimum as the least element of the set of ratios over
Hermitian $A$ with $\operatorname{vol} L(A)\ne0$ (for scalar $A$ both
volumes vanish).

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevA.104.042420 (Phys. Rev. A 104,
  042420, published 2021-10-25).
- URL: https://arxiv.org/abs/2107.04365v1 (the only version, 2021-07-09;
  source `SNRJNRratio.tex`, md5 `9de8e3a2899bc229ba5e7fa6140ca52f`):
  Definition 1 (l. 153–162), the volume sentence (l. 163), Definition 2
  (l. 199–207), Proposition 7 (l. 308–310), Conjecture 8 (l. 312–315), the
  Bell-projector bound (l. 316–318) and the conclusion (l. 521). The theorem
  environments share one counter, which numbers the conjecture 8.
