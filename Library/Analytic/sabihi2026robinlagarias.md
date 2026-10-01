---
bibkey: sabihi2026robinlagarias
authors: Ahmad Sabihi
year: 2026
title: Robin inequality, Lagarias criterion, and Riemann hypothesis
doi: 10.33774/coe-2026-4mf39
url: https://arxiv.org/abs/1605.08273v14
claim: The v14 preprint claims an RH proof by combining Robin and Lagarias criteria with odd integer class-number sets; its key derivative-transfer proposition is false, so the claimed proof is not established.
strata_touched: []
license: citation-only
triage: audit
---

# Robin/Lagarias proof claim and its derivative-transfer gap

The source is [arXiv:1605.08273v14](https://arxiv.org/abs/1605.08273v14), submitted 9 February 2026, and is also deposited as [10.33774/coe-2026-4mf39](https://doi.org/10.33774/coe-2026-4mf39). The Cambridge record states that the manuscript is not peer reviewed. It partitions the integers into a finite computer-checked range and odd integer class-number sets, then claims Robin and Lagarias inequalities on every remaining class.

## The key proposition is false as stated

Proposition 1 claims that, under positivity, differentiability, fixed sign and the absence of oscillation, $f=O(g)$ together with $g'>0$ implies $f'=O(g')$. Monotonicity does not permit this derivative transfer. Let $\phi$ be a nonnegative $C^1$ bump supported in $(-1/2,1/2)$ with $\phi(0)=1$, and set

$$
k(x)=\sum_{n\ge1}n^2\phi\bigl(n^4(x-n)\bigr),
\qquad
h(x)=\int_0^x k(t)\,dt,
$$

where the supports are disjoint. The integral of the $n$-th spike is $O(n^{-2})$, so $h$ is bounded and increasing, while $k=h'$ is unbounded. With $g(x)=x$ and $f(x)=x+h(x)$, both functions are nonnegative, increasing, differentiable, and have no sign change or oscillation in the ordinary monotone sense; $f=O(g)$, but

$$
f'(x)=1+k(x)
$$

is not $O(g'(x))=O(1)$. Thus the proposition cannot justify the derivative estimate used later.

## Consequence for the manuscript's Robin route

The proof of Lemma 9 applies this proposition to a prime-counting asymptotic and writes an estimate for $\pi'(x)$. The prime-counting function is a step function, and differentiating an $O$-term is not valid without an independent differentiable remainder estimate. Therefore the stated proof of the strict monotonicity of $RO_1$ is incomplete. Later large-number arguments cite Lemma 9 (and its consequences), so the manuscript does not establish its claimed all $n$ Robin inequality or RH proof.

This audit does not assert that the stated Robin or Lagarias criteria are false; it identifies a failure in this proposed proof. It also does not create a FIB/RH bridge: the manuscript works directly with ordinary prime products and the divisor sum, without transporting those quantities to the project's $N_g=1+F_rg$ family.
