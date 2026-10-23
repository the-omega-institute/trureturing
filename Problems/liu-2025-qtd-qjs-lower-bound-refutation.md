---
slug: liu-2025-qtd-qjs-lower-bound-refutation
bibkey: liu2025quantumtriangular
doi: 10.48550/arXiv.2303.01952
url: https://arxiv.org/abs/2303.01952v5
triage: theorem
motivation_gids:
  - D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.result
---

# QTD squared can exceed base-2 quantum Jensen–Shannon divergence

## Problem

Yupan Liu, *Quantum state testing beyond the polarizing regime and quantum triangular discrimination*, arXiv:2303.01952v5, §1.3, “Improved inequalities on the quantum triangular discrimination”, printed p. 7, states:

> We observe that Theorem 1.4(ii) is not tight. Numerical simulations indicate that the tight bound is QTD²(ρ₀, ρ₁) ≤ QJS₂(ρ₀, ρ₁) ≤ QTD(ρ₀, ρ₁) for any states ρ₀ and ρ₁.

After Theorem 3.4:

> Numerical simulations suggest that the tight bound is QTD²(ρ₀, ρ₁) ≤ QJS₂(ρ₀, ρ₁) ≤ QTD(ρ₀, ρ₁), while we only managed to prove a slightly weaker bound ½QTD²(ρ₀, ρ₁) ≤ QJS₂(ρ₀, ρ₁) ≤ QTD(ρ₀, ρ₁) in Theorem 3.4.

The paper was published in *Computational Complexity* 34 (2025), article 11. Definition 3.1 specifies the inverse square root on the support. Definition 2.10 defines QJS by the entropy of the average minus the average entropy; QJS₂ uses base-2 logarithms.

## Motivation

The proposed lower inequality strengthens the factor-½ lower bound of Theorem 3.4. Commuting states allow exact evaluation without ambiguity about noncommuting matrix products or inverses on singular supports.

## Gap

The lower conjunct asserts $\operatorname{QTD}(\rho,\sigma)^2\le\operatorname{QJS}_2(\rho,\sigma)$ for every pair of states. A full-rank diagonal qubit pair suffices to test this assertion within the classical subclass.

## Route

Let $a=1/256$, $\rho=\operatorname{diag}(1-a,a)$ and $\sigma=\operatorname{diag}(a,1-a)$. Both matrices are positive semidefinite with unit trace. Their sum is the identity, so its inverse square root is also the identity. Writing

$$
h(a)=-a\log_2 a-(1-a)\log_2(1-a),
$$

the two divergences are

$$
Q_a=(1-2a)^2=(127/128)^2,\qquad J_a=1-h(a).
$$

The continuous functional calculus on a real diagonal complex matrix applies the scalar function to each diagonal entry. Thus these are evaluations of the matrix definitions, rather than replacement scalar definitions.

## Falsifier

Since $\log_2(1/256)=-8$ and $\log_2(255/256)<0$, we have $h(1/256)\ge1/32$. Consequently,

$$
J_a\le31/32<(127/128)^4=Q_a^2,
\qquad Q_a^2-J_a\ge\frac{97793}{268435456}>0.
$$

Both eigenvalues of each state are strictly positive; singular-support conventions do not affect the counterexample.

## Evidence

`D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.lean` defines `IsState`, `vonNeumann2`, `QJS2`, `QTD`, and `claim`, with the designated theorem `result : ¬ claim`. All supporting definitions and lemmas are private. The proof evaluates Mathlib's real continuous functional calculus on complex diagonal matrices, verifies the two state predicates, computes QTD exactly, and bounds QJS₂ using exact logarithm identities and inequalities.

The theorem uses only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`, with no `sorry` or additional axiom. The asymptotic consequences below are mathematical reasoning, not additional Lean theorems in this module.

## Triage

### What the settlement shows

1. **Proved (Lean) — the proposed lower inequality fails.** The displayed full-rank commuting qubit pair refutes $\operatorname{QTD}^2\le\operatorname{QJS}_2$ with a positive rational margin.

2. **Reasoning — no fixed positive power repairs the lower inequality.** For $0<a<1/2$, the same family has $Q_a=(1-2a)^2$ and $J_a=1-h(a)$, and

   $$
   \frac{1-J_a}{1-Q_a}=\frac{h(a)}{4a(1-a)}\longrightarrow\infty\quad(a\to0^+).
   $$

   Indeed $h(a)\ge-a\log_2 a$, so this ratio is at least $-\log_2 a/[4(1-a)]$. For every fixed $p>0$, $(1-Q^p)/(1-Q)\to p$ as $Q\to1^-$. Hence $Q_a^p>J_a$ for sufficiently small positive $a$.

3. **Reasoning — a locally Lipschitz endpoint function also fails.** If $F(1)=1$ and $F$ is locally Lipschitz at 1, then $1-F(Q_a)\le L(1-Q_a)$ near 1 for some finite $L$. The diverging ratio gives $1-J_a>L(1-Q_a)$, whence $F(Q_a)>J_a$. Thus no such $F$ satisfies $F(Q)\le J$ for all states. The obstruction is the logarithmic entropy deficit near orthogonal supports and already occurs for commuting, classical states.

4. **Not addressed — neighboring assertions.** The upper conjunct $\operatorname{QJS}_2\le\operatorname{QTD}$ and the metric conjecture for $\sqrt{\operatorname{QTD}}$ are not settled here.

5. **Literature note.** The classical joint range of triangular discrimination and Jensen–Shannon divergence was not checked against this specific claim. No novelty or priority conclusion follows from this refutation.

## ASSUMED-UNVERIFIED

The asymptotic power and locally Lipschitz consequences are not separately formalized. The classical joint-range literature has not been checked against this claim.
