---
slug: li-luo-zhang-2025-fisher-discord-partial-trace-refutation
bibkey: liluozhang2025fisherdiscord
doi: 10.1103/6kv3-hr92
url: https://arxiv.org/abs/2510.15375v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/FisherDiscord/Result.result
---

# Partial trace can increase Fisher discord

## Problem

H. Li, S. Luo and Y. Zhang, *Fisher discord as a quantifier of quantum
complexity*, arXiv:2510.15375v1; published as *Fisher discord as a quantifier
of quantum metrological complexity*, Phys. Rev. A 114, 032449 (2026).

§VI (Summary), verbatim:

> Both the quantum Fisher information based on the symmetric logarithmic derivative and the skew information does not increase under the partial traces, that is, I_F(ρ₁₂, H ⊗ 1) ≥ I_F(ρ₁, H), I_W(ρ₁₂, H ⊗ 1) ≥ I_W(ρ₁, H) … It is natural to consider such an open question: Whether quantum Fisher discord C(ρ₁₂, H ⊗ 1) = I_F(ρ₁₂, H ⊗ 1) − I_W(ρ₁₂, H ⊗ 1) for bipartite states does not increase under the partial trace.

| Source object | Formal reading |
|---|---|
| Density matrix | A positive semidefinite finite complex matrix of trace one, `Defs.IsDensity`. |
| Second-factor partial trace | `Defs.partialTrace₂ ρ i j = ∑ b, ρ (i,b) (j,b)`. |
| Local observable | Hermitian `H`, lifted as `Defs.liftLeft H = H ⊗ 1`. |
| Equation (6) | `Defs.IsSLD ρ H L`: Hermitian `L` with $i[\rho,H]=(L\rho+\rho L)/2$; `Defs.fisherSLD ρ L` is $\tfrac14\operatorname{Re}\operatorname{tr}(\rho L^2)$. |
| Equation (7) | `Defs.skewWY ρ H` is $-\tfrac12\operatorname{Re}\operatorname{tr}[\sqrt\rho,H]^2$, with the positive matrix square root. |
| Equation (10) | $C=I_F-I_W$, expressed as the difference of those two real quantities. |
| Universal comparison | `Defs.claim` quantifies over both finite dimensions, every joint density matrix, every Hermitian local observable and every Hermitian SLD solution on both spaces, and requires $C(\operatorname{tr}_2\rho,H)\le C(\rho,H\otimes1)$. |

## Motivation

Separate monotonicity of two information quantities does not imply monotonicity
of their difference. Classical flags isolate this distinction without
entanglement or numerical approximation.

## Gap

The comparison asserts an inequality for every extension of every marginal.
A diagonal two-level marginal with positive discord has a classical flag
extension of zero discord. This contradicts the proposed inequality.

## Route

In an eigenbasis with nonnegative eigenvalues $\lambda_i$, every Hermitian
SLD solution gives

$$
I_F=\frac12\sum_{i,j}\frac{(\lambda_i-\lambda_j)^2}{\lambda_i+\lambda_j}|H_{ij}|^2,
\qquad
I_W=\frac12\sum_{i,j}(\sqrt{\lambda_i}-\sqrt{\lambda_j})^2|H_{ij}|^2.
$$

The joint-zero-eigenvalue term is zero. Subtraction gives

$$
C=\frac12\sum_{i,j}c(\lambda_i,\lambda_j)|H_{ij}|^2,
\qquad
c(a,b)=\frac{2\sqrt{ab}(\sqrt a-\sqrt b)^2}{a+b}\ge0.
$$

For a normalized nonnegative diagonal $\rho=\operatorname{diag}(w)$, put
$\Omega=\sum_iw_i|i,i\rangle\langle i,i|$. Its marginal is $\rho$.
The lifted observable connects only equal flag coordinates. Between two
positive-weight support vectors this forces equal vectors, and a term with
a zero weight has $c(a,0)=0$. Thus $C(\Omega,H\otimes1)=0$ for every SLD.
Nonnegativity for arbitrary positive semidefinite matrices gives the converse:
zero marginal discord implies the inequality against every extension.

Take $p=1/5$, $q=4/5$, $\rho=\operatorname{diag}(p,q)$ and
$H=X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$. Then

$$
C(\rho,X)=2\sqrt{pq}-4pq=\frac45-\frac{16}{25}=\frac4{25}.
$$

SLD existence is explicit. The marginal solution is
$L=\begin{pmatrix}0&-6i/5\\6i/5&0\end{pmatrix}$.
In product-basis order $00,01,10,11$, a joint solution is

$$
L_{12}=\begin{pmatrix}
0&0&2i&0\\
0&0&0&-2i\\
-2i&0&0&0\\
0&2i&0&0
\end{pmatrix}.
$$

The spectral identities show that the two discord values hold for every
Hermitian solution, including freedom on a joint kernel.

## Falsifier

The joint state $\Omega=p|00\rangle\langle00|+q|11\rangle\langle11|$ is a
density matrix with marginal $\rho$. For every Hermitian SLD solution on
either space,

$$
C(\Omega,X\otimes1)=0<\frac4{25}=C(\rho,X).
$$

## Evidence

The result GID is `D5/S3/Quantum/Information/FisherDiscord/Result.result`.
It has the unconditional type `¬ Defs.claim`. Its principal dependencies are
`Extension.monotone_discord_zero`, `Extension.flag_partialTrace`,
`Extension.flag_discord_zero`, `Spectral.discord_diag`,
`Spectral.discord_spectral` and `Spectral.discord_nonneg`.
The marginal evaluation applies to arbitrary SLD solutions; explicit
solutions supply existence. The compiled axiom closure consists only of
`propext`, `Classical.choice` and `Quot.sound`.

The proof route was derived with the assistance of the ChatGPT Pro model.
The source proves separate partial-trace monotonicity of $I_F$ and $I_W$,
positivity of $C$, pure-state vanishing and direct-sum additivity, and leaves
partial-trace monotonicity of the difference open. No settlement was found
in the searched scope covering the identifier, both titles and Fisher
discord with partial trace, monotonicity and counterexample. Citation-index
coverage is not exhaustive; this is no assertion that every later work
has been excluded.

## Triage

### What the settlement shows

1. **PROVED — the counterexample.**
   `D5/S3/Quantum/Information/FisherDiscord/Result.result` refutes the universal
   comparison through the diagonal-marginal necessary condition. At $p=1/5$,
   $C(\Omega,X\otimes1)=0<4/25=C(\rho,X)$ for every Hermitian SLD solution;
   explicit solutions exist on both spaces.

2. **PROVED — the spectral formula.**
   `D5/S3/Quantum/Information/FisherDiscord/Spectral.discord_spectral`
   gives $C=\tfrac12\sum_{i,j}c(\lambda_i,\lambda_j)|H_{ij}|^2$ for every
   finite positive semidefinite complex matrix, Hermitian observable and
   Hermitian SLD solution. `pairKernel_nonneg` proves $c\ge0$.
   `fisherSLD_diag`, `skewWY_diag`, `fisherSLD_spectral` and `skewWY_spectral`
   provide the component formulas in diagonal and general eigenbases.

3. **PROVED — flagged-extension necessary condition.**
   `D5/S3/Quantum/Information/FisherDiscord/Extension.monotone_discord_zero`
   covers normalized nonnegative diagonal marginals of every finite size,
   a Hermitian observable, a marginal SLD and an SLD existence witness for
   the flag extension. Within this scope, the inequality against every
   finite extension and every joint SLD forces marginal discord to be zero.
   Extension states may be arbitrary density matrices.
   The explicit two-qubit solution above discharges the existence premise
   for the counterexample. General nondiagonal marginal classification is
   not an additional Lean conclusion here.

4. **PROVED in prose — the support zero criterion.**
   Let $P$ be the support projection. The nonnegative spectral sum vanishes
   exactly when $H_{ij}=0$ for every pair of unequal positive eigenvalues:
   its coefficient is strictly positive exactly when
   $\lambda_i,\lambda_j>0$ and $\lambda_i\ne\lambda_j$.
   In the same basis,
   $[\rho,PHP]_{ij}=(\lambda_i-\lambda_j)
   \mathbf1_{\lambda_i>0}\mathbf1_{\lambda_j>0}H_{ij}$.
   Therefore $C(\rho,H)=0$ if and only if $[\rho,PHP]=0$.
   This zero criterion is not separately formalized.

5. **COMPUTED — exact value.**
   $\sqrt{pq}=2/5$ at $p=1/5$, so the marginal value is exactly $4/25$;
   the decimal $0.16$ is only its finite decimal representation.

6. **OPEN — further comparisons.**
   Whether $C(\rho_{12},H\otimes1)-C(\rho_1,H)$ has a useful lower bound
   vanishing on product states, or monotonicity holds for restricted
   classes such as extensions with full-rank marginal pinned to a product
   structure, are directions for further study. No such bound or
   restricted monotonicity theorem is asserted here.

## ASSUMED-UNVERIFIED

The support-projection zero criterion is proved in prose, not as a separate
Lean theorem. The Lean classification has a diagonal marginal and an
explicit flag-SLD existence premise. No general nondiagonal-marginal
classification, exhaustive citation-index survey or restricted comparison
is claimed.
