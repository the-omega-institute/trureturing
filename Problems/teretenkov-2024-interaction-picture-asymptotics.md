---
slug: teretenkov-2024-interaction-picture-asymptotics
bibkey: madouremizovvafadar2024semigroups
doi: 10.48550/arXiv.2410.00416
url: https://arxiv.org/abs/2410.00416v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.result
---

# Interaction-picture asymptotics

## Problem

F. Madou, I. Remizov, M. Vafadar (eds.), *Open problems in one-parameter operator semigroups theory*, arXiv:2410.00416v2, p. 21, Problem 29 (A. E. Teretenkov), state verbatim:

> Problem 29 (A.E. Teretenkov). Let B be a Banach space. Let P be a projection on a finite-dimensional Banach subspace of B. Let L0 + λL be a generator of C0-semigroup U^λ_t on B for all λ ∈ [0, λsup). Let U^0_t leave both PB and its complement (I − P)B invariant, let PLP = 0. Denote L_t ≡ (U^0_t)^{−1} L U^0_t. Let the integrals ∫_{−∞}^{t} dt_1 … ∫_{−∞}^{t_{k−1}} dt_k P L_{t_1} … L_{t_k} P, k = 1, …, n + 1 be finite for all t ⩾ 0. If is it possible to find such a λ-dependent operator r^{n,λ} on PB, which is polynomial in λ, and λ-dependent semigroup u^{n,λ}_t on PB, whose generator is polynomial in λ, such that P(U^0_{t/λ²})^{−1} U^λ_{t/λ²} P = u^{n,λ}_t r^{n,λ} + O(λ^{2n+2}), λ → +0 for all t > 0 ? Let us emphasize that we do not assume here asymptotic behaviour to be uniform in t, it is just assumed for each fixed t > 0. If there are counterexamples, what further restrictions should be assumed to obtain such an asymptotic estimate?

## Motivation

The problem concerns perturbative corrections to Markovian quantum master equations and generalization of E. B. Davies' weak-coupling results. It asks whether finiteness of past interaction integrals suffices for a polynomial preparation and polynomial-generator semigroup approximation on the weak-coupling time scale $t/\lambda^2$.

## Gap

The problem list keeps Problem 29 open and asks both for counterexamples and for restrictions restoring the estimate. Its first question is refuted by the finite-dimensional instance below; sufficient additional restrictions are not settled by this result. The source's presentation does not establish novelty outside the list.

## Route

Take $B=\mathbb C^3$ with the sup norm, $L_0=D$, $L=N$, and

$$
P=\operatorname{diag}(1,0,1),\qquad
D=\operatorname{diag}(-3,-2,-1),\qquad
N=E_{12}+E_{23},\qquad E=N^2=E_{13}.
$$

Here $E_{ij}$ uses one-based coordinates. Bounded matrix generators give $C_0$-semigroups $U_s^\lambda=e^{s(D+\lambda N)}$ for every real $\lambda$. The free evolution $U_s^0=e^{sD}$ is a group. The relations $P^2=P$, $DP=PD$, and $PNP=0$ give a rank-two projection, invariance of both summands, and the source condition $PLP=0$.

The interaction-picture coupling is

$$
L_s=e^{-sD}Ne^{sD}=e^sN.
$$

Consequently $PL_sP=0$ and $PL_{s_1}L_{s_2}P=e^{s_1+s_2}E$. The inner and outer integrals are

$$
\int_{-\infty}^{s_1}PL_{s_1}L_{s_2}P\,ds_2=e^{2s_1}E,\qquad
\int_{-\infty}^{t}e^{2s_1}E\,ds_1=\tfrac12e^{2t}E.
$$

These are Lebesgue integrals, with integrable integrands for every real endpoint, which is stronger than the source's restriction to $t\ge0$. Thus the order-one hypotheses hold. The exact interaction-picture formula is

$$
e^{-sD}e^{s(D+\lambda N)}
=I+\lambda(e^s-1)N+\frac{\lambda^2}{2}(e^s-1)^2E.
$$

Projection removes the linear term. The Lean module establishes the projected $(1,3)$ entry needed for the contradiction; the full displayed matrix identity and the finite-dimensional semigroup correspondence are exact mathematical reasoning.

## Falsifier

For each fixed $t>0$ and $\lambda>0$, the projected $(1,3)$ entry at $s=t/\lambda^2$ satisfies

$$
\frac{\lambda^2}{2}(e^{t/\lambda^2}-1)^2
\ge\frac{t^2}{2\lambda^2}\longrightarrow+\infty.
$$

The inequality follows from $e^x-1\ge x$ for $x\ge0$. Every candidate $e^{tG(\lambda)}R(\lambda)$ with matrix polynomials $G,R$ is continuous at $\lambda=0$ and hence bounded near zero. An error bounded by $C\lambda^4$ cannot reconcile these bounds. The Lean contradiction uses the single fixed time $t=1$, so no uniformity in $t$ is needed.

Operators on $PB$ embed as matrices supported on the projected subspace. If $G=PGP$ and $R=PRP$, then the full matrix exponential $e^{tG}R$ equals the embedded semigroup on $PB$ times its preparation. Allowing arbitrary $3\times3$ coefficient matrices therefore enlarges the class of approximants; refuting this larger class refutes the source's class as well.

## Evidence

The public declarations in `D5/S3/Quantum/Semigroups/InteractionPictureAsymptotics.lean` are `M3`, `coupling`, `Hyp`, `Expansion`, `claim`, and `result`. The matrices `P`, `D`, `N`, `E`, the change-of-basis matrices `S`, `T`, and supporting lemmas are private.

`M3` is `Matrix (Fin 3) (Fin 3) ℂ`. The matrix norm in the estimate is the entrywise sup norm. `coupling D N s` is $e^{-sD}Ne^{sD}$. `Hyp P D N` asserts $P^2=P$, $DP=PD$, $PNP=0$, integrability of the first projected integrand on $(-\infty,t]$, integrability of each second inner integrand on $(-\infty,s_1]$, and integrability of the resulting inner integral as a function of $s_1$ on $(-\infty,t]$, for every real $t$.

`Expansion P D N` asserts that there exist $m:\mathbb N$ and coefficient families $R,G:\mathrm{Fin}\,m\to\mathrm{M3}$ such that for every $t>0$ there exist real $C,\delta$ with $\delta>0$ and, for every $0<\lambda<\delta$,

$$
\left\|Pe^{-(t/\lambda^2)D}e^{(t/\lambda^2)(D+\lambda N)}P
-e^{t\sum_{j<m}\lambda^jG_j}\sum_{j<m}\lambda^jR_j\right\|
\le C\lambda^4.
$$

The degree bound $m$ is arbitrary and fixed independently of $\lambda$ and $t$; different polynomial degrees can be padded with zero coefficients. The constants $C,\delta$ may depend on $t$, and no separate positivity condition is imposed on $C$. The formal order is $n=1$.

`claim` is $\forall P,D,N:\mathrm{M3},\ \mathrm{Hyp}(P,D,N)\Rightarrow\mathrm{Expansion}(P,D,N)$. `coupling_formula`, `projection_algebra`, `first_integrand`, `second_integrand`, `inner_integral`, and `hypotheses` establish the instance's hypotheses. `ST`, `conjugate`, `exp_D`, and `exp_perturbed` give the exponential calculation used by `projected_entry`. `entry_norm_le` and `growth` turn that entry into the lower bound $1\le2\lambda^2\|Pe^{-D/\lambda^2}e^{(D+\lambda N)/\lambda^2}P\|$. `polynomial_continuous` and `locally_bounded` bound the approximant near zero. `no_expansion` contradicts the error estimate at $t=1$. The theorem `D5.S3.Quantum.Semigroups.InteractionPictureAsymptotics.result` has type `¬ claim`.

The module's axiom closure is $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$, with no `sorry` or additional axiom. Identification of bounded matrices with generators on $\mathbb C^3$, invariance of the two summands, and embedding operators on $PB$ explain the correspondence with the source; the formal predicates are the matrix conditions above.

## Triage

### What the settlement shows

1. **Proved (Lean) — the counterexample at $n=1$.** The $3\times3$ instance satisfies `Hyp` and admits no `Expansion`, even with arbitrary matrix polynomial coefficients. Via the finite-dimensional correspondence, the first question of Problem 29 has a negative answer.

2. **Computed (exact mathematical reasoning) — higher orders.** Since $L_s=e^sN$ and $N^3=0$, all projected products with three or more interactions vanish. The same instance satisfies the source's integrability assumptions for every $n\ge2$. An $O(\lambda^{2n+2})$ error would imply an $O(\lambda^4)$ error for $0<\lambda<1$, contradicting the order-one result. This extension is not formalized in the module.

3. **Computed (exact mathematical reasoning) — the mechanism.** The free evolution contracts exponentially, while its inverse amplifies the interaction-picture coupling to $e^sN$. Finiteness of past integrals at each fixed endpoint supplies no bound at endpoints $t/\lambda^2\to\infty$. The projected quadratic term diverges at each fixed positive rescaled time.

4. **Open — sufficient restrictions, the second question of Problem 29.** Requiring $U_s^0$ on $(I-P)B$ to be isometric, or uniformly bounded with uniformly bounded inverse for $s\ge0$, excludes this example: on that complement $U_s^0=e^{-2s}I$ and its inverse has norm $e^{2s}$. Whether either restriction suffices for the desired asymptotic estimate, with the other source hypotheses, is not settled by this result. These are candidate restrictions, not sufficient conditions proved here.

## ASSUMED-UNVERIFIED

The connection to Teretenkov's motivating physics literature (arXiv:2008.02820) and Davies' weak-coupling literature is limited to titles and abstracts. Their detailed hypotheses, estimates, and applicability to this counterexample are ASSUMED-UNVERIFIED. No theorem from those works is used to establish the matrix refutation.

Whether the observation is known outside the problem list is unverified; no literature priority is established. The quotation binds to arXiv:2410.00416v2, p. 21, Problem 29. The full matrix identity, finite-dimensional source correspondence, and $n\ge2$ extension are exact mathematical reasoning, rather than additional statements of the Lean module. Sufficiency of the proposed restrictions is not settled by this result.
