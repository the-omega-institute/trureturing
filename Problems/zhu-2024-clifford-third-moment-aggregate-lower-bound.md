---
slug: zhu-2024-clifford-third-moment-aggregate-lower-bound
bibkey: zhu2024thirdmoments
doi: 10.48550/arXiv.2410.13575
url: https://arxiv.org/abs/2410.13575v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.result
---

# The isotropic aggregate of a two-qudit state in dimension five is below six

## Problem

H. Zhu, C. Mao and C. Yi, *Third moments of qudit Clifford orbits and 3-designs based on magic
orbits*, arXiv:2410.13575v1, Section VII.1, Conjecture 2, asserts for an odd prime $d$ and
$|\Psi\rangle\in\mathcal H_d^{\otimes n}$ the pointwise bounds $0\le\kappa(\Psi,\mathcal T)\le1$ on
$\Sigma(d)$ together with the aggregate bounds $6\le\kappa(\Psi,\Sigma(d))\le2d+2$,
$0\le\kappa(\Psi,\mathscr T_{\rm ns})\le2d-4$ and $\kappa(\Psi,\mathscr T_{\rm iso})\ge6$. Here
$\kappa(\Psi,\mathscr T)=\sum_{\mathcal T\in\mathscr T}\kappa(\Psi,\mathcal T)$ and
$\mathscr T_{\rm iso}=\{\mathcal T_O : O\in O_3(d)\}$. The verbatim statements are in
[the literature note](../Library/QuantumStates/zhu2024thirdmoments.md).

The pointwise clause was refuted earlier with one qudit at $d=11$
([dossier](zhu-2024-clifford-third-moment-kappa-negativity.md)); for that state the aggregate bounds
hold. Issue [#14561](https://github.com/the-omega-institute/trureturing/issues/14561) targets the
remaining aggregate lower bound in its printed form $\kappa(\Psi,\mathscr T_{\rm iso})\ge6$.

## Motivation

The paper derives the aggregate bounds from the pointwise clause and uses the aggregate sums for the
shadow norms of stabilizer projectors and for the third frame potential of Clifford orbits. With the
pointwise clause refuted, whether the aggregate lower bounds still hold decides whether those
consequences survive.

## Gap

The paper proves $4(D+d)/(D+1)\le\kappa(\Psi,\Sigma(d))$ with $D=d^n$, which is at least $6$ for one
qudit, and the upper bounds; the conjecture for $d=3$; and positivity for its cubic-phase
magic-state families. Issue #14561 records the literature check before any Lean: no later work
proves or refutes the aggregate lower bounds; `not-found-in-searched-scope`.

## Route

At $d=5$ the stochastic orthogonal group has twelve elements: the six permutation matrices and the
six row orders of the rows $(3,4,4)$, $(4,3,4)$, $(4,4,3)$. For a graph subspace,
$\kappa(\Psi,\mathcal T_O)=\sum_Y\prod_{k=1}^3\Psi(Y_k)\overline{\Psi((OY)_k)}$. Reordering the rows of
$O$ permutes the three copies and leaves $\kappa$ unchanged. For the two-qudit state $\Psi=v/\sqrt{458}$
of #14561, each permutation gives $\kappa=1$ and each other matrix gives $-2577430/458^3$, so
$\kappa(\Psi,\mathscr T_{\rm iso})=140241723/24017978<6$.

## Falsifier

An error in the identification of $O_3(5)$ or in the integer sum, or an intended reading of
$\mathscr T_{\rm iso}$ other than the graphs of $O_3(d)$. The positive controls $|00\rangle$ and the
uniform state give $\kappa(\Psi,\mathscr T_{\rm iso})=12$, as the paper's Proposition 4 requires for
stabilizer states.

## Evidence

The canonical source is `D5/S3/Quantum/Magic/CliffordThirdMomentAggregateRefutation.lean`, with
public `claim` and `result : ¬ claim`. The axiom closure of `result` is exactly `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry`, `native_decide` or new axiom. The module
statement is `sha256:65ed3998f4c2e42ef1bf54606f148acd70756738c1254765624f173ac568b6f5`, the `result`
statement `sha256:ab48ed35cda00d5b5ba176f1008985182fada677985722d41f50b46958fef103` and the `claim`
statement `sha256:ab9e4fef8616bd26d3d8aadc3b24de1f1b45f45c9af27f30edc00c309fdcb1e5`. The Freeze event is
`sha256:420c48b7e4e47288b70f3155f161e07c6d78f69dd72eb7aba429f4986d3d633c`; its one project-level
prerequisite is the frozen node `sha256:6f1e7f1909bb5bd57dcbacf1b57dd272d84520dc0cf284c3de6f6235b4209edd` of
`D5/S3/Quantum/Magic/CliffordThirdMomentNegativity`, whose `R`, `stateCube` and `kappa` the module
reuses.

## Triage

Tier 1 printed clause of an October 2024 conjecture (open after the pointwise refutation),
preregistered in issue #14561 before any Lean. `theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

The private declarations (the graph collapse for $n$ qudits, the row-order invariance, the
twelve-element description of $O_3(5)$, the normalized state, the integer slices of the
$15625$-term sum and the resulting values of $\kappa$) are each used on the proof of `result`.
All are bind-only: instantiation, reindexing and kernel-evaluated arithmetic. The settlement is
admitted as an external open-problem resolution.

Utility is `kind=certified-instance; basis=refutes` (the claim and its refutation). There is no
digestion atom.

### What the refutation shows

**Proved by `result`:** the aggregate lower bound $\kappa(\Psi,\mathscr T_{\rm iso})\ge6$ of
Conjecture 2 fails for a normalized two-qudit state at $d=5$.

**Argued, not formalized.**
- *The other aggregate lower bounds.* For $d\equiv2\pmod3$ every stochastic Lagrangian subspace is
  a graph (the paper; an exhaustive enumeration gives $|\Sigma(5)|=12$), so
  $\kappa(\Psi,\Sigma(5))=\kappa(\Psi,\mathscr T_{\rm iso})<6$. Since $\kappa=1$ on
  $\mathscr T_{\rm sym}$, also $\kappa(\Psi,\mathscr T_{\rm ns})=-3866145/24017978<0$. The pointwise
  clause fails at $d=5$ as well: each non-permutation value is negative.
- *Every $n\ge2$.* Graph expectations are multiplicative under tensor products and equal $1$ for a
  stabilizer state, so $\Psi\otimes|0\rangle^{\otimes(n-2)}$ has the same values.
- *Mechanism.* The proven bound $4(D+d)/(D+1)$ is at least $6$ only for one qudit. Numerical
  minimization finds no violation for one qudit at $d=3,5,7$ or for two qudits at $d=3$, and the
  minimum of $\kappa(\Psi,\mathscr T_{\rm ns})$ over two qudits at $d=5$ is numerically $-1/6$. Product
  states do not suffice: their numerical minimum of $\kappa(\Psi,\Sigma(5))$ is about $6.37$. The
  failure needs entanglement across the two qudits.

**Open.** Whether the aggregate lower bounds hold for two qudits at $d=7$ and higher primes, the
exact minimum of $\kappa(\Psi,\Sigma(d))$ for $n\ge2$, and how the paper's conditional consequences
for shadow norms change below $6$, are not determined here.

## ASSUMED-UNVERIFIED

The main text of the published Communications in Mathematical Physics version is subscription-gated
and was not read; that it prints Conjecture 2 unchanged is not verified firsthand. The bounded
literature check does not establish exhaustive worldwide novelty, priority, or the absence of an
independent refutation.
