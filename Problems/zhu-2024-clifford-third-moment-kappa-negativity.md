---
slug: zhu-2024-clifford-third-moment-kappa-negativity
bibkey: zhu2024thirdmoments
doi: 10.48550/arXiv.2410.13575
url: https://arxiv.org/abs/2410.13575v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.result
---

# A negative Clifford third-moment expectation at dimension eleven

## Problem

H. Zhu, C. Mao and C. Yi, *Third moments of qudit Clifford orbits and 3-designs based on magic
orbits*, arXiv:2410.13575v1 (Commun. Math. Phys. 407, 242 (2026)), Conjecture 2: for an odd
prime $d$ and $|\Psi\rangle\in\mathcal H_d^{\otimes n}$, $0\le\kappa(\Psi,\mathcal T)\le1$ for every
stochastic Lagrangian subspace $\mathcal T\in\Sigma(d)$, together with three aggregate
inequalities that the authors derive from it. Here
$\kappa(\Psi,\mathcal T)=\operatorname{tr}[R(\mathcal T)(|\Psi\rangle\langle\Psi|)^{\otimes3}]$,
$R(\mathcal T)=r(\mathcal T)^{\otimes n}$ and $r(\mathcal T)=\sum_{(x;y)\in\mathcal T}|x\rangle\langle y|$.
The verbatim statements are in [the literature note](../Library/QuantumStates/zhu2024thirdmoments.md).

Issue [#14367](https://github.com/the-omega-institute/trureturing/issues/14367) targets the
pointwise clause for every odd prime $d$, every $n$, every normalized $\Psi$ and every
$\mathcal T\in\Sigma(d)$.

## Motivation

The coefficients $\kappa(\Psi,\mathcal T)$ expand the third moment operator of a Clifford orbit in
the commutant frame $\{R(\mathcal T)\}$; their nonnegativity would give the paper's conditional
bounds on shadow norms and on the aggregate sums.

## Gap

The authors prove $-1\le\kappa\le1$ (Lemma 20), the conjecture for $d=3$, $\kappa=1$ for stabilizer
states and nonnegativity for their cubic-phase families. Issue #14367 records the literature check
before any Lean: no later work exhibits a negative $\kappa$; `not-found-in-searched-scope`.

## Route

$d=11$, $n=1$, $\Psi=v/\sqrt{40}$ with
$v=(-2,0,-2i,1-2i,-1-i,1+2i,-1-2i,-2,-2i,2-i,1-i)$, and $\mathcal T=\{(Oy;y)\}$ with
$O=\begin{pmatrix}7&8&8\\8&7&8\\8&8&7\end{pmatrix}$ over $\mathbb F_{11}$ ($O^{\mathsf T}O=I$, $O\mathbf 1=\mathbf 1$).
Since $r(\mathcal T)$ maps $|y\rangle$ to $|Oy\rangle$, $\kappa(\Psi,\mathcal T)=40^{-3}\sum_y\prod_k
v_{y_k}\overline{v_{(Oy)_k}}=-1196/64000=-299/16000$.

## Falsifier

The refutation concerns the pointwise clause as printed (every $\mathcal T\in\Sigma(d)$); the
aggregate inequalities are a different statement and are not refuted here.

## Evidence

The canonical source is `D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.lean`, with public
`claim` and `result : ¬ claim`. The axiom closure of `result` is exactly `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry`, `native_decide` or new axiom.
The 1331-term Gaussian-integer sum is evaluated by kernel `decide`.
The module statement is `sha256:8532a0ef00a289544d8e4740ee71c4efe03920036ea636be7b7dca2fd58c007b`,
the `result` statement `sha256:9600966d695b68a10866e2785508ddc3c245fc3c18eea03ea3890f4af1b6ec75` and the
`claim` statement `sha256:f77b58eed855b84858dd3983d641a85311fc5b754f5dca40843b4a8ca26b0e25`. The Freeze
event is `sha256:6f1e7f1909bb5bd57dcbacf1b57dd272d84520dc0cf284c3de6f6235b4209edd`; it has no
project-level prerequisite (the module imports Mathlib only).

## Triage

Tier 1 conjecture of an October 2024 paper (kept in the 2026 CMP version), preregistered in issue
#14367 before any Lean. `theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

The private declarations (the subspace `T`, its membership criterion `mem_T`, `stochastic_T`, the
state `psi`, `norm_v`, `normalized_psi`, `gaussian_sum`, `kappa_T`, `kappa_psi`) are each used on
the proof of `result`; all are bind-only (instantiation, linear-algebra rewriting and
kernel-evaluated arithmetic). The settlement is admitted as an external open-problem resolution.

Utility is `kind=certified-instance; basis=refutes` (the claim and its refutation). There is no
digestion atom.

### What the refutation shows

**Proved by `result`:** the pointwise clause of Conjecture 2 fails at $d=11$, already for one
qudit: $\kappa(\Psi,\mathcal T)=-299/16000$.

**Computed, not formalized** (exact rational arithmetic over $\mathbb F_{11}$ and the Gaussian
integers).

- *Mechanism.* For $\mathcal T=\mathcal T_O$ the operator $r(\mathcal T)$ is the permutation
  $|y\rangle\mapsto|Oy\rangle$ of $\mathcal H_d^{\otimes3}$, so
  $\kappa(\Psi,\mathcal T_O)=\langle\Psi^{\otimes3}|r(\mathcal T_O)|\Psi^{\otimes3}\rangle$. For
  $O\in S_3$ it permutes tensor factors and $\kappa=1$; for a non-permutation $O$ it mixes the
  three coordinates of the computational basis, and the overlap of $\Psi^{\otimes3}$ with its
  image can be negative once the amplitudes are unequal.
- *All stochastic Lagrangian subspaces at $d=11$.* The stochastic orthogonal group $O_3(11)$ has
  24 elements, equal to $|\Sigma(11)|=2(11+1)$, so every $\mathcal T\in\Sigma(11)$ is a graph
  $\mathcal T_O$. For the state above the 24 values are $1$ (six permutations), $15763/64000$
  (twelve) and $-299/16000$ (six); all are real.
- *What survives.* For this state $\kappa(\Psi,\Sigma(11))=28299/3200\approx8.84\in[6,24]$,
  $\kappa(\Psi,\mathscr T_{ns})=28299/3200-6\approx2.84\in[0,18]$ and
  $\kappa(\Psi,\mathscr T_{iso})=28299/3200\ge6$: the three aggregate inequalities of Conjecture 2
  hold here, so the pointwise clause is not necessary for them.

**Open.** Whether the aggregate inequalities hold for every state, and whether the pointwise clause
holds for $d=5$ and $d=7$, are not determined here.

**Effect on the paper.** The derivation of the aggregate inequalities "thanks to Lemma 20" from the
pointwise clause no longer applies; the aggregate inequalities need a separate argument.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or
the absence of an independent proof.
