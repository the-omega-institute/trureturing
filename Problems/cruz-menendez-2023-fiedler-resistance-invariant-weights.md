---
slug: cruz-menendez-2023-fiedler-resistance-invariant-weights
bibkey: cruzortegamenendezconde2023fiedlerresistance
doi: 10.15381/pesquimat.v26i2.24218
url: https://arxiv.org/abs/2306.08187v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.result
---

# Refutation of the fixed-resistance Fiedler invariance conjecture

## Problem

Cruz Ortega and Menéndez-Conde, *Conectividad algebraica máxima para caminos con resistencia total fija*, arXiv:2306.08187v1 and *Pesquimat* 26(2) (2023), Section 5, define

$$
\breve a(G)=\max\{\lambda_2(G;\omega)\mid R(G;\omega)=R(G)\}
$$

and conjecture that the maximum is always attained by edge weights invariant under graph automorphisms. Issue #15242 records the literal source statement, the $K_{2,m}$ route and the Lean conventions.

## Motivation

The source proves the constrained optimum for $P_3$ and $P_4$ and leaves the graph-wide invariance assertion as a conjecture. The preregistration asks whether an asymmetric weighting of $K_{2,m}$ can preserve total resistance while increasing algebraic connectivity, and whether automorphism invariance then forces the unweighted assignment.

## Gap

The target quantifies over every connected finite simple graph of order at least three and asserts an invariant feasible maximizer. The settling declaration uses the source definitions of weighted Laplacian, algebraic connectivity, harmonic effective resistance, total resistance, feasibility and edgewise automorphism invariance, and states the exact negation at $K_{2,3}$.

## Route

For the family $K_{2,m}$ with hubs $u,v$ and leaves $x_i$, let $B_m$ have conductance $2$ on the $u$-edges and $1$ on the $v$-edges. The route recorded in issue #15242 is:

1. For every $m\ge3$, the leaf-difference vector is a Fiedler vector of $B_m$ with $\lambda_2(B_m)=3$. The quadratic-form identity on the subspace orthogonal to constants is a sum of squares, so every Rayleigh quotient is at least $3$ and the leaf-difference vector attains $3$. The unweighted graph has $\lambda_2=2$.
2. Explicit harmonic voltages give
   $r(u,v)=3/(2m)$, $r(u,x_i)=(2m+1)/(6m)$,
   $r(v,x_i)=(m+2)/(3m)$ and $r(x_i,x_j)=2/3$. Thus
   $R(B_m)=(2m^3+2m^2+5m+9)/(6m)$, while the unweighted value is $D_m/(2m)$ for $D_m=m^3+m^2+2m+4$.
3. Scaling conductances by $c$ sends total resistance to $R/c$ and $\lambda_2$ to $c\lambda_2$. With
   $c_m=(2m^3+2m^2+5m+9)/(3D_m)$, the scaled assignment is feasible and
   $\lambda_2=3c_m=2+(m+1)/D_m>2$.
4. Leaf permutations and the hub swap act transitively on the edges. An invariant edge weighting is therefore constant, and feasibility forces that constant to be $1$, so every invariant feasible assignment has $\lambda_2=2$.

The module specializes this route to $m=3$: conductances $32/23$ and $16/23$ give $R=23/3$ and $\lambda_2=48/23$, while invariant feasibility forces the unweighted value $2$.

The three Lean elaboration repairs preserve the source's meaning. `harmonicExt` chooses a harmonic vector when one exists and is zero otherwise; existence and uniqueness are proved for every pair used by `totalRes` on positive $K_{2,3}$. `pairRes` orients each unordered pair by `min` and `max`. `Feasible` and `AutInvariant` constrain edges only, and `invariants_congr` shows that edgewise equality suffices.

## Falsifier

A failure of the kernel-checked declaration `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.result` would invalidate this settlement. Its type is `¬ claim`, with `claim` the source-aligned universal assertion. The module's public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

## Evidence

- **Kernel-checked instance.** The frozen declaration `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.result` proves `¬ claim` at $K_{2,3}$ in Lean. Its axiom closure is contained in `{propext, Classical.choice, Quot.sound}`.
- **Exact computation.** The experiment entry [`docs/reports/cruz-menendez-2023-fiedler-resistance-invariant-weights/check.py`](https://github.com/the-omega-institute/trureturing-experiments/tree/23d1becaec1b4d039d1fb77f9a609a22e663e98e/docs/reports/cruz-menendez-2023-fiedler-resistance-invariant-weights) was run with `python3 check.py` and exited 0 (`bad= 0`). The script sha256 is `885d090ffe7213ed35c77a5763df657e55b50c6efb1130945e75e92f68e8173f`. It checks the exact formulas and spectra for $m=3,\dots,8$, including $\lambda_2=48/23$ and $R=23/3$ at $m=3$.
- **Literature.** The source is arXiv:2306.08187v1, Section 5; the complete-graph result is in Menéndez-Conde, *Pädi Bol. Cient. ICBI* 14(28) (2027).

## Triage

The settling node carries `OpenProblemResolutionClaim(Refuted)` for issue #15242. The rows below keep kernel evidence, the paper argument and the experiment computation distinct.

### Mechanism (proved)

- **Kernel-checked instance.** `result` proves the $K_{2,3}$ witness: the asymmetric conductances preserve $R=R(K_{2,3})$, give $\lambda_2=48/23>2$, and invariant feasible assignments have value $2$. This is the formal refutation mechanism for the named instance.
- **Prose proof for every $m\ge3$.** The four route steps in `## Route` give the family mechanism: the asymmetric hub weighting preserves the leaf-difference Fiedler vector, raises the scale-invariant product $\lambda_2R$, scaling restores the unweighted resistance, and edge transitivity forces invariant feasible assignments to be unweighted. This family extension is a paper-level derivation recorded in the preregistration, not a theorem stated by this Lean module.
- **Averaging boundary.** For $m=3$, the witness and its hub-swap average give the constant conductance $24/23$. By the scaling law in route step 3 its total resistance is $(23/24)R(K_{2,3})\ne R(K_{2,3})$. Thus automorphism averaging does not preserve the resistance level set. Under Fiedler's total-weight constraint the averaging argument does apply because that constraint is linear and $\lambda_2$ is concave in the weights; this neighbouring statement is source-level context.

### Family (proved in prose; computed)

- **Prose proof for every $m\ge3$.** The route steps 1–4 establish in prose that the scaled assignment has
  $$\lambda_2=2+\frac{m+1}{D_m},\qquad D_m=m^3+m^2+2m+4,$$
  and that every invariant feasible assignment is unweighted with value $2$. This is proved in the route argument, not in Lean for arbitrary $m$.
- **Exact computation for $m=3,\dots,8$.** The experiment entry named in `## Evidence` recomputes the spectra, harmonic resistances, scaling and edge-transitivity checks on exactly that range; the command is `python3 check.py`, exit 0, script sha256 `885d090ffe7213ed35c77a5763df657e55b50c6efb1130945e75e92f68e8173f`.

### What survives

- **$P_3$ source result (proved by the source).** Theorem 5.1 assumes $1/c_1+1/c_2=2$ and proves $\lambda_2(P_3;\omega)\le 1$, with equality iff $c_1=c_2=1$.
- **Printed $P_4$ optimizer (computed: inconsistent with the stated resistance constraint).** The source's Theorem 5.5 prints
  $$d_1=d_3=\frac{13\sqrt3}{5(\sqrt3-1)},\qquad d_2=\frac5{26}\left(6-(\sqrt3-1)\right),$$
  alongside the constraint $3/d_1+4/d_2+3/d_3=10$. Since $1<\sqrt3<2$ gives $d_1>26/5$ and $d_2>25/26$,
  $$\frac6{d_1}+\frac4{d_2}<\frac{15}{13}+\frac{104}{25}=\frac{1727}{325}<10,$$
  so the printed weights do not satisfy that constraint; the gap is exact rather than rounding.
- **$P_4$ invariant-end-edge conclusion (proved by the source).** The source's Lemma `simetriaP4` and its following corollary prove that any $P_4$ maximizer under the fixed-total-resistance problem has equal end weights $c_1=c_3$, independently of the printed numerical values; the end-edge conclusion therefore survives.
- **Correct $P_4$ optimizer (open).** No corrected optimizer is recorded here without an exact verification.
- **Complete graphs (proved by the follow-up).** Menéndez-Conde's follow-up proves that constant weights solve the corresponding constrained problem for complete graphs. This is a neighbouring graph class and is not a theorem of the Lean module.

### Open

- Whether the constrained maximum is attained at all on $K_{2,m}$, and its value beyond the exhibited feasible value, remains open.
- Which graph classes beyond $P_3$, $P_4$ and complete graphs have invariant maximizers remains open.

## ASSUMED-UNVERIFIED

The source and follow-up were checked through the cited versions and the preregistered literature screen. Exhaustive literature coverage, publication priority and a general theorem for all $m\ge3$ remain unverified beyond the route argument and the exact experiment range.
